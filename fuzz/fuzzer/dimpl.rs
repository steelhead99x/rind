//! Feeds rind-dimpl what a DTLS peer controls, through the traits dimpl
//! calls, and compares each answer with dimpl's own aws-lc-rs provider. Then
//! drives whole handshakes between two rind endpoints, editing the packets in
//! flight, so the same code is reached through dimpl's parsing.
//!
//! Keys come at the lengths each suite names, as dimpl derives them.

#![no_main]

use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use arrayvec::ArrayVec;
use dimpl::crypto::{
    Aad, Buf, CryptoProvider, HashAlgorithm, Nonce, SignatureAlgorithm, SupportedKxGroup, TmpBuf,
    aws_lc_rs,
};
use dimpl::{Config, Dtls, DtlsCertificate, Output};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};

mod edit;
use edit::Edit;

fuzz_target!(|input: Input| match input {
    Input::Record {
        dtls13,
        suite,
        key,
        nonce,
        aad,
        plain,
        edit,
    } => record(dtls13, suite, &key, nonce, &aad, &plain, &edit),
    Input::RecordNumber { suite, key, sample } => record_number(suite, &key, &sample),
    Input::KeyShare { group, share } => key_share(group, share),
    Input::Certificate {
        hash,
        certificate,
        data,
        signature,
    } => verify(hash, certificate, &data, signature),
    Input::Handshake(handshake) => handshake.run(),
});

#[derive(Arbitrary, Debug)]
enum Input {
    /// A record the peer sealed, then edited. DTLS 1.2's additional data is
    /// 13 bytes; DTLS 1.3's is the record's 3 to 5 byte header.
    Record {
        dtls13: bool,
        suite: u8,
        key: [u8; 32],
        nonce: [u8; 12],
        aad: [u8; 13],
        plain: Vec<u8>,
        edit: Edit,
    },
    /// A DTLS 1.3 record's ciphertext sample, which masks its record number.
    RecordNumber {
        suite: u8,
        key: [u8; 32],
        sample: [u8; 16],
    },
    /// The peer's key share.
    KeyShare {
        group: u8,
        share: Share,
    },
    /// The peer's certificate and its signature over the handshake.
    Certificate {
        hash: bool,
        certificate: PeerCertificate,
        data: Vec<u8>,
        signature: PeerSignature,
    },
    Handshake(Handshake),
}

/// A key share: the fuzzer's bytes, or a valid one edited.
#[derive(Arbitrary, Debug)]
enum Share {
    Raw(Vec<u8>),
    Edited(Edit),
}

/// A certificate: the fuzzer's bytes, or a test certificate edited.
#[derive(Arbitrary, Debug)]
enum PeerCertificate {
    Raw(Vec<u8>),
    Test(bool, Edit),
}

/// A signature: the fuzzer's bytes, or the test key's over the data, edited.
#[derive(Arbitrary, Debug)]
enum PeerSignature {
    Raw(Vec<u8>),
    Signed(Edit),
}

fn rind() -> &'static CryptoProvider {
    static PROVIDER: OnceLock<CryptoProvider> = OnceLock::new();
    PROVIDER.get_or_init(rind_dimpl::default_provider)
}

fn baseline() -> &'static CryptoProvider {
    static PROVIDER: OnceLock<CryptoProvider> = OnceLock::new();
    PROVIDER.get_or_init(aws_lc_rs::default_provider)
}

/// A failed open leaves each byte as the peer sent it or zero.
fn assert_no_plaintext(sent: &[u8], left: &[u8]) {
    assert!(
        sent.iter().zip(left).all(|(s, l)| s == l || *l == 0),
        "a failed open left other bytes than the peer's"
    );
}

fn record(
    dtls13: bool,
    suite: u8,
    key: &[u8; 32],
    nonce: [u8; 12],
    aad: &[u8; 13],
    plain: &[u8],
    edit: &Edit,
) {
    // The cipher each provider makes for the suite, keyed at its length.
    let (ours, theirs, aad) = match dtls13 {
        false => {
            let suites = rind().cipher_suites;
            let ours = suites[usize::from(suite) % suites.len()];
            let theirs = baseline()
                .cipher_suites
                .iter()
                .find(|theirs| theirs.suite() == ours.suite())
                .expect("aws-lc-rs has every suite rind-dimpl has");
            let key = &key[..ours.key_lengths().1];
            let ciphers = [ours, *theirs].map(|s| s.create_cipher(key).unwrap());
            let [ours, theirs] = ciphers;
            (ours, theirs, &aad[..])
        }
        true => {
            let suites = rind().dtls13_cipher_suites;
            let ours = suites[usize::from(suite) % suites.len()];
            let theirs = baseline()
                .dtls13_cipher_suites
                .iter()
                .find(|theirs| theirs.suite() == ours.suite())
                .expect("aws-lc-rs has every suite rind-dimpl has");
            let key = &key[..ours.key_len()];
            let ciphers = [ours, *theirs].map(|s| s.create_cipher(key).unwrap());
            let [ours, theirs] = ciphers;
            (ours, theirs, &aad[..3 + usize::from(aad[0]) % 3])
        }
    };
    let aad = || Aad(ArrayVec::try_from(aad).unwrap());

    let mut sealed = Buf::new();
    sealed.extend_from_slice(plain);
    let mut theirs = theirs;
    theirs.encrypt(&mut sealed, aad(), Nonce(nonce)).unwrap();
    let mut sealed = sealed.into_vec();
    let edited = edit.apply(&mut sealed);

    let open = |cipher: &mut Box<dyn dimpl::crypto::Cipher>| {
        let mut buf = sealed.clone();
        let mut tmp = TmpBuf::new(&mut buf);
        let opened = cipher
            .decrypt(&mut tmp, aad(), Nonce(nonce))
            .map(|()| tmp.as_ref().to_vec());
        if opened.is_err() {
            assert_no_plaintext(&sealed, &buf);
        }
        opened.ok()
    };
    let mut ours = ours;
    let opened = open(&mut ours);
    assert_eq!(opened, open(&mut theirs));
    if !edited {
        assert_eq!(opened.as_deref(), Some(plain), "an unedited record opens");
    }
}

fn record_number(suite: u8, key: &[u8; 32], sample: &[u8; 16]) {
    let suites = rind().dtls13_cipher_suites;
    let ours = suites[usize::from(suite) % suites.len()];
    let theirs = baseline()
        .dtls13_cipher_suites
        .iter()
        .find(|theirs| theirs.suite() == ours.suite())
        .expect("aws-lc-rs has every suite rind-dimpl has");
    let key = &key[..ours.key_len()];
    // dimpl XORs at most two mask bytes over the sequence number, and aws-lc-rs's
    // ChaCha20 mask fills only the first five, as QUIC's does.
    assert_eq!(
        ours.encrypt_sn(key, sample)[..5],
        theirs.encrypt_sn(key, sample)[..5]
    );
}

fn key_share(group: u8, share: Share) {
    let ours = rind().kx_groups[usize::from(group) % rind().kx_groups.len()];
    let theirs = *baseline()
        .kx_groups
        .iter()
        .find(|theirs| theirs.name() == ours.name())
        .expect("aws-lc-rs has every group rind-dimpl has");

    let share = match share {
        Share::Raw(share) => share,
        Share::Edited(edit) => {
            let mut share = theirs
                .start_exchange(Buf::new())
                .unwrap()
                .pub_key()
                .to_vec();
            edit.apply(&mut share);
            share
        }
    };

    // The secrets are random, so only whether each accepts the share compares.
    let complete = |group: &dyn SupportedKxGroup| {
        let mut out = Buf::new();
        group
            .start_exchange(Buf::new())
            .unwrap()
            .complete(&share, &mut out)
            .is_ok()
    };
    assert_eq!(complete(ours), complete(theirs), "{:?}", ours.name());
}

/// A self-signed certificate and its PKCS#8 key on P-256, then on P-384.
fn certificates() -> &'static [DtlsCertificate; 2] {
    static CERTIFICATES: OnceLock<[DtlsCertificate; 2]> = OnceLock::new();
    CERTIFICATES.get_or_init(|| {
        [
            &rcgen::PKCS_ECDSA_P256_SHA256,
            &rcgen::PKCS_ECDSA_P384_SHA384,
        ]
        .map(|algorithm| {
            let key = rind_rcgen::KeyPair::generate_for(algorithm).unwrap();
            let certificate = rcgen::CertificateParams::new(Vec::<String>::new())
                .unwrap()
                .self_signed(&key)
                .unwrap();
            DtlsCertificate {
                certificate: certificate.der().to_vec(),
                private_key: key.serialize_der(),
            }
        })
    })
}

fn verify(hash: bool, certificate: PeerCertificate, data: &[u8], signature: PeerSignature) {
    let hash = match hash {
        false => HashAlgorithm::SHA256,
        true => HashAlgorithm::SHA384,
    };
    let (certificate, signature) = match certificate {
        PeerCertificate::Raw(certificate) => match signature {
            PeerSignature::Raw(signature) => (certificate, signature),
            PeerSignature::Signed(_) => return,
        },
        PeerCertificate::Test(curve, edit) => {
            let test = &certificates()[usize::from(curve)];
            let mut certificate = test.certificate.clone();
            edit.apply(&mut certificate);
            let signature = match signature {
                PeerSignature::Raw(signature) => signature,
                PeerSignature::Signed(edit) => {
                    let mut key = baseline()
                        .key_provider
                        .load_private_key(&test.private_key)
                        .unwrap();
                    let mut signature = Buf::new();
                    // Each key signs with its own curve's hash.
                    if key.sign(data, hash, &mut signature).is_err() {
                        return;
                    }
                    let mut signature = signature.into_vec();
                    edit.apply(&mut signature);
                    signature
                }
            };
            (certificate, signature)
        }
    };

    let verify = |provider: &CryptoProvider| {
        provider
            .signature_verification
            .verify_signature(
                &certificate,
                data,
                &signature,
                hash,
                SignatureAlgorithm::ECDSA,
            )
            .is_ok()
    };
    assert_eq!(verify(rind()), verify(baseline()));
}

/// A handshake between a rind client and a rind server, with the packets the
/// edits name changed in flight.
#[derive(Arbitrary, Debug)]
struct Handshake {
    dtls13: bool,
    suite: u8,
    group: u8,
    client_curve: bool,
    server_curve: bool,
    edits: Vec<(u8, Edit)>,
}

impl Handshake {
    fn run(&self) {
        let builder = Config::builder()
            .with_crypto_provider(rind_dimpl::default_provider())
            .kx_groups(&[
                rind().kx_groups[usize::from(self.group) % rind().kx_groups.len()].name(),
            ]);
        let builder = match self.dtls13 {
            false => {
                let suites = rind().cipher_suites;
                builder
                    .dtls12_cipher_suites(&[suites[usize::from(self.suite) % suites.len()].suite()])
            }
            true => {
                let suites = rind().dtls13_cipher_suites;
                builder
                    .dtls13_cipher_suites(&[suites[usize::from(self.suite) % suites.len()].suite()])
            }
        };
        let config = Arc::new(builder.build().unwrap());

        let now = Instant::now();
        let endpoint = |curve: bool| {
            let certificate = certificates()[usize::from(curve)].clone();
            match self.dtls13 {
                false => Dtls::new_12(config.clone(), certificate, now),
                true => Dtls::new_13(config.clone(), certificate, now),
            }
        };
        let mut endpoints = [endpoint(self.client_curve), endpoint(self.server_curve)];
        endpoints[0].set_active(true);
        endpoints[1].set_active(false);

        let mut index = 0u8;
        let mut connected = [false; 2];
        let mut sent_data = false;
        for turn in 0..16 {
            let now = now + Duration::from_millis(10 * turn);
            for (side, connected) in connected.iter_mut().enumerate() {
                let [from, to] = match side {
                    0 => endpoints.each_mut(),
                    _ => {
                        let [client, server] = endpoints.each_mut();
                        [server, client]
                    }
                };
                if from.handle_timeout(now).is_err() {
                    return;
                }
                let (packets, done) = poll(from);
                *connected |= done;
                for mut packet in packets {
                    for (target, edit) in &self.edits {
                        if target % 32 == index {
                            edit.apply(&mut packet);
                        }
                    }
                    index = index.wrapping_add(1);
                    if to.handle_packet(&packet).is_err() {
                        return;
                    }
                }
            }
            if connected == [true; 2] && !sent_data {
                sent_data = true;
                if endpoints[0].send_application_data(b"from client").is_err()
                    || endpoints[1].send_application_data(b"from server").is_err()
                {
                    return;
                }
            }
        }
    }
}

/// The packets `dtls` has to send, and whether it reported being connected.
fn poll(dtls: &mut Dtls) -> (Vec<Vec<u8>>, bool) {
    let mut buf = vec![0u8; 2048];
    let mut packets = Vec::new();
    let mut connected = false;
    loop {
        match dtls.poll_output(&mut buf) {
            Output::Packet(p) => packets.push(p.to_vec()),
            Output::Connected => connected = true,
            Output::Timeout(_) => return (packets, connected),
            Output::BufferTooSmall { needed } => buf.resize(needed, 0),
            _ => {}
        }
    }
}
