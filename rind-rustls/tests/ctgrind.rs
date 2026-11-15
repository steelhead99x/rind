//! Constant-time checks for each secret path, run under valgrind by
//! `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. rind itself marks the private keys it
//! generates or parses, and the ticket key it is given.

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use rustls::crypto::aws_lc_rs;
use rustls::crypto::cipher::{AeadKey, InboundOpaqueMessage, Iv, OutboundPlainMessage};
use rustls::crypto::tls13::OkmBlock;
use rustls::pki_types::PrivateKeyDer;
use rustls::pki_types::pem::PemObject;
use rustls::{ContentType, ProtocolVersion, SupportedCipherSuite};

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

#[test]
fn key_exchange() {
    for group in rind_rustls::ALL_KX_GROUPS {
        let client = group.start().unwrap();
        let server = group.start_and_complete(client.pub_key()).unwrap();
        let client_secret = client.complete(&server.pub_key).unwrap();

        public(client_secret.secret_bytes());
        public(server.secret.secret_bytes());
        assert_eq!(
            client_secret.secret_bytes(),
            server.secret.secret_bytes(),
            "{:?}",
            group.name()
        );

        // A hybrid client completes its classical part alone when the server
        // picks the classical group.
        let client = group.start().unwrap();
        let Some((name, share)) = client.hybrid_component() else {
            continue;
        };
        let classical = rind_rustls::ALL_KX_GROUPS
            .iter()
            .find(|classical| classical.name() == name)
            .unwrap();
        let server = classical.start_and_complete(share).unwrap();
        let client_secret = client.complete_hybrid_component(&server.pub_key).unwrap();

        public(client_secret.secret_bytes());
        public(server.secret.secret_bytes());
        assert_eq!(
            client_secret.secret_bytes(),
            server.secret.secret_bytes(),
            "{:?}",
            group.name()
        );
    }
}

#[test]
fn tls13_key_schedule() {
    for (suite, reference) in [
        (
            rind_rustls::cipher_suite::TLS13_AES_128_GCM_SHA256,
            aws_lc_rs::cipher_suite::TLS13_AES_128_GCM_SHA256,
        ),
        (
            rind_rustls::cipher_suite::TLS13_AES_256_GCM_SHA384,
            aws_lc_rs::cipher_suite::TLS13_AES_256_GCM_SHA384,
        ),
    ] {
        let (SupportedCipherSuite::Tls13(suite), SupportedCipherSuite::Tls13(reference)) =
            (suite, reference)
        else {
            unreachable!()
        };

        let shared_secret = [0x42; 32];
        let expected = reference
            .hkdf_provider
            .extract_from_secret(Some(b"salt"), &shared_secret)
            .expand_block(&[b"info"]);

        secret(&shared_secret);
        let okm = suite
            .hkdf_provider
            .extract_from_secret(Some(b"salt"), &shared_secret)
            .expand_block(&[b"info"]);

        public(okm.as_ref());
        assert_eq!(okm.as_ref(), expected.as_ref());
    }
}

#[cfg(feature = "tls12")]
#[test]
fn tls12_prf() {
    for (suite, reference) in [
        (
            rind_rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
            aws_lc_rs::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
        ),
        (
            rind_rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
            aws_lc_rs::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
        ),
    ] {
        let (SupportedCipherSuite::Tls12(suite), SupportedCipherSuite::Tls12(reference)) =
            (suite, reference)
        else {
            unreachable!()
        };

        let shared_secret = [0x42; 48];
        let mut expected = [0u8; 48];
        reference
            .prf_provider
            .for_secret(&mut expected, &shared_secret, b"label", b"seed");

        secret(&shared_secret);
        let mut output = [0u8; 48];
        suite
            .prf_provider
            .for_secret(&mut output, &shared_secret, b"label", b"seed");

        public(&output);
        assert_eq!(output, expected);
    }
}

/// A record key of `len` bytes. rustls builds keys shorter than 32 bytes only
/// through its key schedule, so expand one with a TLS 1.3 AEAD of that length.
fn record_key(len: usize) -> AeadKey {
    let suite = rind_rustls::ALL_CIPHER_SUITES
        .iter()
        .find_map(|suite| match suite {
            SupportedCipherSuite::Tls13(suite) if suite.aead_alg.key_len() == len => Some(suite),
            _ => None,
        })
        .unwrap();
    let expander = suite
        .hkdf_provider
        .expander_for_okm(&OkmBlock::new(&[0x42; 32]));
    rustls::internal::derive_traffic_key(&*expander, suite.aead_alg)
}

#[test]
fn record_protection() {
    for suite in rind_rustls::ALL_CIPHER_SUITES {
        let key_len = match suite {
            SupportedCipherSuite::Tls13(suite) => suite.aead_alg.key_len(),
            SupportedCipherSuite::Tls12(suite) => suite.aead_alg.key_block_shape().enc_key_len,
        };
        // Each direction consumes its own copy of the key.
        let (key, decrypt_key) = (record_key(key_len), record_key(key_len));
        secret(key.as_ref());
        secret(decrypt_key.as_ref());
        let iv = [0x24; 12];

        let (mut encrypter, mut decrypter) = match suite {
            SupportedCipherSuite::Tls13(suite) => (
                suite.aead_alg.encrypter(key, Iv::new(iv)),
                suite.aead_alg.decrypter(decrypt_key, Iv::new(iv)),
            ),
            SupportedCipherSuite::Tls12(suite) => {
                let shape = suite.aead_alg.key_block_shape();
                let (fixed, explicit) = iv.split_at(shape.fixed_iv_len);
                let explicit = &explicit[..shape.explicit_nonce_len];
                (
                    suite.aead_alg.encrypter(key, fixed, explicit),
                    suite.aead_alg.decrypter(decrypt_key, fixed),
                )
            }
        };

        let message = OutboundPlainMessage {
            typ: ContentType::ApplicationData,
            version: ProtocolVersion::TLSv1_2,
            payload: b"hello"[..].into(),
        };
        let encrypted = encrypter.encrypt(message, 7).unwrap();
        let mut encoded = encrypted.encode();
        public(&encoded[..]);

        // Strip the record header the decrypter is handed without.
        let (typ, version) = (ContentType::from(encoded[0]), ProtocolVersion::TLSv1_2);
        let payload = &mut encoded[5..];
        let decrypted = decrypter
            .decrypt(InboundOpaqueMessage::new(typ, version, payload), 7)
            .unwrap();

        public(decrypted.payload);
        assert_eq!(decrypted.payload, b"hello", "{:?}", suite.suite());
    }
}

#[test]
fn quic_protection() {
    use rustls::Side;
    use rustls::quic::{Keys, Version};

    for suite in [
        rind_rustls::cipher_suite::TLS13_AES_128_GCM_SHA256,
        rind_rustls::cipher_suite::TLS13_AES_256_GCM_SHA384,
        rind_rustls::cipher_suite::TLS13_CHACHA20_POLY1305_SHA256,
    ] {
        let SupportedCipherSuite::Tls13(suite) = suite else {
            unreachable!()
        };
        let label = suite.common.suite;
        let quic = suite.quic.unwrap();

        // Initial keys come from a public connection ID, but deriving them from
        // a secret one is the only public path to packet and header keys at
        // each suite's own key length.
        let secret_id = [0x42; 20];
        secret(&secret_id);
        let client = Keys::initial(Version::V1, suite, quic, &secret_id, Side::Client);
        let server = Keys::initial(Version::V1, suite, quic, &secret_id, Side::Server);
        let (send, recv) = (client.local, server.remote);

        let header = b"header";
        let mut packet = *b"payload";
        let tag = send
            .packet
            .encrypt_in_place(7, header, &mut packet)
            .unwrap();
        public(&packet);
        public(tag.as_ref());

        let mut sealed = [&packet[..], tag.as_ref()].concat();
        let opened = recv
            .packet
            .decrypt_in_place(7, header, &mut sealed)
            .unwrap();
        public(opened);
        assert_eq!(opened, b"payload", "{label:?}");

        let sample = [0x11; 16];
        let (mut first, mut packet_number) = (0xc3, [1, 2, 3, 4]);
        send.header
            .encrypt_in_place(&sample, &mut first, &mut packet_number)
            .unwrap();
        public(&first);
        public(&packet_number);
        recv.header
            .decrypt_in_place(&sample, &mut first, &mut packet_number)
            .unwrap();
        public(&first);
        public(&packet_number);
        assert_eq!((first, packet_number), (0xc3, [1, 2, 3, 4]), "{label:?}");
    }
}

#[test]
fn signing() {
    let provider = rind_rustls::default_provider();
    let algorithms = provider.signature_verification_algorithms;

    for slug in [
        "rsa-2048",
        "rsa-3072",
        "rsa-4096",
        "ecdsa-p256",
        "ecdsa-p384",
        "ecdsa-p521",
        "ed25519",
    ] {
        let path = format!("{}/tests/keys/{slug}/end.key", env!("CARGO_MANIFEST_DIR"));
        let key = PrivateKeyDer::from_pem_file(path).unwrap();
        let key = provider.key_provider.load_private_key(key).unwrap();
        let spki = key.public_key().unwrap();
        public(spki.as_ref());

        let mut signed = 0;
        for &(scheme, verifiers) in algorithms.mapping {
            let Some(signer) = key.choose_scheme(&[scheme]) else {
                continue;
            };
            let signature = signer.sign(b"message").unwrap();
            public(&signature[..]);

            verifiers[0]
                .verify_signature(subject_public_key(&spki), b"message", &signature)
                .unwrap_or_else(|e| panic!("{slug} {scheme:?}: {e:?}"));
            signed += 1;
        }
        assert_ne!(signed, 0, "{slug}");
    }
}

/// The key bits of a DER SubjectPublicKeyInfo, the form signature algorithms verify with.
fn subject_public_key(spki: &[u8]) -> &[u8] {
    // Splits one DER element into its contents and whatever follows it.
    fn element(der: &[u8]) -> (&[u8], &[u8]) {
        let (len, header) = match der[1] {
            len @ 0..=0x7f => (usize::from(len), 2),
            0x81 => (usize::from(der[2]), 3),
            0x82 => (usize::from(u16::from_be_bytes([der[2], der[3]])), 4),
            _ => unreachable!(),
        };
        der[header..].split_at(len)
    }

    let (fields, _) = element(spki);
    let (_algorithm, rest) = element(fields);
    let (bits, _) = element(rest);
    // The first byte counts unused bits, always zero for a key.
    &bits[1..]
}

#[cfg(feature = "std")]
#[test]
fn tickets() {
    let ticketer = rind_rustls::Ticketer::new().unwrap();
    let ticket = ticketer.encrypt(b"session state").unwrap();
    public(&ticket[..]);

    let state = ticketer.decrypt(&ticket).unwrap();
    public(&state[..]);
    assert_eq!(state, b"session state");
}

#[test]
fn hpke() {
    use rustls::crypto::hpke::HpkePrivateKey;

    for suite in rind_rustls::hpke::ALL_SUPPORTED_SUITES {
        let (public_key, private_key) = suite.generate_key_pair().unwrap();
        let (enc, ciphertext) = suite
            .seal(b"info", b"aad", b"plaintext", &public_key)
            .unwrap();

        // The private key's bytes, as rustls hands them back to open.
        let private_key = HpkePrivateKey::from(private_key.secret_bytes().to_vec());
        secret(private_key.secret_bytes());
        let mut opener = suite.setup_opener(&enc, b"info", &private_key).unwrap();
        let plaintext = opener.open(b"aad", &ciphertext).unwrap();
        public(&plaintext[..]);
        assert_eq!(plaintext, b"plaintext", "{:?}", suite.suite());
    }
}
