//! Constant-time checks for each secret path, run under valgrind by
//! `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. rind itself marks the private keys it
//! generates or parses.

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use dimpl::crypto::{
    Aad, Buf, Cipher, CryptoProvider, HashAlgorithm, Nonce, SignatureAlgorithm, TmpBuf, aws_lc_rs,
};

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

fn rind() -> CryptoProvider {
    rind_dimpl::default_provider()
}

#[test]
fn key_exchange() {
    for group in rind().kx_groups {
        let client = group.start_exchange(Buf::new()).unwrap();
        let server = group.start_exchange(Buf::new()).unwrap();
        let (client_pub, server_pub) = (client.pub_key().to_vec(), server.pub_key().to_vec());

        let mut client_secret = Buf::new();
        client.complete(&server_pub, &mut client_secret).unwrap();
        let mut server_secret = Buf::new();
        server.complete(&client_pub, &mut server_secret).unwrap();

        public(client_secret.as_ref());
        public(server_secret.as_ref());
        assert_eq!(
            client_secret.as_ref(),
            server_secret.as_ref(),
            "{:?}",
            group.name()
        );
    }
}

#[test]
fn hmac() {
    let reference = aws_lc_rs::default_provider();
    for hash in [HashAlgorithm::SHA256, HashAlgorithm::SHA384] {
        let key = [0x42u8; 48];
        let mut expected = [0u8; 48];
        let len = reference
            .hmac_provider
            .hmac(hash, &key, b"data", &mut expected)
            .unwrap();

        secret(&key);
        let mut tag = [0u8; 48];
        assert_eq!(
            rind().hmac_provider.hmac(hash, &key, b"data", &mut tag),
            Ok(len)
        );

        public(&tag);
        assert_eq!(tag[..len], expected[..len], "{hash:?}");
    }
}

#[test]
fn record_protection() {
    let provider = rind();
    for suite in provider.cipher_suites {
        let (_, key_len, _) = suite.key_lengths();
        let key = vec![0x42; key_len];
        secret(&key[..]);
        let cipher = suite.create_cipher(&key).unwrap();
        round_trip(&format!("{:?}", suite.suite()), cipher);
    }
    for suite in provider.dtls13_cipher_suites {
        let key = vec![0x42; suite.key_len()];
        secret(&key[..]);
        let cipher = suite.create_cipher(&key).unwrap();
        round_trip(&format!("{:?}", suite.suite()), cipher);
    }
}

fn round_trip(label: &str, mut cipher: Box<dyn Cipher>) {
    let nonce = Nonce([1; 12]);
    let mut record = Buf::new();
    record.extend_from_slice(b"record");
    cipher
        .encrypt(&mut record, Aad(Default::default()), nonce)
        .unwrap();
    public(record.as_ref());

    let mut opened = record.to_vec();
    let mut buf = TmpBuf::new(&mut opened);
    cipher
        .decrypt(&mut buf, Aad(Default::default()), nonce)
        .unwrap();
    public(buf.as_ref());
    assert_eq!(buf.as_ref(), b"record", "{label}");
}

#[test]
fn record_number_mask() {
    let reference = aws_lc_rs::default_provider();
    for suite in rind().dtls13_cipher_suites {
        let expected = reference
            .dtls13_cipher_suites
            .iter()
            .find(|s| s.suite() == suite.suite())
            .unwrap();
        let sn_key = vec![0x42; suite.key_len()];
        let sample = *b"0123456789abcdef";
        let want = expected.encrypt_sn(&sn_key, &sample);

        secret(&sn_key[..]);
        let mask = suite.encrypt_sn(&sn_key, &sample);

        public(&mask);
        // aws-lc-rs fills only the five bytes QUIC uses for ChaCha20.
        assert_eq!(mask[..5], want[..5], "{:?}", suite.suite());
    }
}

#[test]
fn signing() {
    let provider = rind();
    for algorithm in [
        &rcgen::PKCS_ECDSA_P256_SHA256,
        &rcgen::PKCS_ECDSA_P384_SHA384,
    ] {
        let key = rcgen::KeyPair::generate_for(algorithm).unwrap();
        let cert = rcgen::CertificateParams::new(Vec::<String>::new())
            .unwrap()
            .self_signed(&key)
            .unwrap();
        let pem = key.serialize_pem().into_bytes();
        for encoding in [key.serialize_der(), pem] {
            let mut key = provider.key_provider.load_private_key(&encoding).unwrap();

            for hash in key.supported_hash_algorithms().to_vec() {
                let mut signature = Buf::new();
                key.sign(b"transcript", hash, &mut signature).unwrap();
                public(signature.as_ref());

                provider
                    .signature_verification
                    .verify_signature(
                        cert.der(),
                        b"transcript",
                        &signature,
                        hash,
                        SignatureAlgorithm::ECDSA,
                    )
                    .unwrap();
            }
        }
    }
}
