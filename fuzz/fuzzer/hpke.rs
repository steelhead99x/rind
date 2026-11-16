#![no_main]

//! HPKE against rustls's aws-lc-rs provider, which builds RFC 9180 from
//! aws-lc's primitives (aws-lc-rs exposes no HPKE of its own): each side
//! opens what the other seals, and a tampered encapsulated key or ciphertext
//! fails on both or opens to the same plaintext on both.

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::hpke::*;
use rustls::crypto::aws_lc_rs::hpke::ALL_SUPPORTED_SUITES;
use rustls::crypto::hpke::{EncapsulatedSecret, HpkePrivateKey, HpkePublicKey};

mod edit;

/// Ours, in the order of aws-lc-rs's `ALL_SUPPORTED_SUITES`.
const SUITES: [(&Kem, Suite); 12] = [
    suite(&DHKEM_P256_HKDF_SHA256, &HKDF_SHA256, &AES_128_GCM),
    suite(&DHKEM_P256_HKDF_SHA256, &HKDF_SHA256, &AES_256_GCM),
    suite(&DHKEM_P256_HKDF_SHA256, &HKDF_SHA256, &CHACHA20_POLY1305),
    suite(&DHKEM_P384_HKDF_SHA384, &HKDF_SHA384, &AES_128_GCM),
    suite(&DHKEM_P384_HKDF_SHA384, &HKDF_SHA384, &AES_256_GCM),
    suite(&DHKEM_P384_HKDF_SHA384, &HKDF_SHA384, &CHACHA20_POLY1305),
    suite(&DHKEM_P521_HKDF_SHA512, &HKDF_SHA512, &AES_128_GCM),
    suite(&DHKEM_P521_HKDF_SHA512, &HKDF_SHA512, &AES_256_GCM),
    suite(&DHKEM_P521_HKDF_SHA512, &HKDF_SHA512, &CHACHA20_POLY1305),
    suite(&DHKEM_X25519_HKDF_SHA256, &HKDF_SHA256, &AES_128_GCM),
    suite(&DHKEM_X25519_HKDF_SHA256, &HKDF_SHA256, &AES_256_GCM),
    suite(&DHKEM_X25519_HKDF_SHA256, &HKDF_SHA256, &CHACHA20_POLY1305),
];

const fn suite(kem: &'static Kem, kdf: &'static Kdf, aead: &'static Aead) -> (&'static Kem, Suite) {
    (kem, Suite { kdf, aead })
}

#[derive(Arbitrary, Debug)]
struct Input {
    suite: u8,
    ikm: Vec<u8>,
    info: Vec<u8>,
    aad: Vec<u8>,
    plaintext: Vec<u8>,
    enc: edit::Edit,
    ciphertext: edit::Edit,
    peer: Vec<u8>,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.suite) % SUITES.len();
    let ((kem, suite), theirs) = (SUITES[index], ALL_SUPPORTED_SUITES[index]);
    let private_key = PrivateKey::derive(kem, &input.ikm).unwrap();
    let public_key = private_key.public_key();
    let their_private = || HpkePrivateKey::from(private_key.to_scalar().as_ref().to_vec());
    let their_public = HpkePublicKey(public_key.as_ref().to_vec());

    // Ours opens what theirs seals, tampered with or not, as theirs does.
    let (enc, ciphertext) = theirs
        .seal(&input.info, &input.aad, &input.plaintext, &their_public)
        .unwrap();
    let mut enc = enc.0;
    let mut ciphertext = ciphertext;
    let changed = input.enc.apply(&mut enc) | input.ciphertext.apply(&mut ciphertext);
    let ours = Recipient::new(suite, &private_key, &enc, &input.info).and_then(|mut recipient| {
        let mut in_out = ciphertext.clone();
        recipient
            .open_in_place(&input.aad, &mut in_out)
            .map(|plaintext| plaintext.to_vec())
    });
    if !changed {
        assert_eq!(ours.as_deref(), Ok(&input.plaintext[..]));
    }
    // Both take or refuse `enc` alike, compressed points included.
    let enc = EncapsulatedSecret(enc);
    if !hybrid(kem, &enc.0) {
        assert_eq!(
            Recipient::new(suite, &private_key, &enc.0, &input.info).is_ok(),
            theirs
                .setup_opener(&enc, &input.info, &their_private())
                .is_ok(),
        );
    }
    let theirs_opened = theirs.open(&enc, &input.info, &input.aad, &ciphertext, &their_private());
    assert_eq!(ours.ok(), theirs_opened.ok());

    // Theirs opens what ours seals.
    let (enc, mut sender) = Sender::new(suite, public_key, &input.info).unwrap();
    let mut sealed = input.plaintext.clone();
    sender
        .seal_in_place_append_tag(&input.aad, &mut sealed)
        .unwrap();
    let enc = EncapsulatedSecret(enc.as_ref().to_vec());
    let opened = theirs.open(&enc, &input.info, &input.aad, &sealed, &their_private());
    assert_eq!(opened.unwrap(), input.plaintext);

    // Both take or refuse a peer's public key alike.
    let ours = PublicKey::new(kem, &input.peer)
        .and_then(|peer| Sender::new(suite, &peer, &input.info))
        .is_ok();
    if input.peer.len() == public_key.as_ref().len() && !hybrid(kem, &input.peer) {
        let theirs = theirs
            .setup_sealer(&input.info, &HpkePublicKey(input.peer))
            .is_ok();
        assert_eq!(ours, theirs);
    } else {
        assert!(!ours);
    }
});

/// Whether `point` is a NIST KEM's point in X9.62's hybrid form, which
/// aws-lc-rs takes and rind refuses everywhere: no consumer sends it, and
/// neither side opens anything under a hybrid `enc`, since the KEM context
/// hashes `enc` as sent and senders send it uncompressed.
fn hybrid(kem: &Kem, point: &[u8]) -> bool {
    !core::ptr::eq(kem, &DHKEM_X25519_HKDF_SHA256) && matches!(point.first(), Some(6 | 7))
}
