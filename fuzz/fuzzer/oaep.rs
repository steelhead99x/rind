#![no_main]

//! RSA-OAEP decryption against aws-lc-rs's and RustCrypto's, of ciphertexts
//! aws-lc-rs encrypted and the fuzzer tampered with.
//!
//! All three load the same key, so for every ciphertext they must agree on
//! whether it decrypts and to what. The first byte picks the algorithm, and
//! the rest is the message, the label, and then the edit.

use std::sync::LazyLock;

use aws_lc_rs::rsa::{self as theirs, OaepPrivateDecryptingKey, OaepPublicEncryptingKey};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::rsa as ours;
use rsa::pkcs8::DecodePrivateKey;
use sha2::digest::{Digest, FixedOutputReset};

mod edit;

const PKCS8: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");

/// Each side's algorithms, ours bound to our key, and RustCrypto's
/// decryption under the same hash for the label and MGF1.
const ALGORITHMS: [(&ours::OaepAlgorithm, &theirs::OaepAlgorithm, Independent); 4] = [
    (
        &ours::legacy::OAEP_SHA1,
        &theirs::OAEP_SHA1_MGF1SHA1,
        rustcrypto::<sha1::Sha1>,
    ),
    (
        &ours::OAEP_SHA256,
        &theirs::OAEP_SHA256_MGF1SHA256,
        rustcrypto::<sha2::Sha256>,
    ),
    (
        &ours::OAEP_SHA384,
        &theirs::OAEP_SHA384_MGF1SHA384,
        rustcrypto::<sha2::Sha384>,
    ),
    (
        &ours::OAEP_SHA512,
        &theirs::OAEP_SHA512_MGF1SHA512,
        rustcrypto::<sha2::Sha512>,
    ),
];

/// RustCrypto's decryption of a ciphertext under a label, or `None` if it
/// refuses it.
type Independent = fn(&rsa::PrivateKey, &[u8], &[u8]) -> Option<Vec<u8>>;

fn rustcrypto<D: Digest + FixedOutputReset>(
    key: &rsa::PrivateKey,
    ciphertext: &[u8],
    label: &[u8],
) -> Option<Vec<u8>> {
    key.decrypt(rsa::Oaep::<D>::new_with_label(label), ciphertext)
        .ok()
}

static KEYS: LazyLock<(
    [ours::DecryptingKey; 4],
    OaepPrivateDecryptingKey,
    OaepPublicEncryptingKey,
    rsa::PrivateKey,
)> = LazyLock::new(|| {
    let theirs = theirs::PrivateDecryptingKey::from_pkcs8(PKCS8).unwrap();
    let public = OaepPublicEncryptingKey::new(theirs.public_key()).unwrap();
    (
        ALGORITHMS
            .map(|(algorithm, ..)| ours::DecryptingKey::from_pkcs8(algorithm, PKCS8).unwrap()),
        OaepPrivateDecryptingKey::new(theirs).unwrap(),
        public,
        rsa::PrivateKey::from_pkcs8_der(PKCS8).unwrap(),
    )
});

#[derive(Arbitrary, Debug)]
struct Input {
    algorithm: u8,
    message: Vec<u8>,
    label: Vec<u8>,
    edit: edit::Edit,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.algorithm % 4);
    let (_, theirs_algorithm, independent) = ALGORITHMS[index];
    let (ours, theirs, public, independent_key) = &*KEYS;
    let ours = &ours[index];

    let message = &input.message[..input
        .message
        .len()
        .min(public.max_plaintext_size(theirs_algorithm))];
    let mut ciphertext = vec![0; public.ciphertext_size()];
    public
        .encrypt(
            theirs_algorithm,
            message,
            &mut ciphertext,
            Some(&input.label),
        )
        .unwrap();
    let changed = input.edit.apply(&mut ciphertext);

    let mut plaintext = vec![0; theirs.min_output_size()];
    let expected = theirs
        .decrypt(
            theirs_algorithm,
            &ciphertext,
            &mut plaintext,
            Some(&input.label),
        )
        .ok();
    assert_eq!(
        independent(independent_key, &ciphertext, &input.label).as_deref(),
        expected.as_deref()
    );
    match ours.decrypt(&ciphertext, &input.label) {
        Ok(ours) => assert_eq!(Some(ours.as_ref()), expected.as_deref()),
        Err(e) => {
            assert_eq!(e, rind::Error::DecryptFailed);
            assert_eq!(expected, None);
        }
    }
    if !changed {
        assert_eq!(expected.as_deref(), Some(message));
    }
});
