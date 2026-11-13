//! Checks that the secret copies rind-aws-lc-rs keeps on the heap, beyond
//! the rind keys it wraps, are wiped before they are freed.
//!
//! rind's own `tests/zeroing.rs` checks that its keys wipe themselves. This
//! one records the blocks freed while the values that held a secret are
//! dropped, and checks none still holds it. Inline values are boxed so they
//! live on the heap too.
//!
//! The wipe is opt-in, so these tests build only with the `wipe` feature.

#![cfg(feature = "wipe")]

#[path = "../../rind/tests/freed/mod.rs"]
mod freed;

use rind_aws_lc_rs::encoding::{
    AsBigEndian, AsDer, Curve25519SeedBin, EcPrivateKeyBin, EcPrivateKeyRfc5915Der, Pkcs8V1Der,
    Pkcs8V2Der,
};
use rind_aws_lc_rs::{agreement, cipher, kem, rsa, signature};

#[global_allocator]
static ALLOCATOR: freed::Record = freed::Record;

/// How many bytes of a secret are looked for.
const NEEDLE_LEN: usize = 16;

/// Counts the blocks freed while `drop` runs that still hold the first
/// bytes of `secret`.
fn leaks(secret: &[u8], drop: impl FnOnce()) -> usize {
    let needle = &secret[..NEEDLE_LEN];
    let ((), blocks) = freed::freed(drop);
    blocks
        .iter()
        .filter(|block| block.windows(NEEDLE_LEN).any(|w| w == needle))
        .count()
}

/// Bytes unlikely to appear anywhere else.
fn distinct<const N: usize>(start: u8) -> [u8; N] {
    core::array::from_fn(|i| start.wrapping_add((i as u8).wrapping_mul(29)))
}

/// The check sees a secret left on the heap, so a clean result means something.
#[test]
fn detects_a_leak() {
    let secret: [u8; 32] = distinct(1);
    let copy = secret.to_vec();
    assert_eq!(leaks(&secret, || drop(copy)), 1);
}

/// A decrypting key's PKCS#8 copy, with every algorithm's key cached and the
/// last clone dropped.
#[test]
fn rsa_oaep() {
    let pkcs8 = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");
    // The last bytes are the CRT coefficient, which only the private key holds.
    let secret = &pkcs8[pkcs8.len() - NEEDLE_LEN..];
    let leaked = leaks(secret, || {
        let key = rsa::PrivateDecryptingKey::from_pkcs8(pkcs8).unwrap();
        let public = rsa::OaepPublicEncryptingKey::new(key.public_key()).unwrap();
        let decrypting = rsa::OaepPrivateDecryptingKey::new(key.clone()).unwrap();
        for algorithm in [
            &rsa::OAEP_SHA1_MGF1SHA1,
            &rsa::OAEP_SHA256_MGF1SHA256,
            &rsa::OAEP_SHA384_MGF1SHA384,
            &rsa::OAEP_SHA512_MGF1SHA512,
        ] {
            let mut ciphertext = [0; 256];
            let ciphertext = public
                .encrypt(algorithm, b"message", &mut ciphertext, None)
                .unwrap();
            let mut plaintext = [0; 256];
            let plaintext = decrypting
                .decrypt(algorithm, ciphertext, &mut plaintext, None)
                .unwrap();
            assert_eq!(plaintext, b"message");
        }
        let der: Pkcs8V1Der<'static> = key.as_der().unwrap();
        assert_eq!(der.as_ref(), pkcs8);
    });
    assert_eq!(leaked, 0);
}

/// An Ed25519 seed, and the PKCS#8 documents and encodings holding it.
#[test]
fn ed25519() {
    let seed: [u8; 32] = distinct(3);
    let leaked = leaks(&seed, || {
        let key = Box::new(signature::Ed25519KeyPair::from_seed_unchecked(&seed).unwrap());
        let exported = Box::new(key.seed().unwrap());
        let bin: Curve25519SeedBin<'static> = exported.as_be_bytes().unwrap();
        assert_eq!(bin.as_ref(), seed);
        let _v1 = key.to_pkcs8v1().unwrap();
        let _v2 = key.to_pkcs8().unwrap();
        let _der_v1: Pkcs8V1Der<'static> = key.as_der().unwrap();
        let _der_v2: Pkcs8V2Der<'static> = key.as_der().unwrap();
    });
    assert_eq!(leaked, 0);
}

/// Key agreement private keys and their encodings.
#[test]
fn agreement() {
    let scalar: [u8; 32] = distinct(5);
    let leaked = leaks(&scalar, || {
        let key = agreement::PrivateKey::from_private_key(&agreement::ECDH_P256, &scalar);
        let key = Box::new(key.unwrap());
        let bin: EcPrivateKeyBin<'static> = key.as_be_bytes().unwrap();
        assert_eq!(bin.as_ref(), scalar);
        let _sec1: EcPrivateKeyRfc5915Der<'static> = key.as_der().unwrap();
        let _pkcs8: Pkcs8V1Der<'static> = key.as_der().unwrap();
    });
    assert_eq!(leaked, 0);

    let seed: [u8; 32] = distinct(7);
    let leaked = leaks(&seed, || {
        let key = agreement::PrivateKey::from_private_key(&agreement::X25519, &seed);
        let key = Box::new(key.unwrap());
        let bin: Curve25519SeedBin<'static> = key.as_be_bytes().unwrap();
        assert_eq!(bin.as_ref(), seed);
    });
    assert_eq!(leaked, 0);
}

/// Raw cipher key bytes, held until a mode expands them.
#[test]
fn cipher() {
    let key_bytes: [u8; 32] = distinct(9);
    let leaked = leaks(&key_bytes, || {
        let key = cipher::UnboundCipherKey::new(&cipher::AES_256, &key_bytes).unwrap();
        drop(Box::new(key));
        let key = cipher::UnboundCipherKey::new(&cipher::AES_256, &key_bytes).unwrap();
        drop(Box::new(cipher::EncryptingKey::ctr(key).unwrap()));
    });
    assert_eq!(leaked, 0);
}

/// An ML-DSA seed, and the PKCS#8 documents that hold it.
#[test]
fn ml_dsa() {
    let seed: [u8; 32] = distinct(11);
    let leaked = leaks(&seed, || {
        let key = Box::new(
            signature::PqdsaKeyPair::from_seed(&signature::ML_DSA_44_SIGNING, &seed).unwrap(),
        );
        let _pkcs8 = key.to_pkcs8v1().unwrap();
        let _der: Pkcs8V1Der<'static> = key.private_key().as_der().unwrap();
    });
    assert_eq!(leaked, 0);
}

/// A generated ML-DSA key, whose seed is read from its own PKCS#8 export
/// before the key, its exports, and the export it was read from are dropped.
#[test]
fn ml_dsa_generated() {
    let key = signature::PqdsaKeyPair::generate(&signature::ML_DSA_65_SIGNING).unwrap();
    let pkcs8 = key.to_pkcs8v1().unwrap();
    let seed: [u8; 32] = pkcs8.as_ref()[pkcs8.as_ref().len() - 32..]
        .try_into()
        .unwrap();
    let leaked = leaks(&seed, move || {
        let _der: Pkcs8V1Der<'static> = key.private_key().as_der().unwrap();
        drop(key);
        drop(pkcs8);
    });
    assert_eq!(leaked, 0);
}

/// An ML-DSA seed loaded from PKCS#8, and the key's exports. The document
/// the test built is dropped after the check.
#[test]
fn ml_dsa_from_pkcs8() {
    let seed: [u8; 32] = distinct(13);
    let pkcs8 = signature::PqdsaKeyPair::from_seed(&signature::ML_DSA_87_SIGNING, &seed)
        .unwrap()
        .to_pkcs8v1()
        .unwrap();
    let leaked = leaks(&seed, || {
        let key = Box::new(
            signature::PqdsaKeyPair::from_pkcs8(&signature::ML_DSA_87_SIGNING, pkcs8.as_ref())
                .unwrap(),
        );
        let _pkcs8 = key.to_pkcs8v1().unwrap();
        let _der: Pkcs8V1Der<'static> = key.private_key().as_der().unwrap();
    });
    assert_eq!(leaked, 0);
}

/// An expanded ML-DSA private key, loaded raw, which the adapter wraps in
/// PKCS#8 itself, and loaded from a PKCS#8 document in expanded form. The
/// needle is FIPS 204's `K`, after `rho`, which the public key repeats.
#[test]
fn ml_dsa_expanded() {
    use aws_lc_rs::encoding::AsRawBytes;

    let raw = aws_lc_rs::signature::PqdsaKeyPair::from_seed(
        &aws_lc_rs::signature::ML_DSA_44_SIGNING,
        &distinct::<32>(17),
    )
    .unwrap()
    .private_key()
    .as_raw_bytes()
    .unwrap()
    .as_ref()
    .to_vec();
    let secret = &raw[32..];
    let leaked = leaks(secret, || {
        let key = Box::new(
            signature::PqdsaKeyPair::from_raw_private_key(&signature::ML_DSA_44_SIGNING, &raw)
                .unwrap(),
        );
        assert!(key.to_pkcs8v1().is_err());
        let mut sig = vec![0; signature::ML_DSA_44_SIGNING.signature_len()];
        key.sign(b"expanded", &mut sig).unwrap();
    });
    assert_eq!(leaked, 0);

    let pkcs8 = expanded_pkcs8(&raw);
    let leaked = leaks(secret, || {
        let key = Box::new(
            signature::PqdsaKeyPair::from_pkcs8(&signature::ML_DSA_44_SIGNING, &pkcs8).unwrap(),
        );
        let mut sig = vec![0; signature::ML_DSA_44_SIGNING.signature_len()];
        key.sign(b"message", &mut sig).unwrap();
    });
    assert_eq!(leaked, 0);
}

/// ML-DSA-44's PKCS#8 v1 in expanded form (RFC 9881).
fn expanded_pkcs8(raw: &[u8]) -> Vec<u8> {
    let len = |n: usize| [0x82, (n >> 8) as u8, n as u8];
    let mut inner = vec![0x04];
    inner.extend(len(raw.len()));
    inner.extend_from_slice(raw);
    let mut body = vec![0x02, 0x01, 0x00];
    // id-ml-dsa-44, 2.16.840.1.101.3.4.3.17
    body.extend([
        0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x11,
    ]);
    body.push(0x04);
    body.extend(len(inner.len()));
    body.extend_from_slice(&inner);
    let mut der = vec![0x30];
    der.extend(len(body.len()));
    der.extend_from_slice(&body);
    der
}

/// An ML-KEM shared secret, on both sides.
#[test]
fn kem() {
    let decapsulation = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
    let (ciphertext, sent) = decapsulation
        .encapsulation_key()
        .unwrap()
        .encapsulate()
        .unwrap();
    let received = decapsulation.decapsulate(ciphertext).unwrap();
    let mut secret = [0; 32];
    secret.copy_from_slice(sent.as_ref());
    assert_eq!(received.as_ref(), secret);
    assert_eq!(leaks(&secret, || drop((sent, received))), 0);
}
