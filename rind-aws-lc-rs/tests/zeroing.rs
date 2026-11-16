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
use rind_aws_lc_rs::signature::KeyPair as _;
use rind_aws_lc_rs::{agreement, cipher, kem, rsa, signature};

#[global_allocator]
static ALLOCATOR: freed::Record = freed::Record;

/// How many bytes of a secret are looked for.
const NEEDLE_LEN: usize = 16;

/// Whether `block` contains `needle`.
fn holds(block: &[u8], needle: &[u8]) -> bool {
    block.windows(needle.len()).any(|window| window == needle)
}

/// Counts the blocks freed while `drop` runs that still hold the first
/// bytes of `secret`.
fn leaks(secret: &[u8], drop: impl FnOnce()) -> usize {
    leaks_ignoring(secret, None, drop)
}

/// Like [`leaks`], skipping the first freed block that is exactly `allow`,
/// whoever freed it. A second exact copy counts. So does a longer block, and
/// a block that holds `allow` only past its first byte.
///
/// Callers check only that the count is zero. Asserting that a block was
/// skipped would pin the adapter's unwiped copy, so wiping it later would
/// fail the test.
fn leaks_ignoring_document(secret: &[u8], allow: &[u8], drop: impl FnOnce()) -> usize {
    leaks_ignoring(secret, Some(allow), drop)
}

fn leaks_ignoring(secret: &[u8], allow: Option<&[u8]>, drop: impl FnOnce()) -> usize {
    let needle = &secret[..NEEDLE_LEN];
    let ((), blocks) = freed::freed(drop);
    let mut ignored = false;
    let mut leaked = 0;
    for block in &blocks {
        if !holds(block, needle) {
            continue;
        }
        // The same length too: a longer block starts with the document and
        // still holds other bytes.
        if let Some(allow) = allow
            && !ignored
            && block.len() == allow.len()
            && block.starts_with(allow)
        {
            ignored = true;
            continue;
        }
        leaked += 1;
    }
    leaked
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

/// The allowance ignores one block that is exactly the document and nothing
/// else. A second copy counts, and so does a copy with the secret again
/// after it, a block that holds the document past its first byte, a longer
/// block whose extra byte is not the needle, and a block that holds only
/// part of the document.
#[test]
fn ignores_one_document() {
    let secret: [u8; 32] = distinct(3);
    let document = [&[0x30, 0x22, 0x04, 0x20][..], &secret].concat();
    let copies = [document.clone(), document.clone()];
    assert_eq!(
        leaks_ignoring_document(&secret, &document, || drop(copies)),
        1
    );
    let one = document.clone();
    assert_eq!(leaks_ignoring_document(&secret, &document, || drop(one)), 0);
    let longer = [&document[..], &secret].concat();
    assert_eq!(
        leaks_ignoring_document(&secret, &document, || drop(longer)),
        1
    );
    let shifted = [&[0xaa], document.as_slice()].concat();
    assert_eq!(
        leaks_ignoring_document(&secret, &document, || drop(shifted)),
        1
    );
    let padded = [&document[..], &[0xa5]].concat();
    assert_eq!(
        leaks_ignoring_document(&secret, &document, || drop(padded)),
        1
    );
    let partial = document[..document.len() - 1].to_vec();
    assert_eq!(
        leaks_ignoring_document(&secret, &document, || drop(partial)),
        1
    );
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

/// An ML-DSA seed and public key, and the PKCS#8 documents holding the seed,
/// for each parameter set. A clone of the key and of the public key are
/// dropped with the key.
#[test]
fn ml_dsa() {
    for (algorithm, start) in [
        (&signature::ML_DSA_44_SIGNING, 11),
        (&signature::ML_DSA_65_SIGNING, 15),
        (&signature::ML_DSA_87_SIGNING, 19),
    ] {
        let seed: [u8; 32] = distinct(start);
        let public_key = signature::PqdsaKeyPair::from_seed(algorithm, &seed)
            .unwrap()
            .public_key()
            .as_ref()
            .to_vec();
        // The public key's bytes past its public seed `rho`.
        let public_needle = &public_key[32..];
        for needle in [&seed[..], public_needle] {
            let leaked = leaks(needle, || {
                let key = Box::new(signature::PqdsaKeyPair::from_seed(algorithm, &seed).unwrap());
                let _clone = key.clone();
                let _public = key.public_key().clone();
                let _pkcs8 = key.to_pkcs8v1().unwrap();
                let _der: Pkcs8V1Der<'static> = key.private_key().as_der().unwrap();
            });
            assert_eq!(leaked, 0);
        }
    }
}

/// A generated ML-DSA key of each parameter set, whose seed is read from its
/// own PKCS#8 export before the key, its exports, and the export it was read
/// from are dropped.
#[test]
fn ml_dsa_generated() {
    for algorithm in [
        &signature::ML_DSA_44_SIGNING,
        &signature::ML_DSA_65_SIGNING,
        &signature::ML_DSA_87_SIGNING,
    ] {
        let key = signature::PqdsaKeyPair::generate(algorithm).unwrap();
        let pkcs8 = key.to_pkcs8v1().unwrap();
        let seed: [u8; 32] = pkcs8.as_ref()[pkcs8.as_ref().len() - 32..]
            .try_into()
            .unwrap();
        let leaked = leaks(&seed, move || {
            let _der: Pkcs8V1Der<'static> = key.private_key().as_der().unwrap();
            drop(key);
            drop(pkcs8);
        });
        assert_eq!(leaked, 0, "{algorithm:?}");
    }
}

/// An ML-DSA seed of each parameter set, loaded from PKCS#8, and the key's
/// exports. The document the test built is dropped after the check.
#[test]
fn ml_dsa_from_pkcs8() {
    for (algorithm, start) in [
        (&signature::ML_DSA_44_SIGNING, 13),
        (&signature::ML_DSA_65_SIGNING, 17),
        (&signature::ML_DSA_87_SIGNING, 21),
    ] {
        let seed: [u8; 32] = distinct(start);
        let pkcs8 = signature::PqdsaKeyPair::from_seed(algorithm, &seed)
            .unwrap()
            .to_pkcs8v1()
            .unwrap();
        let leaked = leaks(&seed, || {
            let key =
                Box::new(signature::PqdsaKeyPair::from_pkcs8(algorithm, pkcs8.as_ref()).unwrap());
            let _pkcs8 = key.to_pkcs8v1().unwrap();
            let _der: Pkcs8V1Der<'static> = key.private_key().as_der().unwrap();
        });
        assert_eq!(leaked, 0, "{algorithm:?}");
    }
}

/// An expanded ML-DSA private key of each parameter set, loaded raw, which
/// the adapter wraps in PKCS#8 itself, and loaded from a PKCS#8 document in
/// expanded form. A raw key of the wrong length, of another parameter set,
/// or whose parts disagree is refused on the same check. The needle is
/// FIPS 204's `K`, after `rho`, which the public key repeats.
#[test]
fn ml_dsa_expanded() {
    use aws_lc_rs::encoding::AsRawBytes;

    for (theirs, ours, other, oid) in [
        (
            &aws_lc_rs::signature::ML_DSA_44_SIGNING,
            &signature::ML_DSA_44_SIGNING,
            &signature::ML_DSA_65_SIGNING,
            0x11,
        ),
        (
            &aws_lc_rs::signature::ML_DSA_65_SIGNING,
            &signature::ML_DSA_65_SIGNING,
            &signature::ML_DSA_87_SIGNING,
            0x12,
        ),
        (
            &aws_lc_rs::signature::ML_DSA_87_SIGNING,
            &signature::ML_DSA_87_SIGNING,
            &signature::ML_DSA_44_SIGNING,
            0x13,
        ),
    ] {
        let raw = aws_lc_rs::signature::PqdsaKeyPair::from_seed(theirs, &distinct::<32>(17))
            .unwrap()
            .private_key()
            .as_raw_bytes()
            .unwrap()
            .as_ref()
            .to_vec();
        let secret = &raw[32..];
        // `from_raw_private_key` frees the document built by `expanded_pkcs8`
        // in `rind-aws-lc-rs/src/pqdsa.rs`, and that function leaves it
        // unwiped. The first freed block that is exactly that document is
        // skipped, whoever freed it. The check is only that nothing else
        // leaked: requiring the skip would fail once that copy is wiped.
        let pkcs8 = expanded_pkcs8(oid, &raw);
        let leaked = leaks_ignoring_document(secret, &pkcs8, || {
            let key = Box::new(signature::PqdsaKeyPair::from_raw_private_key(ours, &raw).unwrap());
            assert!(key.to_pkcs8v1().is_err());
            let mut sig = vec![0; ours.signature_len()];
            key.sign(b"expanded", &mut sig).unwrap();
        });
        assert_eq!(leaked, 0, "{oid:#x}: {EXPANDED_PKCS8_MUST_MATCH}");

        let leaked = leaks(secret, || {
            let key = Box::new(signature::PqdsaKeyPair::from_pkcs8(ours, &pkcs8).unwrap());
            let mut sig = vec![0; ours.signature_len()];
            key.sign(b"message", &mut sig).unwrap();
        });
        assert_eq!(leaked, 0, "{oid:#x}");

        // A short key and another parameter set return before the document
        // is built. An inconsistent key still builds it, then the load fails.
        // `K` is intact in each, so a heap copy freed on the way out counts.
        let short = &raw[..raw.len() - 1];
        let short_doc = expanded_pkcs8(oid, short);
        let leaked = leaks_ignoring_document(secret, &short_doc, || {
            assert!(signature::PqdsaKeyPair::from_raw_private_key(ours, short).is_err());
        });
        assert_eq!(leaked, 0, "{oid:#x} wrong length");

        let leaked = leaks_ignoring_document(secret, &pkcs8, || {
            assert!(signature::PqdsaKeyPair::from_raw_private_key(other, &raw).is_err());
        });
        assert_eq!(leaked, 0, "{oid:#x} wrong parameter set");

        // `tr` follows `rho` and `K`. Flipping it leaves `K` in place and
        // makes the expanded key inconsistent.
        let mut inconsistent = raw.clone();
        inconsistent[64] ^= 0x01;
        let inconsistent_doc = expanded_pkcs8(oid, &inconsistent);
        let leaked = leaks_ignoring_document(secret, &inconsistent_doc, || {
            assert!(signature::PqdsaKeyPair::from_raw_private_key(ours, &inconsistent).is_err());
        });
        assert_eq!(leaked, 0, "{oid:#x}: {EXPANDED_PKCS8_MUST_MATCH}");
    }
}

/// Shown when a leak may be the test's PKCS#8 bytes disagreeing with the
/// adapter's private encoder.
const EXPANDED_PKCS8_MUST_MATCH: &str =
    "the test's expanded_pkcs8 must match rind-aws-lc-rs/src/pqdsa.rs";

/// An ML-DSA PKCS#8 v1 in expanded form (RFC 9881), for the parameter set
/// whose OID, 2.16.840.1.101.3.4.3.`oid`, ends in `oid`. Its bytes must match
/// the private `expanded_pkcs8` in `rind-aws-lc-rs/src/pqdsa.rs`.
fn expanded_pkcs8(oid: u8, raw: &[u8]) -> Vec<u8> {
    let len = |n: usize| [0x82, (n >> 8) as u8, n as u8];
    let mut inner = vec![0x04];
    inner.extend(len(raw.len()));
    inner.extend_from_slice(raw);
    let mut body = vec![0x02, 0x01, 0x00];
    body.extend([
        0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, oid,
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

/// A smaller set's decapsulation key leaves no stale stack bytes on the heap:
/// held inline in space sized for ML-KEM-1024, its slack would carry what the
/// stack last held, such as another key's seed, past the key's own wipe.
#[test]
fn kem_slack() {
    let stale: [u8; NEEDLE_LEN] = distinct(7);
    for alg in [&kem::ML_KEM_512, &kem::ML_KEM_768] {
        let leaked = leaks(&stale, || {
            paint_stack(&stale);
            drop(boxed_decapsulation_key(alg));
        });
        assert_eq!(leaked, 0, "{alg:?}");
    }
}

/// A smaller ML-DSA set's key leaves no stale stack bytes on the heap: held
/// in one allocation sized for ML-DSA-87, its slack would carry what the
/// stack last held, such as another key's seed, past the key's own wipe.
#[test]
fn ml_dsa_slack() {
    let stale: [u8; NEEDLE_LEN] = distinct(27);
    for alg in [&signature::ML_DSA_44_SIGNING, &signature::ML_DSA_65_SIGNING] {
        let leaked = leaks(&stale, || {
            paint_stack(&stale);
            drop(boxed_pqdsa_key(alg));
        });
        assert_eq!(leaked, 0, "{alg:?}");
    }
}

/// Fills the stack the next call will use with `stale`, as a secret a
/// returned function left behind.
#[inline(never)]
fn paint_stack(stale: &[u8; NEEDLE_LEN]) {
    let mut stack = [0u8; 64 * 1024];
    for chunk in stack.as_chunks_mut::<NEEDLE_LEN>().0 {
        chunk.copy_from_slice(stale);
    }
    core::hint::black_box(&mut stack);
}

/// A decapsulation key for `alg`, moved to the heap through the stack.
#[inline(never)]
fn boxed_decapsulation_key(alg: &'static kem::Algorithm) -> Box<kem::DecapsulationKey> {
    Box::new(kem::DecapsulationKey::generate(alg).unwrap())
}

/// An ML-DSA key for `alg`, moved to the heap through the stack.
#[inline(never)]
fn boxed_pqdsa_key(alg: &'static signature::PqdsaSigningAlgorithm) -> Box<signature::PqdsaKeyPair> {
    Box::new(signature::PqdsaKeyPair::generate(alg).unwrap())
}
