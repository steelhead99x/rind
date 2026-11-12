//! Verification that, under the `wipe` feature, heap scratch derived from a
//! private key is wiped before it is freed.
//!
//! `tests/zeroing.rs` checks the bytes of each key value; this checks the
//! blocks an operation frees while it holds one. Messages, public values,
//! and encodings of public keys may be freed as they are, so a block is
//! judged by what it depends on rather than its content: each operation
//! runs under two keys with the same public inputs, and a freed block whose
//! bytes differ between the runs varies with the key, so is derived from it.
//! Key generation has no input but randomness, so everything it frees must
//! be zero.
//!
//! The allocator covers the whole binary, so this is a test binary of its
//! own. RSA key generation is slow, so it runs only under `SLOW_TESTS`.

#![cfg(feature = "wipe")]

mod freed;

use std::hint::black_box;

use freed::freed;

#[global_allocator]
static ALLOCATOR: freed::Record = freed::Record;

/// The blocks `op` frees under each of `keys`, after one unrecorded run so
/// one-time setup, such as CPU detection, stays out of the record.
fn freed_blocks<K, R>(keys: [K; 2], op: impl Fn(&K) -> R) -> [Vec<Vec<u8>>; 2] {
    op(&keys[0]);
    keys.map(|key| freed(|| op(&key)).1)
}

/// The index of the first freed block that differs, in count, length, or bytes.
fn first_difference(left: &[Vec<u8>], right: &[Vec<u8>]) -> Option<usize> {
    let shared = left.len().min(right.len());
    (0..shared)
        .find(|&i| left[i].len() != right[i].len() || left[i] != right[i])
        .or_else(|| (left.len() != right.len()).then_some(shared))
}

/// Index of the first freed block whose bytes vary with the key.
/// `assert_independent` panics on `Some`. The canary asserts `Some` for a
/// planted leak, so dropping the comparison here turns that canary red.
fn independent<K, R>(keys: [K; 2], op: impl Fn(&K) -> R) -> Option<usize> {
    let [left, right] = freed_blocks(keys, op);
    first_difference(&left, &right)
}

/// Fails if `op` frees a block under one of `keys` whose bytes differ from
/// those of the block it frees at the same point under the other.
fn assert_independent<K, R>(what: &str, keys: [K; 2], op: impl Fn(&K) -> R) {
    if let Some(i) = independent(keys, op) {
        panic!("{what}: freed block {i} holds bytes of the key");
    }
}

/// Index of the first freed block that is not all zero, after one unrecorded
/// run. `assert_zeroed` panics on `Some`. The canary asserts `Some` for a
/// planted leak, so dropping the comparison here turns that canary red.
fn first_nonzero<R>(op: impl Fn() -> R) -> Option<usize> {
    op();
    freed(&op)
        .1
        .iter()
        .position(|block| block.iter().any(|&byte| byte != 0))
}

/// Fails if `op` frees a block that is not all zero.
fn assert_zeroed<R>(what: &str, op: impl Fn() -> R) {
    if let Some(i) = first_nonzero(op) {
        panic!("{what}: freed block {i} holds bytes of the key");
    }
}

/// The check sees key-derived bytes left on the heap, so a clean result
/// means something. The canaries call `independent` and `first_nonzero`, the
/// same functions the real checks use, and report the result instead of panicking:
/// wasm32-wasip2 aborts on panic, and a `should_panic` test cannot run there.
#[test]
fn detects_a_leak() {
    let leaked = independent([[1u8; 32], [2u8; 32]], |key| {
        drop(black_box(key.map(|b| b ^ 0x5a).to_vec()))
    });
    assert!(
        leaked.is_some(),
        "planted key bytes were not visible in a freed block",
    );
}

#[test]
fn detects_a_leak_in_key_generation() {
    // Without black_box, the optimizer can drop the unused allocation, and
    // the check then has nothing to find.
    assert!(
        first_nonzero(|| drop(black_box(vec![1u8; 32]))).is_some(),
        "planted key bytes were not visible in a freed block",
    );
}

/// Two distinct PKCS#8 RSA keys of each size.
fn rsa_keys() -> impl Iterator<Item = [Vec<u8>; 2]> {
    use rind::signature::RsaKeyPair;
    [
        (
            &include_bytes!("../src/high/rsa/rsa2048.pkcs8.der")[..],
            &include_bytes!("../src/high/rsa/rsa2048-other.der")[..],
        ),
        (
            include_bytes!("../src/high/rsa/rsa3072.pkcs8.der"),
            include_bytes!("../src/high/rsa/rsa3072-other.der"),
        ),
        (
            include_bytes!("../src/high/rsa/rsa4096.pkcs8.der"),
            include_bytes!("../src/high/rsa/rsa4096-other.der"),
        ),
        (
            include_bytes!("../src/high/rsa/rsa6144.pkcs8.der"),
            include_bytes!("../src/high/rsa/rsa6144-other.der"),
        ),
        (
            include_bytes!("../src/high/rsa/rsa8192.pkcs8.der"),
            include_bytes!("../src/high/rsa/rsa8192-other.der"),
        ),
    ]
    .into_iter()
    .map(|(pkcs8, pkcs1)| {
        let pkcs1 = RsaKeyPair::from_pkcs1(pkcs1).unwrap();
        assert_ne!(
            RsaKeyPair::from_pkcs8(pkcs8).unwrap().to_spki().as_ref(),
            pkcs1.to_spki().as_ref(),
        );
        [pkcs8.to_vec(), pkcs1.to_pkcs8().as_ref().to_vec()]
    })
}

#[test]
fn rsa() {
    use rind::signature::{RsaKeyPair, sign};
    for pkcs8 in rsa_keys() {
        assert_independent("RSA load", pkcs8.clone(), |der| {
            RsaKeyPair::from_pkcs8(der).unwrap()
        });
        let keys = pkcs8.map(|der| RsaKeyPair::from_pkcs8(&der).unwrap());
        assert_independent("RSA export", keys.each_ref(), |key| key.to_pkcs8());
        for algorithm in [&sign::RSA_PKCS1_SHA256, &sign::RSA_PSS_SHA256] {
            assert_independent("RSA signing", keys.each_ref(), |key| {
                key.sign(algorithm, b"message").unwrap()
            });
        }
    }
}

#[test]
fn rsa_oaep() {
    use rind::rsa::{DecryptingKey, OAEP_SHA256};
    for pkcs8 in rsa_keys() {
        let keys = pkcs8.map(|der| {
            let key = DecryptingKey::from_pkcs8(&OAEP_SHA256, &der).unwrap();
            let ciphertext = key.public_key().encrypt(b"message", b"").unwrap();
            (key, ciphertext)
        });
        assert_independent("RSA decryption", keys, |(key, ciphertext)| {
            key.decrypt(ciphertext.as_ref(), b"").unwrap()
        });
    }
}

#[test]
fn rsa_generate() {
    use rind::rsa::KeySize;
    use rind::signature::RsaKeyPair;
    if std::env::var_os("SLOW_TESTS").is_none() {
        return;
    }
    // Larger sizes take the same paths, much more slowly.
    for size in [KeySize::Rsa2048, KeySize::Rsa3072, KeySize::Rsa4096] {
        assert_zeroed("RSA key generation", || RsaKeyPair::generate(size).unwrap());
    }
}

#[test]
fn ecdsa() {
    use rind::signature::{EcdsaKeyPair, sign};
    for algorithm in [
        &sign::ECDSA_P256_SHA256_ASN1,
        &sign::ECDSA_P384_SHA384_ASN1,
        &sign::ECDSA_P521_SHA512_ASN1,
    ] {
        assert_zeroed("ECDSA key generation", || {
            EcdsaKeyPair::generate(algorithm).unwrap()
        });
        let pkcs8 = [(); 2].map(|()| {
            let key = EcdsaKeyPair::generate(algorithm).unwrap();
            key.to_pkcs8().as_ref().to_vec()
        });
        assert_independent("ECDSA load", pkcs8.clone(), |der| {
            EcdsaKeyPair::from_pkcs8(algorithm, der).unwrap()
        });
        let keys = pkcs8.map(|der| EcdsaKeyPair::from_pkcs8(algorithm, &der).unwrap());
        assert_independent("ECDSA export", keys.each_ref(), |key| key.to_pkcs8());
        assert_independent("ECDSA signing", keys.each_ref(), |key| {
            key.sign(b"message").unwrap()
        });
    }
}

#[test]
fn ed25519() {
    use rind::signature::Ed25519KeyPair;
    assert_zeroed("Ed25519 key generation", || {
        Ed25519KeyPair::generate().unwrap()
    });
    let pkcs8 = [(); 2].map(|()| {
        let key = Ed25519KeyPair::generate().unwrap();
        key.to_pkcs8().as_ref().to_vec()
    });
    assert_independent("Ed25519 load", pkcs8.clone(), |der| {
        Ed25519KeyPair::from_pkcs8(der).unwrap()
    });
    let keys = pkcs8.map(|der| Ed25519KeyPair::from_pkcs8(&der).unwrap());
    assert_independent("Ed25519 export", keys.each_ref(), |key| key.to_pkcs8());
    assert_independent("Ed25519 signing", keys.each_ref(), |key| {
        key.sign(b"message")
    });
}

// aws-lc expands the key. It does not build for wasm or under Miri, so this
// comparison stays on the targets that build it. The canaries and the other
// wipe checks in this file still compile everywhere.
#[cfg(not(any(miri, target_family = "wasm")))]
#[test]
fn ml_dsa() {
    use aws_lc_rs::signature::{ML_DSA_44_SIGNING, ML_DSA_65_SIGNING, ML_DSA_87_SIGNING};
    use rind::signature::sign::{MlDsa44, MlDsa65, MlDsa87};
    ml_dsa_set::<MlDsa44>(&ML_DSA_44_SIGNING);
    ml_dsa_set::<MlDsa65>(&ML_DSA_65_SIGNING);
    ml_dsa_set::<MlDsa87>(&ML_DSA_87_SIGNING);
}

#[cfg(not(any(miri, target_family = "wasm")))]
fn ml_dsa_set<P: rind::signature::sign::MlDsaParameterSet>(
    theirs: &'static aws_lc_rs::signature::PqdsaSigningAlgorithm,
) {
    use rind::signature::sign::MlDsaKeyPair;
    assert_zeroed("ML-DSA key generation", || {
        MlDsaKeyPair::<P>::generate().unwrap()
    });
    let seeds = [[1u8; 32], [2u8; 32]];
    assert_independent("ML-DSA seed load", seeds, |seed| {
        MlDsaKeyPair::<P>::from_seed(seed).unwrap()
    });
    let keys = seeds.map(|seed| MlDsaKeyPair::<P>::from_seed(&seed).unwrap());
    assert_independent("ML-DSA export", keys.each_ref(), |key| key.to_pkcs8());
    // The expanded form, whose load checks the key.
    let expanded = seeds.map(|seed| ml_dsa_expanded_pkcs8(theirs, &seed));
    assert_independent("ML-DSA expanded load", expanded, |der| {
        MlDsaKeyPair::<P>::from_pkcs8(der).unwrap()
    });
    // Signing is hedged, so even under one key its randomness varies: every
    // block it frees must be wiped.
    for key in &keys {
        assert_zeroed("ML-DSA signing", || key.sign(b"message").unwrap());
    }
}

/// The key `seed` expands to, as PKCS#8 in RFC 9881's expanded form, which
/// rind writes only for a key loaded from it, so aws-lc-rs expands it.
#[cfg(not(any(miri, target_family = "wasm")))]
fn ml_dsa_expanded_pkcs8(
    algorithm: &'static aws_lc_rs::signature::PqdsaSigningAlgorithm,
    seed: &[u8; 32],
) -> Vec<u8> {
    use aws_lc_rs::encoding::AsRawBytes;
    use aws_lc_rs::signature::PqdsaKeyPair;
    let key = PqdsaKeyPair::from_seed(algorithm, seed).unwrap();
    let expanded = key.private_key().as_raw_bytes().unwrap();
    // The seed form's version and `AlgorithmIdentifier`, which the expanded
    // form shares: `SEQUENCE { INTEGER 0, SEQUENCE { OID } ...`.
    let seed_form = key.to_pkcs8v1().unwrap();
    let header = &seed_form.as_ref()[2..2 + 3 + 13];
    let private_key = der(0x04, &der(0x04, expanded.as_ref()));
    der(0x30, &[header, &private_key].concat())
}

/// A DER element of `tag` holding `body`, under 64 KiB.
#[cfg(not(any(miri, target_family = "wasm")))]
fn der(tag: u8, body: &[u8]) -> Vec<u8> {
    let len = match body.len() {
        len @ 0..=0x7f => vec![len as u8],
        len @ 0x80..=0xff => vec![0x81, len as u8],
        len => [&[0x82][..], &u16::try_from(len).unwrap().to_be_bytes()].concat(),
    };
    [&[tag][..], &len, body].concat()
}

#[test]
fn ecdh() {
    use rind::agreement::{ECDH_P256, ECDH_P384, ECDH_P521, PrivateKey, X25519};
    for algorithm in [&X25519, &ECDH_P256, &ECDH_P384, &ECDH_P521] {
        assert_zeroed("ECDH key generation", || {
            PrivateKey::generate(algorithm).unwrap()
        });
        let peer = PrivateKey::generate(algorithm).unwrap();
        let pkcs8 = [(); 2].map(|()| {
            let key = PrivateKey::generate(algorithm).unwrap();
            key.to_pkcs8().as_ref().to_vec()
        });
        assert_independent("ECDH load", pkcs8.clone(), |der| {
            PrivateKey::from_pkcs8(algorithm, der).unwrap()
        });
        let keys = pkcs8.map(|der| PrivateKey::from_pkcs8(algorithm, &der).unwrap());
        assert_independent("ECDH export", keys.each_ref(), |key| key.to_pkcs8());
        assert_independent("ECDH agreement", keys.each_ref(), |key| {
            key.agree(peer.public_key().as_ref()).unwrap()
        });
    }
}

#[test]
fn mlkem768() {
    use rind::kem::{DecapsulationKey, ML_KEM_768};
    assert_zeroed("ML-KEM key generation", || {
        DecapsulationKey::generate(&ML_KEM_768).unwrap()
    });
    let keys = [(); 2].map(|()| {
        let key = DecapsulationKey::generate(&ML_KEM_768).unwrap();
        let (ciphertext, _) = key.public_key().encapsulate().unwrap();
        (key, ciphertext)
    });
    assert_independent("ML-KEM decapsulation", keys, |(key, ciphertext)| {
        key.decapsulate(ciphertext.as_ref()).unwrap()
    });
}
