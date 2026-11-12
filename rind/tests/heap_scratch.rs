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

/// How the blocks freed under two keys differ.
#[derive(Debug)]
enum Difference {
    /// A different number or size of blocks: the key steered the allocations.
    Layout,
    /// Block `i` holds different bytes under each key.
    Bytes(usize),
}

/// How `left` and `right` differ, if they do.
fn difference(left: &[Vec<u8>], right: &[Vec<u8>]) -> Option<Difference> {
    let layout = |blocks: &[Vec<u8>]| blocks.iter().map(Vec::len).collect::<Vec<_>>();
    if layout(left) != layout(right) {
        return Some(Difference::Layout);
    }
    left.iter()
        .zip(right)
        .position(|(a, b)| a != b)
        .map(Difference::Bytes)
}

/// Fails if `op` frees a block under one of `keys` whose bytes differ from
/// those of the block it frees at the same point under the other.
fn independent<K, R>(what: &str, keys: [K; 2], op: impl Fn(&K) -> R) {
    let [left, right] = freed_blocks(keys, op);
    match difference(&left, &right) {
        None => {}
        Some(Difference::Layout) => panic!("{what}: the blocks freed depend on the key"),
        Some(Difference::Bytes(i)) => panic!("{what}: freed block {i} holds bytes of the key"),
    }
}

/// The first block `op` frees that is not all zero, after one unrecorded run.
fn first_nonzero<R>(op: impl Fn() -> R) -> Option<usize> {
    op();
    freed(&op)
        .1
        .iter()
        .position(|block| block.iter().any(|&byte| byte != 0))
}

/// Fails if `op` frees a block that is not all zero.
fn zeroed<R>(what: &str, op: impl Fn() -> R) {
    if let Some(i) = first_nonzero(op) {
        panic!("{what}: freed block {i} holds bytes of the key");
    }
}

/// The check sees key-derived bytes left on the heap, so a clean result
/// means something. The canaries return that fact instead of panicking:
/// wasm32-wasip2 aborts on panic, and a `should_panic` test cannot run there.
/// Each goes through the comparison `independent` and `zeroed` use, and
/// passes only when that comparison finds the planted bytes, not when the
/// allocations merely differ.
#[test]
fn detects_a_leak() {
    let [left, right] = freed_blocks([[1u8; 32], [2u8; 32]], |key| {
        drop(black_box(key.map(|b| b ^ 0x5a).to_vec()))
    });
    let found = difference(&left, &right);
    assert!(
        matches!(found, Some(Difference::Bytes(_))),
        "planted key bytes were not found in a freed block: {found:?}",
    );
}

#[test]
fn detects_a_leak_in_key_generation() {
    // Without black_box, the optimizer can drop the unused allocation, and
    // the check then has nothing to find.
    assert!(
        first_nonzero(|| drop(black_box(vec![1u8; 32]))).is_some(),
        "planted key bytes were not found in a freed block",
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
        independent("RSA load", pkcs8.clone(), |der| {
            RsaKeyPair::from_pkcs8(der).unwrap()
        });
        let keys = pkcs8.map(|der| RsaKeyPair::from_pkcs8(&der).unwrap());
        independent("RSA export", keys.each_ref(), |key| key.to_pkcs8());
        for algorithm in [&sign::RSA_PKCS1_SHA256, &sign::RSA_PSS_SHA256] {
            independent("RSA signing", keys.each_ref(), |key| {
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
        independent("RSA decryption", keys, |(key, ciphertext)| {
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
    // Larger sizes take the same paths, much more slowly. Under wasmtime,
    // where `just wasm` sets SLOW_TESTS, the portable backend runs under a
    // JIT and every freed block is copied, so RSA-2048 alone covers them.
    let sizes: &[KeySize] = if cfg!(target_family = "wasm") {
        &[KeySize::Rsa2048]
    } else {
        &[KeySize::Rsa2048, KeySize::Rsa3072, KeySize::Rsa4096]
    };
    for &size in sizes {
        zeroed("RSA key generation", || RsaKeyPair::generate(size).unwrap());
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
        zeroed("ECDSA key generation", || {
            EcdsaKeyPair::generate(algorithm).unwrap()
        });
        let pkcs8 = [(); 2].map(|()| {
            let key = EcdsaKeyPair::generate(algorithm).unwrap();
            key.to_pkcs8().as_ref().to_vec()
        });
        independent("ECDSA load", pkcs8.clone(), |der| {
            EcdsaKeyPair::from_pkcs8(algorithm, der).unwrap()
        });
        let keys = pkcs8.map(|der| EcdsaKeyPair::from_pkcs8(algorithm, &der).unwrap());
        independent("ECDSA export", keys.each_ref(), |key| key.to_pkcs8());
        independent("ECDSA signing", keys.each_ref(), |key| {
            key.sign(b"message").unwrap()
        });
    }
}

#[test]
fn ed25519() {
    use rind::signature::Ed25519KeyPair;
    zeroed("Ed25519 key generation", || {
        Ed25519KeyPair::generate().unwrap()
    });
    let pkcs8 = [(); 2].map(|()| {
        let key = Ed25519KeyPair::generate().unwrap();
        key.to_pkcs8().as_ref().to_vec()
    });
    independent("Ed25519 load", pkcs8.clone(), |der| {
        Ed25519KeyPair::from_pkcs8(der).unwrap()
    });
    let keys = pkcs8.map(|der| Ed25519KeyPair::from_pkcs8(&der).unwrap());
    independent("Ed25519 export", keys.each_ref(), |key| key.to_pkcs8());
    independent("Ed25519 signing", keys.each_ref(), |key| {
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
    zeroed("ML-DSA key generation", || {
        MlDsaKeyPair::<P>::generate().unwrap()
    });
    let seeds = [[1u8; 32], [2u8; 32]];
    independent("ML-DSA seed load", seeds, |seed| {
        MlDsaKeyPair::<P>::from_seed(seed).unwrap()
    });
    let keys = seeds.map(|seed| MlDsaKeyPair::<P>::from_seed(&seed).unwrap());
    independent("ML-DSA export", keys.each_ref(), |key| key.to_pkcs8());
    // The expanded form, whose load checks the key.
    let expanded = seeds.map(|seed| ml_dsa_expanded_pkcs8(theirs, &seed));
    independent("ML-DSA expanded load", expanded, |der| {
        MlDsaKeyPair::<P>::from_pkcs8(der).unwrap()
    });
    // Signing is hedged, so even under one key its randomness varies: every
    // block it frees must be wiped.
    for key in &keys {
        zeroed("ML-DSA signing", || key.sign(b"message").unwrap());
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
        zeroed("ECDH key generation", || {
            PrivateKey::generate(algorithm).unwrap()
        });
        let peer = PrivateKey::generate(algorithm).unwrap();
        let pkcs8 = [(); 2].map(|()| {
            let key = PrivateKey::generate(algorithm).unwrap();
            key.to_pkcs8().as_ref().to_vec()
        });
        independent("ECDH load", pkcs8.clone(), |der| {
            PrivateKey::from_pkcs8(algorithm, der).unwrap()
        });
        let keys = pkcs8.map(|der| PrivateKey::from_pkcs8(algorithm, &der).unwrap());
        independent("ECDH export", keys.each_ref(), |key| key.to_pkcs8());
        independent("ECDH agreement", keys.each_ref(), |key| {
            key.agree(peer.public_key().as_ref()).unwrap()
        });
    }
}

#[test]
fn mlkem768() {
    use rind::kem::{DecapsulationKey, ML_KEM_768};
    zeroed("ML-KEM key generation", || {
        DecapsulationKey::generate(&ML_KEM_768).unwrap()
    });
    let keys = [(); 2].map(|()| {
        let key = DecapsulationKey::generate(&ML_KEM_768).unwrap();
        let (ciphertext, _) = key.public_key().encapsulate().unwrap();
        (key, ciphertext)
    });
    independent("ML-KEM decapsulation", keys, |(key, ciphertext)| {
        key.decapsulate(ciphertext.as_ref()).unwrap()
    });
}
