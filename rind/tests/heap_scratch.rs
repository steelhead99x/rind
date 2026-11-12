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

/// Whether the freed blocks differ, in count, length, or bytes.
fn blocks_differ(left: &[Vec<u8>], right: &[Vec<u8>]) -> bool {
    left.len() != right.len()
        || left
            .iter()
            .zip(right)
            .any(|(a, b)| a.len() != b.len() || a != b)
}

/// Fails if `op` frees a block under one of `keys` whose bytes differ from
/// those of the block it frees at the same point under the other.
fn independent<K, R>(what: &str, keys: [K; 2], op: impl Fn(&K) -> R) {
    let [left, right] = freed_blocks(keys, op);
    assert!(
        !blocks_differ(&left, &right),
        "{what}: holds bytes of the key",
    );
}

/// Whether `op` frees a block that is not all zero, after one unrecorded run.
fn frees_nonzero<R>(op: impl Fn() -> R) -> bool {
    op();
    freed(&op)
        .1
        .iter()
        .any(|block| block.iter().any(|&byte| byte != 0))
}

/// Fails if `op` frees a block that is not all zero.
fn zeroed<R>(what: &str, op: impl Fn() -> R) {
    assert!(!frees_nonzero(op), "{what}: holds bytes of the key",);
}

/// The check sees key-derived bytes left on the heap, so a clean result
/// means something. The canaries return that fact instead of panicking:
/// wasm32-wasip2 aborts on panic, and a `should_panic` test cannot run there.
#[test]
fn detects_a_leak() {
    let [left, right] = freed_blocks([[1u8; 32], [2u8; 32]], |key| {
        drop(black_box(key.map(|b| b ^ 0x5a).to_vec()))
    });
    assert!(
        blocks_differ(&left, &right),
        "planted key bytes were not visible in a freed block",
    );
}

#[test]
fn detects_a_leak_in_key_generation() {
    // Without black_box, the optimizer can drop the unused allocation, and
    // the check then has nothing to find.
    assert!(
        frees_nonzero(|| drop(black_box(vec![1u8; 32]))),
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
    // Larger sizes take the same paths, much more slowly.
    eprintln!("slow-tests: rsa_generate 2048 3072 4096");
    for size in [KeySize::Rsa2048, KeySize::Rsa3072, KeySize::Rsa4096] {
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
