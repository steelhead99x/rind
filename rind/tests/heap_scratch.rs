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

/// Fails if `op` frees a block under one of `keys` whose bytes differ from
/// those of the block it frees at the same point under the other.
fn independent<K, R>(what: &str, keys: [K; 2], op: impl Fn(&K) -> R) {
    // A first, unrecorded run keeps one-time setup out of the record, such
    // as CPU detection, which frees the names it reads.
    op(&keys[0]);
    let [(_a, a), (_b, b)] = keys.map(|key| freed(|| op(&key)));
    assert_eq!(
        a.iter().map(Vec::len).collect::<Vec<_>>(),
        b.iter().map(Vec::len).collect::<Vec<_>>(),
        "{what}: the blocks freed depend on the key",
    );
    for (i, (a, b)) in a.iter().zip(&b).enumerate() {
        assert!(a == b, "{what}: freed block {i} holds bytes of the key");
    }
}

/// Fails if `op` frees a block that is not all zero.
fn zeroed<R>(what: &str, op: impl Fn() -> R) {
    // Unrecorded first, as `independent` does.
    op();
    let (_result, blocks) = freed(op);
    for (i, block) in blocks.iter().enumerate() {
        assert!(
            block.iter().all(|&b| b == 0),
            "{what}: freed block {i} holds bytes of the key",
        );
    }
}

/// The check sees key-derived bytes left on the heap, so a clean result
/// means something.
#[test]
#[should_panic(expected = "holds bytes of the key")]
fn detects_a_leak() {
    independent("planted", [[1u8; 32], [2u8; 32]], |key| {
        drop(key.map(|b| b ^ 0x5a).to_vec())
    });
}

#[test]
#[should_panic(expected = "holds bytes of the key")]
fn detects_a_leak_in_key_generation() {
    // Without black_box, the optimizer can drop the unused allocation, and
    // the check then has nothing to find.
    zeroed("planted", || drop(black_box(vec![1u8; 32])));
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
fn ml_dsa() {
    use aws_lc_rs::signature::{ML_DSA_44_SIGNING, ML_DSA_65_SIGNING, ML_DSA_87_SIGNING};
    use rind::signature::sign::{MlDsa44, MlDsa65, MlDsa87};
    ml_dsa_set::<MlDsa44>(&ML_DSA_44_SIGNING);
    ml_dsa_set::<MlDsa65>(&ML_DSA_65_SIGNING);
    ml_dsa_set::<MlDsa87>(&ML_DSA_87_SIGNING);
}

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
fn spake2plus() {
    use rind::spake2plus::{ProverSecrets, VerifierRecord};
    // No randomness: the freed blocks are the scalar reduction and L = w1*G.
    let passwords = [[0x11u8; 40], [0x22u8; 40]];
    independent("SPAKE2+ prover", passwords, |w0| {
        ProverSecrets::new(w0, &[0x33; 40]).unwrap()
    });
    independent("SPAKE2+ verifier", passwords, |w0| {
        VerifierRecord::from_w1(w0, &[0x33; 40]).unwrap()
    });
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
