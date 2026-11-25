//! Verification that heap scratch derived from a private key is wiped before
//! it is freed.
//!
//! `tests/zeroing.rs` checks the bytes of each key value; this checks the
//! blocks an operation frees while it holds one. Messages, public values,
//! and encodings of public keys may be freed as they are, so a block is
//! judged by what it depends on rather than its content: each operation
//! runs under two keys with the same public inputs, and a freed block whose
//! bytes differ between the runs varies with the key, so is derived from it.
//! Key generation has no input but randomness, so everything it frees must
//! be zero. A randomized protocol step can free public values its randomness
//! reached, such as a proof's terms, so it is judged by search instead: no
//! freed block may hold one of the secrets the step had, in either byte
//! order.
//!
//! The allocator covers the whole binary, so this is a test binary of its
//! own. RSA key generation is slow, so it runs only under `SLOW_TESTS`.

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

/// How the blocks freed under each of `keys` vary with the key, if they do.
/// `assert_independent` panics on `Some`. The canary asserts a byte
/// difference for a planted leak, so dropping the comparison here turns that
/// canary red.
fn independent<K, R>(keys: [K; 2], op: impl Fn(&K) -> R) -> Option<Difference> {
    let [left, right] = freed_blocks(keys, op);
    difference(&left, &right)
}

/// Fails if `op` frees a block under one of `keys` whose bytes differ from
/// those of the block it frees at the same point under the other.
fn assert_independent<K, R>(what: &str, keys: [K; 2], op: impl Fn(&K) -> R) {
    match independent(keys, op) {
        None => {}
        Some(Difference::Layout) => panic!("{what}: the blocks freed depend on the key"),
        Some(Difference::Bytes(i)) => panic!("{what}: freed block {i} holds bytes of the key"),
    }
}

/// Index of the first freed block that is not all zero, after one unrecorded
/// run. `assert_zeroed` panics on `Some`. The canary asserts `Some` for a
/// planted leak, so dropping the comparison here turns that canary red.
fn first_nonzero<R>(op: impl Fn() -> R) -> Option<usize> {
    first_nonzero_given(|| (), |()| op())
}

/// As `first_nonzero`, for an `op` given a fresh `setup()` it may consume,
/// such as a protocol state, whose making stays out of the record. What `op`
/// drops of it is recorded; what `op` returns is not.
fn first_nonzero_given<S, R>(setup: impl Fn() -> S, op: impl Fn(S) -> R) -> Option<usize> {
    op(setup());
    let input = setup();
    freed(|| op(input))
        .1
        .iter()
        .position(|block| block.iter().any(|&byte| byte != 0))
}

/// Fails if `op` frees a block that is not all zero.
fn assert_zeroed<R>(what: &str, op: impl Fn() -> R) {
    assert_zeroed_given(what, || (), |()| op());
}

/// Fails if `op`, given a fresh `setup()`, frees a block that is not all zero.
fn assert_zeroed_given<S, R>(what: &str, setup: impl Fn() -> S, op: impl Fn(S) -> R) {
    if let Some(i) = first_nonzero_given(setup, op) {
        panic!("{what}: freed block {i} holds bytes of the key");
    }
}

/// Index of the first block `op` frees, given a fresh `setup()` it may
/// consume, that holds one of `secrets` in either byte order, after one
/// unrecorded run. `assert_absent` panics on `Some`, and the canary asserts
/// `Some` for a planted leak.
fn first_holding<S, R>(
    secrets: &[&[u8]],
    setup: impl Fn() -> S,
    op: impl Fn(S) -> R,
) -> Option<usize> {
    op(setup());
    let input = setup();
    assert!(secrets.iter().all(|secret| !secret.is_empty()));
    let wanted: Vec<Vec<u8>> = secrets
        .iter()
        .flat_map(|secret| [secret.to_vec(), secret.iter().rev().copied().collect()])
        .collect();
    freed(|| op(input)).1.iter().position(|block| {
        wanted
            .iter()
            .any(|secret| block.windows(secret.len()).any(|window| window == secret))
    })
}

/// Fails if `op`, given a fresh `setup()`, frees a block holding one of
/// `secrets`.
fn assert_absent<S, R>(what: &str, secrets: &[&[u8]], setup: impl Fn() -> S, op: impl Fn(S) -> R) {
    if let Some(i) = first_holding(secrets, setup, op) {
        panic!("{what}: freed block {i} holds bytes of the key");
    }
}

/// The check sees key-derived bytes left on the heap, so a clean result
/// means something. These canaries call `independent` and `first_nonzero`, the
/// comparisons the real checks use, and report the result instead of panicking:
/// wasm32-wasip2 aborts on panic, and a `should_panic` test cannot run there.
/// Native targets also have `should_panic` canaries that go through the
/// `assert_*` wrappers, so a no-op arm there cannot pass unnoticed.
#[test]
fn detects_a_leak() {
    let leaked = independent([[1u8; 32], [2u8; 32]], |key| {
        drop(black_box(key.map(|b| b ^ 0x5a).to_vec()))
    });
    // A layout difference would pass a weaker check without finding the
    // planted bytes, so only a byte difference counts.
    assert!(
        matches!(leaked, Some(Difference::Bytes(_))),
        "planted key bytes were not found in a freed block: {leaked:?}",
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

#[test]
fn detects_a_leak_by_search() {
    let secret = [7u8, 1, 2, 3, 4, 5, 6, 7];
    // Reversed, as a little-endian word holds a big-endian encoding.
    let leaked = first_holding(
        &[&secret],
        || (),
        |()| {
            let mut block = vec![0u8; 24];
            block[5..13].copy_from_slice(&secret);
            block[5..13].reverse();
            drop(black_box(block))
        },
    );
    assert!(
        leaked.is_some(),
        "planted key bytes were not found in a freed block"
    );
}

/// Native-only: a planted leak must fail through `assert_independent`, not
/// only through `independent`. wasm32-wasip2 aborts on panic, so this stays
/// off that target.
#[cfg(not(target_family = "wasm"))]
#[test]
#[should_panic(expected = "holds bytes of the key")]
fn detects_a_leak_through_assert_independent() {
    assert_independent("planted leak", [[1u8; 32], [2u8; 32]], |key| {
        drop(black_box(key.map(|b| b ^ 0x5a).to_vec()))
    });
}

/// Native-only: a planted leak must fail through `assert_absent`.
#[cfg(not(target_family = "wasm"))]
#[test]
#[should_panic(expected = "holds bytes of the key")]
fn detects_a_leak_through_assert_absent() {
    assert_absent(
        "planted leak",
        &[&[9u8; 8]],
        || (),
        |()| drop(black_box(vec![9u8; 8])),
    );
}

/// Native-only: a planted leak must fail through `assert_zeroed`.
#[cfg(not(target_family = "wasm"))]
#[test]
#[should_panic(expected = "holds bytes of the key")]
fn detects_a_leak_in_key_generation_through_assert_zeroed() {
    assert_zeroed("planted leak", || drop(black_box(vec![1u8; 32])));
}

/// Two distinct PKCS#8 RSA keys of each size.
fn rsa_keys() -> impl Iterator<Item = [Vec<u8>; 2]> {
    use rind::rsa::KeyPair as RsaKeyPair;
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
            RsaKeyPair::from_pkcs8(pkcs8)
                .unwrap()
                .public_key()
                .to_spki()
                .as_ref(),
            pkcs1.public_key().to_spki().as_ref(),
        );
        [pkcs8.to_vec(), pkcs1.to_pkcs8().as_ref().to_vec()]
    })
}

#[test]
fn rsa() {
    use rind::rsa::{KeyPair as RsaKeyPair, sign};
    for pkcs8 in rsa_keys() {
        assert_independent("RSA load", pkcs8.clone(), |der| {
            RsaKeyPair::from_pkcs8(der).unwrap()
        });
        // A wrong CRT coefficient, the encoding's last bytes, parses but
        // fails the key's check, after the private values are loaded.
        let corrupt = pkcs8.clone().map(|mut der| {
            *der.last_mut().unwrap() ^= 1;
            der
        });
        assert_independent("RSA refused load", corrupt, |der| {
            RsaKeyPair::from_pkcs8(der).unwrap_err()
        });
        let keys = pkcs8.map(|der| RsaKeyPair::from_pkcs8(&der).unwrap());
        assert_independent("RSA export", keys.each_ref(), |key| key.to_pkcs8());
        for algorithm in [&sign::PKCS1_SHA256, &sign::PSS_SHA256] {
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
        assert_independent("RSA decryption", keys.each_ref(), |(key, ciphertext)| {
            key.decrypt(ciphertext.as_ref(), b"").unwrap()
        });
        // The first key's ciphertext, cleared in its top byte to fall below
        // both moduli and changed in its last so it is never the ciphertext
        // itself, which a top byte already zero would leave, fails the
        // padding check under each key.
        let mut forged = keys[0].1.as_ref().to_vec();
        forged[0] = 0;
        *forged.last_mut().unwrap() ^= 1;
        assert_independent("RSA refused decryption", keys, |(key, _)| {
            key.decrypt(&forged, b"").unwrap_err()
        });
    }
}

#[test]
fn rsa_generate() {
    use rind::rsa::KeyPair as RsaKeyPair;
    use rind::rsa::KeySize;
    if std::env::var_os("SLOW_TESTS").is_none() {
        return;
    }
    // Under wasmtime, where `just wasm` sets SLOW_TESTS, larger sizes take
    // far longer, so wasm generates RSA-2048 keys only. Key generation
    // allocates the same way at every size.
    let sizes: &[KeySize] = if cfg!(target_family = "wasm") {
        &[KeySize::Rsa2048]
    } else {
        &[KeySize::Rsa2048, KeySize::Rsa3072, KeySize::Rsa4096]
    };
    for &size in sizes {
        assert_zeroed("RSA key generation", || RsaKeyPair::generate(size).unwrap());
    }
}

#[test]
fn ecdsa() {
    use rind::ecdsa::{KeyPair as EcdsaKeyPair, sign};
    for algorithm in [
        &sign::P256_SHA256_ASN1,
        &sign::P384_SHA384_ASN1,
        &sign::P521_SHA512_ASN1,
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
    use rind::ed25519::KeyPair as Ed25519KeyPair;
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

#[test]
fn ml_dsa() {
    use rind::ml_dsa::{MlDsa44, MlDsa65, MlDsa87};
    ml_dsa_set::<MlDsa44>();
    ml_dsa_set::<MlDsa65>();
    ml_dsa_set::<MlDsa87>();
}

/// The expanded-form load. rind writes that form only for a key loaded from
/// it, so the fixtures are aws-lc-rs's expansion of seeds `[1u8; 32]` and
/// `[2u8; 32]`, which `ml_dsa_expanded_fixtures` holds them to. Miri skips
/// the file I/O and the large encodings.
#[test]
#[cfg(not(miri))]
fn ml_dsa_expanded() {
    use rind::ml_dsa::{MlDsa44, MlDsa65, MlDsa87};
    ml_dsa_expanded_set::<MlDsa44>("44");
    ml_dsa_expanded_set::<MlDsa65>("65");
    ml_dsa_expanded_set::<MlDsa87>("87");
}

/// The fixtures `ml_dsa_expanded` loads stay aws-lc's expansion, which wasm
/// cannot ask.
#[test]
#[cfg(not(any(miri, target_family = "wasm")))]
fn ml_dsa_expanded_fixtures() {
    use aws_lc_rs::signature::{ML_DSA_44_SIGNING, ML_DSA_65_SIGNING, ML_DSA_87_SIGNING};
    for (set, theirs) in [
        ("44", &ML_DSA_44_SIGNING),
        ("65", &ML_DSA_65_SIGNING),
        ("87", &ML_DSA_87_SIGNING),
    ] {
        for seed in [1u8, 2] {
            let path = ml_dsa_fixture_path(set, seed);
            assert_eq!(
                std::fs::read(&path).unwrap_or_else(|err| panic!("cannot read {path}: {err}")),
                ml_dsa_expanded_pkcs8(theirs, &[seed; 32]),
                "{path}",
            );
        }
    }
}

fn ml_dsa_set<P: rind::ml_dsa::ParameterSet>() {
    use rind::ml_dsa::KeyPair as MlDsaKeyPair;
    assert_zeroed("ML-DSA key generation", || {
        MlDsaKeyPair::<P>::generate().unwrap()
    });
    let seeds = [[1u8; 32], [2u8; 32]];
    assert_independent("ML-DSA seed load", seeds, |seed| {
        MlDsaKeyPair::<P>::from_seed(seed).unwrap()
    });
    // A key pair's expansion is as good as its key, so its drop wipes it.
    assert_independent("ML-DSA key pair drop", seeds, |seed| {
        drop(MlDsaKeyPair::<P>::from_seed(seed).unwrap())
    });
    let keys = seeds.map(|seed| MlDsaKeyPair::<P>::from_seed(&seed).unwrap());
    assert_independent("ML-DSA export", keys.each_ref(), |key| key.to_pkcs8());
    // Signing is hedged, so even under one key its randomness varies: every
    // block it frees must be wiped.
    for key in &keys {
        assert_zeroed("ML-DSA signing", || key.sign(b"message").unwrap());
    }
}

/// The PKCS#8 path of one recorded expanded-form fixture.
#[cfg(not(miri))]
fn ml_dsa_fixture_path(set: &str, seed: u8) -> String {
    format!(
        "{}/tests/heap_scratch/ml-dsa-{set}-{seed}.pkcs8",
        env!("CARGO_MANIFEST_DIR")
    )
}

/// The expanded form, whose load checks the key. `set` is "44", "65", or "87".
#[cfg(not(miri))]
fn ml_dsa_expanded_set<P: rind::ml_dsa::ParameterSet>(set: &str) {
    use rind::ml_dsa::KeyPair as MlDsaKeyPair;
    let expanded = [1, 2].map(|seed| {
        let path = ml_dsa_fixture_path(set, seed);
        std::fs::read(&path).unwrap_or_else(|err| panic!("cannot read {path}: {err}"))
    });
    // Dropped inside the check: the expansion is freed then, and `freed`
    // stops recording before it drops the closure's result.
    assert_independent("ML-DSA expanded load", expanded, |der| {
        drop(MlDsaKeyPair::<P>::from_pkcs8(der).unwrap())
    });
}

#[test]
fn slh_dsa() {
    use rind::slh_dsa::{SlhDsaSha2_128f, SlhDsaShake128f};
    slh_dsa_set::<SlhDsaSha2_128f>();
    slh_dsa_set::<SlhDsaShake128f>();
}

fn slh_dsa_set<P: rind::slh_dsa::ParameterSet>() {
    use rind::slh_dsa::KeyPair;
    assert_zeroed("SLH-DSA key generation", || {
        KeyPair::<P>::generate().unwrap()
    });
    let keys = [(); 2].map(|()| KeyPair::<P>::generate().unwrap());
    assert_independent("SLH-DSA export", keys.each_ref(), |key| key.to_pkcs8());
    let pkcs8 = keys.each_ref().map(|key| key.to_pkcs8().as_ref().to_vec());
    // Loading checks the key by making it again.
    assert_independent("SLH-DSA load", pkcs8, |der| {
        KeyPair::<P>::from_pkcs8(der).unwrap()
    });
    // Signing is randomized, so even under one key it varies: every block
    // it frees must be wiped.
    for key in &keys {
        assert_zeroed("SLH-DSA signing", || key.sign(b"message").unwrap());
    }
}

/// Argon2id's memory is as good as the password to an attacker, who could
/// finish the hash from it without paying for the memory.
#[test]
fn argon2() {
    let params = rind::argon2::Params::new(32, 2, 2).unwrap();
    assert_independent(
        "Argon2id",
        [*b"password one", *b"password two"],
        |password| {
            // The secret keeps its password on the heap.
            let secret = rind::argon2::Secret::new(password);
            let mut out = [0u8; 32];
            secret.derive(params, b"saltsalt", &mut out).unwrap();
            // Verifying derives its key on the heap.
            black_box(secret.verify(params, b"saltsalt", &out).is_ok())
        },
    );
}

/// PBKDF2's verification derives its key on the heap where it runs
/// pyca/verified-garbage's routine, which derives no block alone.
#[test]
fn pbkdf2() {
    use rind::pbkdf2::{
        PBKDF2_HMAC_SHA256, PBKDF2_HMAC_SHA384, PBKDF2_HMAC_SHA512, Secret,
        legacy::PBKDF2_HMAC_SHA1,
    };
    let iterations = std::num::NonZeroU32::new(2).unwrap();
    for algorithm in [
        &PBKDF2_HMAC_SHA1,
        &PBKDF2_HMAC_SHA256,
        &PBKDF2_HMAC_SHA384,
        &PBKDF2_HMAC_SHA512,
    ] {
        // Longer than one hash, so verification derives more than a block.
        let mut stored = [0u8; 133];
        Secret::new(algorithm, b"password one")
            .derive(iterations, b"saltsalt", &mut stored)
            .unwrap();
        assert_independent(
            &format!("{algorithm:?}"),
            [*b"password one", *b"password two"],
            |password| {
                let secret = Secret::new(algorithm, password);
                black_box(secret.verify(iterations, b"saltsalt", &stored).is_ok())
            },
        );
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
fn spake2plus() {
    use rind::spake2plus::{ProverSecrets, RFC9383, Session, VerifierRecord};
    // SPAKE2+ allocates nothing today; this holds it to wiping if it starts
    // to. A handshake's heap scratch would derive from the password or the
    // ephemeral scalars, so a block freed unwiped differs between the runs
    // and fails, even one only the randomness reached.
    //
    // Varying only `w0` misses scratch that depends on `w1` alone, including
    // `L = w1*G`. Each constructor is run both ways. The handshake's two runs
    // use different pairs, so scratch from either scalar differs.
    let w0s = [[0x11u8; 40], [0x22u8; 40]];
    let w1s = [[0x33u8; 40], [0x44u8; 40]];
    assert_independent("SPAKE2+ prover w0", w0s, |w0| {
        ProverSecrets::new(w0, &[0x33; 40]).unwrap()
    });
    assert_independent("SPAKE2+ prover w1", w1s, |w1| {
        ProverSecrets::new(&[0x11; 40], w1).unwrap()
    });
    assert_independent("SPAKE2+ verifier w0", w0s, |w0| {
        VerifierRecord::from_w1(w0, &[0x33; 40]).unwrap()
    });
    assert_independent("SPAKE2+ verifier w1", w1s, |w1| {
        VerifierRecord::from_w1(&[0x11; 40], w1).unwrap()
    });
    let handshakes = [(w0s[0], w1s[0]), (w0s[1], w1s[1])];
    assert_independent("SPAKE2+ handshake", handshakes, |(w0, w1)| {
        let prover = ProverSecrets::new(w0, w1).unwrap();
        let record = VerifierRecord::from_w1(w0, w1).unwrap();
        let (share_p, prover) = prover
            .start(
                &RFC9383,
                &Session {
                    context: b"ctx",
                    id_prover: b"a",
                    id_verifier: b"b",
                },
            )
            .unwrap();
        let (share_v, confirm_v, verifier) = record
            .start(
                &RFC9383,
                &Session {
                    context: b"ctx",
                    id_prover: b"a",
                    id_verifier: b"b",
                },
                &share_p,
            )
            .unwrap();
        let (confirm_p, key) = prover.finish(&share_v, &confirm_v).unwrap();
        (key, verifier.finish(&confirm_p).unwrap())
    });
}

#[test]
fn mlkem() {
    use rind::kem::{Algorithm, DecapsulationKey, MlKem512, MlKem768, MlKem1024};
    fn check<A: Algorithm>() {
        assert_zeroed("ML-KEM key generation", || {
            DecapsulationKey::<A>::generate().unwrap()
        });
        let keys = [(); 2].map(|()| {
            let key = DecapsulationKey::<A>::generate().unwrap();
            let (ciphertext, _) = key.public_key().encapsulate().unwrap();
            (key, ciphertext)
        });
        assert_independent("ML-KEM decapsulation", keys, |(key, ciphertext)| {
            key.decapsulate(ciphertext)
        });
    }
    check::<MlKem512>();
    check::<MlKem768>();
    check::<MlKem1024>();
}

#[test]
fn hpke() {
    use rind::hpke::{
        AES_128_GCM, AES_256_GCM, CHACHA20_POLY1305, DHKEM_P256_HKDF_SHA256,
        DHKEM_P384_HKDF_SHA384, DHKEM_P521_HKDF_SHA512, DHKEM_X25519_HKDF_SHA256, Exporter,
        HKDF_SHA256, HKDF_SHA384, HKDF_SHA512, PrivateKey, Recipient, Sender, Suite,
    };
    for kem in [
        &DHKEM_X25519_HKDF_SHA256,
        &DHKEM_P256_HKDF_SHA256,
        &DHKEM_P384_HKDF_SHA384,
        &DHKEM_P521_HKDF_SHA512,
    ] {
        assert_zeroed("HPKE key generation", || PrivateKey::generate(kem).unwrap());
        let ikms = [[1u8; 64], [2u8; 64]];
        assert_independent("HPKE key derivation", ikms, |ikm| {
            PrivateKey::derive(kem, ikm).unwrap()
        });
        let keys = ikms.map(|ikm| PrivateKey::derive(kem, &ikm).unwrap());
        // One encapsulated key, which each key decapsulates to its own secret.
        let (enc, _) = Exporter::sender(&HKDF_SHA256, keys[0].public_key(), b"info").unwrap();
        for kdf in [&HKDF_SHA256, &HKDF_SHA384, &HKDF_SHA512] {
            for aead in [&AES_128_GCM, &AES_256_GCM, &CHACHA20_POLY1305] {
                let suite = Suite { kdf, aead };
                // The ephemeral key is random, so the sender must free nothing
                // unwiped.
                assert_zeroed("HPKE sender", || {
                    let (_, mut sender) =
                        Sender::new(suite, keys[0].public_key(), b"info").unwrap();
                    // Room for the tag, so sealing does not move the message.
                    let mut message = Vec::with_capacity(64);
                    message.extend_from_slice(b"message");
                    sender
                        .seal_in_place_append_tag(b"aad", &mut message)
                        .unwrap();
                    let mut out = [0u8; 32];
                    sender.export(b"context", &mut out).unwrap();
                    (message, out)
                });
                // The message is sealed to neither key, so both refuse it.
                assert_independent("HPKE recipient", keys.each_ref(), |key| {
                    let mut recipient = Recipient::new(suite, key, enc.as_ref(), b"info").unwrap();
                    let mut sealed = [0x5au8; 48];
                    let refused = recipient.open_in_place(b"aad", &mut sealed).is_err();
                    let mut out = [0u8; 32];
                    recipient.export(b"context", &mut out).unwrap();
                    (refused, out)
                });
            }
            assert_zeroed("HPKE export-only sender", || {
                let (_, exporter) = Exporter::sender(kdf, keys[0].public_key(), b"info").unwrap();
                let mut out = [0u8; 32];
                exporter.export(b"context", &mut out).unwrap();
                out
            });
            assert_independent("HPKE export-only recipient", keys.each_ref(), |key| {
                let exporter = Exporter::recipient(kdf, key, enc.as_ref(), b"info").unwrap();
                let mut out = [0u8; 32];
                exporter.export(b"context", &mut out).unwrap();
                out
            });
        }
    }
}

#[test]
fn oprf() {
    use rind::oprf::{
        Blind, P256_SHA256, P384_SHA384, P521_SHA512, RISTRETTO255_SHA512, ServerKey, voprf,
    };
    for suite in [
        &RISTRETTO255_SHA512,
        &P256_SHA256,
        &P384_SHA384,
        &P521_SHA512,
    ] {
        assert_zeroed("OPRF key generation", || {
            ServerKey::generate(suite).unwrap()
        });
        assert_zeroed("VOPRF key generation", || {
            voprf::ServerKey::generate(suite).unwrap()
        });
        let seeds = [[1u8; 32], [2u8; 32]];
        assert_independent("OPRF key derivation", seeds, |seed| {
            ServerKey::derive(suite, seed, b"info").unwrap()
        });
        assert_independent("VOPRF key derivation", seeds, |seed| {
            voprf::ServerKey::derive(suite, seed, b"info").unwrap()
        });

        let keys = seeds.map(|seed| ServerKey::derive(suite, &seed, b"info").unwrap());
        let (_, blinded) = Blind::new(suite, b"input").unwrap();
        assert_independent("OPRF evaluation", keys.each_ref(), |key| {
            (
                key.evaluate(b"input").unwrap(),
                key.blind_evaluate(blinded.as_ref()).unwrap(),
            )
        });
        // Finalizing frees nothing public, so it must free nothing unwiped,
        // the blind included.
        assert_zeroed_given(
            "OPRF finalization",
            || {
                let (blind, blinded) = Blind::new(suite, b"input").unwrap();
                (blind, keys[0].blind_evaluate(blinded.as_ref()).unwrap())
            },
            |(blind, evaluated)| blind.finalize(evaluated.as_ref()).unwrap(),
        );

        let keys = seeds.map(|seed| voprf::ServerKey::derive(suite, &seed, b"info").unwrap());
        assert_independent("VOPRF evaluation", keys.each_ref(), |key| {
            key.evaluate(b"input").unwrap()
        });
        let key = &keys[0];
        let public = voprf::PublicKey::new(suite, key.public_key().as_ref()).unwrap();
        let outputs = [b"input", b"other"].map(|input| key.evaluate(input).unwrap());
        // A batch of two blinds, its evaluation, and the proof of another
        // batch's.
        let batch = || {
            let (first, a) = voprf::Blind::new(suite, b"input").unwrap();
            let (second, b) = voprf::Blind::new(suite, b"other").unwrap();
            let blinded = [a.as_ref(), b.as_ref()].concat();
            let (evaluated, proof) = key.blind_evaluate(&blinded).unwrap();
            let (_, wrong) = key
                .blind_evaluate(&[b.as_ref(), a.as_ref()].concat())
                .unwrap();
            (vec![first, second], evaluated, proof, wrong)
        };
        // The proof's nonce is random, and the server frees the batch's
        // public terms, so the key is searched for.
        let scalar = key.to_scalar();
        assert_absent(
            "VOPRF blind evaluation",
            &[scalar.as_ref()],
            || {
                let (_, a) = voprf::Blind::new(suite, b"input").unwrap();
                let (_, b) = voprf::Blind::new(suite, b"other").unwrap();
                [a.as_ref(), b.as_ref()].concat()
            },
            |blinded| key.blind_evaluate(&blinded).unwrap(),
        );
        let secrets = [outputs[0].as_ref(), outputs[1].as_ref()];
        assert_absent(
            "VOPRF finalization",
            &secrets,
            || {
                let (blind, blinded) = voprf::Blind::new(suite, b"input").unwrap();
                let (evaluated, proof) = key.blind_evaluate(blinded.as_ref()).unwrap();
                (blind, evaluated, proof)
            },
            |(blind, evaluated, proof)| {
                blind
                    .finalize(evaluated.as_ref(), proof.as_ref(), &public)
                    .unwrap()
            },
        );
        assert_absent(
            "VOPRF batch finalization",
            &secrets,
            batch,
            |(blinds, evaluated, proof, _)| {
                voprf::Blind::finalize_batch(blinds, evaluated.as_ref(), proof.as_ref(), &public)
                    .unwrap()
            },
        );
        assert_absent(
            "VOPRF refused batch",
            &secrets,
            batch,
            |(blinds, evaluated, _, wrong)| {
                voprf::Blind::finalize_batch(blinds, evaluated.as_ref(), wrong.as_ref(), &public)
                    .unwrap_err()
            },
        );
    }
}

#[test]
fn frost() {
    use rind::frost::{
        ED25519_SHA512, P256_SHA256, RISTRETTO255_SHA512, SigningNonces, SigningPackage,
        SigningShare, deal,
    };
    for suite in [&ED25519_SHA512, &RISTRETTO255_SHA512, &P256_SHA256] {
        // Dealing and committing draw only randomness.
        assert_zeroed("FROST dealing", || deal(suite, 2, 3).unwrap());
        let (shares, commitment) = deal(suite, 2, 3).unwrap();
        assert_zeroed("FROST commitment", || {
            SigningNonces::commit(&shares[0]).unwrap()
        });
        // The package is public; signing consumes fresh nonces.
        assert_zeroed_given(
            "FROST signing",
            || {
                let (nonces, mine) = SigningNonces::commit(&shares[0]).unwrap();
                let (_, theirs) = SigningNonces::commit(&shares[1]).unwrap();
                let package =
                    SigningPackage::new(commitment.public_key(), &[mine, theirs], b"message")
                        .unwrap();
                (nonces, package)
            },
            // The package is returned, so its public blocks free after the
            // record stops.
            |(nonces, package)| (nonces.sign(&shares[0], &package).unwrap(), package),
        );
        // Loading a share checks it against the dealer's public commitment,
        // whose terms it frees.
        for share in &shares {
            let scalar = share.to_scalar();
            assert_absent(
                "FROST share load",
                &[scalar.as_ref()],
                || (),
                |()| SigningShare::from_scalar(share.identifier(), scalar.as_ref(), &commitment),
            );
        }
    }
}

#[test]
fn vrf() {
    use rind::vrf::{ECVRF_EDWARDS25519_SHA512_TAI, ECVRF_P256_SHA256_TAI, KeyPair};
    for algorithm in [&ECVRF_EDWARDS25519_SHA512_TAI, &ECVRF_P256_SHA256_TAI] {
        assert_zeroed("ECVRF key generation", || {
            KeyPair::generate(algorithm).unwrap()
        });
        let seeds = [[1u8; 32], [2u8; 32]];
        assert_independent("ECVRF load", seeds, |seed| {
            KeyPair::from_seed(algorithm, seed).unwrap()
        });
        let keys = seeds.map(|seed| KeyPair::from_seed(algorithm, &seed).unwrap());
        assert_independent("ECVRF proof", keys.each_ref(), |key| {
            key.prove(b"alpha").unwrap()
        });
    }
}

#[test]
fn blind_rsa() {
    use rind::blind_rsa::{
        KeyPair, RSABSSA_SHA384_PSS_DETERMINISTIC, RSABSSA_SHA384_PSS_RANDOMIZED,
        RSABSSA_SHA384_PSSZERO_DETERMINISTIC, RSABSSA_SHA384_PSSZERO_RANDOMIZED,
    };
    for algorithm in [
        &RSABSSA_SHA384_PSS_RANDOMIZED,
        &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
        &RSABSSA_SHA384_PSS_DETERMINISTIC,
        &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
    ] {
        for pkcs8 in rsa_keys() {
            assert_independent("blind RSA load", pkcs8.clone(), |der| {
                KeyPair::from_pkcs8(algorithm, der).unwrap()
            });
            let keys = pkcs8.map(|der| KeyPair::from_pkcs8(algorithm, &der).unwrap());
            // Below either modulus, whose top bit is set.
            let mut blinded = vec![0x5a; modulus_len(&keys[0])];
            blinded[0] = 0x01;
            assert_independent("blind RSA signing", keys.each_ref(), |key| {
                key.blind_sign(&blinded).unwrap()
            });
            // The blind is random, and the client's state is wiped on drop,
            // so blinding and finalizing must free nothing unwiped.
            let key = &keys[0];
            assert_zeroed("blind RSA blinding", || {
                key.public_key().blind(b"message").unwrap()
            });
            assert_zeroed_given(
                "blind RSA finalization",
                || {
                    let (blinded, blinding) = key.public_key().blind(b"message").unwrap();
                    (blinding, key.blind_sign(blinded.as_ref()).unwrap())
                },
                |(blinding, signature)| blinding.finalize(signature.as_ref()).unwrap(),
            );
            assert_zeroed_given(
                "blind RSA refused reply",
                || key.public_key().blind(b"message").unwrap().1,
                |blinding| blinding.finalize(&blinded).unwrap_err(),
            );
        }
    }
}

/// The modulus length of `key`, in bytes.
fn modulus_len(key: &rind::blind_rsa::KeyPair) -> usize {
    let (blinded, _) = key.public_key().blind(b"").unwrap();
    blinded.as_ref().len()
}

/// The AEADs, ciphers, key wrap, HKDF, and HMAC allocate nothing today; this
/// holds each to wiping if it starts to, on its success and refusal paths.
#[test]
fn symmetric() {
    use rind::aead::{
        self, AES_128_GCM, AES_192_GCM, AES_256_GCM, CHACHA20_POLY1305, Nonce, RandomizedNonceKey,
    };
    use rind::cipher::{
        AES_128, AES_192, AES_256, Aes, AesCbcDecryptingKey, AesCbcEncryptingKey, AesCtr, CbcIv,
        ChaCha20,
    };
    let keys = [[0x11u8; 32], [0x22u8; 32]];
    for algorithm in [&AES_128_GCM, &AES_192_GCM, &AES_256_GCM, &CHACHA20_POLY1305] {
        assert_independent(&format!("{algorithm:?}"), keys, |key| {
            let key = aead::Key::new(algorithm, &key[..algorithm.key_len()]).unwrap();
            let nonce = || Nonce::assume_unique_for_key([7; 12]);
            let mut message = [0x33u8; 80];
            let tag = key
                .seal_in_place_separate_tag(nonce(), b"aad", &mut message)
                .unwrap();
            let mut forged = [0x44u8; 96];
            let refused = key.open_in_place(nonce(), b"aad", &mut forged).is_err();
            (message, tag, refused)
        });
    }
    assert_independent("XChaCha20-Poly1305", keys, |key| {
        let key = RandomizedNonceKey::new(key);
        let mut forged = [0x44u8; 96];
        key.open_in_place([7; 24].into(), b"aad", &mut forged)
            .is_err()
    });
    for (algorithm, len) in [(&AES_128, 16), (&AES_192, 24), (&AES_256, 32)] {
        use rind::aead::gcm::{Iv, Key, TagLength};
        use rind::key_wrap::{AesKek, Mode};
        assert_independent("AES-GCM with a long IV", keys, |key| {
            let key = Key::new(algorithm, &key[..len], TagLength::Truncated32).unwrap();
            let iv = [7u8; 20];
            let mut message = [0x33u8; 80];
            let tag = key
                .seal_in_place_separate_tag(
                    Iv::assume_unique_for_key(&iv).unwrap(),
                    b"aad",
                    &mut message,
                )
                .unwrap();
            let mut forged = [0x44u8; 96];
            let refused = key
                .open_in_place(Iv::assume_unique_for_key(&iv).unwrap(), b"aad", &mut forged)
                .is_err();
            (message, tag, refused)
        });
        assert_independent("AES", keys, |key| {
            let mut block = [0x33u8; 16];
            Aes::new(algorithm, &key[..len])
                .unwrap()
                .encrypt_block(&mut block);
            let mut stream = [0x33u8; 80];
            AesCtr::new(algorithm, &key[..len], 32)
                .unwrap()
                .apply_keystream(&[0; 16], &mut stream)
                .unwrap();
            (block, stream)
        });
        assert_independent("AES-CBC", keys, |key| {
            let mut blocks = [0x33u8; 80];
            AesCbcEncryptingKey::new(algorithm, &key[..len])
                .unwrap()
                .encrypt_blocks(CbcIv::assume_unpredictable([7; 16]), &mut blocks)
                .unwrap();
            // Its padding fails to check under either key.
            let mut padded = [0x44u8; 80];
            let refused = AesCbcDecryptingKey::new(algorithm, &key[..len])
                .unwrap()
                .decrypt(&[7; 16], &mut padded)
                .is_err();
            (blocks, refused)
        });
        assert_independent("AES key wrap", keys, |key| {
            let kek = AesKek::new(algorithm, &key[..len]).unwrap();
            let mut wrapped = [0u8; 40];
            kek.wrap_key(Mode::Kw, &[0x33; 32], &mut wrapped).unwrap();
            let mut unwrapped = [0u8; 32];
            let refused = kek
                .unwrap_key(Mode::Kwp, &[0x44; 40], &mut unwrapped)
                .is_err();
            (wrapped, refused)
        });
    }
    assert_independent("ChaCha20", keys, |key| {
        let mut stream = [0x33u8; 80];
        ChaCha20::new(key)
            .apply_keystream(&[7; 12], 1, &mut stream)
            .unwrap();
        stream
    });
    for algorithm in [
        &aead::quic::AES_128,
        &aead::quic::AES_256,
        &aead::quic::CHACHA20,
    ] {
        assert_independent("QUIC header protection", keys, |key| {
            aead::quic::HeaderProtectionKey::new(algorithm, &key[..algorithm.key_len()])
                .unwrap()
                .mask(&[0x33; 16])
        });
    }

    use rind::hkdf::{HKDF_SHA256, HKDF_SHA384, HKDF_SHA512, Prk, Salt, legacy::HKDF_SHA1};
    use rind::hmac;
    for algorithm in [&HKDF_SHA1, &HKDF_SHA256, &HKDF_SHA384, &HKDF_SHA512] {
        assert_independent("HKDF", keys, |ikm| {
            let prk = Salt::new(algorithm, b"salt").extract(ikm).unwrap();
            let info: &[&[u8]] = &[b"info"];
            let mut out = [0u8; 200];
            prk.fill(info, &mut out).unwrap();
            let next = Prk::from(prk.expand(info, algorithm).unwrap());
            let key = aead::Key::from(prk.expand(info, &AES_256_GCM).unwrap());
            (out, next, key)
        });
    }
    for algorithm in [
        &hmac::legacy::HMAC_SHA1,
        &hmac::HMAC_SHA256,
        &hmac::HMAC_SHA384,
        &hmac::HMAC_SHA512,
    ] {
        // A key longer than a block is hashed first.
        let keys = [[0x11u8; 200], [0x22u8; 200]];
        for len in [32, 200] {
            assert_independent("HMAC", keys, |key| {
                let key = hmac::Key::new(algorithm, &key[..len]);
                let mut ctx = hmac::Context::with_key(&key);
                ctx.update(&[0x33; 3]);
                let tag = ctx.sign();
                let refused = hmac::verify(&key, b"message", &[0x44; 64]).is_err();
                (tag, refused)
            });
        }
    }
}
