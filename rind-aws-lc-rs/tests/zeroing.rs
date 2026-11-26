//! Checks that the secret copies rind-aws-lc-rs keeps on the heap, beyond
//! the rind keys it wraps, are wiped before they are freed.
//!
//! rind's own `tests/zeroing.rs` checks that its keys wipe themselves. This
//! one records the blocks freed while the values that held a secret are
//! dropped, and checks none still holds it. Inline values are boxed so they
//! live on the heap too.

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

/// An ML-DSA seed and public key, and the PKCS#8 documents holding the seed.
#[test]
fn ml_dsa() {
    let seed: [u8; 32] = distinct(5);
    let public_key = signature::PqdsaKeyPair::from_seed(&signature::ML_DSA_65_SIGNING, &seed)
        .unwrap()
        .public_key()
        .as_ref()
        .to_vec();
    // The public key's bytes past its public seed `rho`.
    let public_needle = &public_key[32..];
    for needle in [&seed[..], public_needle] {
        let leaked = leaks(needle, || {
            let key =
                signature::PqdsaKeyPair::from_seed(&signature::ML_DSA_65_SIGNING, &seed).unwrap();
            let _clone = key.clone();
            let _public = key.public_key().clone();
            let _v1 = key.to_pkcs8v1().unwrap();
            let _der: Pkcs8V1Der<'static> = key.private_key().as_der().unwrap();
        });
        assert_eq!(leaked, 0);
    }
}

/// An expanded ML-DSA private key, loaded raw, which the adapter wraps in
/// PKCS#8 itself, and loaded from a PKCS#8 document in expanded form. The
/// keys are loaded before the check: the PKCS#8 copy loading makes lives
/// only inside the call, which the repository leaves unwiped. The needle is
/// FIPS 204's `K`, after `rho`, which the public key repeats.
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
    let pkcs8 = expanded_pkcs8(&raw);
    for key in [
        signature::PqdsaKeyPair::from_raw_private_key(&signature::ML_DSA_44_SIGNING, &raw).unwrap(),
        signature::PqdsaKeyPair::from_pkcs8(&signature::ML_DSA_44_SIGNING, &pkcs8).unwrap(),
    ] {
        let key = Box::new(key);
        let leaked = leaks(secret, || {
            let clone = key.clone();
            assert!(clone.to_pkcs8v1().is_err());
            let mut sig = vec![0; signature::ML_DSA_44_SIGNING.signature_len()];
            clone.sign(b"expanded", &mut sig).unwrap();
            drop(clone);
            drop(key);
        });
        assert_eq!(leaked, 0);
    }
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

/// A DER element, for the documents below.
fn der(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    match body.len() {
        len @ 0..=0x7f => out.push(len as u8),
        len @ 0x80..=0xff => out.extend([0x81, len as u8]),
        len => out.extend([0x82, (len >> 8) as u8, len as u8]),
    }
    out.extend_from_slice(body);
    out
}

/// PKCS#8 v1 around `private_key`, with `algorithm`'s contents.
fn pkcs8(algorithm: &[u8], private_key: &[u8]) -> Vec<u8> {
    der(
        0x30,
        &[
            &[0x02, 0x01, 0x00][..],
            &der(0x30, algorithm),
            &der(0x04, private_key),
        ]
        .concat(),
    )
}

/// Counts the blocks freed while `PqdsaKeyPair::from_pkcs8` refuses or loads
/// `doc`, and drops what it returned, that still hold `needle`'s bytes.
fn pqdsa_leaks(doc: &[u8], needle: &[u8], expected: Result<(), &str>) -> usize {
    leaks(needle, || {
        let result = signature::PqdsaKeyPair::from_pkcs8(&signature::ML_DSA_44_SIGNING, doc);
        match expected {
            Ok(()) => assert!(result.is_ok()),
            Err(kind) => assert_eq!(result.err().unwrap().description_(), kind),
        }
    })
}

const EC_PUBLIC_KEY: [u8; 9] = [0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];

/// The "another algorithm" checks in `PqdsaKeyPair::from_pkcs8` that copy a
/// private key: EC keys on a curve rind cannot back, consistent and not; RSA
/// keys below 2048 bits, consistent and not; and the PKCS#8 documents the
/// adapter rebuilds, for a P-256 key with explicit parameters, a hybrid
/// public key, or a short scalar, and for an ML-DSA seed followed by stray
/// bytes. Every heap copy of the scalar, the RSA primes, or the seed is
/// wiped before it is freed, on refusal and on success.
#[test]
fn key_type_checks() {
    // secp256k1: OpenSSL's key, then its scalar with G as the public key.
    let sec1 = include_bytes!("unbacked/secp256k1.der");
    let scalar = sec1[7..39].to_vec();
    let k1 = [
        &EC_PUBLIC_KEY[..],
        &der(0x06, &[0x2b, 0x81, 0x04, 0x00, 0x0a]),
    ]
    .concat();
    assert_eq!(
        pqdsa_leaks(&pkcs8(&k1, sec1), &scalar, Err("WrongAlgorithm")),
        0
    );
    let g = hex::decode("0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8").unwrap();
    let mismatched = der(
        0x30,
        &[
            der(0x02, &[1]),
            der(0x04, &scalar),
            der(0xa1, &der(0x03, &[&[0][..], &g].concat())),
        ]
        .concat(),
    );
    assert_eq!(
        pqdsa_leaks(&pkcs8(&k1, &mismatched), &scalar, Err("InvalidEncoding")),
        0
    );

    // RSA-1024 from Wycheproof, then with its CRT coefficient corrupted; the
    // needle is the start of p.
    let rsa = hex::decode("30820277020100300d06092a864886f70d0101010500048202613082025d02010002818100d8917628e8923e137bea7c3e38e8b3c9f450c7a367d600e1a8c11342f058ffe805489d4d92f8588d014f18e5c27cea30fa644e71d46696447c44503bb9dc52e51422a571a85bf4a905da23f9ea59ce30b5f2eec76dab1c16944ea8b48483028202d18480d7e0e3ce78d078a6b783c33431dac86e34faf55cb3b6e0211ff2424b02030100010281807957874d04826c259e989364899e589e1f35e3a5bad83d4632b77b83560787db089ad7085000b61ccb4ef63445f4978339c859eb8d86ad4b5215349f4254205d117f98e11bb3557e3c6c2f5b2858992e43c5e07c9434f40c3852bbbd3587eb6bb3cea25cbc90a71de1ce189b83ff90daa4e3155fcc623cc5eec74a942f1c8901024100fde3a3ce09c42388577b89b51f698f0bacb8901009b5e2dabc0ffd87603827b341fc7c9a6de912f4590eebb35efc4b8639fb8b1a7a68bdb8a6e10987783a8f79024100da5e63e8305a91c2137849ae4328e6dcff7e9b617777c991340e1e11ea5d244aafeaa0c0624a1c9a41ce4e4e47b84a8b202802135aa06e7704276ce2a698dae3024100b53d8bf1c986fad6999cd6f1353b65a22fea90ece201b5aff0107a2be9c42c930ac7f32b4acad77d17164fabfc629e87735cde3048b1fcbd94639129e3e9ea0102402246b4a9ea851ce1f8ca65ce5bae5ce68d9822ed9ea207daa9f0195a388e5c36f8fbfc359678099b50ff001d9b765b05118c161f5197631f7d606edff8c47f7f024100d84310b6d51b56e7e5f32aa5f09ef77ef2aa0d13a592228c418a9794276beea194345cdf5c1003ab48a83a1dd3c99ef87e6bd8b47dd3d5e423b348ac0da5ac7b").unwrap();
    let p = rsa
        .windows(3)
        .position(|w| w == [0x02, 0x41, 0x00])
        .unwrap()
        + 3;
    let prime = rsa[p..p + NEEDLE_LEN].to_vec();
    // The check holds p as little-endian 64-bit limbs, whose bytes in memory
    // are p's reversed: look for that too.
    let limbs: Vec<u8> = rsa[p..p + 64].iter().rev().copied().collect();
    let mut bad = rsa.clone();
    *bad.last_mut().unwrap() ^= 1;
    for needle in [&prime[..], &limbs[..NEEDLE_LEN]] {
        assert_eq!(pqdsa_leaks(&rsa, needle, Err("WrongAlgorithm")), 0);
        assert_eq!(pqdsa_leaks(&bad, needle, Err("InvalidEncoding")), 0);
    }

    // P-256, generated by rind, with explicit parameters, with a hybrid
    // public key, and with a scalar of 31 bytes.
    let explicit = include_bytes!("../src/evp/p256.der");
    let named = der(0x06, &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]);
    let generated =
        signature::EcdsaKeyPair::generate(&signature::ECDSA_P256_SHA256_FIXED_SIGNING).unwrap();
    let doc = generated.to_pkcs8v1().unwrap();
    // The scalar is the 32 bytes after the ECPrivateKey's OCTET STRING header.
    let at = doc
        .as_ref()
        .windows(2)
        .position(|w| w == [0x04, 0x20])
        .unwrap()
        + 2;
    let scalar = doc.as_ref()[at..at + 32].to_vec();
    let point = generated.public_key().as_ref().to_vec();
    let ec = |scalar: &[u8], point: &[u8]| {
        der(
            0x30,
            &[
                der(0x02, &[1]),
                der(0x04, scalar),
                der(0xa1, &der(0x03, &[&[0][..], point].concat())),
            ]
            .concat(),
        )
    };
    let algorithm = [&EC_PUBLIC_KEY[..], explicit].concat();
    assert_eq!(
        pqdsa_leaks(
            &pkcs8(&algorithm, &ec(&scalar, &point)),
            &scalar,
            Err("WrongAlgorithm")
        ),
        0
    );
    let mut hybrid = point.clone();
    hybrid[0] = 0x06 | (point[64] & 1);
    let algorithm = [&EC_PUBLIC_KEY[..], &named].concat();
    assert_eq!(
        pqdsa_leaks(
            &pkcs8(&algorithm, &ec(&scalar, &hybrid)),
            &scalar,
            Err("WrongAlgorithm")
        ),
        0
    );
    let short = [&[0u8; 31][..], &[0x2a]].concat();
    let short_doc = pkcs8(
        &algorithm,
        &der(0x30, &[der(0x02, &[1]), der(0x04, &short[31..])].concat()),
    );
    // A one-byte scalar has no distinct bytes; the padded copy is what holds
    // it, so look for the zeros that pad it and the byte.
    assert_eq!(
        pqdsa_leaks(&short_doc, &short[16..], Err("WrongAlgorithm")),
        0
    );

    // ML-DSA-44 from a seed, with a byte after the document: the adapter
    // rebuilds it without the byte, then rind loads it.
    let seed: [u8; 32] = distinct(0x51);
    let mldsa = [
        0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x11,
    ];
    let mut seeded = pkcs8(&mldsa, &der(0x80, &seed));
    seeded.push(0);
    assert_eq!(pqdsa_leaks(&seeded, &seed, Ok(())), 0);
}
