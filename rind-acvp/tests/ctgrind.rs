//! Constant-time checks for the secret paths `rind-acvp` adds over rind, run
//! under valgrind by `admin/ctgrind`.
//!
//! Secret arguments are marked undefined, so memcheck flags any branch or
//! memory index that depends on them. Replies are marked defined before the
//! test checks them. rind itself marks the keys it generates or parses: an
//! RSA exponent at its public length, before the load, and
//! an ML-KEM decapsulation key's `dk_pke` and `z`, since its check reads
//! `ek` and `H(ek)`.

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use rind::agreement::{ECDH_P256, ECDH_P384, ECDH_P521, PrivateKey};
use rind_acvp::{Reply, handle};

/// Marks `value`'s bytes secret. Pass the bytes, not a `Vec`: its header
/// holds the public length.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value`'s bytes public, so the test may branch on them.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

/// Every span of `reply`, marked public.
fn reveal(reply: &Reply) -> Vec<Vec<u8>> {
    reply
        .slices()
        .into_iter()
        .map(|part| {
            let part = part.to_vec();
            public(part.as_slice());
            part
        })
        .collect()
}

fn run(command: &str, args: &[Vec<u8>]) -> Vec<Vec<u8>> {
    reveal(&handle(command, args).unwrap())
}

/// ECDH with ACVP's given private scalar, at the field's width and with a
/// zero prefix whose public length fixes how many bytes are checked.
#[test]
fn ecdh_given_scalar() {
    for (curve, alg, field) in [("P-256", &ECDH_P256, 32), ("P-384", &ECDH_P384, 48)] {
        let peer = PrivateKey::from_scalar(alg, &vec![0x03; field]).unwrap();
        let point = peer.public_key().as_ref().to_vec();
        let (x, y) = point[1..].split_at(field);
        let args = |scalar: Vec<u8>| vec![x.to_vec(), y.to_vec(), scalar];
        let wanted = run(&format!("ECDH/{curve}"), &args(vec![0x02; field]));
        let scalar = vec![0x02; field];
        secret(scalar.as_slice());
        assert_eq!(
            run(&format!("ECDH/{curve}"), &args(scalar)),
            wanted,
            "{curve}"
        );
        // One public padding byte, then the same field. The prefix length is
        // public; the field bytes stay secret.
        let mut padded = vec![0u8];
        padded.extend(std::iter::repeat_n(0x02, field));
        secret(padded.as_slice());
        assert_eq!(
            run(&format!("ECDH/{curve}"), &args(padded)),
            wanted,
            "{curve} padded"
        );
    }
}

/// ECDSA signing normalizes a secret scalar once for both key loaders.
/// Every accepted encoding signs for the same public key.
#[test]
fn ecdsa_given_scalar() {
    for (curve, alg, field, hash) in [
        ("P-256", &ECDH_P256, 32, "SHA2-256"),
        ("P-384", &ECDH_P384, 48, "SHA2-384"),
        ("P-521", &ECDH_P521, 66, "SHA2-512"),
    ] {
        let mut canonical = vec![0u8; field];
        canonical[field - 1] = 2;
        let key = PrivateKey::from_scalar(alg, &canonical).unwrap();
        let point = key.public_key().as_ref();
        let (x, y) = point[1..].split_at(field);
        let mut padded = vec![0u8; 2];
        padded.extend_from_slice(&canonical);
        for scalar in [canonical, vec![2], padded] {
            secret(scalar.as_slice());
            let signature = run(
                "ECDSA/sigGen",
                &[
                    curve.as_bytes().to_vec(),
                    scalar,
                    hash.as_bytes().to_vec(),
                    b"message".to_vec(),
                ],
            );
            let verified = run(
                "ECDSA/sigVer",
                &[
                    curve.as_bytes().to_vec(),
                    hash.as_bytes().to_vec(),
                    b"message".to_vec(),
                    x.to_vec(),
                    y.to_vec(),
                    signature[0].clone(),
                    signature[1].clone(),
                ],
            );
            assert_eq!(verified[0], [1], "{curve}");
        }
        let mut overlong = vec![1u8];
        overlong.resize(field + 1, 0);
        secret(overlong.as_slice());
        assert!(
            handle(
                "ECDSA/sigGen",
                &[
                    curve.as_bytes().to_vec(),
                    overlong,
                    hash.as_bytes().to_vec(),
                    b"message".to_vec(),
                ],
            )
            .is_err(),
            "{curve} nonzero prefix"
        );
    }
}

/// A hmacDRBG command's suffix, its arguments, and which of them are entropy.
type DrbgCase = (&'static str, Vec<Vec<u8>>, &'static [usize]);

/// hmacDRBG's entropy inputs, through rind's HMAC_DRBG, for the plain,
/// reseed, and prediction-resistance commands.
#[test]
fn hmac_drbg_entropy() {
    let len = 80u32.to_ne_bytes().to_vec();
    for hash in ["SHA-1", "SHA2-256", "SHA2-384", "SHA2-512"] {
        // generate: length, entropy, personalisation, ad1, ad2, nonce.
        // reseed: length, entropy, personalisation, reseed ad,
        // reseed entropy, ad1, ad2, nonce. pr: length, entropy,
        // personalisation, ad1, entropy1, ad2, entropy2, nonce.
        let cases: [DrbgCase; 3] = [
            (
                "",
                vec![
                    len.clone(),
                    vec![0x5a; 32],
                    b"p".to_vec(),
                    b"a1".to_vec(),
                    b"a2".to_vec(),
                    vec![0xa5; 16],
                ],
                &[1],
            ),
            (
                "-reseed",
                vec![
                    len.clone(),
                    vec![0x5a; 32],
                    b"p".to_vec(),
                    b"r".to_vec(),
                    vec![0x3c; 32],
                    b"a1".to_vec(),
                    b"a2".to_vec(),
                    vec![0xa5; 16],
                ],
                &[1, 4],
            ),
            (
                "-pr",
                vec![
                    len.clone(),
                    vec![0x5a; 32],
                    b"p".to_vec(),
                    b"a1".to_vec(),
                    vec![0x3c; 32],
                    b"a2".to_vec(),
                    vec![0x69; 32],
                    vec![0xa5; 16],
                ],
                &[1, 4, 6],
            ),
        ];
        for (kind, args, secrets) in cases {
            let command = format!("hmacDRBG{kind}/{hash}");
            let wanted = run(&command, &args);
            assert_eq!(wanted[0].len(), 80, "{command}");
            for &i in secrets {
                secret(args[i].as_slice());
            }
            assert_eq!(run(&command, &args), wanted, "{command}");
        }
    }
}

/// ML-KEM-768 keyGen from secret `d` and `z`, encap of a secret message, and
/// decap with a key ACVP hands over, for a ciphertext the key accepts and
/// one it rejects.
#[test]
fn mlkem768() {
    let keygen = |d: Vec<u8>, z: Vec<u8>| run("ML-KEM/ML-KEM-768/keyGen", &[d, z]);
    let wanted = keygen(vec![0x5a; 32], vec![0x3c; 32]);
    let (d, z) = (vec![0x5a; 32], vec![0x3c; 32]);
    secret(d.as_slice());
    secret(z.as_slice());
    let generated = keygen(d, z);
    assert_eq!(generated, wanted);
    let (ek, dk) = (generated[0].clone(), generated[1].clone());

    let m = vec![0xa5; 32];
    let wanted = run("ML-KEM/ML-KEM-768/encap", &[ek.clone(), m.clone()]);
    secret(m.as_slice());
    let sealed = run("ML-KEM/ML-KEM-768/encap", &[ek, m]);
    assert_eq!(sealed, wanted);

    let mut ciphertext = sealed[0].clone();
    let opened = run("ML-KEM/ML-KEM-768/decap", &[dk.clone(), ciphertext.clone()]);
    assert_eq!(opened[0], sealed[1]);
    ciphertext[0] ^= 1;
    let rejected = run("ML-KEM/ML-KEM-768/decap", &[dk, ciphertext]);
    assert_ne!(rejected[0], sealed[1]);
}

/// The RSA signature and decryption primitives with a secret `d`, which rind
/// marks before loading it at its public width.
#[test]
fn rsa_primitives() {
    let mut n = vec![0xc3u8; 256];
    n[255] = 0xc5;
    let d = vec![0x5a; 256];
    let e = vec![0x01, 0x00, 0x01];
    let message = vec![0x11; 256];
    secret(d.as_slice());
    let signed = run(
        "RSA/signaturePrimitive",
        &[d.clone(), n.clone(), e.clone(), message.clone()],
    );
    assert_eq!(signed[0], [1]);
    let mut leading = vec![0u8; 256];
    leading[253..].fill(0x5a);
    secret(leading.as_slice());
    let from_leading = run(
        "RSA/signaturePrimitive",
        &[leading, n.clone(), e.clone(), message.clone()],
    );
    assert_eq!(from_leading[0], [1]);
    let short = vec![0x5a; 3];
    secret(short.as_slice());
    let from_short = run(
        "RSA/signaturePrimitive",
        &[short, n.clone(), e.clone(), message.clone()],
    );
    assert_eq!(from_leading[1], from_short[1]);
    let decrypted = run("RSA/decryptionPrimitive", &[message, d, n, e]);
    assert_eq!(decrypted, signed);
}

/// ML-DSA sigGen with a secret expanded key and a secret `rnd`, against the
/// key keyGen returns from a secret seed.
#[test]
fn mldsa_siggen() {
    let seed = vec![0x5a; 32];
    secret(seed.as_slice());
    let generated = run("ML-DSA/ML-DSA-44/keyGen", &[seed]);
    let sk = generated[1].clone();
    let sign = |sk: Vec<u8>, rnd: Vec<u8>| {
        // sk, message, mu, rnd, context, externalMu.
        run(
            "ML-DSA/ML-DSA-44/sigGen",
            &[
                sk,
                b"message".to_vec(),
                Vec::new(),
                rnd,
                b"ctx".to_vec(),
                vec![0],
            ],
        )
    };
    let wanted = sign(sk.clone(), vec![0xa5; 32]);
    let rnd = vec![0xa5; 32];
    secret(sk.as_slice());
    secret(rnd.as_slice());
    assert_eq!(sign(sk, rnd), wanted);
}
