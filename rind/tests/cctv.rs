//! C2SP's CCTV vectors that need only rind's public API. The ML-KEM vectors
//! inject randomness, so they run in `src/high/kem.rs`, and RFC 6979's
//! rejection vector in `src/high/ecdsa.rs`.

// Miri does not run this file (`cfg(not(miri))`): the recorded verdicts come
// from aws-lc, which Miri cannot execute. wasm cannot build aws-lc either.
// `tests/cctv/ed25519-verdicts.txt` is aws-lc's accept/reject for each vector.
// `ed25519_verdicts_match_aws_lc` checks that file against aws-lc where aws-lc
// builds, and every run of `ed25519_edge_cases`, including wasm, checks rind
// against the file.
#![cfg(not(miri))]

#[cfg(not(target_family = "wasm"))]
use aws_lc_rs::signature::{ED25519, UnparsedPublicKey};
use rind::Error;
use rind::signature::{self, verify};
use serde::Deserialize;

#[derive(Deserialize)]
struct Ed25519Vector {
    number: usize,
    #[serde(with = "hex::serde")]
    key: Vec<u8>,
    #[serde(with = "hex::serde")]
    sig: Vec<u8>,
    msg: String,
    flags: Option<Vec<String>>,
}

fn ed25519_vectors() -> Vec<Ed25519Vector> {
    let path = format!(
        "{}/../thirdparty/cctv/ed25519/ed25519vectors.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let file = std::fs::File::open(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
    let vectors: Vec<Ed25519Vector> = serde_json::from_reader(file).unwrap();
    assert_eq!(vectors.len(), 914);
    vectors
}

/// aws-lc's verify verdict for each vector, `true` when aws-lc accepts.
/// Line `n` is vector `n`, `accept` or `reject`.
fn ed25519_verdicts() -> Vec<bool> {
    let path = format!(
        "{}/tests/cctv/ed25519-verdicts.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    let text = std::fs::read_to_string(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
    let verdicts: Vec<bool> = text
        .lines()
        .enumerate()
        .map(|(i, line)| {
            let mut parts = line.split(' ');
            let number: usize = parts
                .next()
                .unwrap_or_else(|| panic!("{path}:{i}: missing number"))
                .parse()
                .unwrap_or_else(|_| panic!("{path}:{i}: bad number"));
            let verdict = parts
                .next()
                .unwrap_or_else(|| panic!("{path}:{i}: missing verdict"));
            assert!(parts.next().is_none(), "{path}:{i}: trailing text");
            assert_eq!(number, i, "{path}:{i}");
            match verdict {
                "accept" => true,
                "reject" => false,
                other => panic!("{path}:{i}: {other}"),
            }
        })
        .collect();
    assert_eq!(verdicts.len(), 914, "{path}");
    verdicts
}

#[cfg(not(target_family = "wasm"))]
fn aws_lc_accepts(vector: &Ed25519Vector) -> bool {
    UnparsedPublicKey::new(&ED25519, &vector.key)
        .verify(vector.msg.as_bytes(), &vector.sig)
        .is_ok()
}

/// The recorded file stays equal to aws-lc. wasm reads the same file.
#[cfg(not(target_family = "wasm"))]
#[test]
fn ed25519_verdicts_match_aws_lc() {
    let verdicts = ed25519_verdicts();
    for vector in ed25519_vectors() {
        assert_eq!(
            aws_lc_accepts(&vector),
            verdicts[vector.number],
            "{}",
            vector.number
        );
    }
}

// Low-order and non-canonical points as Ed25519's `A` and `R`, from "Taming
// the many EdDSAs". rind verifies each as aws-lc does, except that it refuses
// a small-order key outright. The accept/reject of a key rind does accept is
// the recorded aws-lc verdict.
#[test]
fn ed25519_edge_cases() {
    let verdicts = ed25519_verdicts();
    for v in ed25519_vectors() {
        let ours = signature::PublicKey::new(&verify::ED25519, &v.key)
            .map(|key| key.verify(v.msg.as_bytes(), &v.sig));
        let flags = v.flags.unwrap_or_default();
        match ours {
            Ok(result) => {
                assert!(
                    !flags.iter().any(|f| f == "low_order_A"),
                    "{}: {flags:?}: a small-order key was accepted",
                    v.number
                );
                match &result {
                    Ok(()) | Err(Error::BadSignature) => {}
                    Err(e) => panic!("{}: {flags:?}: {e:?}", v.number),
                }
                assert_eq!(
                    result.is_ok(),
                    verdicts[v.number],
                    "{}: {flags:?}: ours {result:?}",
                    v.number
                );
            }
            Err(Error::KeyRejected(e)) => {
                assert!(
                    flags.iter().any(|f| f == "low_order_A"),
                    "{}: {flags:?}: {e}",
                    v.number
                );
                assert!(e.to_string().contains("small-order"), "{}: {e}", v.number);
            }
            Err(e) => panic!("{}: {e:?}", v.number),
        }
    }
}
