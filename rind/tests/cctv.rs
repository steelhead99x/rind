//! C2SP's CCTV vectors that need only rind's public API. The ML-KEM vectors
//! inject randomness, so they run in `src/high/kem.rs`, and RFC 6979's
//! rejection vector in `src/high/ecdsa.rs`.

// aws-lc's C, which Miri cannot run, checks each vector on native targets.
// wasm cannot build aws-lc, so there `ed25519-verdicts.txt`, aws-lc's
// recorded verdicts, stands in for it.
#![cfg(not(miri))]

#[cfg(not(target_family = "wasm"))]
use aws_lc_rs::signature::{ED25519, UnparsedPublicKey};
use rind::Error;
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
        "{}/../thirdparty/vectors/cctv/ed25519/ed25519vectors.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let file = std::fs::File::open(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
    let vectors: Vec<Ed25519Vector> = serde_json::from_reader(file).unwrap();
    assert_eq!(vectors.len(), 914);
    // The verdict file is indexed by vector number.
    for (i, v) in vectors.iter().enumerate() {
        assert_eq!(v.number, i, "{path}");
    }
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
            // Messages name the line as editors and grep number it.
            let at = i + 1;
            let mut parts = line.split(' ');
            let number: usize = parts
                .next()
                .unwrap_or_else(|| panic!("{path}:{at}: missing number"))
                .parse()
                .unwrap_or_else(|_| panic!("{path}:{at}: bad number"));
            let verdict = parts
                .next()
                .unwrap_or_else(|| panic!("{path}:{at}: missing verdict"));
            assert!(parts.next().is_none(), "{path}:{at}: trailing text");
            assert_eq!(number, i, "{path}:{at}");
            match verdict {
                "accept" => true,
                "reject" => false,
                other => panic!("{path}:{at}: {other}"),
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

/// The recorded file stays equal to aws-lc, which wasm cannot ask. A change
/// in aws-lc fails here with the vector numbers to flip in the file.
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
// a small-order key outright. aws-lc's verdicts are the recorded ones, which
// `ed25519_verdicts_match_aws_lc` holds to aws-lc where it builds.
#[test]
fn ed25519_edge_cases() {
    let verdicts = ed25519_verdicts();
    let mut failures = Vec::new();
    for v in ed25519_vectors() {
        let ours =
            rind::ed25519::PublicKey::new(&v.key).map(|key| key.verify(v.msg.as_bytes(), &v.sig));
        let flags = v.flags.as_deref().unwrap_or(&[]);
        let mut fail = |msg: String| failures.push(format!("{}: {flags:?}: {msg}", v.number));
        match ours {
            Ok(result) => {
                // A `low_order_A` point the small-order filter does not catch
                // is judged like any other accepted key.
                match &result {
                    Ok(()) | Err(Error::BadSignature) => {}
                    Err(e) => {
                        fail(format!("{e:?}"));
                        continue;
                    }
                }
                if result.is_ok() != verdicts[v.number] {
                    fail(format!("ours {result:?}, file {}", verdicts[v.number]));
                }
            }
            Err(Error::KeyRejected(e)) => {
                if !flags.iter().any(|f| f == "low_order_A")
                    || !e.to_string().contains("small-order")
                {
                    fail(format!("{e}"));
                }
            }
            Err(e) => fail(format!("{e:?}")),
        }
    }
    assert!(
        failures.is_empty(),
        "ed25519 edge cases:\n{}",
        failures.join("\n")
    );
}
