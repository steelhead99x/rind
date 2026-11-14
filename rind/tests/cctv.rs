//! C2SP's CCTV vectors that need only rind's public API. The ML-KEM vectors
//! inject randomness, so they run in `src/high/kem.rs`, and RFC 6979's
//! rejection vector in `src/high/ecdsa.rs`. A mismatch with
//! `ed25519-verdicts.txt` fails the test.

// Miri does not run this file (`cfg(not(miri))`): its native tests call
// aws-lc's C, which Miri cannot execute, and checking all 914 vectors against
// the recorded file would be slow under it. wasm cannot build aws-lc either.
// `tests/cctv/ed25519-verdicts.txt` is aws-lc's accept/reject for each vector.
// `ed25519_verdicts_match_aws_lc` checks that file against aws-lc where aws-lc
// builds. `ed25519_edge_cases` checks rind against the file on every target,
// and on native targets also against live aws-lc. `ed25519_record_aws_lc_verdicts`
// rewrites the file from aws-lc. It is ignored, and writes only with
// `RIND_RECORD_VERDICTS=1`, so `--include-ignored` runs alongside the readers
// without touching the file.
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

fn ed25519_verdicts_path() -> String {
    format!(
        "{}/tests/cctv/ed25519-verdicts.txt",
        env!("CARGO_MANIFEST_DIR")
    )
}

/// aws-lc's verify verdict for each vector, `true` when aws-lc accepts.
/// Line `n` is vector `n`, `accept` or `reject`.
fn ed25519_verdicts() -> Vec<bool> {
    let path = ed25519_verdicts_path();
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

/// Rewrites `tests/cctv/ed25519-verdicts.txt` from aws-lc when
/// `RIND_RECORD_VERDICTS=1`, and otherwise does nothing.
///
/// Other tests in this binary read the file at the same time, so the new
/// text goes to a temporary file that then replaces it by a rename: a reader
/// sees the old file or the new one, never a partial one.
#[cfg(not(target_family = "wasm"))]
#[test]
#[ignore = "rewrites rind/tests/cctv/ed25519-verdicts.txt from aws-lc"]
fn ed25519_record_aws_lc_verdicts() {
    if std::env::var_os("RIND_RECORD_VERDICTS").is_none_or(|value| value != "1") {
        eprintln!("set RIND_RECORD_VERDICTS=1 to rewrite the verdicts file");
        return;
    }
    let path = ed25519_verdicts_path();
    let vectors = ed25519_vectors();
    let mut text = String::new();
    for (i, vector) in vectors.iter().enumerate() {
        assert_eq!(vector.number, i);
        let verdict = if aws_lc_accepts(vector) {
            "accept"
        } else {
            "reject"
        };
        text.push_str(&format!("{i} {verdict}\n"));
    }
    // Include the process id so two recording runs, such as two worktrees
    // sharing a target directory, do not share a temporary path.
    let temporary = format!("{path}.{}.tmp", std::process::id());
    std::fs::write(&temporary, &text)
        .unwrap_or_else(|err| panic!("cannot write {temporary}: {err}"));
    // On Windows, rename fails if another test still has the file open.
    // Retry briefly; a reader then sees the old file or the new one.
    let mut last_err = None;
    for _ in 0..16 {
        match std::fs::rename(&temporary, &path) {
            Ok(()) => {
                last_err = None;
                break;
            }
            Err(err) => {
                last_err = Some(err);
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
        }
    }
    if let Some(err) = last_err {
        // Leave no stray temporary file in the source tree.
        let _ = std::fs::remove_file(&temporary);
        panic!("cannot replace {path}: {err}");
    }
    // The file reads back as written and parses as the readers parse it.
    let written = std::fs::read_to_string(&path).unwrap();
    assert_eq!(written, text, "{path}");
    ed25519_verdicts();
}

// Low-order and non-canonical points as Ed25519's `A` and `R`, from "Taming
// the many EdDSAs". rind verifies each as aws-lc does, except that it refuses
// a small-order key outright. The accept/reject of a key rind does accept is
// the recorded aws-lc verdict.
#[test]
fn ed25519_edge_cases() {
    let verdicts = ed25519_verdicts();
    let mut failures = Vec::new();
    for v in ed25519_vectors() {
        let ours = signature::PublicKey::new(&verify::ED25519, &v.key)
            .map(|key| key.verify(v.msg.as_bytes(), &v.sig));
        let flags = v.flags.as_deref().unwrap_or(&[]);
        let mut fail = |msg: String| failures.push(format!("{}: {flags:?}: {msg}", v.number));
        match ours {
            Ok(result) => {
                if flags.iter().any(|f| f == "low_order_A") {
                    fail("a small-order key was accepted".into());
                    continue;
                }
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
                // Native targets have aws-lc, so a stale file cannot hide a
                // difference when this test runs alone.
                #[cfg(not(target_family = "wasm"))]
                if result.is_ok() != aws_lc_accepts(&v) {
                    fail(format!("ours {result:?}, aws-lc {}", aws_lc_accepts(&v)));
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
