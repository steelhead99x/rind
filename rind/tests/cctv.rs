//! C2SP's CCTV vectors that need only rind's public API. The ML-KEM vectors
//! inject randomness, so they run in `src/high/kem.rs`, and RFC 6979's
//! rejection vector in `src/high/ecdsa.rs`.

// Each vector is checked against aws-lc, which Miri cannot run and which
// does not build for wasm. Those targets still run the vectors: a small-order
// key is rejected, and any other key is not.
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

// Low-order and non-canonical points as Ed25519's `A` and `R`, from "Taming
// the many EdDSAs". rind verifies each as aws-lc does, except that it refuses
// a small-order key outright.
#[test]
fn ed25519_edge_cases() {
    let path = format!(
        "{}/../thirdparty/cctv/ed25519/ed25519vectors.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let file = std::fs::File::open(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
    let vectors: Vec<Ed25519Vector> = serde_json::from_reader(file).unwrap();
    assert_eq!(vectors.len(), 914);

    for v in vectors {
        #[cfg(not(target_family = "wasm"))]
        let theirs = UnparsedPublicKey::new(&ED25519, &v.key)
            .verify(v.msg.as_bytes(), &v.sig)
            .is_ok();
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
                // A key rind accepts yields a signature verdict. Whether that
                // verdict matches aws-lc is checked where aws-lc builds.
                match &result {
                    Ok(()) | Err(Error::BadSignature) => {}
                    Err(e) => panic!("{}: {flags:?}: {e:?}", v.number),
                }
                #[cfg(not(target_family = "wasm"))]
                assert_eq!(
                    result.is_ok(),
                    theirs,
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
