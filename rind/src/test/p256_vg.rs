// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Wycheproof's P-256 vectors for each variant of pyca/verified-garbage's
//! routines, which the CPU's widest variant hides from rind's other tests.

use super::{Expected, wycheproof, wycheproof_groups};
use crate::low::ct;
use crate::mid::sha2::Sha256Context;

/// Checks `ecdh`, given a private key and a peer's X9.62 uncompressed point,
/// against Wycheproof's P-256 ECDH vectors with such points, with the
/// private key secret for `admin/ctgrind`.
pub(crate) fn check_ecdh(ecdh: impl Fn(&[u8; 32], &[u8; 65]) -> Option<[u8; 32]>) {
    #[derive(serde::Deserialize)]
    struct Test {
        #[serde(rename = "tcId")]
        id: usize,
        #[serde(with = "hex::serde")]
        public: Vec<u8>,
        #[serde(with = "hex::serde")]
        private: Vec<u8>,
        #[serde(with = "hex::serde")]
        shared: Vec<u8>,
        result: Expected,
    }

    let mut ran = 0;
    for test in wycheproof::<Test>("ecdh_secp256r1_ecpoint_test.json") {
        let Ok(public) = <[u8; 65]>::try_from(&test.public[..]) else {
            continue;
        };
        // An integer, which may have a sign byte.
        let digits = &test.private[test.private.len().saturating_sub(32)..];
        let mut d = [0u8; 32];
        d[32 - digits.len()..].copy_from_slice(digits);
        let shared = ecdh(&ct::into_secret(d), &public);
        match test.result {
            Expected::Valid => assert_eq!(
                shared.as_ref().map(|s| &s[..]),
                Some(&test.shared[..]),
                "{}",
                test.id
            ),
            Expected::Invalid => assert_eq!(shared, None, "{}", test.id),
            Expected::Acceptable => {}
        }
        ran += 1;
    }
    assert!(ran > 0);
}

/// Checks `verify`, given an X9.62 uncompressed public key, a SHA-256 hash,
/// and a fixed-length signature, against Wycheproof's P-256 ECDSA vectors
/// with SHA-256.
pub(crate) fn check_verify(verify: impl Fn(&[u8; 65], &[u8; 32], &[u8; 64]) -> bool) {
    #[derive(serde::Deserialize)]
    struct Group {
        #[serde(rename = "publicKey")]
        public_key: Key,
        tests: Vec<Test>,
    }

    #[derive(serde::Deserialize)]
    struct Key {
        #[serde(with = "hex::serde")]
        uncompressed: Vec<u8>,
    }

    #[derive(serde::Deserialize)]
    struct Test {
        #[serde(rename = "tcId")]
        id: usize,
        #[serde(with = "hex::serde")]
        msg: Vec<u8>,
        #[serde(with = "hex::serde")]
        sig: Vec<u8>,
        result: Expected,
    }

    let mut ran = 0;
    for group in wycheproof_groups::<Group>("ecdsa_secp256r1_sha256_p1363_test.json") {
        let public: [u8; 65] = group.public_key.uncompressed[..].try_into().unwrap();
        for test in group.tests {
            // A signature of another length is refused before VG's routine.
            let Ok(sig) = <[u8; 64]>::try_from(&test.sig[..]) else {
                continue;
            };
            let mut hash = Sha256Context::new();
            hash.update(&test.msg);
            let valid = verify(&public, &hash.finish(), &sig);
            match test.result {
                Expected::Valid => assert!(valid, "{}", test.id),
                Expected::Invalid => assert!(!valid, "{}", test.id),
                Expected::Acceptable => {}
            }
            ran += 1;
        }
    }
    assert!(ran > 0);
}
