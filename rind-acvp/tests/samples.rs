// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Checks handlers against NIST's sample vectors, the same answers rind's
//! in-process tests use. Monte Carlo and multi-gigabyte groups stay with
//! `acvptool`: they are slow, and `acvptool` drives their iteration.

use std::path::PathBuf;

use rind_acvp::handle;
use serde_json::Value;

fn set(name: &str) -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../thirdparty/acvp")
        .join(format!("{name}.json"));
    serde_json::from_reader(std::fs::File::open(&path).unwrap()).unwrap()
}

fn hex(value: &Value, name: &str) -> Vec<u8> {
    let text = value[name].as_str().unwrap();
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
        .collect()
}

fn u32_ne(n: u32) -> Vec<u8> {
    n.to_ne_bytes().to_vec()
}

#[test]
fn sha2_256_aft() {
    let set = set("SHA2-256-1.0");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        if group["testType"] != "AFT" {
            continue;
        }
        for test in group["tests"].as_array().unwrap() {
            let msg = hex(test, "msg");
            let len = test["len"].as_u64().unwrap() as usize / 8;
            let reply = handle("SHA2-256", &[msg[..len].to_vec()]).unwrap();
            assert_eq!(reply[0], hex(test, "md"));
            checked += 1;
        }
    }
    assert!(checked > 0);
}

#[test]
fn hmac_sha256() {
    let set = set("HMAC-SHA2-256-2.0");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        for test in group["tests"].as_array().unwrap() {
            let mac_bytes = test["macLen"].as_u64().unwrap() as usize / 8;
            let reply = handle("HMAC-SHA2-256", &[hex(test, "msg"), hex(test, "key")]).unwrap();
            assert_eq!(&reply[0][..mac_bytes], hex(test, "mac"));
            checked += 1;
        }
    }
    assert!(checked > 0);
}

#[test]
fn aes_gcm_external() {
    let set = set("ACVP-AES-GCM-1.0");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        assert_eq!(group["ivGen"], "external");
        let tag_bytes = group["tagLen"].as_u64().unwrap() as u32 / 8;
        let encrypt = group["direction"] == "encrypt";
        for test in group["tests"].as_array().unwrap() {
            let key = hex(test, "key");
            let iv = hex(test, "iv");
            let aad = hex(test, "aad");
            if encrypt {
                let reply = handle(
                    "AES-GCM/seal",
                    &[u32_ne(tag_bytes), key, hex(test, "pt"), iv, aad],
                )
                .unwrap();
                let (ct, tag) = reply[0].split_at(reply[0].len() - tag_bytes as usize);
                assert_eq!(ct, hex(test, "ct"));
                assert_eq!(tag, hex(test, "tag"));
            } else {
                let mut combined = hex(test, "ct");
                combined.extend(hex(test, "tag"));
                let reply =
                    handle("AES-GCM/open", &[u32_ne(tag_bytes), key, combined, iv, aad]).unwrap();
                let passed = test["testPassed"].as_bool().unwrap();
                assert_eq!(reply[0] == [1], passed);
                if passed {
                    assert_eq!(reply[1], hex(test, "pt"));
                }
            }
            checked += 1;
        }
    }
    assert!(checked > 0);
}

#[test]
fn mlkem768_keygen_from_seed() {
    let set = set("ML-KEM-keyGen-FIPS203");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        for test in group["tests"].as_array().unwrap() {
            let reply = handle(
                "ML-KEM/ML-KEM-768/keyGen",
                &[hex(test, "d"), hex(test, "z")],
            )
            .unwrap();
            assert_eq!(reply[0], hex(test, "ek"));
            assert_eq!(reply[1], hex(test, "dk"));
            checked += 1;
        }
    }
    assert!(checked > 0);
}

#[test]
fn mldsa44_keygen_from_seed() {
    let set = set("ML-DSA-keyGen-FIPS204");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        if group["parameterSet"] != "ML-DSA-44" {
            continue;
        }
        for test in group["tests"].as_array().unwrap().iter().take(2) {
            let reply = handle("ML-DSA/ML-DSA-44/keyGen", &[hex(test, "seed")]).unwrap();
            assert_eq!(reply[0], hex(test, "pk"), "pk");
            assert_eq!(reply[1], hex(test, "sk"), "sk");
            checked += 1;
        }
    }
    assert!(checked > 0);
}

#[test]
fn sha2_256_mct_standard() {
    let set = set("SHA2-256-1.0");
    for group in set["testGroups"].as_array().unwrap() {
        if group["testType"] != "MCT" || group["mctVersion"] != "standard" {
            continue;
        }
        for test in group["tests"].as_array().unwrap() {
            let mut digest = hex(test, "msg");
            for result in test["resultsArray"].as_array().unwrap() {
                let reply = handle("SHA2-256/MCT", &[digest]).unwrap();
                digest = reply[0].to_vec();
                assert_eq!(digest, hex(result, "md"));
            }
        }
    }
}

#[test]
fn aes_ecb_aft() {
    let set = set("ACVP-AES-ECB-1.0");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        if group["testType"] != "AFT" || group["direction"] != "encrypt" {
            continue;
        }
        for test in group["tests"].as_array().unwrap() {
            let reply = handle(
                "AES/encrypt",
                &[
                    hex(test, "key"),
                    hex(test, "pt"),
                    1u32.to_ne_bytes().to_vec(),
                ],
            )
            .unwrap();
            assert_eq!(reply[0], hex(test, "ct"));
            checked += 1;
        }
    }
    assert!(checked > 0);
}

#[test]
fn ecdsa_sigver_p256() {
    let set = set("ECDSA-SigVer-FIPS186-5");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        if group["curve"] != "P-256" || group["hashAlg"] != "SHA2-256" {
            continue;
        }
        let curve = b"P-256".to_vec();
        let hash = b"SHA2-256".to_vec();
        for test in group["tests"].as_array().unwrap() {
            let reply = handle(
                "ECDSA/sigVer",
                &[
                    curve.clone(),
                    hash.clone(),
                    hex(test, "message"),
                    hex(test, "qx"),
                    hex(test, "qy"),
                    hex(test, "r"),
                    hex(test, "s"),
                ],
            )
            .unwrap();
            assert_eq!(reply[0] == [1], test["testPassed"].as_bool().unwrap());
            checked += 1;
        }
    }
    assert!(checked > 0);
}

#[test]
fn ecdsa_keyver_p256() {
    let set = set("ECDSA-KeyVer-FIPS186-5");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        if group["curve"] != "P-256" {
            continue;
        }
        let curve = group["curve"].as_str().unwrap().as_bytes().to_vec();
        for test in group["tests"].as_array().unwrap() {
            let reply = handle(
                "ECDSA/keyVer",
                &[curve.clone(), hex(test, "qx"), hex(test, "qy")],
            )
            .unwrap();
            assert_eq!(reply[0] == [1], test["testPassed"].as_bool().unwrap());
            checked += 1;
        }
    }
    assert!(checked > 0);
}
