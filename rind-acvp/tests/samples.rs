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

fn hex_opt(value: &Value, name: &str) -> Vec<u8> {
    value
        .get(name)
        .and_then(Value::as_str)
        .filter(|text| !text.is_empty())
        .map(|_| hex(value, name))
        .unwrap_or_default()
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

/// `ivGen: internal`: an empty nonce, and the reply is ciphertext || tag ||
/// the 12-byte IV `acvptool` splits off. The sample file has no such group.
#[test]
fn aes_gcm_internal_iv() {
    for (key_len, tag_bits, pt) in [
        (16, 128u32, &b""[..]),
        (24, 128, b"hello"),
        (32, 32, b"internal-iv"),
        (32, 120, b"x"),
    ] {
        let tag_bytes = tag_bits / 8;
        let key = vec![0x3c; key_len];
        let aad = b"aad".to_vec();
        let reply = handle(
            "AES-GCM/seal",
            &[
                u32_ne(tag_bytes),
                key.clone(),
                pt.to_vec(),
                Vec::new(),
                aad.clone(),
            ],
        )
        .unwrap();
        let buf = &reply[0];
        let split = buf.len() - 12;
        let (tagged, iv) = buf.split_at(split);
        let (ct, tag) = tagged.split_at(tagged.len() - tag_bytes as usize);
        assert_eq!(ct.len(), pt.len(), "key {key_len} tag {tag_bits}");
        assert_eq!(iv.len(), 12);
        assert_eq!(tag.len(), tag_bytes as usize);
        let mut combined = ct.to_vec();
        combined.extend_from_slice(tag);
        let opened = handle(
            "AES-GCM/open",
            &[u32_ne(tag_bytes), key, combined, iv.to_vec(), aad],
        )
        .unwrap();
        assert_eq!(opened[0], vec![1]);
        assert_eq!(&opened[1], pt);
    }

    let key = vec![0x11; 16];
    let seal = |pt: &[u8]| {
        handle(
            "AES-GCM/seal",
            &[u32_ne(16), key.clone(), pt.to_vec(), Vec::new(), Vec::new()],
        )
        .unwrap()
    };
    let one = seal(b"a");
    let two = seal(b"a");
    assert_ne!(&one[0][one[0].len() - 12..], &two[0][two[0].len() - 12..]);
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

/// Standard Monte Carlo, the iteration `acvptool` sends. The vendored
/// SHA-256 set has only the alternate version, which `acvptool` does not
/// drive; SHA-384 and the other files here carry the standard one.
#[test]
fn hash_mct_standard() {
    let mut checked = 0;
    for name in [
        "SHA2-384-1.0",
        "SHA2-512-1.0",
        "SHA2-512-256-1.0",
        "SHA3-256-2.0",
        "SHA3-384-2.0",
        "SHA3-512-2.0",
    ] {
        let set = set(name);
        let command = set["algorithm"].as_str().unwrap();
        for group in set["testGroups"].as_array().unwrap() {
            if group["testType"] != "MCT" || group["mctVersion"] != "standard" {
                continue;
            }
            for test in group["tests"].as_array().unwrap() {
                let mut digest = hex(test, "msg");
                for result in test["resultsArray"].as_array().unwrap() {
                    let reply = handle(&format!("{command}/MCT"), &[digest]).unwrap();
                    digest = reply[0].to_vec();
                    assert_eq!(digest, hex(result, "md"), "{name}");
                }
                checked += 1;
            }
        }
    }
    assert!(checked > 0);
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

#[test]
fn mldsa_sigver() {
    let set = set("ML-DSA-sigVer-FIPS204");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        let set_name = group["parameterSet"].as_str().unwrap();
        let interface = group["signatureInterface"]
            .as_str()
            .unwrap()
            .as_bytes()
            .to_vec();
        let external_mu = vec![u8::from(group["externalMu"].as_bool().unwrap())];
        for test in group["tests"].as_array().unwrap() {
            let reply = handle(
                &format!("ML-DSA/{set_name}/sigVer"),
                &[
                    hex(test, "signature"),
                    hex(test, "pk"),
                    hex_opt(test, "message"),
                    hex_opt(test, "mu"),
                    hex_opt(test, "context"),
                    external_mu.clone(),
                    interface.clone(),
                ],
            )
            .unwrap();
            assert_eq!(
                reply[0] == [1],
                test["testPassed"].as_bool().unwrap(),
                "tcId {}",
                test["tcId"]
            );
            checked += 1;
        }
    }
    assert!(checked > 0);
}

#[test]
fn rsa_decryption_primitive() {
    let set = set("RSA-DecryptionPrimitive-Sp800-56Br2");
    let mut checked = 0;
    for group in set["testGroups"].as_array().unwrap() {
        let crt = group["keyMode"] == "crt";
        let command = if crt {
            "RSA/decryptionPrimitive/crt"
        } else {
            "RSA/decryptionPrimitive"
        };
        for test in group["tests"].as_array().unwrap() {
            let args = if crt {
                vec![
                    hex(test, "ct"),
                    hex(test, "d"),
                    hex_opt(test, "dmp1"),
                    hex_opt(test, "dmq1"),
                    hex_opt(test, "iqmp"),
                    hex_opt(test, "p"),
                    hex_opt(test, "q"),
                    hex(test, "n"),
                    hex(test, "e"),
                ]
            } else {
                vec![
                    hex(test, "ct"),
                    hex(test, "d"),
                    hex(test, "n"),
                    hex(test, "e"),
                ]
            };
            let reply = handle(command, &args).unwrap();
            let passed = test["testPassed"].as_bool().unwrap();
            assert_eq!(reply[0] == [1], passed, "tcId {}", test["tcId"]);
            if passed {
                assert_eq!(reply[1], hex(test, "pt"), "tcId {}", test["tcId"]);
            }
            checked += 1;
        }
    }
    assert!(checked > 0);
}
