// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Exercise the executable with the framing and arguments acvptool sends.

use std::io::{Read, Write};
use std::process::{Command, Stdio};

use serde_json::Value;

fn hex(text: &str) -> Vec<u8> {
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
        .collect()
}

fn transact(requests: &[(&str, Vec<Vec<u8>>)]) -> Vec<Vec<Vec<u8>>> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_rind-acvp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    let mut output = child.stdout.take().unwrap();
    let mut replies = Vec::new();
    for (command, args) in requests {
        let parts: Vec<_> = std::iter::once(command.as_bytes())
            .chain(args.iter().map(Vec::as_slice))
            .collect();
        input
            .write_all(&(parts.len() as u32).to_ne_bytes())
            .unwrap();
        for part in &parts {
            input.write_all(&(part.len() as u32).to_ne_bytes()).unwrap();
        }
        for part in parts {
            input.write_all(part).unwrap();
        }
        input.flush().unwrap();
        let mut word = [0; 4];
        output.read_exact(&mut word).unwrap();
        let count = u32::from_ne_bytes(word) as usize;
        assert!((1..=16).contains(&count), "{command}: {count} replies");
        let lengths: Vec<_> = (0..count)
            .map(|_| {
                output.read_exact(&mut word).unwrap();
                u32::from_ne_bytes(word) as usize
            })
            .collect();
        let mut reply = Vec::new();
        for len in lengths {
            assert!(len <= 1 << 20, "{command}: {len} reply bytes");
            let mut bytes = vec![0; len];
            output.read_exact(&mut bytes).unwrap();
            reply.push(bytes);
        }
        replies.push(reply);
    }
    drop(input);
    assert!(child.wait().unwrap().success());
    let mut trailing = Vec::new();
    output.read_to_end(&mut trailing).unwrap();
    assert!(trailing.is_empty());
    replies
}

fn config() -> Vec<Value> {
    let replies = transact(&[("getConfig", Vec::new())]);
    serde_json::from_slice(&replies[0][0]).unwrap()
}

#[test]
fn registration_describes_the_client_supported_capabilities() {
    // NIST's algorithm registration tables require these fields. In particular,
    // an algorithm/mode/revision identifier alone cannot request fresh vectors.
    // https://pages.nist.gov/ACVP/
    let entries = config();
    assert!(!entries.is_empty());
    for entry in entries {
        let algorithm = entry["algorithm"].as_str().unwrap();
        let mode = entry["mode"].as_str().unwrap_or("");
        let required: &[&str] = match (algorithm, mode) {
            (name, _) if name.starts_with("HMAC-") => {
                // acvptool reads the revision 1.0 group-level lengths.
                assert_eq!(entry["revision"], "1.0");
                &["keyLen", "macLen"]
            }
            ("ACVP-AES-CTR", _) => {
                assert_eq!(entry["payloadLen"][0]["max"], 128);
                &[
                    "payloadLen",
                    "incrementalCounter",
                    "overflowCounter",
                    "performCounterTests",
                ]
            }
            ("ACVP-AES-GCM", _) => {
                assert_eq!(entry["ivGen"], "external");
                &["payloadLen", "aadLen"]
            }
            ("ACVP-AES-GMAC", _) => {
                assert_eq!(entry["ivGen"], "external");
                &["aadLen"]
            }
            ("ACVP-AES-KW" | "ACVP-AES-KWP", _) => &["payloadLen"],
            ("KDA", "HKDF") => {
                // acvptool omits t from Z || T; do not request hybrid vectors.
                assert_eq!(entry["usesHybridSharedSecret"], false);
                &[
                    "fixedInfoPattern",
                    "encoding",
                    "hmacAlg",
                    "macSaltMethods",
                    "l",
                    "z",
                    "performMultiExpansionTests",
                ]
            }
            ("PBKDF", _) => &["capabilities"],
            ("ECDSA", "sigGen" | "sigVer") => &["capabilities"],
            ("EDDSA", "sigGen" | "sigVer") => {
                assert_eq!(entry["pure"], true);
                assert_eq!(entry["preHash"], false);
                &[]
            }
            ("KAS-ECC-SSC", _) => &["scheme", "domainParameterGenerationMethods"],
            ("ML-KEM", "encapDecap") => {
                assert_eq!(entry["revision"], "FIPS203-tr1");
                assert_eq!(entry["keyFormats"], serde_json::json!(["expanded"]));
                &["functions"]
            }
            ("ML-DSA", "sigGen" | "sigVer") => {
                // Presence of the client's externalMu flag distinguishes the
                // internal interface from pure external signatures.
                assert_eq!(
                    entry["signatureInterfaces"],
                    serde_json::json!(["internal", "external"])
                );
                assert_eq!(entry["preHash"], serde_json::json!(["pure"]));
                assert!(entry["capabilities"][0]["contextLength"].is_array());
                if mode == "sigGen" {
                    assert_eq!(entry["revision"], "FIPS204-tr1");
                    assert_eq!(entry["keyFormats"], serde_json::json!(["expanded"]));
                    assert!(entry["deterministic"].is_array());
                }
                &["capabilities", "externalMu"]
            }
            ("RSA", "sigGen" | "sigVer") => &["capabilities"],
            ("RSA", "signaturePrimitive" | "decryptionPrimitive") => {
                &["modulo", "keyFormat", "pubExpMode"]
            }
            ("hmacDRBG", _) => {
                // Revision 1.0 uses one integer, unlike SP800-90Ar1's domain.
                assert_eq!(entry["revision"], "1.0");
                for capability in entry["capabilities"].as_array().unwrap() {
                    let bits = capability["returnedBitsLen"].as_u64().unwrap();
                    let minimum = match capability["mode"].as_str().unwrap() {
                        "SHA-1" => 160,
                        "SHA2-256" => 256,
                        "SHA2-384" => 384,
                        "SHA2-512" => 512,
                        mode => panic!("unrecognized DRBG mode {mode}"),
                    };
                    assert!((minimum..=4096).contains(&bits));
                    assert_eq!(bits % 8, 0);
                    assert_eq!(capability["entropyInputLen"][0]["max"], 65536);
                    assert_eq!(capability["nonceLen"][0]["max"], 65536);
                }
                &["capabilities", "reseedImplemented", "predResistanceEnabled"]
            }
            _ => &[],
        };
        for field in required {
            let value = &entry[*field];
            assert!(!value.is_null(), "{algorithm}/{mode} lacks {field}");
            if let Some(array) = value.as_array() {
                assert!(!array.is_empty(), "{algorithm}/{mode} has empty {field}");
            }
        }
    }
}

#[test]
fn published_vectors_share_one_wrapper_process() {
    // RFC 4231 case 1, RFC 6070 case 5, and aws-lc's testmodulewrapper
    // HMAC_DRBG reseed vector, with acvptool's message/key and DRBG order.
    let replies = transact(&[
        ("SHA2-256", vec![b"abc".to_vec()]),
        ("HMAC-SHA2-256", vec![b"Hi There".to_vec(), vec![0x0b; 20]]),
        (
            "PBKDF",
            vec![
                b"passwordPASSWORDpassword".to_vec(),
                b"saltSALTsaltSALTsaltSALTsaltSALTsalt".to_vec(),
                4096u32.to_ne_bytes().to_vec(),
                b"SHA-1".to_vec(),
                200u32.to_ne_bytes().to_vec(),
            ],
        ),
        (
            "hmacDRBG-reseed/SHA2-256",
            vec![
                128u32.to_ne_bytes().to_vec(),
                hex("06032cd5eed33f39265f49ecb142c511da9aff2af71203bffaf34a9ca5bd9c0d"),
                vec![],
                vec![],
                hex("01920a4e669ed3a85ae8a33b35a74ad7fb2a6bb4cf395ce00334a9c9a5a5d552"),
                vec![],
                vec![],
                hex("0e66f71edc43e42a45ad3c6fc6cdc4df"),
            ],
        ),
    ]);
    let expected = [
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
        "3d2eec4fe41c849b80c8d83662c0e44a8b291a964cf2f07038",
        concat!(
            "76fc79fe9b50beccc991a11b5635783a83536add03c157fb30645e611c2898bb2b",
            "1bc215000209208cd506cb28da2a51bdb03826aaf2bd2335d576d519160842e7",
            "158ad0949d1a9ec3e66ea1b1a064b005de914eac2e9d4f2d72a8616a80225422",
            "918250ff66a41bd2f864a6a38cc5b6499dc43f7f2bd09e1e0f8f5885935124"
        ),
    ];
    for (reply, expected) in replies.iter().zip(expected) {
        assert_eq!(reply.len(), 1);
        assert_eq!(reply[0], hex(expected));
    }
}

#[test]
fn ecdh_matches_the_vendored_cavp_vectors_over_the_wire() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../thirdparty/vectors/aws-lc/crypto/ecdh_extra/ecdh_tests.txt");
    let vectors = std::fs::read_to_string(path).unwrap();
    let mut requests = Vec::new();
    let mut expected = Vec::new();
    for block in vectors.split("\n\n") {
        let fields: std::collections::BTreeMap<_, _> = block
            .lines()
            .filter_map(|line| line.split_once(" = "))
            .collect();
        let command = match fields.get("Curve") {
            Some(&"P-256") => "ECDH/P-256",
            Some(&"P-384") => "ECDH/P-384",
            Some(&"P-521") => "ECDH/P-521",
            _ => continue,
        };
        requests.push((
            command,
            vec![
                hex(fields["PeerX"]),
                hex(fields["PeerY"]),
                hex(fields["Private"]),
            ],
        ));
        expected.push(vec![hex(fields["X"]), hex(fields["Y"]), hex(fields["Z"])]);
    }
    assert_eq!(requests.len(), 75);
    assert_eq!(transact(&requests), expected);
}
