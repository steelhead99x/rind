// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Reject malformed operation requests before they can produce an answer.

use std::io::Write;
use std::process::{Command, Stdio};

use rind_acvp::{Reply, Wrapper};

fn handle(command: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    Wrapper::default().handle(command, args)
}
use serde_json::Value;

fn u32_ne(n: u32) -> Vec<u8> {
    n.to_ne_bytes().to_vec()
}

#[test]
fn operation_argument_counts_are_exact() {
    let requests = [
        ("getConfig", vec![Vec::new()]),
        ("SHA2-256", vec![b"abc".to_vec(), Vec::new()]),
        (
            "HMAC-SHA2-256",
            vec![b"message".to_vec(), b"key".to_vec(), Vec::new()],
        ),
        ("AES-KW/seal", vec![Vec::new(), vec![1; 16], vec![2; 16]]),
        (
            "RSA/decryptionPrimitive",
            vec![vec![2; 16], vec![3; 16], vec![0x85; 16]],
        ),
        ("EDDSA/ED-25519/keyGen", vec![Vec::new()]),
        (
            "ML-DSA/ML-DSA-44/sigGen",
            vec![vec![1; 32], b"message".to_vec()],
        ),
        (
            "HKDF/SHA2-256/extract",
            vec![b"key".to_vec(), b"salt".to_vec(), Vec::new()],
        ),
    ];
    for (command, args) in requests {
        assert!(handle(command, &args).is_err(), "{command}");
    }
}

#[test]
fn binary_refuses_an_extra_operation_argument() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_rind-acvp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let args = [b"SHA2-256".as_slice(), b"abc", b"ignored"];
    let mut request = u32_ne(args.len() as u32);
    for arg in args {
        request.extend(u32_ne(arg.len() as u32));
    }
    for arg in args {
        request.extend_from_slice(arg);
    }
    child.stdin.take().unwrap().write_all(&request).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
}

#[test]
fn mldsa_explicit_interface_still_validates_external_mu() {
    let generated = handle("ML-DSA/ML-DSA-44/keyGen", &[vec![1; 32]]).unwrap();
    let sk = generated[1].to_vec();
    let message = b"message".to_vec();
    let mut signing = vec![
        sk,
        message.clone(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![0],
        b"internal".to_vec(),
    ];
    let signature = handle("ML-DSA/ML-DSA-44/sigGen", &signing).unwrap();
    let mut verifying = vec![
        signature[0].to_vec(),
        generated[0].to_vec(),
        message,
        Vec::new(),
        Vec::new(),
        vec![0],
        b"internal".to_vec(),
    ];
    assert_eq!(
        handle("ML-DSA/ML-DSA-44/sigVer", &verifying).unwrap()[0],
        [1]
    );
    for interface in [b"internal".as_slice(), b"external"] {
        signing[6] = interface.to_vec();
        verifying[6] = interface.to_vec();
        for flag in [vec![2], vec![0, 0], vec![1, 0]] {
            signing[5] = flag.clone();
            verifying[5] = flag;
            assert!(handle("ML-DSA/ML-DSA-44/sigGen", &signing).is_err());
            assert!(handle("ML-DSA/ML-DSA-44/sigVer", &verifying).is_err());
        }
    }
}

#[test]
fn gcm_checks_parameters_before_a_short_ciphertext() {
    let valid = vec![u32_ne(16), vec![0; 16], Vec::new(), vec![0; 12], Vec::new()];
    let failed = handle("AES-GCM/open", &valid).unwrap();
    assert_eq!(failed[0], [0]);
    assert!(failed[1].is_empty());

    for tag_bytes in [0, 1, 3, 17, u32::MAX] {
        let mut invalid = valid.clone();
        invalid[0] = u32_ne(tag_bytes);
        assert!(handle("AES-GCM/open", &invalid).is_err());
    }
    let mut invalid = valid.clone();
    invalid[1] = vec![0; 15];
    assert!(handle("AES-GCM/open", &invalid).is_err());
    let mut invalid = valid;
    invalid[3].clear();
    assert!(handle("AES-GCM/open", &invalid).is_err());
}

fn hex(test: &Value, field: &str) -> Vec<u8> {
    let text = test[field].as_str().unwrap();
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn rsa_standard_primitives_validate_the_public_key_and_private_result() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../thirdparty/acvp/RSA-SignaturePrimitive-2.0.json");
    let set: Value = serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
    let group = set["testGroups"]
        .as_array()
        .unwrap()
        .iter()
        .find(|group| group["keyMode"] == "standard" && group["modulo"] == 2048)
        .unwrap();
    let test = group["tests"]
        .as_array()
        .unwrap()
        .iter()
        .find(|test| test["testPassed"] == true)
        .unwrap();
    for (command, fields, exponent_at, private_at) in [
        ("RSA/signaturePrimitive", ["d", "n", "e", "message"], 2, 0),
        ("RSA/decryptionPrimitive", ["message", "d", "n", "e"], 3, 1),
    ] {
        let args: Vec<_> = fields.into_iter().map(|field| hex(test, field)).collect();
        let valid = handle(command, &args).unwrap();
        assert_eq!(valid[0], [1], "{command}");
        assert_eq!(valid[1], hex(test, "signature"));
        for e in [vec![0], vec![1], vec![2]] {
            let mut invalid = args.clone();
            invalid[exponent_at] = e;
            let failed = handle(command, &invalid).unwrap();
            assert_eq!(failed[0], [0], "{command} malformed public exponent");
            assert!(failed[1].is_empty());
        }
        let mut invalid = args;
        invalid[private_at] = vec![1];
        let failed = handle(command, &invalid).unwrap();
        assert_eq!(failed[0], [0], "{command} inconsistent private exponent");
        assert!(failed[1].is_empty());
    }
}

#[test]
fn rsa_crt_uses_and_checks_every_key_component() {
    // The signature primitive's first 2048-bit CRT vector has e = 65537.
    // Its raw operation is also a decryption primitive for this input.
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../thirdparty/acvp/RSA-SignaturePrimitive-2.0.json");
    let set: Value = serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
    let group = set["testGroups"]
        .as_array()
        .unwrap()
        .iter()
        .find(|group| group["keyMode"] == "crt" && group["modulo"] == 2048)
        .unwrap();
    let test = group["tests"]
        .as_array()
        .unwrap()
        .iter()
        .find(|test| test["testPassed"] == true)
        .unwrap();
    let args: Vec<_> = ["message", "d", "dmp1", "dmq1", "iqmp", "p", "q", "n", "e"]
        .into_iter()
        .map(|field| hex(test, field))
        .collect();
    let command = "RSA/decryptionPrimitive/crt";
    let valid = handle(command, &args).unwrap();
    assert_eq!(valid[0], [1]);
    assert_eq!(valid[1], hex(test, "signature"));
    for index in [2, 3, 4, 5, 6, 8] {
        let mut invalid = args.clone();
        invalid[index] = vec![0];
        let failed = handle(command, &invalid).unwrap();
        assert_eq!(failed[0], [0], "zero component {index}");
        assert!(failed[1].is_empty());
    }
    assert!(handle(command, &args[..8]).is_err());
}
