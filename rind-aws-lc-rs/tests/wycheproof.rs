//! rind-aws-lc-rs builds HKDF on rind's HMAC, for every hash aws-lc-rs
//! offers it with.

use std::fs::File;
use std::io::BufReader;

use rind_aws_lc_rs::signature;
use rind_aws_lc_rs::{error, hkdf};
use serde::Deserialize;

#[derive(Deserialize)]
struct TestFile {
    #[serde(rename = "testGroups")]
    groups: Vec<TestGroup>,
}

#[derive(Deserialize)]
struct TestGroup {
    tests: Vec<Test>,
}

#[derive(Deserialize)]
struct Test {
    #[serde(rename = "tcId")]
    id: usize,
    #[serde(with = "hex::serde")]
    ikm: Vec<u8>,
    #[serde(with = "hex::serde")]
    salt: Vec<u8>,
    #[serde(with = "hex::serde")]
    info: Vec<u8>,
    size: usize,
    #[serde(with = "hex::serde")]
    okm: Vec<u8>,
    result: String,
}

#[test]
fn hkdf() {
    for (file, algorithm) in [
        ("hkdf_sha1_test.json", hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY),
        ("hkdf_sha256_test.json", hkdf::HKDF_SHA256),
        ("hkdf_sha384_test.json", hkdf::HKDF_SHA384),
        ("hkdf_sha512_test.json", hkdf::HKDF_SHA512),
    ] {
        let data = File::open(format!(
            "{}/../thirdparty/wycheproof/testvectors_v1/{file}",
            env!("CARGO_MANIFEST_DIR")
        ))
        .unwrap_or_else(|_| panic!("failed to open {file}"));
        let tests: TestFile = serde_json::from_reader(BufReader::new(data)).unwrap();
        let mut count = 0;

        for test in tests.groups.into_iter().flat_map(|group| group.tests) {
            let prk = hkdf::Salt::new(algorithm, &test.salt).extract(&test.ikm);
            let info = [test.info.as_slice()];
            let mut okm = vec![0u8; test.size];
            let result = prk
                .expand(&info, OutputLen(test.size))
                .and_then(|okm_| okm_.fill(&mut okm));

            match (test.result.as_str(), result) {
                ("valid", Ok(())) => assert_eq!(okm, test.okm, "{file} {}", test.id),
                // Past 255 hash outputs, which `expand` refuses.
                ("invalid", Err(error::Unspecified)) => {}
                (expected, result) => {
                    panic!("{file} {}: expected {expected}, got {result:?}", test.id)
                }
            }
            count += 1;
        }
        assert!(count > 0, "{file} has no tests");
    }
}

/// ML-DSA verification. The adapter verifies only with the empty context,
/// as it signs, so a signature made under another context must be refused.
#[test]
fn ml_dsa_verify() {
    for (file, algorithm, theirs_algorithm) in [
        (
            "mldsa_44_verify_test.json",
            &signature::ML_DSA_44,
            &aws_lc_rs::signature::ML_DSA_44,
        ),
        (
            "mldsa_65_verify_test.json",
            &signature::ML_DSA_65,
            &aws_lc_rs::signature::ML_DSA_65,
        ),
        (
            "mldsa_87_verify_test.json",
            &signature::ML_DSA_87,
            &aws_lc_rs::signature::ML_DSA_87,
        ),
    ] {
        let data = File::open(format!(
            "{}/../thirdparty/wycheproof/testvectors_v1/{file}",
            env!("CARGO_MANIFEST_DIR")
        ))
        .unwrap_or_else(|_| panic!("failed to open {file}"));
        let tests: MlDsaFile = serde_json::from_reader(BufReader::new(data)).unwrap();
        let mut count = 0;
        let mut contexts = 0;
        for group in tests.groups {
            for test in group.tests {
                if !test.ctx.is_empty() || test.flags.iter().any(|flag| flag == "Internal") {
                    let theirs = aws_lc_rs::signature::UnparsedPublicKey::new(
                        theirs_algorithm,
                        &group.public_key,
                    )
                    .verify(&test.msg, &test.sig)
                    .is_ok();
                    let ours = signature::UnparsedPublicKey::new(algorithm, &group.public_key)
                        .verify(&test.msg, &test.sig)
                        .is_ok();
                    let parsed = signature::ParsedPublicKey::new(algorithm, &group.public_key)
                        .is_ok_and(|key| key.verify_sig(&test.msg, &test.sig).is_ok());
                    assert!(!ours && !parsed && !theirs, "{file} {}", test.id);
                    contexts += 1;
                    continue;
                }
                let unparsed = signature::UnparsedPublicKey::new(algorithm, &group.public_key)
                    .verify(&test.msg, &test.sig)
                    .is_ok();
                let parsed = match signature::ParsedPublicKey::new(algorithm, &group.public_key) {
                    Ok(key) => key.verify_sig(&test.msg, &test.sig).is_ok(),
                    Err(_) => false,
                };
                match test.result.as_str() {
                    "valid" => assert!(unparsed && parsed, "{file} {}", test.id),
                    "invalid" => assert!(!unparsed && !parsed, "{file} {}", test.id),
                    // Wycheproof allows either verdict. Match aws-lc-rs's.
                    "acceptable" => {
                        let theirs_unparsed = aws_lc_rs::signature::UnparsedPublicKey::new(
                            theirs_algorithm,
                            &group.public_key,
                        )
                        .verify(&test.msg, &test.sig)
                        .is_ok();
                        let theirs_parsed = match aws_lc_rs::signature::ParsedPublicKey::new(
                            theirs_algorithm,
                            &group.public_key,
                        ) {
                            Ok(key) => key.verify_sig(&test.msg, &test.sig).is_ok(),
                            Err(_) => false,
                        };
                        assert_eq!(
                            (unparsed, parsed),
                            (theirs_unparsed, theirs_parsed),
                            "{file} {}",
                            test.id
                        );
                    }
                    expected => panic!("{file} {}: unexpected result {expected}", test.id),
                }
                count += 1;
            }
        }
        assert!(count > 0, "{file} has no empty-context tests");
        assert!(contexts > 0, "{file} has no context tests");
    }
}

/// The ML-DSA signing vectors: each group's key loaded from its seed, its
/// PKCS#8 document, or its expanded form, refused where the file says it is
/// invalid, and otherwise checked against the file's public key. Signing is
/// hedged, so each signature the key makes is verified, by rind and by
/// aws-lc-rs, rather than compared with the file's.
///
/// A case under a non-empty context checks that its signature is refused,
/// since the adapter neither signs nor verifies with a context. An
/// `Internal` case signs FIPS 204's `mu` directly, which neither aws-lc-rs's
/// `PqdsaKeyPair` nor this one offers; its group's key is still loaded and
/// checked, and signs a message of its own.
#[test]
fn ml_dsa_sign() {
    use signature::KeyPair as _;

    for (set, algorithm, theirs_algorithm, verify, theirs_verify) in [
        (
            "44",
            &signature::ML_DSA_44_SIGNING,
            &aws_lc_rs::signature::ML_DSA_44_SIGNING,
            &signature::ML_DSA_44,
            &aws_lc_rs::signature::ML_DSA_44,
        ),
        (
            "65",
            &signature::ML_DSA_65_SIGNING,
            &aws_lc_rs::signature::ML_DSA_65_SIGNING,
            &signature::ML_DSA_65,
            &aws_lc_rs::signature::ML_DSA_65,
        ),
        (
            "87",
            &signature::ML_DSA_87_SIGNING,
            &aws_lc_rs::signature::ML_DSA_87_SIGNING,
            &signature::ML_DSA_87,
            &aws_lc_rs::signature::ML_DSA_87,
        ),
    ] {
        for form in ["seed", "noseed"] {
            let file = format!("mldsa_{set}_sign_{form}_test.json");
            let data = File::open(format!(
                "{}/../thirdparty/wycheproof/testvectors_v1/{file}",
                env!("CARGO_MANIFEST_DIR")
            ))
            .unwrap_or_else(|_| panic!("failed to open {file}"));
            let tests: MlDsaSignFile = serde_json::from_reader(BufReader::new(data)).unwrap();
            let (mut signed, mut refused_keys, mut contexts, mut internal) = (0, 0, 0, 0);
            for group in tests.groups {
                let invalid_key = group.tests.iter().any(|test| {
                    test.flags.iter().any(|flag| {
                        flag == "IncorrectPrivateKeyLength" || flag == "InvalidPrivateKey"
                    })
                });
                let first = group.tests.first().map_or(0, |test| test.id);

                // Every form of the key the group gives, from both libraries.
                let mut keys = Vec::new();
                if let Some(seed) = hex(&group.private_seed) {
                    let ours = signature::PqdsaKeyPair::from_seed(algorithm, &seed);
                    let theirs =
                        aws_lc_rs::signature::PqdsaKeyPair::from_seed(theirs_algorithm, &seed);
                    keys.push(("seed", ours, theirs.is_ok()));
                }
                if let Some(pkcs8) = hex(&group.private_key_pkcs8).filter(|der| !der.is_empty()) {
                    let ours = signature::PqdsaKeyPair::from_pkcs8(algorithm, &pkcs8);
                    let theirs =
                        aws_lc_rs::signature::PqdsaKeyPair::from_pkcs8(theirs_algorithm, &pkcs8);
                    keys.push(("PKCS#8", ours, theirs.is_ok()));
                }
                if let Some(raw) = hex(&group.private_key) {
                    let ours = signature::PqdsaKeyPair::from_raw_private_key(algorithm, &raw);
                    let theirs = aws_lc_rs::signature::PqdsaKeyPair::from_raw_private_key(
                        theirs_algorithm,
                        &raw,
                    );
                    keys.push(("expanded", ours, theirs.is_ok()));
                }
                assert!(!keys.is_empty(), "{file} {first}: no private key");

                if invalid_key {
                    for (how, ours, theirs) in keys {
                        assert!(ours.is_err(), "{file} {first}: {how} key loaded");
                        assert!(!theirs, "{file} {first}: aws-lc-rs loaded the {how} key");
                    }
                    refused_keys += 1;
                    continue;
                }

                let public_key = hex(&group.public_key).expect("a valid key's public key");
                let keys: Vec<_> = keys
                    .into_iter()
                    .map(|(how, ours, theirs)| {
                        assert!(theirs, "{file} {first}: aws-lc-rs refused the {how} key");
                        let ours =
                            ours.unwrap_or_else(|err| panic!("{file} {first}: {how} key: {err:?}"));
                        assert_eq!(
                            ours.public_key().as_ref(),
                            public_key,
                            "{file} {first}: {how} key"
                        );
                        ours
                    })
                    .collect();
                let ours = signature::UnparsedPublicKey::new(verify, &public_key);
                let theirs =
                    aws_lc_rs::signature::UnparsedPublicKey::new(theirs_verify, &public_key);

                for test in &group.tests {
                    let internal_case = test.flags.iter().any(|flag| flag == "Internal");
                    let message: &[u8] = if internal_case {
                        b"Internal case"
                    } else {
                        &test.msg
                    };
                    if internal_case {
                        internal += 1;
                    } else if !test.ctx.is_empty() {
                        assert!(
                            ours.verify(&test.msg, &test.sig).is_err(),
                            "{file} {}: verified under a context",
                            test.id
                        );
                        contexts += 1;
                        continue;
                    } else {
                        assert_eq!(test.result, "valid", "{file} {}", test.id);
                        assert!(
                            ours.verify(&test.msg, &test.sig).is_ok(),
                            "{file} {}: the file's signature",
                            test.id
                        );
                        signed += 1;
                    }
                    for key in &keys {
                        let mut sig = vec![0; algorithm.signature_len()];
                        let len = key.sign(message, &mut sig).unwrap();
                        assert!(
                            ours.verify(message, &sig[..len]).is_ok(),
                            "{file} {}",
                            test.id
                        );
                        assert!(
                            theirs.verify(message, &sig[..len]).is_ok(),
                            "{file} {}",
                            test.id
                        );
                    }
                }
            }
            assert!(
                signed > 0 && refused_keys > 0 && contexts > 0 && internal > 0,
                "{file}: {signed} signed, {refused_keys} keys refused, {contexts} contexts, \
                 {internal} internal"
            );
        }
    }
}

#[derive(Deserialize)]
struct MlDsaFile {
    #[serde(rename = "testGroups")]
    groups: Vec<MlDsaGroup>,
}

#[derive(Deserialize)]
struct MlDsaGroup {
    #[serde(rename = "publicKey", with = "hex::serde")]
    public_key: Vec<u8>,
    tests: Vec<MlDsaCase>,
}

#[derive(Deserialize)]
struct MlDsaCase {
    #[serde(rename = "tcId")]
    id: usize,
    #[serde(default, with = "hex::serde")]
    msg: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    ctx: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    sig: Vec<u8>,
    result: String,
    #[serde(default)]
    flags: Vec<String>,
}

#[derive(Deserialize)]
struct MlDsaSignFile {
    #[serde(rename = "testGroups")]
    groups: Vec<MlDsaSignGroup>,
}

/// A signing group. The file gives `null` for a missing public key, so each
/// field is read as text.
#[derive(Deserialize)]
struct MlDsaSignGroup {
    #[serde(rename = "privateSeed", default)]
    private_seed: Option<String>,
    #[serde(rename = "privateKeyPkcs8", default)]
    private_key_pkcs8: Option<String>,
    #[serde(rename = "privateKey", default)]
    private_key: Option<String>,
    #[serde(rename = "publicKey", default)]
    public_key: Option<String>,
    tests: Vec<MlDsaCase>,
}

/// Decodes a field the group has. An empty seed or expanded key is a key
/// of length zero, which must be refused; the seed-length groups leave
/// `privateKeyPkcs8` empty, which means they give none.
fn hex(field: &Option<String>) -> Option<Vec<u8>> {
    field.as_deref().map(|text| ::hex::decode(text).unwrap())
}

/// A caller's own key type, which aws-lc-rs lets any crate define.
struct OutputLen(usize);

impl hkdf::KeyType for OutputLen {
    fn len(&self) -> usize {
        self.0
    }
}
