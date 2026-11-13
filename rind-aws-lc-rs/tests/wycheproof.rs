//! rind-aws-lc-rs builds HKDF on rind's HMAC, for every hash aws-lc-rs
//! offers it with.

use std::fs::File;
use std::io::BufReader;

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

/// A caller's own key type, which aws-lc-rs lets any crate define.
struct OutputLen(usize);

impl hkdf::KeyType for OutputLen {
    fn len(&self) -> usize {
        self.0
    }
}
