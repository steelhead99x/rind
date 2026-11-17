//! rind-aws-lc-rs builds HKDF on rind's HMAC, for every hash aws-lc-rs
//! offers it with.

use std::fs::File;
use std::io::BufReader;

use aws_lc_rs::signature::KeyPair as _;
use rind_aws_lc_rs::signature::KeyPair as _;
use rind_aws_lc_rs::{error, hkdf, signature};
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
            "{}/../thirdparty/vectors/wycheproof/testvectors_v1/{file}",
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

/// ML-DSA key loading from the vendored Wycheproof signing vectors.
///
/// `sign_seed` loads [`signature::PqdsaKeyPair::from_seed`] and, when the
/// vector has one, `from_pkcs8`. `sign_noseed` loads
/// [`signature::PqdsaKeyPair::from_raw_private_key`]. The adapter signs with
/// fresh randomness, so these vectors check the loaded key and its public
/// key, not the signature bytes. A group whose key does not load must be
/// refused with aws-lc-rs's reason.
#[cfg(not(any(miri, target_family = "wasm")))]
#[test]
fn ml_dsa_sign() {
    for (seed_file, noseed_file, ours, theirs) in [
        (
            "mldsa_44_sign_seed_test.json",
            "mldsa_44_sign_noseed_test.json",
            &signature::ML_DSA_44_SIGNING,
            &aws_lc_rs::signature::ML_DSA_44_SIGNING,
        ),
        (
            "mldsa_65_sign_seed_test.json",
            "mldsa_65_sign_noseed_test.json",
            &signature::ML_DSA_65_SIGNING,
            &aws_lc_rs::signature::ML_DSA_65_SIGNING,
        ),
        (
            "mldsa_87_sign_seed_test.json",
            "mldsa_87_sign_noseed_test.json",
            &signature::ML_DSA_87_SIGNING,
            &aws_lc_rs::signature::ML_DSA_87_SIGNING,
        ),
    ] {
        let mut count = 0;
        for group in sign_groups(seed_file) {
            let seed = hex::decode(&group.private_seed).unwrap();
            agree_key(
                seed_file,
                signature::PqdsaKeyPair::from_seed(ours, &seed),
                aws_lc_rs::signature::PqdsaKeyPair::from_seed(theirs, &seed),
                group.public_key.as_deref(),
            );
            if !group.private_key_pkcs8.is_empty() {
                let pkcs8 = hex::decode(&group.private_key_pkcs8).unwrap();
                agree_key(
                    seed_file,
                    signature::PqdsaKeyPair::from_pkcs8(ours, &pkcs8),
                    aws_lc_rs::signature::PqdsaKeyPair::from_pkcs8(theirs, &pkcs8),
                    group.public_key.as_deref(),
                );
            }
            count += 1;
        }
        assert!(count > 0, "{seed_file} has no groups");

        count = 0;
        for group in sign_groups(noseed_file) {
            let raw = hex::decode(&group.private_key).unwrap();
            agree_key(
                noseed_file,
                signature::PqdsaKeyPair::from_raw_private_key(ours, &raw),
                aws_lc_rs::signature::PqdsaKeyPair::from_raw_private_key(theirs, &raw),
                group.public_key.as_deref(),
            );
            count += 1;
        }
        assert!(count > 0, "{noseed_file} has no groups");
    }
}

fn sign_groups(file: &str) -> Vec<SignGroup> {
    let data = File::open(format!(
        "{}/../thirdparty/vectors/wycheproof/testvectors_v1/{file}",
        env!("CARGO_MANIFEST_DIR")
    ))
    .unwrap_or_else(|_| panic!("failed to open {file}"));
    serde_json::from_reader::<_, SignFile>(BufReader::new(data))
        .unwrap()
        .groups
}

fn agree_key(
    file: &str,
    ours: Result<signature::PqdsaKeyPair, error::KeyRejected>,
    theirs: Result<aws_lc_rs::signature::PqdsaKeyPair, aws_lc_rs::error::KeyRejected>,
    public_key: Option<&str>,
) {
    match (ours, theirs) {
        (Ok(ours), Ok(theirs)) => {
            let public = hex::decode(public_key.expect("a loaded key has a public key")).unwrap();
            assert_eq!(ours.public_key().as_ref(), public.as_slice(), "{file}");
            assert_eq!(theirs.public_key().as_ref(), public.as_slice(), "{file}");
        }
        (Err(ours), Err(theirs)) => {
            assert_eq!(ours.description_(), theirs.description_(), "{file}: {ours}");
        }
        (ours, theirs) => panic!(
            "{file}: ours {} theirs {}",
            ours.as_ref().map(|_| "ok").unwrap_or("err"),
            theirs.as_ref().map(|_| "ok").unwrap_or("err"),
        ),
    }
}

#[derive(Deserialize)]
struct SignFile {
    #[serde(rename = "testGroups")]
    groups: Vec<SignGroup>,
}

#[derive(Deserialize)]
struct SignGroup {
    #[serde(default, rename = "privateSeed")]
    private_seed: String,
    #[serde(default, rename = "privateKey")]
    private_key: String,
    #[serde(default, rename = "privateKeyPkcs8")]
    private_key_pkcs8: String,
    #[serde(default, rename = "publicKey")]
    public_key: Option<String>,
}

/// A caller's own key type, which aws-lc-rs lets any crate define.
struct OutputLen(usize);

impl hkdf::KeyType for OutputLen {
    fn len(&self) -> usize {
        self.0
    }
}
