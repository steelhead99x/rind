use std::fs::File;
use std::io::BufReader;

use rind::Error;
use rind::aead::{
    AES_128_GCM, AES_192_GCM, AES_256_GCM, CHACHA20_POLY1305, Key, Nonce, RandomNonce,
    RandomizedNonceKey, Tag, gcm,
};
use rind::cipher::{
    AES_128, AES_192, AES_256, AesCbcDecryptingKey, AesCbcEncryptingKey, CbcIv, ChaCha20,
};
use rind::key_wrap::{self, AesKek};
use rind::rsa::{self, DecryptingKey, OaepAlgorithm};
use rind::signature::verify::legacy;
use rind::signature::{self, RsaPssSaltLength, RsaVerificationAlgorithm, sign, verify};
use rind::{hkdf, hmac, pbkdf2};
use serde::Deserialize;

/// The path of the Wycheproof vector file `name`, from any directory, as the
/// iOS simulator runs the tests.
fn vectors(name: &str) -> String {
    let dir = env!("CARGO_MANIFEST_DIR");
    format!("{dir}/../thirdparty/wycheproof/testvectors_v1/{name}")
}

#[derive(Deserialize, Debug)]
struct TestFile {
    #[serde(rename(deserialize = "testGroups"))]
    groups: Vec<TestGroup>,
}

#[derive(Deserialize, Debug)]
struct TestGroup {
    #[serde(rename(deserialize = "type"))]
    typ: String,

    #[serde(default, rename(deserialize = "publicKey"))]
    public_key: PublicKey,

    #[serde(default, rename(deserialize = "publicKeyAsn"), with = "hex::serde")]
    public_key_asn: Vec<u8>,

    // The same key as a `SubjectPublicKeyInfo`.
    #[serde(default, rename(deserialize = "publicKeyDer"), with = "hex::serde")]
    public_key_der: Vec<u8>,

    // The PKCS#1 public key of a signing group.
    #[serde(default, rename(deserialize = "keyAsn"), with = "hex::serde")]
    key_asn: Vec<u8>,

    #[serde(default, rename(deserialize = "keySize"))]
    key_size: usize,

    #[serde(default, rename(deserialize = "privateKeyPkcs8"), with = "hex::serde")]
    private_key_pkcs8: Vec<u8>,

    #[serde(default)]
    sha: String,

    #[serde(default, rename(deserialize = "mgfSha"))]
    mgf_sha: String,

    #[serde(default, rename(deserialize = "sLen"))]
    salt_len: usize,

    #[serde(default)]
    mgf: String,

    tests: Vec<Test>,
}

#[derive(Deserialize, Debug)]
struct Test {
    #[serde(rename(deserialize = "tcId"))]
    #[allow(unused)] // for Debug
    id: usize,
    #[allow(unused)] // for Debug
    comment: Option<String>,
    #[serde(default, with = "hex::serde")]
    key: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    msg: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    tag: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    sig: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    ct: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    aad: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    iv: Vec<u8>,
    #[serde(default, rename(deserialize = "initialCounter"), with = "hex::serde")]
    initial_counter: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    ikm: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    salt: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    info: Vec<u8>,
    #[serde(default)]
    size: usize,
    #[serde(default, with = "hex::serde")]
    okm: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    password: Vec<u8>,
    #[serde(default, rename(deserialize = "iterationCount"))]
    iteration_count: u32,
    #[serde(default, with = "hex::serde")]
    dk: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    label: Vec<u8>,
    #[serde(default)]
    flags: Vec<String>,
    result: ExpectedResult,
}

#[derive(Deserialize, Debug, Default)]
struct PublicKey {
    #[serde(default, with = "hex::serde")]
    uncompressed: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    pk: Vec<u8>,
    // RSA, as a DER `INTEGER`, so with a sign byte when the top bit is set.
    #[serde(default, with = "hex::serde")]
    modulus: Vec<u8>,
    #[serde(default, rename(deserialize = "publicExponent"), with = "hex::serde")]
    public_exponent: Vec<u8>,
}

#[derive(Copy, Clone, Deserialize, Debug, PartialEq)]
#[serde(rename_all = "lowercase")]
enum ExpectedResult {
    Valid,
    Invalid,
    Acceptable,
}

struct Summary {
    started: usize,
    skipped: usize,
    in_test: bool,
}

impl Summary {
    fn new() -> Self {
        Self {
            started: 0,
            skipped: 0,
            in_test: false,
        }
    }

    fn group(&mut self, group: &TestGroup) {
        println!("  group: {:?}", group.typ);
        self.in_test = false;
    }

    fn start(&mut self, test: &Test) {
        println!("    test {}:", test.id);
        self.started += 1;
        self.in_test = true;
    }

    fn skipped(&mut self, why: &str) {
        if self.in_test {
            println!("      skipped: {why}");
            self.skipped += 1;
            self.in_test = false;
        } else {
            println!("    skipped group: {why}");
        }
    }
}

impl Drop for Summary {
    fn drop(&mut self) {
        let passed = self.started - self.skipped;
        println!(
            "DONE: started {} passed {} skipped {}",
            self.started, passed, self.skipped
        );
        assert_ne!(self.started, self.skipped, "all tests were skipped");
    }
}

#[test]
fn hmac_tests() {
    for (file, algorithm) in [
        ("hmac_sha1_test.json", &hmac::legacy::HMAC_SHA1),
        ("hmac_sha256_test.json", &hmac::HMAC_SHA256),
        ("hmac_sha384_test.json", &hmac::HMAC_SHA384),
        ("hmac_sha512_test.json", &hmac::HMAC_SHA512),
    ] {
        let data_file =
            File::open(vectors(file)).unwrap_or_else(|_| panic!("failed to open data file {file}"));

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);
            for test in group.tests {
                summary.start(&test);

                let key = hmac::Key::new(algorithm, &test.key);
                let result = match test.tag.len() == algorithm.tag_len() {
                    true => hmac::verify(&key, &test.msg, &test.tag),
                    false => truncated(hmac::sign(&key, &test.msg).as_ref(), &test.tag),
                };

                match (test.result, result) {
                    (ExpectedResult::Valid, Ok(())) => {}
                    (ExpectedResult::Invalid, Err(Error::BadSignature)) => {}
                    _ => panic!("expected {:?} got {:?}", test.result, result),
                }
            }
        }
    }
}

// rind compares only whole tags; these vectors also truncate them.
fn truncated(tag: &[u8], expected: &[u8]) -> Result<(), Error> {
    match tag.starts_with(expected) {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

#[test]
fn hkdf_tests() {
    fn check(file: &str, algorithm: &'static hkdf::Algorithm) {
        let data_file =
            File::open(file).unwrap_or_else(|_| panic!("failed to open data file {file}"));
        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);
            for test in group.tests {
                summary.start(&test);

                let mut okm = vec![0u8; test.size];
                let prk = hkdf::Salt::new(algorithm, &test.salt).extract(&test.ikm);
                let info = [test.info.as_slice()];
                let result = prk.expand(&info, okm.len()).fill(&mut okm);

                match (test.result, result) {
                    (ExpectedResult::Valid, Ok(())) => assert_eq!(okm, test.okm),
                    (ExpectedResult::Invalid, Err(Error::WrongLength)) => {}
                    _ => panic!("expected {:?} got {:?}", test.result, result),
                }
            }
        }
    }

    for (file, algorithm) in [
        ("hkdf_sha1_test.json", &hkdf::legacy::HKDF_SHA1),
        ("hkdf_sha256_test.json", &hkdf::HKDF_SHA256),
        ("hkdf_sha384_test.json", &hkdf::HKDF_SHA384),
        ("hkdf_sha512_test.json", &hkdf::HKDF_SHA512),
    ] {
        check(&vectors(file), algorithm);
    }
}

#[test]
fn pbkdf2_tests() {
    // Most vectors run 4096 iterations, and one 16,777,216: about a minute
    // in a debug build, so only the release run takes them. The gate's
    // differential tests against aws-lc-rs use few iterations instead.
    if std::env::var_os("SLOW_TESTS").is_none() {
        return;
    }

    // SHA-224, which rind does not offer, has its own file and is skipped.
    for (file, algorithm, algorithm_len) in [
        (
            "pbkdf2_hmacsha1_test.json",
            &pbkdf2::legacy::PBKDF2_HMAC_SHA1,
            20,
        ),
        (
            "pbkdf2_hmacsha256_test.json",
            &pbkdf2::PBKDF2_HMAC_SHA256,
            32,
        ),
        (
            "pbkdf2_hmacsha384_test.json",
            &pbkdf2::PBKDF2_HMAC_SHA384,
            48,
        ),
        (
            "pbkdf2_hmacsha512_test.json",
            &pbkdf2::PBKDF2_HMAC_SHA512,
            64,
        ),
    ] {
        let data_file =
            File::open(vectors(file)).unwrap_or_else(|_| panic!("failed to open data file {file}"));

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();
        let mut cases = 0usize;

        for group in tests.groups {
            summary.group(&group);
            for test in group.tests {
                cases += 1;
                summary.start(&test);

                // Every vector is valid: none has a zero count or empty key.
                assert_eq!(test.result, ExpectedResult::Valid);
                let iterations = core::num::NonZeroU32::new(test.iteration_count).unwrap();
                let secret = pbkdf2::Secret::new(algorithm, &test.password);
                let mut dk = vec![0u8; test.dk.len()];
                secret.derive(iterations, &test.salt, &mut dk).unwrap();
                assert_eq!(dk, test.dk);
                // rind verifies only keys at least as long as the HMAC output.
                let wanted = match test.dk.len() < algorithm_len {
                    true => Err(Error::WrongLength),
                    false => Ok(()),
                };
                assert_eq!(secret.verify(iterations, &test.salt, &test.dk), wanted);
            }
        }
        eprintln!("slow-tests: pbkdf2 {file} {cases}");
    }
}

#[test]
fn test_verify_ecdsa() {
    // Each file whose curve, hash, and encoding has a constant.
    for (file, algorithm) in [
        (
            "ecdsa_secp256r1_sha256_p1363_test.json",
            &verify::ECDSA_P256_SHA256_FIXED,
        ),
        (
            "ecdsa_secp256r1_sha256_test.json",
            &verify::ECDSA_P256_SHA256_ASN1,
        ),
        (
            "ecdsa_secp256r1_sha512_test.json",
            &verify::ECDSA_P256_SHA512_ASN1,
        ),
        (
            "ecdsa_secp384r1_sha256_test.json",
            &verify::ECDSA_P384_SHA256_ASN1,
        ),
        (
            "ecdsa_secp384r1_sha384_p1363_test.json",
            &verify::ECDSA_P384_SHA384_FIXED,
        ),
        (
            "ecdsa_secp384r1_sha384_test.json",
            &verify::ECDSA_P384_SHA384_ASN1,
        ),
        (
            "ecdsa_secp384r1_sha512_test.json",
            &verify::ECDSA_P384_SHA512_ASN1,
        ),
        (
            "ecdsa_secp521r1_sha512_p1363_test.json",
            &verify::ECDSA_P521_SHA512_FIXED,
        ),
        (
            "ecdsa_secp521r1_sha512_test.json",
            &verify::ECDSA_P521_SHA512_ASN1,
        ),
    ] {
        let data_file = File::open(vectors(file))
            .unwrap_or_else(|_| panic!("failed to open data file {}", file));

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);

            let public_key =
                signature::PublicKey::new(algorithm, &group.public_key.uncompressed).unwrap();
            check_ecdsa_spki(algorithm, &group, &public_key);

            for test in group.tests {
                summary.start(&test);

                let result = public_key.verify(&test.msg, &test.sig);
                match (test.result, result) {
                    (ExpectedResult::Valid, Ok(())) => {}
                    (ExpectedResult::Invalid, Err(Error::BadSignature)) => {}
                    _ => panic!("expected {:?} got {:?}", test.result, result),
                }
            }
        }
    }
}

/// The group's SPKI parses as its point, and encodes back to itself; and
/// with its point compressed, parses as the same point.
fn check_ecdsa_spki(
    algorithm: &'static signature::VerificationAlgorithm,
    group: &TestGroup,
    key: &signature::PublicKey,
) {
    let der = &group.public_key_der;
    let from_spki = signature::PublicKey::from_spki(algorithm, der).unwrap();
    assert_eq!(from_spki.as_ref(), key.as_ref());
    assert_eq!(from_spki.to_spki().as_ref(), &der[..]);

    let point = key.as_ref();
    let (x, y) = point[1..].split_at(point.len() / 2);
    let compressed = [&[2 | (y[y.len() - 1] & 1)][..], x].concat();
    let compressed_der = spki(algorithm_identifier(der), &compressed);
    let from_compressed = signature::PublicKey::from_spki(algorithm, &compressed_der);
    assert_eq!(from_compressed.unwrap().as_ref(), key.as_ref());
}

/// A DER element: `tag`, the length of `body`, and `body`.
fn der(tag: u8, body: &[u8]) -> Vec<u8> {
    let length = match body.len() {
        len @ 0..0x80 => vec![len as u8],
        len @ 0x80..0x100 => vec![0x81, len as u8],
        len => vec![0x82, (len >> 8) as u8, len as u8],
    };
    [&[tag][..], &length, body].concat()
}

/// A `SubjectPublicKeyInfo` of `algorithm`, an encoded
/// `AlgorithmIdentifier`, holding `key`.
fn spki(algorithm: &[u8], key: &[u8]) -> Vec<u8> {
    let key = der(0x03, &[&[0][..], key].concat());
    der(0x30, &[algorithm, &key].concat())
}

/// The encoded `AlgorithmIdentifier` that opens a `SubjectPublicKeyInfo`,
/// whose own length is one byte.
fn algorithm_identifier(spki: &[u8]) -> &[u8] {
    let body = match spki[1] {
        0x81 => &spki[3..],
        _ => &spki[2..],
    };
    &body[..2 + body[1] as usize]
}

#[test]
fn test_verify_ecdsa_digest() {
    use rind::digest::{self, SHA256, SHA384, SHA512};

    // Each file whose curve rind has and whose hash its signatures take,
    // with an algorithm for its curve and encoding: the digest names the hash.
    for (file, algorithm, hash) in [
        (
            "ecdsa_secp256r1_sha256_p1363_test.json",
            &verify::ECDSA_P256_SHA256_FIXED,
            &SHA256,
        ),
        (
            "ecdsa_secp256r1_sha256_test.json",
            &verify::ECDSA_P256_SHA256_ASN1,
            &SHA256,
        ),
        (
            "ecdsa_secp256r1_sha512_p1363_test.json",
            &verify::ECDSA_P256_SHA256_FIXED,
            &SHA512,
        ),
        (
            "ecdsa_secp256r1_sha512_test.json",
            &verify::ECDSA_P256_SHA256_ASN1,
            &SHA512,
        ),
        (
            "ecdsa_secp384r1_sha256_test.json",
            &verify::ECDSA_P384_SHA384_ASN1,
            &SHA256,
        ),
        (
            "ecdsa_secp384r1_sha384_p1363_test.json",
            &verify::ECDSA_P384_SHA384_FIXED,
            &SHA384,
        ),
        (
            "ecdsa_secp384r1_sha384_test.json",
            &verify::ECDSA_P384_SHA384_ASN1,
            &SHA384,
        ),
        (
            "ecdsa_secp384r1_sha512_p1363_test.json",
            &verify::ECDSA_P384_SHA384_FIXED,
            &SHA512,
        ),
        (
            "ecdsa_secp384r1_sha512_test.json",
            &verify::ECDSA_P384_SHA384_ASN1,
            &SHA512,
        ),
        (
            "ecdsa_secp521r1_sha512_p1363_test.json",
            &verify::ECDSA_P521_SHA512_FIXED,
            &SHA512,
        ),
        (
            "ecdsa_secp521r1_sha512_test.json",
            &verify::ECDSA_P521_SHA512_ASN1,
            &SHA512,
        ),
    ] {
        let data_file = File::open(vectors(file))
            .unwrap_or_else(|_| panic!("failed to open data file {}", file));

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);

            let public_key =
                signature::PublicKey::new(algorithm, &group.public_key.uncompressed).unwrap();

            for test in group.tests {
                summary.start(&test);

                let digest = digest::digest(hash, &test.msg);
                let result = public_key.verify_digest(&digest, &test.sig);
                match (test.result, result) {
                    (ExpectedResult::Valid, Ok(())) => {}
                    (ExpectedResult::Invalid, Err(Error::BadSignature)) => {}
                    _ => panic!("{file}: expected {:?} got {:?}", test.result, result),
                }
            }
        }
    }
}

#[test]
fn test_aes_gcm() {
    aes_gcm("aes_gcm_test.json", false);
}

#[test]
fn test_aes_gmac() {
    aes_gcm("aes_gmac_test.json", true);
}

/// Runs a file of AES-GCM tests, or of GMAC's if `gmac`, whose message is the
/// AAD of an empty one, through `gcm::Key`, and those with 96-bit IVs through
/// `aead::Key` too.
fn aes_gcm(file: &str, gmac: bool) {
    let data_file = File::open(vectors(file)).expect("failed to open data file");

    let reader = BufReader::new(data_file);
    let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
    let mut summary = Summary::new();

    for group in tests.groups {
        summary.group(&group);

        for test in group.tests {
            summary.start(&test);

            let (algorithm, aes) = match test.key.len() {
                16 => (&AES_128_GCM, &AES_128),
                24 => (&AES_192_GCM, &AES_192),
                32 => (&AES_256_GCM, &AES_256),
                len => panic!("unexpected key length {len}"),
            };
            let (aad, msg, ct) = match gmac {
                true => (&test.msg[..], &[][..], &[][..]),
                false => (&test.aad[..], &test.msg[..], &test.ct[..]),
            };
            let valid = test.result == ExpectedResult::Valid;
            // A tag of another length, or an empty IV, for which GCM is
            // undefined.
            let malformed = test.tag.len() != 16 || test.iv.is_empty();

            if let Ok(iv) = <[u8; 12]>::try_from(test.iv.as_slice()) {
                let ctx = Key::new(algorithm, &test.key).unwrap();
                let nonce = || Nonce::assume_unique_for_key(iv);

                let mut got = ct.to_vec();
                let result = Tag::try_from(test.tag.as_slice()).and_then(|tag| {
                    ctx.open_in_place_separate_tag(nonce(), aad, tag, &mut got)
                        .map(|_| ())
                });
                check_open(valid, malformed, result);
                if valid {
                    assert_eq!(got, msg);
                }

                let mut got = msg.to_vec();
                let tag = ctx
                    .seal_in_place_separate_tag(nonce(), aad, &mut got)
                    .unwrap();
                if valid {
                    assert_eq!((&got[..], tag.as_ref()), (ct, &test.tag[..]));
                }
            }

            let ctx = gcm::Key::new(aes, &test.key, gcm::TagLength::Full).unwrap();
            let iv = || gcm::Iv::assume_unique_for_key(&test.iv);
            let mut got = ct.to_vec();
            let result = iv()
                .and_then(|iv| ctx.open_in_place_separate_tag(iv, aad, &test.tag, &mut got))
                .map(|_| ());
            check_open(valid, malformed, result);
            if valid {
                assert_eq!(got, msg);
            }

            let mut got = msg.to_vec();
            match iv().and_then(|iv| ctx.seal_in_place_separate_tag(iv, aad, &mut got)) {
                Ok(tag) if valid => assert_eq!((&got[..], tag.as_ref()), (ct, &test.tag[..])),
                Ok(_) => assert!(!test.iv.is_empty()),
                Err(Error::WrongLength) => assert!(test.iv.is_empty()),
                Err(e) => panic!("sealing failed with {e:?}"),
            }
        }
    }
}

/// Checks an open's result: an invalid test fails to authenticate, or is
/// refused as malformed.
fn check_open(valid: bool, malformed: bool, result: Result<(), Error>) {
    match (valid, result) {
        (true, Ok(())) | (false, Err(Error::DecryptFailed)) => {}
        (false, Err(Error::WrongLength)) if malformed => {}
        (_, result) => panic!("expected valid {valid}, got {result:?}"),
    }
}

#[test]
fn test_aes_cbc_pkcs7() {
    let data_file =
        File::open(vectors("aes_cbc_pkcs5_test.json")).expect("failed to open data file");

    let reader = BufReader::new(data_file);
    let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
    let mut summary = Summary::new();

    for group in tests.groups {
        summary.group(&group);

        for test in group.tests {
            summary.start(&test);

            let algorithm = match test.key.len() {
                16 => &AES_128,
                24 => &AES_192,
                32 => &AES_256,
                len => panic!("unexpected key length {len}"),
            };
            let iv: [u8; 16] = test.iv[..].try_into().unwrap();
            let enc = AesCbcEncryptingKey::new(algorithm, &test.key).unwrap();
            let dec = AesCbcDecryptingKey::new(algorithm, &test.key).unwrap();

            let mut in_out = test.ct.clone();
            let result = dec.decrypt(&iv, &mut in_out).map(|pt| pt.to_vec());
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(pt)) => {
                    assert_eq!(pt, test.msg);
                    let mut ct = test.msg.clone();
                    enc.encrypt(CbcIv::assume_unpredictable(iv), &mut ct);
                    assert_eq!(ct, test.ct);
                }
                // Every invalid test is a whole number of blocks whose
                // padding is malformed, so decryption clears it.
                (ExpectedResult::Invalid, Err(Error::DecryptFailed)) => {
                    assert!(in_out.iter().all(|b| *b == 0));
                }
                (_, result) => panic!("expected {:?} got {:?}", test.result, result),
            }

            // Without padding, every ciphertext decrypts to the padded
            // plaintext and encrypts back.
            let mut in_out = test.ct.clone();
            dec.decrypt_blocks(&iv, &mut in_out).unwrap();
            enc.encrypt_blocks(CbcIv::assume_unpredictable(iv), &mut in_out)
                .unwrap();
            assert_eq!(in_out, test.ct);
        }
    }
}

#[test]
fn test_aes_wrap() {
    let data_file = File::open(vectors("aes_wrap_test.json")).expect("failed to open data file");

    let reader = BufReader::new(data_file);
    let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
    let mut summary = Summary::new();

    for group in tests.groups {
        summary.group(&group);

        for test in group.tests {
            summary.start(&test);

            let algorithm = match test.key.len() {
                16 => &key_wrap::AES_128,
                24 => &key_wrap::AES_192,
                32 => &key_wrap::AES_256,
                len => panic!("unexpected key length {len}"),
            };
            let kek = AesKek::new(algorithm, &test.key).unwrap();

            let mut key = vec![0xaa; test.ct.len().saturating_sub(8)];
            let result = kek.unwrap(&test.ct, &mut key);
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(())) => assert_eq!(key, test.msg),
                // RFC 3394 wraps no key shorter than 16 bytes, which the
                // acceptable tests are.
                (
                    ExpectedResult::Invalid | ExpectedResult::Acceptable,
                    Err(Error::DecryptFailed),
                ) => {
                    assert!(key.iter().all(|b| *b == 0) || key.iter().all(|b| *b == 0xaa));
                }
                (_, result) => panic!("expected {:?} got {:?}", test.result, result),
            }

            let mut wrapped = vec![0u8; test.msg.len() + 8];
            let result = kek.wrap(&test.msg, &mut wrapped);
            let wrappable = test.msg.len() >= 16 && test.msg.len().is_multiple_of(8);
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(())) => assert_eq!(wrapped, test.ct),
                // a key wrapped and then altered
                (ExpectedResult::Invalid, Ok(())) if wrappable => assert_ne!(wrapped, test.ct),
                (ExpectedResult::Invalid | ExpectedResult::Acceptable, Err(Error::WrongLength))
                    if !wrappable => {}
                (_, result) => panic!("expected {:?} got {:?}", test.result, result),
            }
        }
    }
}

#[test]
fn test_aes_kwp() {
    let data_file = File::open(vectors("aes_kwp_test.json")).expect("failed to open data file");

    let reader = BufReader::new(data_file);
    let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
    let mut summary = Summary::new();

    for group in tests.groups {
        summary.group(&group);

        for test in group.tests {
            summary.start(&test);

            let algorithm = match test.key.len() {
                16 => &key_wrap::AES_128,
                24 => &key_wrap::AES_192,
                32 => &key_wrap::AES_256,
                len => panic!("unexpected key length {len}"),
            };
            let kek = AesKek::new(algorithm, &test.key).unwrap();

            let mut key = vec![0xaa; test.ct.len().saturating_sub(8)];
            let result = kek
                .unwrap_padded(&test.ct, &mut key)
                .map(|key| key.to_vec());
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(key)) => assert_eq!(key, test.msg),
                (ExpectedResult::Invalid, Err(Error::DecryptFailed)) => {
                    assert!(key.iter().all(|b| *b == 0) || key.iter().all(|b| *b == 0xaa));
                }
                (_, result) => panic!("expected {:?} got {:?}", test.result, result),
            }

            let mut wrapped = vec![0u8; test.msg.len().next_multiple_of(8) + 8];
            let result = kek.wrap_padded(&test.msg, &mut wrapped);
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(())) => assert_eq!(wrapped, test.ct),
                // a key wrapped and then altered
                (ExpectedResult::Invalid, Ok(())) => assert_ne!(wrapped, test.ct),
                // RFC 5649 wraps no empty key
                (ExpectedResult::Invalid, Err(Error::WrongLength)) if test.msg.is_empty() => {}
                (_, result) => panic!("expected {:?} got {:?}", test.result, result),
            }
        }
    }
}

#[test]
fn test_rsa_pkcs1_verify() {
    for file in &[
        "rsa_signature_2048_sha256_test.json",
        "rsa_signature_2048_sha384_test.json",
        "rsa_signature_2048_sha512_test.json",
        "rsa_signature_3072_sha256_test.json",
        "rsa_signature_3072_sha384_test.json",
        "rsa_signature_3072_sha512_test.json",
        "rsa_signature_4096_sha256_test.json",
        "rsa_signature_4096_sha384_test.json",
        "rsa_signature_4096_sha512_test.json",
        "rsa_signature_8192_sha256_test.json",
        "rsa_signature_8192_sha384_test.json",
        "rsa_signature_8192_sha512_test.json",
    ] {
        let data_file = File::open(vectors(file)).expect("failed to open data file");
        println!("file: {data_file:?}");

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);

            // Each algorithm for this hash, with the smallest modulus it takes.
            let algorithms: &[(&'static RsaVerificationAlgorithm, usize)] = match group.sha.as_ref()
            {
                "SHA-256" => &[
                    (&verify::RSA_PKCS1_SHA256, 2048),
                    (&legacy::RSA_PKCS1_1024_SHA256, 1024),
                ],
                "SHA-384" => &[
                    (&verify::RSA_PKCS1_SHA384, 2048),
                    (&legacy::RSA_PKCS1_3072_SHA384, 3072),
                ],
                "SHA-512" => &[
                    (&verify::RSA_PKCS1_SHA512, 2048),
                    (&legacy::RSA_PKCS1_1024_SHA512, 1024),
                ],
                other => panic!("unhandled sha {other:?}"),
            };
            let n = group.public_key.modulus.strip_prefix(&[0]).unwrap();
            let components = rind::rsa::PublicKeyComponents {
                n,
                e: &group.public_key.public_exponent[..],
            };

            for &(algorithm, min_bits) in algorithms {
                let key = signature::PublicKey::new(algorithm, &group.public_key_asn);
                if group.key_size < min_bits {
                    assert!(matches!(key, Err(Error::KeyRejected(_))));
                    assert!(matches!(
                        signature::PublicKey::from_components(algorithm, &components),
                        Err(Error::KeyRejected(_))
                    ));
                    continue;
                }
                let key = key.unwrap();
                let from_components =
                    signature::PublicKey::from_components(algorithm, &components).unwrap();
                assert_eq!(from_components.as_ref(), key.as_ref());
                let from_spki =
                    signature::PublicKey::new(algorithm, &group.public_key_der).unwrap();
                assert_eq!(from_spki.as_ref(), key.as_ref());
                let from_spki =
                    signature::PublicKey::from_spki(algorithm, &group.public_key_der).unwrap();
                assert_eq!(from_spki.as_ref(), key.as_ref());
                assert_eq!(from_spki.to_spki().as_ref(), &group.public_key_der[..]);
                assert!(signature::PublicKey::from_spki(algorithm, &group.public_key_asn).is_err());

                // The modulus with its sign byte is not minimal.
                let signed = rind::rsa::PublicKeyComponents {
                    n: &group.public_key.modulus[..],
                    e: components.e,
                };
                assert!(matches!(
                    signature::PublicKey::from_components(algorithm, &signed),
                    Err(Error::KeyRejected(_))
                ));

                for test in &group.tests {
                    summary.start(test);

                    let result = key.verify(&test.msg, &test.sig);
                    match (test.result, &result) {
                        (ExpectedResult::Valid, Ok(())) => {}
                        (
                            ExpectedResult::Invalid | ExpectedResult::Acceptable,
                            Err(Error::BadSignature),
                        ) => {}
                        _ => panic!("expected {:?} got {:?}", test.result, result.err()),
                    }
                    assert_eq!(from_components.verify(&test.msg, &test.sig), result);
                }
            }
        }
    }
}

#[test]
fn test_rsa_pkcs1_legacy_verify() {
    // Wycheproof has no verification files for SHA-1 or 1024-bit moduli,
    // but its signing files hold valid signatures for both.
    for file in &[
        "rsa_pkcs1_1024_sig_gen_test.json",
        "rsa_pkcs1_1536_sig_gen_test.json",
        "rsa_pkcs1_2048_sig_gen_test.json",
    ] {
        let data_file = File::open(vectors(file)).expect("failed to open data file");
        println!("file: {data_file:?}");

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);

            // Each algorithm for this hash, with the smallest modulus it takes.
            let algorithms: &[(&'static RsaVerificationAlgorithm, usize)] = match group.sha.as_ref()
            {
                "SHA-1" => &[
                    (&legacy::RSA_PKCS1_1024_SHA1, 1024),
                    (&legacy::RSA_PKCS1_SHA1, 2048),
                ],
                "SHA-256" => &[
                    (&legacy::RSA_PKCS1_1024_SHA256, 1024),
                    (&verify::RSA_PKCS1_SHA256, 2048),
                ],
                "SHA-384" => &[
                    (&verify::RSA_PKCS1_SHA384, 2048),
                    (&legacy::RSA_PKCS1_3072_SHA384, 3072),
                ],
                "SHA-512" => &[
                    (&legacy::RSA_PKCS1_1024_SHA512, 1024),
                    (&verify::RSA_PKCS1_SHA512, 2048),
                ],
                other => {
                    summary.skipped(&format!("pkcs1 verification with {other} not supported"));
                    continue;
                }
            };

            for &(algorithm, min_bits) in algorithms {
                let key = signature::PublicKey::new(algorithm, &group.key_asn);
                if group.key_size < min_bits {
                    assert!(matches!(key, Err(Error::KeyRejected(_))));
                    continue;
                }
                let key = key.unwrap();

                for test in &group.tests {
                    summary.start(test);

                    // Every case is valid or acceptable (a small modulus or
                    // a weak hash), and binds its message.
                    key.verify(&test.msg, &test.sig).unwrap();
                    assert_eq!(
                        key.verify(&[&test.msg[..], b"!"].concat(), &test.sig),
                        Err(Error::BadSignature)
                    );
                }
            }
        }
    }
}

#[test]
fn test_rsa_pkcs1_sign() {
    // The 1024- and 1536-bit files hold only keys below our 2048-bit minimum.
    for file in &[
        "rsa_pkcs1_2048_sig_gen_test.json",
        "rsa_pkcs1_3072_sig_gen_test.json",
        "rsa_pkcs1_4096_sig_gen_test.json",
    ] {
        let data_file = File::open(vectors(file)).expect("failed to open data file");
        println!("file: {data_file:?}");

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);

            let algorithm = match group.sha.as_ref() {
                "SHA-256" => &sign::RSA_PKCS1_SHA256,
                "SHA-384" => &sign::RSA_PKCS1_SHA384,
                "SHA-512" => &sign::RSA_PKCS1_SHA512,
                other => {
                    summary.skipped(&format!("pkcs1 signing with {other} not supported"));
                    continue;
                }
            };

            let key = signature::RsaKeyPair::from_pkcs8(&group.private_key_pkcs8).unwrap();

            for test in group.tests {
                summary.start(&test);

                let signature = key.sign(algorithm, &test.msg).unwrap();

                // Every case is valid or acceptable (a small public exponent),
                // and PKCS#1 v1.5 signing is deterministic.
                assert_eq!(signature.as_ref(), test.sig);
            }
        }
    }
}

#[test]
fn test_rsa_oaep_decrypt() {
    // Every file whose hash and MGF1 hash agree on one rind supports; the
    // misc file mixes them, and holds keys below our 2048-bit minimum.
    for file in &[
        "rsa_oaep_2048_sha1_mgf1sha1_test.json",
        "rsa_oaep_2048_sha256_mgf1sha256_test.json",
        "rsa_oaep_2048_sha384_mgf1sha384_test.json",
        "rsa_oaep_2048_sha512_mgf1sha512_test.json",
        "rsa_oaep_3072_sha256_mgf1sha256_test.json",
        "rsa_oaep_3072_sha512_mgf1sha512_test.json",
        "rsa_oaep_4096_sha256_mgf1sha256_test.json",
        "rsa_oaep_4096_sha512_mgf1sha512_test.json",
        "rsa_oaep_misc_test.json",
    ] {
        let data_file = File::open(vectors(file)).expect("failed to open data file");
        println!("file: {data_file:?}");

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);
            assert_eq!(group.mgf, "MGF1");

            let algorithm: &'static OaepAlgorithm =
                match (group.sha.as_ref(), group.mgf_sha.as_ref()) {
                    ("SHA-1", "SHA-1") => &rsa::legacy::OAEP_SHA1,
                    ("SHA-256", "SHA-256") => &rsa::OAEP_SHA256,
                    ("SHA-384", "SHA-384") => &rsa::OAEP_SHA384,
                    ("SHA-512", "SHA-512") => &rsa::OAEP_SHA512,
                    other => {
                        summary.skipped(&format!(
                            "oaep with sha={} mgf={} not supported",
                            other.0, other.1
                        ));
                        continue;
                    }
                };

            let key = DecryptingKey::from_pkcs8(algorithm, &group.private_key_pkcs8);
            if group.key_size < 2048 {
                assert!(matches!(key, Err(Error::KeyRejected(_))), "{key:?}");
                summary.skipped("key below 2048 bits");
                continue;
            }
            let key = key.unwrap();

            for test in group.tests {
                summary.start(&test);

                let result = key.decrypt(&test.ct, &test.label);
                match (test.result, &result) {
                    (ExpectedResult::Valid | ExpectedResult::Acceptable, Ok(plaintext)) => {
                        assert_eq!(plaintext.as_ref(), test.msg)
                    }
                    (ExpectedResult::Invalid, Err(Error::DecryptFailed)) => {}
                    _ => panic!("expected {:?} got {:?}", test.result, result),
                }
            }
        }
    }
}

#[test]
fn test_rsa_pss_verify() {
    for file in &[
        "rsa_pss_2048_sha256_mgf1_0_test.json",
        "rsa_pss_2048_sha256_mgf1_32_test.json",
        "rsa_pss_2048_sha384_mgf1_48_test.json",
        "rsa_pss_3072_sha256_mgf1_32_test.json",
        "rsa_pss_4096_sha256_mgf1_32_test.json",
        "rsa_pss_4096_sha384_mgf1_48_test.json",
        "rsa_pss_4096_sha512_mgf1_32_test.json",
        "rsa_pss_4096_sha512_mgf1_64_test.json",
        "rsa_pss_misc_test.json",
    ] {
        let data_file = File::open(vectors(file)).expect("failed to open data file");
        println!("file: {data_file:?}");

        let reader = BufReader::new(data_file);
        let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
        let mut summary = Summary::new();

        for group in tests.groups {
            summary.group(&group);

            type Pss = fn(RsaPssSaltLength) -> RsaVerificationAlgorithm;
            let (pss, any_salt): (Pss, _) = match (group.sha.as_ref(), group.mgf_sha.as_ref()) {
                ("SHA-256", "SHA-256") => (
                    RsaVerificationAlgorithm::pss_sha256,
                    &verify::RSA_PSS_SHA256_ANY_SALT,
                ),
                ("SHA-384", "SHA-384") => (
                    RsaVerificationAlgorithm::pss_sha384,
                    &verify::RSA_PSS_SHA384_ANY_SALT,
                ),
                ("SHA-512", "SHA-512") => (
                    RsaVerificationAlgorithm::pss_sha512,
                    &verify::RSA_PSS_SHA512_ANY_SALT,
                ),
                other => {
                    summary.skipped(&format!(
                        "pss with sha={} mgf={} not supported",
                        other.0, other.1
                    ));
                    continue;
                }
            };
            // Loaded from its SPKI; the PKCS#1 tests load the raw key.
            let spki = &group.public_key_der;
            let salt = |len: usize| pss(RsaPssSaltLength::Custom(len.try_into().unwrap()));
            let key = signature::PublicKey::new(&salt(group.salt_len), spki).unwrap();
            let any_salt_key = signature::PublicKey::new(any_salt, spki).unwrap();
            // The hash-length salt has its own constant, which must agree.
            let hash_salt_key = match (group.sha.as_ref(), group.salt_len) {
                ("SHA-256", 32) => Some(&verify::RSA_PSS_SHA256),
                ("SHA-384", 48) => Some(&verify::RSA_PSS_SHA384),
                ("SHA-512", 64) => Some(&verify::RSA_PSS_SHA512),
                _ => None,
            }
            .map(|algorithm| signature::PublicKey::new(algorithm, spki).unwrap());

            for test in group.tests {
                summary.start(&test);

                let result = key.verify(&test.msg, &test.sig);
                match (test.result, &result) {
                    (ExpectedResult::Valid, Ok(())) => {}
                    (
                        ExpectedResult::Invalid | ExpectedResult::Acceptable,
                        Err(Error::BadSignature),
                    ) => {}
                    _ => panic!("expected {:?} got {:?}", test.result, result.err()),
                }
                if let Some(hash_salt_key) = &hash_salt_key {
                    assert_eq!(hash_salt_key.verify(&test.msg, &test.sig), result);
                }

                // These are well formed with another salt length, which
                // verifies them.
                match test
                    .comment
                    .as_deref()
                    .and_then(|c| c.strip_prefix("s_len changed to "))
                {
                    Some(len) => {
                        let len = len.parse().unwrap();
                        signature::PublicKey::new(&salt(len), spki)
                            .unwrap()
                            .verify(&test.msg, &test.sig)
                            .unwrap();
                        any_salt_key.verify(&test.msg, &test.sig).unwrap();
                    }
                    None => assert_eq!(any_salt_key.verify(&test.msg, &test.sig), result),
                }
            }
        }
    }
}

#[test]
fn test_ed25519_verify() {
    let data_file = File::open(vectors("ed25519_test.json")).expect("failed to open data file");
    println!("file: {data_file:?}");

    let reader = BufReader::new(data_file);
    let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
    let mut summary = Summary::new();

    for group in tests.groups {
        summary.group(&group);

        let key = signature::PublicKey::new(&verify::ED25519, &group.public_key.pk);
        let from_spki = signature::PublicKey::from_spki(&verify::ED25519, &group.public_key_der);
        match (&key, from_spki) {
            (Ok(key), Ok(from_spki)) => {
                assert_eq!(from_spki.as_ref(), key.as_ref());
                assert_eq!(from_spki.to_spki().as_ref(), &group.public_key_der[..]);
            }
            (Err(e), Err(from_spki)) => assert_eq!(*e, from_spki),
            (key, from_spki) => panic!("{key:?} but from SPKI {from_spki:?}"),
        }

        for test in group.tests {
            summary.start(&test);

            // rind refuses a small-order key, which verifies forgeries.
            if test.flags.iter().any(|flag| flag == "SmallOrderPublicKey") {
                assert_eq!(test.result, ExpectedResult::Acceptable);
                let err = key.as_ref().unwrap_err().to_string();
                assert!(err.contains("small-order"), "{err}");
                continue;
            }

            let result = key.as_ref().unwrap().verify(&test.msg, &test.sig);
            match (test.result, result) {
                // "acceptable" cases are mixed-order public keys
                (ExpectedResult::Valid | ExpectedResult::Acceptable, Ok(())) => {}
                (
                    ExpectedResult::Invalid | ExpectedResult::Acceptable,
                    Err(Error::BadSignature),
                ) => {}
                _ => panic!("expected {:?} got {:?}", test.result, result.err()),
            }
        }
    }
}

#[test]
fn test_chacha20poly1305() {
    let data_file =
        File::open(vectors("chacha20_poly1305_test.json")).expect("failed to open data file");

    let reader = BufReader::new(data_file);
    let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
    let mut summary = Summary::new();

    for group in tests.groups {
        summary.group(&group);

        for test in group.tests {
            summary.start(&test);

            if test.iv.len() != 12 {
                summary.skipped("chacha20_poly1305 nonce must be 96 bit");
                continue;
            }

            let ctx = Key::new(&CHACHA20_POLY1305, &test.key).unwrap();
            let iv: [u8; 12] = test.iv.try_into().unwrap();
            let nonce = || Nonce::assume_unique_for_key(iv);

            // try decrypt
            let mut msg = test.ct.clone();
            let result = Tag::try_from(test.tag.as_slice()).and_then(|tag| {
                ctx.open_in_place_separate_tag(nonce(), &test.aad, tag, &mut msg)
                    .map(|_| ())
            });

            match (test.result, &result) {
                (ExpectedResult::Valid, Ok(())) => {
                    assert_eq!(msg, test.msg);
                }
                (ExpectedResult::Invalid, Err(Error::DecryptFailed)) => {}
                (ExpectedResult::Invalid, Err(Error::WrongLength)) if test.tag.len() != 16 => {}
                _ => panic!("expected {:?} got {:?}", test.result, result.err()),
            }

            // and encrypt
            let mut ct = test.msg.clone();
            let tag = ctx
                .seal_in_place_separate_tag(nonce(), &test.aad, &mut ct)
                .unwrap();

            if test.result == ExpectedResult::Valid {
                assert_eq!(ct, test.ct);
                assert_eq!(tag.as_ref(), &test.tag[..]);
            }
        }
    }
}

#[test]
fn test_chacha20() {
    let data_file =
        File::open(vectors("chacha20_counter_test.json")).expect("failed to open data file");

    let reader = BufReader::new(data_file);
    let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
    let mut summary = Summary::new();

    for group in tests.groups {
        summary.group(&group);

        for test in group.tests {
            summary.start(&test);

            if test.iv.len() != 12 {
                summary.skipped("only the 96-bit nonce variant is exposed");
                continue;
            }

            let ctx = ChaCha20::new(test.key.as_slice().try_into().unwrap());
            let counter = u32::from_le_bytes(test.initial_counter.try_into().unwrap());

            let mut buf = test.msg.clone();
            let result = ctx.apply_keystream(&test.iv.try_into().unwrap(), counter, &mut buf);

            match (test.result, result) {
                (ExpectedResult::Valid, Ok(())) => assert_eq!(buf, test.ct),
                (ExpectedResult::Invalid, Err(Error::WrongLength)) => assert_eq!(buf, test.msg),
                (_, result) => panic!("expected {:?} got {:?}", test.result, result),
            }
        }
    }
}

#[test]
fn test_xchacha20poly1305() {
    let data_file =
        File::open(vectors("xchacha20_poly1305_test.json")).expect("failed to open data file");

    let reader = BufReader::new(data_file);
    let tests: TestFile = serde_json::from_reader(reader).expect("invalid test JSON");
    let mut summary = Summary::new();

    for group in tests.groups {
        summary.group(&group);

        for test in group.tests {
            summary.start(&test);

            if test.iv.len() != 24 {
                summary.skipped("xchacha20_poly1305 nonce must be 192 bit");
                continue;
            }

            let ctx = RandomizedNonceKey::new(&test.key.try_into().unwrap());
            let iv: [u8; 24] = test.iv.try_into().unwrap();

            // try decrypt
            let mut sealed = [&test.ct[..], &test.tag[..]].concat();
            let result = ctx
                .open_in_place(RandomNonce::from(iv), &test.aad, &mut sealed)
                .map(|msg| msg.to_vec());

            match (test.result, &result) {
                (ExpectedResult::Valid, Ok(msg)) => {
                    assert_eq!(msg, &test.msg);
                }
                (ExpectedResult::Invalid, Err(Error::DecryptFailed)) => {}
                _ => panic!("expected {:?} got {:?}", test.result, result.err()),
            }

            // Sealing picks its own nonce, so check it round trips; the unit
            // tests check a sealed vector.
            let mut sealed = test.msg.clone();
            let nonce = ctx
                .seal_in_place_append_tag(&test.aad, &mut sealed)
                .unwrap();
            assert_eq!(
                ctx.open_in_place(nonce, &test.aad, &mut sealed).unwrap(),
                &test.msg[..]
            );
        }
    }
}
