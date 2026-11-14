// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Wycheproof's vectors for each algorithm rind-fips offers, through the
//! module's C ABI and its own optimized build of rind, rather than the build
//! `rind/tests/wycheproof.rs` checks. Each vector's expected result is
//! checked directly. Where the module refuses what FIPS 140-3 does not
//! approve, which rind takes, such as a PBKDF2 salt under 16 bytes or a
//! 1536-bit RSA modulus, the refusal is checked instead.
#![cfg(rind_fips_module)]

use std::fs::File;
use std::io::BufReader;
use std::num::NonZeroU32;

use rind_fips::aead::{AES_128_GCM, AES_192_GCM, AES_256_GCM, Key, Nonce, Tag, gcm};
use rind_fips::cipher::{
    AES_128, AES_192, AES_256, AesCbcDecryptingKey, AesCbcEncryptingKey, CbcIv,
};
use rind_fips::key_wrap::AesKek;
use rind_fips::signature::verify::legacy;
use rind_fips::signature::{self, RsaVerificationAlgorithm, sign, verify};
use rind_fips::{Error, agreement, digest, hkdf, hmac, kem, pbkdf2};
use serde::Deserialize;

/// The path of the Wycheproof vector file `name`.
fn vectors(name: &str) -> String {
    let dir = env!("CARGO_MANIFEST_DIR");
    format!("{dir}/../thirdparty/wycheproof/testvectors_v1/{name}")
}

fn read<T: for<'de> Deserialize<'de>>(name: &str) -> T {
    let file = File::open(vectors(name)).unwrap_or_else(|_| panic!("failed to open {name}"));
    serde_json::from_reader(BufReader::new(file)).expect("invalid test JSON")
}

#[derive(Deserialize, Debug)]
struct TestFile {
    #[serde(rename(deserialize = "testGroups"))]
    groups: Vec<TestGroup>,
}

#[derive(Deserialize, Debug)]
struct TestGroup {
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

    tests: Vec<Test>,
}

#[derive(Deserialize, Debug)]
struct Test {
    #[serde(rename(deserialize = "tcId"))]
    id: usize,
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
    #[serde(default)]
    flags: Vec<String>,
    result: ExpectedResult,
}

impl Test {
    fn has_flag(&self, flag: &str) -> bool {
        self.flags.iter().any(|f| f == flag)
    }
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

/// Counts a file's tests, failing if every one was skipped.
struct Summary {
    file: &'static str,
    started: usize,
    skipped: usize,
}

impl Summary {
    fn new(file: &'static str) -> Self {
        Self {
            file,
            started: 0,
            skipped: 0,
        }
    }

    fn start(&mut self) {
        self.started += 1;
    }

    fn skip(&mut self, count: usize) {
        self.started += count;
        self.skipped += count;
    }

    /// Counts `count` tests the module refused as a group, as it must: each
    /// is checked, not skipped.
    fn refused(&mut self, count: usize) {
        self.started += count;
    }
}

impl Drop for Summary {
    fn drop(&mut self) {
        println!(
            "{}: started {} skipped {}",
            self.file, self.started, self.skipped
        );
        if !std::thread::panicking() {
            assert_ne!(
                self.started, self.skipped,
                "{}: every test skipped",
                self.file
            );
        }
    }
}

/// Checks that `result` refused a key, saying `why`.
fn rejected<T: core::fmt::Debug>(result: Result<T, Error>, why: &str) {
    match result {
        Err(Error::KeyRejected(reason)) => {
            assert!(reason.to_string().contains(why), "{reason} is not {why:?}")
        }
        other => panic!("expected a key rejected for {why:?}, got {other:?}"),
    }
}

#[test]
fn hmac() {
    for (file, algorithm) in [
        ("hmac_sha1_test.json", &hmac::legacy::HMAC_SHA1),
        ("hmac_sha256_test.json", &hmac::HMAC_SHA256),
        ("hmac_sha384_test.json", &hmac::HMAC_SHA384),
        ("hmac_sha512_test.json", &hmac::HMAC_SHA512),
    ] {
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
            for test in group.tests {
                summary.start();
                let key = hmac::Key::new(algorithm, &test.key);
                // The module compares only whole tags; these vectors also
                // truncate them.
                let result = match test.tag.len() == algorithm.tag_len() {
                    true => hmac::verify(&key, &test.msg, &test.tag),
                    false => match hmac::sign(&key, &test.msg).as_ref().starts_with(&test.tag) {
                        true => Ok(()),
                        false => Err(Error::BadSignature),
                    },
                };
                match (test.result, result) {
                    (ExpectedResult::Valid, Ok(())) => {}
                    (ExpectedResult::Invalid, Err(Error::BadSignature)) => {}
                    _ => panic!(
                        "{file} {}: expected {:?} got {result:?}",
                        test.id, test.result
                    ),
                }

                // Through a context, a message split anywhere signs the same.
                let mut ctx = hmac::Context::with_key(&key);
                let (head, tail) = test.msg.split_at(test.msg.len() / 3);
                ctx.update(head);
                ctx.update(tail);
                assert_eq!(
                    ctx.sign().as_ref(),
                    hmac::sign(&key, &test.msg).as_ref(),
                    "{file} {}",
                    test.id
                );
            }
        }
    }
}

#[test]
fn hkdf() {
    for (file, algorithm) in [
        ("hkdf_sha1_test.json", &hkdf::legacy::HKDF_SHA1),
        ("hkdf_sha256_test.json", &hkdf::HKDF_SHA256),
        ("hkdf_sha384_test.json", &hkdf::HKDF_SHA384),
        ("hkdf_sha512_test.json", &hkdf::HKDF_SHA512),
    ] {
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
            for test in group.tests {
                summary.start();
                let mut okm = vec![0u8; test.size];
                let info = [test.info.as_slice()];
                let result = hkdf::Salt::new(algorithm, &test.salt)
                    .extract(&test.ikm)
                    .and_then(|prk| prk.expand(&info, okm.len())?.fill(&mut okm));
                // FIPS 140-3 approves no empty salt or info.
                if test.salt.is_empty() || test.info.is_empty() {
                    assert_eq!(result, Err(Error::WrongLength), "{file} {}", test.id);
                    continue;
                }
                match (test.result, result) {
                    (ExpectedResult::Valid, Ok(())) => assert_eq!(okm, test.okm),
                    // Longer than 255 hash blocks.
                    (ExpectedResult::Invalid, Err(Error::WrongLength)) => {}
                    _ => panic!(
                        "{file} {}: expected {:?} got {result:?}",
                        test.id, test.result
                    ),
                }
            }
        }
    }
}

#[test]
fn pbkdf2() {
    // SHA-224, which the module does not offer, has its own file.
    for (file, algorithm, hmac_len) in [
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
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
            for test in group.tests {
                // Every vector is valid: none has a zero count or empty key.
                assert_eq!(test.result, ExpectedResult::Valid);
                let iterations = NonZeroU32::new(test.iteration_count).unwrap();
                let secret = pbkdf2::Secret::new(algorithm, &test.password);
                let mut dk = vec![0u8; test.dk.len()];
                let result = secret.derive(iterations, &test.salt, &mut dk);

                // SP 800-132's floors, which most of these vectors miss.
                let approved = test.password.len() >= 14
                    && test.salt.len() >= 16
                    && test.iteration_count >= 1000
                    && test.dk.len() >= 14;
                if !approved {
                    summary.start();
                    assert_eq!(result, Err(Error::WrongLength), "{file} {}", test.id);
                    assert!(dk.iter().all(|b| *b == 0), "{file} {}", test.id);
                    assert_eq!(
                        secret.verify(iterations, &test.salt, &test.dk),
                        Err(Error::WrongLength),
                        "{file} {}",
                        test.id
                    );
                    continue;
                }
                // One SHA-1 vector runs 16,777,216 iterations: seconds even
                // in the module's optimized build.
                if test.iteration_count > 100_000 && std::env::var_os("SLOW_TESTS").is_none() {
                    summary.skip(1);
                    continue;
                }
                summary.start();
                result.unwrap();
                assert_eq!(dk, test.dk, "{file} {}", test.id);
                // The module verifies only keys at least as long as the HMAC
                // output.
                let wanted = match test.dk.len() < hmac_len {
                    true => Err(Error::WrongLength),
                    false => Ok(()),
                };
                assert_eq!(
                    secret.verify(iterations, &test.salt, &test.dk),
                    wanted,
                    "{file} {}",
                    test.id
                );
            }
        }
    }
}

#[test]
fn ecdsa_verify() {
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
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
            let public_key =
                signature::PublicKey::new(algorithm, &group.public_key.uncompressed).unwrap();
            check_ecdsa_spki(algorithm, &group, &public_key);

            for test in group.tests {
                summary.start();
                let result = public_key.verify(&test.msg, &test.sig);
                match (test.result, result) {
                    (ExpectedResult::Valid, Ok(())) => {}
                    (ExpectedResult::Invalid, Err(Error::BadSignature)) => {}
                    _ => panic!(
                        "{file} {}: expected {:?} got {result:?}",
                        test.id, test.result
                    ),
                }
            }
        }
    }
}

/// The group's SPKI parses as its point, and encodes back to itself; with
/// its point compressed, it parses as the same point; and the raw point
/// compressed is refused, as `PublicKey::new` takes only uncompressed ones.
fn check_ecdsa_spki(
    algorithm: &'static signature::VerificationAlgorithm,
    group: &TestGroup,
    key: &signature::PublicKey,
) {
    let der = &group.public_key_der;
    let from_spki = signature::PublicKey::from_spki(algorithm, der).unwrap();
    assert_eq!(from_spki.as_ref(), key.as_ref());
    assert_eq!(from_spki.to_spki().as_ref(), &der[..]);

    let compressed = compress(key.as_ref());
    let compressed_der = spki(algorithm_identifier(der), &compressed);
    let from_compressed = signature::PublicKey::from_spki(algorithm, &compressed_der);
    assert_eq!(from_compressed.unwrap().as_ref(), key.as_ref());
    rejected(
        signature::PublicKey::new(algorithm, &compressed),
        "compressed",
    );
}

/// The point `uncompressed`, compressed.
fn compress(uncompressed: &[u8]) -> Vec<u8> {
    let (x, y) = uncompressed[1..].split_at(uncompressed.len() / 2);
    [&[2 | (y[y.len() - 1] & 1)][..], x].concat()
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
fn ecdsa_verify_digest() {
    use digest::{SHA256, SHA384, SHA512};

    // Each file whose curve the module has and whose hash its signatures
    // take, with an algorithm for its curve and encoding: the digest names
    // the hash, which replaces the algorithm's.
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
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
            let public_key =
                signature::PublicKey::new(algorithm, &group.public_key.uncompressed).unwrap();
            for test in group.tests {
                summary.start();
                let digest = digest::digest(hash, &test.msg);
                let result = public_key.verify_digest(&digest, &test.sig);
                match (test.result, result) {
                    (ExpectedResult::Valid, Ok(())) => {}
                    (ExpectedResult::Invalid, Err(Error::BadSignature)) => {}
                    _ => panic!(
                        "{file} {}: expected {:?} got {result:?}",
                        test.id, test.result
                    ),
                }
            }
        }
    }
}

#[test]
fn aes_gcm() {
    aes_gcm_file("aes_gcm_test.json", false);
}

#[test]
fn aes_gmac() {
    aes_gcm_file("aes_gmac_test.json", true);
}

/// Opens a file of AES-GCM tests, or of GMAC's if `gmac`, whose message is
/// the AAD of an empty one, through `gcm::Key`, and those with 96-bit IVs
/// through `aead::Key` too. The module does not seal.
fn aes_gcm_file(file: &'static str, gmac: bool) {
    let mut summary = Summary::new(file);
    for group in read::<TestFile>(file).groups {
        for test in group.tests {
            summary.start();
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
                let key = Key::new(algorithm, &test.key).unwrap();
                let mut got = ct.to_vec();
                let result = Tag::try_from(test.tag.as_slice()).and_then(|tag| {
                    key.open_in_place_separate_tag(
                        Nonce::assume_unique_for_key(iv),
                        aad,
                        tag,
                        &mut got,
                    )
                    .map(|_| ())
                });
                check_open(file, test.id, valid, malformed, result);
                match valid {
                    true => assert_eq!(got, msg),
                    // A failed open clears the ciphertext.
                    false if !malformed => assert!(got.iter().all(|b| *b == 0)),
                    false => {}
                }

                // The tag appended opens alike.
                let mut appended = [ct, &test.tag].concat();
                let result = key
                    .open_in_place(Nonce::assume_unique_for_key(iv), aad, &mut appended)
                    .map(|plaintext| plaintext.to_vec());
                match (valid, malformed, result) {
                    (true, _, Ok(plaintext)) => assert_eq!(plaintext, msg),
                    (false, _, Err(Error::DecryptFailed)) => {}
                    (valid, _, result) => {
                        panic!("{file} {}: expected valid {valid}, got {result:?}", test.id)
                    }
                }
            }

            let key = gcm::Key::new(aes, &test.key, gcm::TagLength::Full).unwrap();
            let mut got = ct.to_vec();
            let result = gcm::Iv::assume_unique_for_key(&test.iv)
                .and_then(|iv| key.open_in_place_separate_tag(iv, aad, &test.tag, &mut got))
                .map(|_| ());
            check_open(file, test.id, valid, malformed, result);
            if valid {
                assert_eq!(got, msg);
            }
        }
    }
}

/// Checks an open's result: an invalid test fails to authenticate, or is
/// refused as malformed.
fn check_open(file: &str, id: usize, valid: bool, malformed: bool, result: Result<(), Error>) {
    match (valid, result) {
        (true, Ok(())) | (false, Err(Error::DecryptFailed)) => {}
        (false, Err(Error::WrongLength)) if malformed => {}
        (_, result) => panic!("{file} {id}: expected valid {valid}, got {result:?}"),
    }
}

#[test]
fn aes_cbc_pkcs7() {
    let file = "aes_cbc_pkcs5_test.json";
    let mut summary = Summary::new(file);
    for group in read::<TestFile>(file).groups {
        for test in group.tests {
            summary.start();
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
                    enc.encrypt(CbcIv::assume_unpredictable(iv), &mut ct)
                        .unwrap();
                    assert_eq!(ct, test.ct);
                }
                // Every invalid test is a whole number of blocks whose
                // padding is malformed, so decryption clears it.
                (ExpectedResult::Invalid, Err(Error::DecryptFailed)) => {
                    assert!(in_out.iter().all(|b| *b == 0));
                }
                (_, result) => panic!(
                    "{file} {}: expected {:?} got {result:?}",
                    test.id, test.result
                ),
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

fn kek(key: &[u8]) -> AesKek {
    let algorithm = match key.len() {
        16 => &AES_128,
        24 => &AES_192,
        32 => &AES_256,
        len => panic!("unexpected key length {len}"),
    };
    AesKek::new(algorithm, key).unwrap()
}

#[test]
fn aes_wrap() {
    let file = "aes_wrap_test.json";
    let mut summary = Summary::new(file);
    for group in read::<TestFile>(file).groups {
        for test in group.tests {
            summary.start();
            let kek = kek(&test.key);

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
                (_, result) => panic!(
                    "{file} {}: expected {:?} got {result:?}",
                    test.id, test.result
                ),
            }

            let mut wrapped = vec![0u8; test.msg.len() + 8];
            let result = kek.wrap(&test.msg, &mut wrapped);
            let wrappable = test.msg.len() >= 16 && test.msg.len().is_multiple_of(8);
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(())) => assert_eq!(wrapped, test.ct),
                // A key wrapped and then altered.
                (ExpectedResult::Invalid, Ok(())) if wrappable => assert_ne!(wrapped, test.ct),
                (ExpectedResult::Invalid | ExpectedResult::Acceptable, Err(Error::WrongLength))
                    if !wrappable => {}
                (_, result) => panic!(
                    "{file} {}: expected {:?} got {result:?}",
                    test.id, test.result
                ),
            }
        }
    }
}

#[test]
fn aes_kwp() {
    let file = "aes_kwp_test.json";
    let mut summary = Summary::new(file);
    for group in read::<TestFile>(file).groups {
        for test in group.tests {
            summary.start();
            let kek = kek(&test.key);

            let mut key = vec![0xaa; test.ct.len().saturating_sub(8)];
            let result = kek
                .unwrap_padded(&test.ct, &mut key)
                .map(|key| key.to_vec());
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(key)) => assert_eq!(key, test.msg),
                (ExpectedResult::Invalid, Err(Error::DecryptFailed)) => {
                    assert!(key.iter().all(|b| *b == 0) || key.iter().all(|b| *b == 0xaa));
                }
                (_, result) => panic!(
                    "{file} {}: expected {:?} got {result:?}",
                    test.id, test.result
                ),
            }

            let mut wrapped = vec![0u8; test.msg.len().next_multiple_of(8) + 8];
            let result = kek.wrap_padded(&test.msg, &mut wrapped);
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(())) => assert_eq!(wrapped, test.ct),
                // A key wrapped and then altered.
                (ExpectedResult::Invalid, Ok(())) => assert_ne!(wrapped, test.ct),
                // RFC 5649 wraps no empty key.
                (ExpectedResult::Invalid, Err(Error::WrongLength)) if test.msg.is_empty() => {}
                (_, result) => panic!(
                    "{file} {}: expected {:?} got {result:?}",
                    test.id, test.result
                ),
            }
        }
    }
}

/// Whether the module takes an RSA modulus of `bits` for an algorithm whose
/// floor is `min_bits`: FIPS 186-5's even lengths from the floor up, or
/// exactly 1024 bits for the legacy algorithms with that floor.
fn rsa_size_approved(bits: usize, min_bits: usize) -> bool {
    bits.is_multiple_of(2) && (bits >= min_bits.max(2048) || bits == min_bits)
}

#[test]
fn rsa_pkcs1_verify() {
    for file in [
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
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
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
            let components = rind_fips::rsa::PublicKeyComponents {
                n,
                e: &group.public_key.public_exponent[..],
            };

            for &(algorithm, min_bits) in algorithms {
                let key = signature::PublicKey::new(algorithm, &group.public_key_asn);
                if !rsa_size_approved(group.key_size, min_bits) {
                    rejected(key, "RSA modulus");
                    rejected(
                        signature::PublicKey::from_components(algorithm, &components),
                        "RSA modulus",
                    );
                    summary.refused(group.tests.len());
                    continue;
                }
                let key = key.unwrap();
                let from_components =
                    signature::PublicKey::from_components(algorithm, &components).unwrap();
                assert_eq!(from_components.as_ref(), key.as_ref());
                let from_der = signature::PublicKey::new(algorithm, &group.public_key_der).unwrap();
                assert_eq!(from_der.as_ref(), key.as_ref());
                let from_spki =
                    signature::PublicKey::from_spki(algorithm, &group.public_key_der).unwrap();
                assert_eq!(from_spki.as_ref(), key.as_ref());
                assert_eq!(from_spki.to_spki().as_ref(), &group.public_key_der[..]);
                assert!(signature::PublicKey::from_spki(algorithm, &group.public_key_asn).is_err());

                // The modulus with its sign byte is not minimal.
                let signed = rind_fips::rsa::PublicKeyComponents {
                    n: &group.public_key.modulus[..],
                    e: components.e,
                };
                assert!(matches!(
                    signature::PublicKey::from_components(algorithm, &signed),
                    Err(Error::KeyRejected(_))
                ));

                for test in &group.tests {
                    summary.start();
                    let result = key.verify(&test.msg, &test.sig);
                    match (test.result, result) {
                        (ExpectedResult::Valid, Ok(())) => {}
                        (
                            ExpectedResult::Invalid | ExpectedResult::Acceptable,
                            Err(Error::BadSignature),
                        ) => {}
                        _ => panic!(
                            "{file} {}: expected {:?} got {result:?}",
                            test.id, test.result
                        ),
                    }
                    assert_eq!(from_components.verify(&test.msg, &test.sig), result);
                }
            }
        }
    }
}

/// SP 800-131A's legacy verification: SHA-1, and 1024-bit moduli, but none
/// between 1024 and 2048 bits, which rind takes.
#[test]
fn rsa_pkcs1_legacy_verify() {
    // Wycheproof has no verification files for SHA-1 or 1024-bit moduli,
    // but its signing files hold valid signatures for both.
    for file in [
        "rsa_pkcs1_1024_sig_gen_test.json",
        "rsa_pkcs1_1536_sig_gen_test.json",
        "rsa_pkcs1_2048_sig_gen_test.json",
    ] {
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
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
                // SHA-224 and SHA-512/224 and /256, which the module has no
                // RSA algorithm for.
                _ => {
                    summary.skip(group.tests.len());
                    continue;
                }
            };

            for &(algorithm, min_bits) in algorithms {
                let key = signature::PublicKey::new(algorithm, &group.key_asn);
                if !rsa_size_approved(group.key_size, min_bits) {
                    rejected(key, "RSA modulus");
                    summary.refused(group.tests.len());
                    continue;
                }
                let key = key.unwrap();
                for test in &group.tests {
                    summary.start();
                    // Every case is valid or acceptable (a small modulus or
                    // a weak hash), and binds its message.
                    key.verify(&test.msg, &test.sig)
                        .unwrap_or_else(|e| panic!("{file} {}: {e:?}", test.id));
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
fn rsa_pkcs1_sign() {
    for file in [
        "rsa_pkcs1_1024_sig_gen_test.json",
        "rsa_pkcs1_1536_sig_gen_test.json",
        "rsa_pkcs1_2048_sig_gen_test.json",
        "rsa_pkcs1_3072_sig_gen_test.json",
        "rsa_pkcs1_4096_sig_gen_test.json",
    ] {
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
            // FIPS 186-5 signs with no modulus under 2048 bits, nor of an
            // odd length.
            let key = signature::RsaKeyPair::from_pkcs8(&group.private_key_pkcs8);
            if !rsa_size_approved(group.key_size, 2048) {
                rejected(key, "RSA modulus");
                summary.refused(group.tests.len());
                continue;
            }
            let key = key.unwrap();

            let algorithm = match group.sha.as_ref() {
                "SHA-256" => &sign::RSA_PKCS1_SHA256,
                "SHA-384" => &sign::RSA_PKCS1_SHA384,
                "SHA-512" => &sign::RSA_PKCS1_SHA512,
                // SHA-1 signing, which SP 800-131A disallows, and hashes the
                // module has no RSA algorithm for.
                _ => {
                    summary.skip(group.tests.len());
                    continue;
                }
            };

            for test in group.tests {
                summary.start();
                let signature = key.sign(algorithm, &test.msg).unwrap();
                // Every case is valid or acceptable (a small public
                // exponent), and PKCS#1 v1.5 signing is deterministic.
                assert_eq!(signature.as_ref(), test.sig, "{file} {}", test.id);
            }
        }
    }
}

#[test]
fn rsa_pss_verify() {
    for file in [
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
        let mut summary = Summary::new(file);
        for group in read::<TestFile>(file).groups {
            let (algorithm, hash_len) = match (group.sha.as_ref(), group.mgf_sha.as_ref()) {
                ("SHA-256", "SHA-256") => (&verify::RSA_PSS_SHA256, 32),
                ("SHA-384", "SHA-384") => (&verify::RSA_PSS_SHA384, 48),
                ("SHA-512", "SHA-512") => (&verify::RSA_PSS_SHA512, 64),
                // Another hash, or MGF1 on another hash.
                _ => {
                    summary.skip(group.tests.len());
                    continue;
                }
            };
            let spki = &group.public_key_der;
            let key = signature::PublicKey::new(algorithm, spki).unwrap();
            assert_eq!(
                signature::PublicKey::from_spki(algorithm, spki)
                    .unwrap()
                    .as_ref(),
                key.as_ref()
            );

            for test in group.tests {
                summary.start();
                let result = key.verify(&test.msg, &test.sig);
                // The module verifies only salts as long as the hash, so a
                // signature with another salt length fails, however valid,
                // as do those whose comment changes it from one.
                let salt_len = match test
                    .comment
                    .as_deref()
                    .and_then(|c| c.strip_prefix("s_len changed to "))
                {
                    Some(len) => len.parse().unwrap(),
                    None => group.salt_len,
                };
                // A group with another salt length marks invalid a signature
                // changed to the hash's, which the module rightly takes.
                let expected = match (salt_len == hash_len, group.salt_len == hash_len) {
                    (true, true) => test.result,
                    (true, false) => ExpectedResult::Valid,
                    (false, _) => ExpectedResult::Invalid,
                };
                match (expected, result) {
                    (ExpectedResult::Valid, Ok(())) => {}
                    (
                        ExpectedResult::Invalid | ExpectedResult::Acceptable,
                        Err(Error::BadSignature),
                    ) => {}
                    _ => panic!("{file} {}: expected {expected:?} got {result:?}", test.id),
                }
            }
        }
    }
}

#[test]
fn ed25519_verify() {
    let file = "ed25519_test.json";
    let mut summary = Summary::new(file);
    for group in read::<TestFile>(file).groups {
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
            summary.start();
            // The module refuses a small-order key, which verifies forgeries.
            if test.has_flag("SmallOrderPublicKey") {
                assert_eq!(test.result, ExpectedResult::Acceptable);
                rejected(key.as_ref().map(|_| ()).map_err(|e| *e), "small-order");
                continue;
            }

            let result = key.as_ref().unwrap().verify(&test.msg, &test.sig);
            match (test.result, result) {
                // "acceptable" cases are mixed-order public keys.
                (ExpectedResult::Valid | ExpectedResult::Acceptable, Ok(())) => {}
                (
                    ExpectedResult::Invalid | ExpectedResult::Acceptable,
                    Err(Error::BadSignature),
                ) => {}
                _ => panic!(
                    "{file} {}: expected {:?} got {result:?}",
                    test.id, test.result
                ),
            }
        }
    }
}

#[derive(Deserialize)]
struct MlDsaFile {
    #[serde(rename(deserialize = "testGroups"))]
    groups: Vec<MlDsaGroup>,
}

#[derive(Deserialize)]
struct MlDsaGroup {
    #[serde(default, rename(deserialize = "privateSeed"), with = "hex::serde")]
    private_seed: Vec<u8>,
    // The seed form, absent from some groups.
    #[serde(default, rename(deserialize = "privateKeyPkcs8"), with = "hex::serde")]
    private_key_pkcs8: Vec<u8>,
    #[serde(default, rename(deserialize = "privateKey"), with = "hex::serde")]
    private_key: Vec<u8>,
    // Hex, or null for a group whose private key is invalid.
    #[serde(rename(deserialize = "publicKey"))]
    public_key: Option<String>,
    #[serde(default, rename(deserialize = "publicKeyDer"), with = "hex::serde")]
    public_key_der: Vec<u8>,
    tests: Vec<MlDsaTest>,
}

#[derive(Deserialize)]
struct MlDsaTest {
    #[serde(rename(deserialize = "tcId"))]
    id: usize,
    #[serde(default, with = "hex::serde")]
    msg: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    ctx: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    sig: Vec<u8>,
    result: ExpectedResult,
    flags: Vec<String>,
}

impl MlDsaTest {
    /// Whether this test signs a message with the empty context, as the
    /// module's API does, rather than a context or only `mu`.
    fn pure(&self) -> bool {
        self.ctx.is_empty() && !self.flags.iter().any(|flag| flag == "Internal")
    }
}

/// A PKCS#8 v1 ML-DSA key of RFC 9881's `id-ml-dsa-*` OID with last arc
/// `arc`, holding `private_key`, an encoded RFC 9881 CHOICE.
fn ml_dsa_pkcs8(arc: u8, private_key: &[u8]) -> Vec<u8> {
    let oid = [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, arc];
    let algorithm = der(0x30, &der(0x06, &oid));
    let version = der(0x02, &[0]);
    der(0x30, &[version, algorithm, der(0x04, private_key)].concat())
}

/// One parameter set's files: its seed and expanded signing keys, and its
/// verification tests.
fn ml_dsa<P: sign::MlDsaParameterSet>(
    [seed, noseed, verify]: [&str; 3],
    algorithm: &'static signature::VerificationAlgorithm,
    arc: u8,
) {
    let mut verified = 0;
    for group in read::<MlDsaFile>(verify).groups {
        let public_key = hex::decode(group.public_key.unwrap()).unwrap();
        let key = signature::PublicKey::new(algorithm, &public_key);
        let from_spki = signature::PublicKey::from_spki(algorithm, &group.public_key_der);
        match (&key, from_spki) {
            (Ok(key), Ok(from_spki)) => {
                assert_eq!(from_spki.as_ref(), key.as_ref());
                assert_eq!(key.to_spki().as_ref(), &group.public_key_der[..]);
            }
            (Err(e), Err(from_spki)) => assert_eq!(*e, from_spki),
            (key, from_spki) => panic!("{key:?} but from SPKI {from_spki:?}"),
        }

        for test in group.tests.iter().filter(|test| test.pure()) {
            let result = match &key {
                Ok(key) => key.verify(&test.msg, &test.sig),
                Err(e) => Err(*e),
            };
            match (test.result, result) {
                (ExpectedResult::Valid, Ok(())) => {}
                (ExpectedResult::Invalid, Err(Error::BadSignature | Error::KeyRejected(_))) => {}
                (expected, result) => {
                    panic!("{verify} {}: expected {expected:?} got {result:?}", test.id)
                }
            }
            verified += 1;
        }
    }
    assert_ne!(verified, 0);

    let mut signed = 0;
    for group in read::<MlDsaFile>(seed).groups {
        let key = sign::MlDsaKeyPair::<P>::from_seed(&group.private_seed);
        let from_pkcs8 = match group.private_key_pkcs8.is_empty() {
            true => None,
            false => Some(sign::MlDsaKeyPair::<P>::from_pkcs8(
                &group.private_key_pkcs8,
            )),
        };
        let Some(public_key) = group.public_key else {
            assert!(key.is_err());
            assert!(from_pkcs8.is_none_or(|key| key.is_err()));
            continue;
        };
        let key = key.unwrap();
        let public_key = hex::decode(public_key).unwrap();
        assert_eq!(key.public_key().as_ref(), public_key);
        assert_eq!(key.to_seed().unwrap().as_ref(), group.private_seed);
        // The module writes the seed form, as aws-lc and Wycheproof do.
        if let Some(from_pkcs8) = from_pkcs8 {
            assert_eq!(from_pkcs8.unwrap().public_key().as_ref(), public_key);
            assert_eq!(key.to_pkcs8().as_ref(), group.private_key_pkcs8);
        }

        let verifier = signature::PublicKey::new(algorithm, &public_key).unwrap();
        for test in group.tests.iter().filter(|test| test.pure()) {
            // Signing is hedged, so check that the signature verifies rather
            // than its bytes.
            let signature = key.sign(&test.msg).unwrap();
            verifier.verify(&test.msg, signature.as_ref()).unwrap();
            assert_eq!(
                verifier.verify(&test.msg, &test.sig).is_ok(),
                test.result == ExpectedResult::Valid,
                "{seed} {}",
                test.id
            );
            signed += 1;
        }
    }
    assert_ne!(signed, 0);

    let mut expanded = 0;
    for group in read::<MlDsaFile>(noseed).groups {
        let der = ml_dsa_pkcs8(arc, &der(0x04, &group.private_key));
        let Ok(key) = sign::MlDsaKeyPair::<P>::from_pkcs8(&der) else {
            // An inconsistent or misshapen key.
            for test in &group.tests {
                assert_eq!(test.result, ExpectedResult::Invalid, "{noseed} {}", test.id);
            }
            continue;
        };
        let public_key = hex::decode(group.public_key.unwrap()).unwrap();
        assert_eq!(key.public_key().as_ref(), public_key);
        // A key loaded in its expanded form has no seed, so it writes that.
        assert!(key.to_seed().is_none());
        assert_eq!(key.to_pkcs8().as_ref(), der);

        // It signs from that form what its public key verifies.
        let verifier = signature::PublicKey::new(algorithm, &public_key).unwrap();
        for test in group.tests.iter().filter(|test| test.pure()) {
            let signature = key.sign(&test.msg).unwrap();
            verifier.verify(&test.msg, signature.as_ref()).unwrap();
            assert_eq!(
                verifier.verify(&test.msg, &test.sig).is_ok(),
                test.result == ExpectedResult::Valid,
                "{noseed} {}",
                test.id
            );
            expanded += 1;
        }
    }
    assert_ne!(expanded, 0);
}

#[test]
fn ml_dsa_44() {
    ml_dsa::<sign::MlDsa44>(
        [
            "mldsa_44_sign_seed_test.json",
            "mldsa_44_sign_noseed_test.json",
            "mldsa_44_verify_test.json",
        ],
        &verify::ML_DSA_44,
        17,
    );
}

#[test]
fn ml_dsa_65() {
    ml_dsa::<sign::MlDsa65>(
        [
            "mldsa_65_sign_seed_test.json",
            "mldsa_65_sign_noseed_test.json",
            "mldsa_65_verify_test.json",
        ],
        &verify::ML_DSA_65,
        18,
    );
}

#[test]
fn ml_dsa_87() {
    ml_dsa::<sign::MlDsa87>(
        [
            "mldsa_87_sign_seed_test.json",
            "mldsa_87_sign_noseed_test.json",
            "mldsa_87_verify_test.json",
        ],
        &verify::ML_DSA_87,
        19,
    );
}

#[derive(Deserialize)]
struct EcdhFile {
    #[serde(rename(deserialize = "testGroups"))]
    groups: Vec<EcdhGroup>,
}

#[derive(Deserialize)]
struct EcdhGroup {
    tests: Vec<EcdhTest>,
}

#[derive(Deserialize, Debug)]
struct EcdhTest {
    #[serde(rename = "tcId")]
    id: usize,
    flags: Vec<String>,
    #[serde(with = "hex::serde")]
    public: Vec<u8>,
    #[serde(with = "hex::serde")]
    private: Vec<u8>,
    #[serde(with = "hex::serde")]
    shared: Vec<u8>,
    result: ExpectedResult,
}

impl EcdhTest {
    fn has_flag(&self, flag: &str) -> bool {
        self.flags.iter().any(|f| f == flag)
    }
}

/// Wycheproof's private key, an integer that may have a sign byte or fewer
/// bytes than the curve's scalar, at the scalar's length.
fn fixed_scalar(private: &[u8], len: usize) -> Vec<u8> {
    let start = private
        .iter()
        .position(|b| *b != 0)
        .unwrap_or(private.len());
    let digits = &private[start..];
    [vec![0; len - digits.len()], digits.to_vec()].concat()
}

/// Wycheproof's X9.62 points, which `agree` takes uncompressed and
/// `PublicKey::new` compressed too.
fn ecdh_points(file: &'static str, algorithm: &'static agreement::Algorithm, len: usize) {
    let mut summary = Summary::new(file);
    for test in read::<EcdhFile>(file)
        .groups
        .into_iter()
        .flat_map(|g| g.tests)
    {
        summary.start();
        let private =
            agreement::PrivateKey::from_scalar(algorithm, &fixed_scalar(&test.private, len))
                .unwrap();
        let direct = private.agree(&test.public).map(|s| s.as_ref().to_vec());
        let parsed = agreement::PublicKey::new(algorithm, &test.public);
        let result = parsed
            .as_ref()
            .map_err(|e| *e)
            .and_then(|peer| private.agree(peer.as_ref()))
            .map(|s| s.as_ref().to_vec());
        let compressed = test.has_flag("CompressedPoint");
        match compressed {
            true => rejected(direct, "compressed"),
            false => assert_eq!(direct, result, "{file} {}", test.id),
        }

        match (test.result, &result) {
            (ExpectedResult::Valid, Ok(shared)) => assert_eq!(shared, &test.shared, "{}", test.id),
            (ExpectedResult::Acceptable, Ok(shared)) if compressed => {
                assert_eq!(shared, &test.shared, "{file} {}", test.id)
            }
            (ExpectedResult::Invalid, Err(_))
                if test.has_flag("InvalidCurveAttack")
                    || test.has_flag("InvalidCompressedPublic") =>
            {
                rejected(result.clone(), "not on the curve")
            }
            (ExpectedResult::Invalid, Err(_)) if test.has_flag("InvalidEncoding") => {
                rejected(result.clone(), "wrong length")
            }
            // A point on the twist, compressed, names no point on the curve;
            // another curve's is the wrong length.
            (ExpectedResult::Invalid, Err(Error::KeyRejected(reason)))
                if test.has_flag("WrongCurve")
                    && ["not on the curve", "wrong length"]
                        .iter()
                        .any(|why| reason.to_string().contains(why)) => {}
            _ => panic!(
                "{file} {}: expected {:?} got {result:?}",
                test.id, test.result
            ),
        }
    }
}

/// Wycheproof's `SubjectPublicKeyInfo` public keys.
fn ecdh_spki(file: &'static str, algorithm: &'static agreement::Algorithm, len: usize) {
    let mut summary = Summary::new(file);
    for test in read::<EcdhFile>(file)
        .groups
        .into_iter()
        .flat_map(|g| g.tests)
    {
        summary.start();
        let private =
            agreement::PrivateKey::from_scalar(algorithm, &fixed_scalar(&test.private, len))
                .unwrap();
        let peer = agreement::PublicKey::from_spki(algorithm, &test.public);
        let result = peer
            .as_ref()
            .map_err(|e| *e)
            .and_then(|peer| private.agree(peer.as_ref()))
            .map(|s| s.as_ref().to_vec());
        match (test.result, &result) {
            (ExpectedResult::Valid | ExpectedResult::Acceptable, Ok(shared)) => {
                assert_eq!(shared, &test.shared, "{file} {}", test.id)
            }
            (ExpectedResult::Invalid | ExpectedResult::Acceptable, Err(_)) => {}
            _ => panic!(
                "{file} {}: expected {:?} got {result:?}",
                test.id, test.result
            ),
        }
        // A key that parsed encodes back to Wycheproof's SPKI, but for a
        // compressed point, which it decompresses.
        if let Ok(peer) = peer
            && !test.has_flag("CompressedPublic")
        {
            assert_eq!(
                peer.to_spki().as_ref(),
                &test.public[..],
                "{file} {}",
                test.id
            );
        }
    }
}

#[test]
fn ecdh_p256() {
    ecdh_points(
        "ecdh_secp256r1_ecpoint_test.json",
        &agreement::ECDH_P256,
        32,
    );
    ecdh_spki("ecdh_secp256r1_test.json", &agreement::ECDH_P256, 32);
}

#[test]
fn ecdh_p384() {
    ecdh_points(
        "ecdh_secp384r1_ecpoint_test.json",
        &agreement::ECDH_P384,
        48,
    );
    ecdh_spki("ecdh_secp384r1_test.json", &agreement::ECDH_P384, 48);
}

#[test]
fn ecdh_p521() {
    ecdh_points(
        "ecdh_secp521r1_ecpoint_test.json",
        &agreement::ECDH_P521,
        66,
    );
    ecdh_spki("ecdh_secp521r1_test.json", &agreement::ECDH_P521, 66);
}

#[derive(Deserialize)]
struct KemFile {
    #[serde(rename(deserialize = "testGroups"))]
    groups: Vec<KemGroup>,
}

#[derive(Deserialize)]
struct KemGroup {
    tests: Vec<KemTest>,
}

#[derive(Deserialize, Debug)]
struct KemTest {
    #[serde(rename = "tcId")]
    id: usize,
    #[serde(default, with = "hex::serde")]
    ek: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    c: Vec<u8>,
    result: ExpectedResult,
}

/// The module takes no seed or encapsulation randomness from its caller, so
/// these check what reaches it through its ABI: each encapsulation key it
/// must parse or refuse, and the ciphertext lengths it must refuse.
#[test]
fn ml_kem_768() {
    let file = "mlkem_768_encaps_test.json";
    let mut summary = Summary::new(file);
    for test in read::<KemFile>(file)
        .groups
        .into_iter()
        .flat_map(|g| g.tests)
    {
        summary.start();
        let key = kem::EncapsulationKey::new(&kem::ML_KEM_768, &test.ek);
        match (test.result, key) {
            (ExpectedResult::Valid, Ok(key)) => {
                assert_eq!(key.as_ref(), &test.ek[..]);
                key.encapsulate().unwrap();
            }
            (ExpectedResult::Invalid, Err(Error::KeyRejected(_))) => {}
            (expected, key) => panic!("{file} {}: expected {expected:?} got {key:?}", test.id),
        }
    }

    let file = "mlkem_768_test.json";
    let mut summary = Summary::new(file);
    let ours = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
    for test in read::<KemFile>(file)
        .groups
        .into_iter()
        .flat_map(|g| g.tests)
    {
        // A key of the vector's own, which only its seed makes.
        if test.c.len() == 1088 {
            summary.skip(1);
            continue;
        }
        summary.start();
        assert_eq!(test.result, ExpectedResult::Invalid, "{file} {}", test.id);
        assert_eq!(
            ours.decapsulate(&test.c).map(|_| ()),
            Err(Error::WrongLength),
            "{file} {}",
            test.id
        );
    }
}
