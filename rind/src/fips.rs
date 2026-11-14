// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! What the FIPS module (`rind-fips`) needs of rind beyond its public API:
//! the known-answer self-tests (CASTs) it runs before each algorithm's first
//! use, its error state, and the codes its C ABI carries errors as.
//!
//! Only the module's build compiles this (`--cfg rind_fips`), so it is no
//! part of rind's API. The DRBG's own self-test is in [`crate::fips_rng`].

use crate::Error;
use crate::error::{KeyFormatError, KeyRejected};
use crate::high::asn1;

/// A known-answer self-test of one algorithm, covering each of its
/// functions (encrypt and decrypt, sign and verify, encapsulate and
/// decapsulate) at its smallest approved size.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelfTest {
    /// SHA-1, which HMAC-SHA-1 and legacy verification run on.
    Sha1,
    /// SHA-256.
    Sha256,
    /// SHA-512, whose compression SHA-384 and SHA-512/256 share.
    Sha512,
    /// SHA3-256, whose permutation the other SHA-3 functions share.
    Sha3,
    /// HMAC, over SHA-256.
    Hmac,
    /// HKDF, over SHA-256.
    Hkdf,
    /// PBKDF2, over HMAC-SHA-256.
    Pbkdf2,
    /// The AES block cipher, forward and inverse, as AES-128-CBC.
    Aes,
    /// AES-128-GCM, sealing and opening.
    AesGcm,
    /// The HMAC_DRBG every random draw comes from.
    Drbg,
    /// ECDSA on P-256 with SHA-256, signing and verifying.
    Ecdsa,
    /// ECDH's shared secret on P-256.
    Ecdh,
    /// Ed25519, signing and verifying.
    Ed25519,
    /// RSA PKCS#1 v1.5 with SHA-256 at 2048 bits, signing and verifying.
    Rsa,
    /// ML-KEM-768: key generation, encapsulation, and decapsulation.
    MlKem,
    /// ML-DSA-44: key generation, signing, and verifying.
    MlDsa,
}

impl SelfTest {
    /// Every self-test, in the order an on-demand run takes them: the
    /// hashes first, since the others hash.
    pub const ALL: [Self; 16] = [
        Self::Sha1,
        Self::Sha256,
        Self::Sha512,
        Self::Sha3,
        Self::Hmac,
        Self::Hkdf,
        Self::Pbkdf2,
        Self::Aes,
        Self::AesGcm,
        Self::Drbg,
        Self::Ecdsa,
        Self::Ecdh,
        Self::Ed25519,
        Self::Rsa,
        Self::MlKem,
        Self::MlDsa,
    ];

    /// Runs this self-test, returning the name of the first function whose
    /// answer was wrong.
    pub fn run(self) -> Result<(), &'static str> {
        match self {
            Self::Sha1 => kat::sha1(),
            Self::Sha256 => kat::sha256(),
            Self::Sha512 => kat::sha512(),
            Self::Sha3 => kat::sha3(),
            Self::Hmac => kat::hmac(),
            Self::Hkdf => kat::hkdf(),
            Self::Pbkdf2 => kat::pbkdf2(),
            Self::Aes => kat::aes(),
            Self::AesGcm => kat::aes_gcm(),
            Self::Drbg => crate::fips_rng::cast().then_some(()).ok_or("drbg"),
            Self::Ecdsa => kat::ecdsa(),
            Self::Ecdh => kat::ecdh(),
            Self::Ed25519 => kat::ed25519(),
            Self::Rsa => kat::rsa(),
            Self::MlKem => kat::ml_kem(),
            Self::MlDsa => kat::ml_dsa(),
        }
    }
}

/// Enters the module's error state: names the self-test that failed and
/// aborts, so no service runs again, as aws-lc's module does.
#[cold]
pub fn fail(test: &str) -> ! {
    std::eprintln!("rind-fips: {test} self-test failed");
    std::process::abort();
}

/// Whether to corrupt self-test `test`'s input, so the lab sees it fail:
/// only in a `--cfg rind_fips_break` build, when `RIND_FIPS_BREAK` names it.
pub fn broken(test: &str) -> bool {
    #[cfg(rind_fips_break)]
    return std::env::var("RIND_FIPS_BREAK").is_ok_and(|name| name == test);
    #[cfg(not(rind_fips_break))]
    {
        let _ = test;
        false
    }
}

/// Lists every [`Error`], each with its code: its place in the list, from 1.
macro_rules! errors {
    (
        plain: [$($plain:ident),* $(,)?],
        key: [$($key:ident),* $(,)?],
        asn1: [$($asn1:ident),* $(,)?] $(,)?
    ) => {
        const ERRORS: &[Error] = &[
            $(Error::$plain,)*
            $(Error::KeyRejected(KeyRejected(KeyFormatError::$key)),)*
            $(Error::KeyRejected(KeyRejected(KeyFormatError::Asn1(asn1::Error::$asn1))),)*
        ];

        // Fails to compile when a variant is added but not listed.
        #[allow(dead_code)]
        fn exhaustive(error: Error) {
            match error {
                $(Error::$plain)|* => {}
                Error::KeyRejected(KeyRejected(reason)) => match reason {
                    $(KeyFormatError::$key)|* => {}
                    KeyFormatError::Asn1(error) => match error {
                        $(asn1::Error::$asn1)|* => {}
                    },
                },
            }
        }
    };
}

errors! {
    plain: [
        WrongLength,
        BadSignature,
        DecryptFailed,
        RngFailed,
        NotEqual,
        Fault,
        MessageLimitReached,
        Unsupported,
    ],
    key: [
        WrongLength,
        LeadingZero,
        Compressed,
        PointEncoding,
        NotOnCurve,
        SmallOrder,
        ScalarOutOfRange,
        RsaModulus,
        RsaExponent,
        RsaPrimes,
        MultiPrimeRsa,
        MlKemModulus,
        MlDsaSecretKey,
        MismatchedMlDsaSeed,
        UnsupportedPkcs8Version,
        MismatchedPkcs8Algorithm,
        MismatchedPkcs8Parameters,
        MismatchedPkcs8PublicKey,
        MismatchedPublicKey,
        MismatchedRsaComponents,
        MismatchedSec1Curve,
        MismatchedSec1PublicKey,
        MismatchedSpkiAlgorithm,
    ],
    asn1: [
        UnexpectedTag,
        UnexpectedEof,
        UnexpectedTrailingData,
        NonCanonicalEncoding,
        UnhandledEnumValue,
        IntegerOutOfRange,
        IllegalNull,
        UnsupportedLargeObjectId,
        UnsupportedLargeObjectLength,
        UnhandledBitString,
    ],
}

/// Wipes every thread's DRBG, returning how many, and fails every draw
/// after: the module's destructor, as the process exits.
pub fn zeroise_drbgs() -> usize {
    crate::fips_rng::zeroise_all()
}

/// Waits for every draw in progress, then holds every thread's DRBG still
/// until the hold drops. The module holds one across `fork`, so the child
/// inherits no draw in progress and no lock that only a thread it lacks
/// would release.
pub fn hold_drbgs() -> DrbgHold {
    DrbgHold(crate::fips_rng::hold())
}

/// What [`hold_drbgs`] returns.
pub struct DrbgHold(crate::fips_rng::Hold);

impl DrbgHold {
    /// Releases the hold in a forked child, after wiping and forgetting the
    /// DRBG of every thread but this one: the child copied them but runs
    /// none of their threads, so none would unregister or wipe its own.
    pub fn release_in_child(self) {
        crate::fips_rng::forked(self.0);
    }
}

/// The name of the first CPU feature the module requires that this CPU
/// lacks, as [`crate::cpu::check`] reports it.
pub fn missing_cpu_feature() -> Option<&'static str> {
    crate::cpu::check().err().map(|missing| missing.name())
}

/// `error`'s code, which is never 0, the code of success.
pub fn error_code(error: Error) -> u32 {
    let index = ERRORS.iter().position(|e| *e == error);
    // `exhaustive` keeps every error listed.
    index.map_or(u32::MAX, |i| i as u32 + 1)
}

/// The error whose code is `code`.
pub fn error_from_code(code: u32) -> Option<Error> {
    ERRORS.get((code as usize).checked_sub(1)?).copied()
}

/// A digest of `algorithm` holding `value`, as the caller computed it, for
/// signing or verifying a digest; `None` unless `value` is its length.
pub fn digest(
    algorithm: &'static crate::digest::Algorithm,
    value: &[u8],
) -> Option<crate::digest::Digest> {
    (value.len() == algorithm.output_len()).then(|| crate::digest::Digest::new(algorithm, value))
}

/// Refuses an RSA key whose modulus FIPS 186-5 does not approve, as
/// aws-lc's service indicator does: an even length of 2048 bits or more,
/// or exactly 1024 bits if `legacy_1024`, for verifying old signatures. A
/// key that is not RSA passes.
pub fn check_rsa_modulus(
    key: &crate::signature::PublicKey,
    legacy_1024: bool,
) -> Result<(), Error> {
    match key.rsa_modulus_bits() {
        Some(bits) if !((bits >= 2048 && bits % 2 == 0) || (legacy_1024 && bits == 1024)) => {
            Err(KeyFormatError::RsaModulus.into())
        }
        _ => Ok(()),
    }
}

/// The known answers, from the standards' own examples where they give one.
mod kat {
    use super::broken;
    use crate::high::hash::{Hash, Sha256};

    /// The SHA-256 of a self-test's output, which the test compares with
    /// the expected answer's.
    fn sha256_of(data: &[u8]) -> [u8; 32] {
        known(Sha256::hash(data).as_ref()).try_into().unwrap()
    }

    /// `value`, marked public for ctgrind: a self-test computes from fixed
    /// inputs, so comparing its output reveals nothing, though rind marks
    /// the keys and secrets it derives as secret.
    fn known(value: &[u8]) -> &[u8] {
        crate::low::ct::public_slice(value);
        value
    }

    /// `input` with its first bit flipped if `test` is broken.
    fn input<const N: usize>(test: &str, input: [u8; N]) -> [u8; N] {
        let mut input = input;
        if broken(test) {
            input[0] ^= 1;
        }
        input
    }

    fn check(test: &'static str, passed: bool) -> Result<(), &'static str> {
        passed.then_some(()).ok_or(test)
    }

    // FIPS 180's example, "abc", for each hash.
    fn digest(
        test: &'static str,
        algorithm: &'static crate::high::digest::Algorithm,
        expected: &[u8],
    ) -> Result<(), &'static str> {
        let digest = crate::high::digest::digest(algorithm, &input(test, *b"abc"));
        check(test, digest.as_ref() == expected)
    }

    pub(super) fn sha1() -> Result<(), &'static str> {
        digest(
            "sha1",
            &crate::high::digest::SHA1,
            &hex("a9993e364706816aba3e25717850c26c9cd0d89d"),
        )
    }

    pub(super) fn sha256() -> Result<(), &'static str> {
        digest(
            "sha256",
            &crate::high::digest::SHA256,
            &hex("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
        )
    }

    pub(super) fn sha512() -> Result<(), &'static str> {
        digest(
            "sha512",
            &crate::high::digest::SHA512,
            &hex(concat!(
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a",
                "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
            )),
        )
    }

    pub(super) fn sha3() -> Result<(), &'static str> {
        digest(
            "sha3",
            &crate::high::digest::SHA3_256,
            &hex("3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"),
        )
    }

    // RFC 4231's test case 2.
    pub(super) fn hmac() -> Result<(), &'static str> {
        use crate::high::hmac::{HMAC_SHA256, Key, sign};
        let key = Key::new(&HMAC_SHA256, &input("hmac", *b"Jefe"));
        let tag = sign(&key, b"what do ya want for nothing?");
        check(
            "hmac",
            tag.as_ref() == hex("5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
        )
    }

    // RFC 5869's test case 1.
    pub(super) fn hkdf() -> Result<(), &'static str> {
        use crate::high::hkdf::{HKDF_SHA256, Salt};
        let salt = Salt::new(&HKDF_SHA256, &hex("000102030405060708090a0b0c"));
        let mut okm = [0u8; 42];
        let info = hex("f0f1f2f3f4f5f6f7f8f9");
        let filled = salt
            .extract(&input("hkdf", [0x0b; 22]))
            .and_then(|prk| prk.expand(&[&info], okm.len())?.fill(&mut okm));
        check(
            "hkdf",
            filled.is_ok()
                && okm[..]
                    == hex(concat!(
                        "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf",
                        "34007208d5b887185865"
                    )),
        )
    }

    // aws-lc's PBKDF2-HMAC-SHA256 vector: two iterations, as IG 10.3.A
    // asks, so the chained HMACs run, with a password and salt the
    // service's floors admit.
    pub(super) fn pbkdf2() -> Result<(), &'static str> {
        use crate::high::pbkdf2::{PBKDF2_HMAC_SHA256, Secret};
        let secret = Secret::new(
            &PBKDF2_HMAC_SHA256,
            &input("pbkdf2", *b"AWS-LCFIPSpassword"),
        );
        let mut out = [0u8; 25];
        let iterations = core::num::NonZeroU32::MIN.saturating_add(1);
        let derived = secret.derive(
            iterations,
            b"saltSALTsaltSALTsaltSALTsaltSALTsalt",
            &mut out,
        );
        check(
            "pbkdf2",
            derived.is_ok() && out[..] == hex("c6ac0779e4a117c922287f5e10e7ee6ba74d8b19519b4cc738"),
        )
    }

    // SP 800-38A's F.2.1 and F.2.2: CBC-AES128, its first two blocks.
    pub(super) fn aes() -> Result<(), &'static str> {
        use crate::cipher::{AES_128, AesCbcDecryptingKey, AesCbcEncryptingKey, CbcIv};
        let key = hex("2b7e151628aed2a6abf7158809cf4f3c");
        let iv: [u8; 16] = hex("000102030405060708090a0b0c0d0e0f").try_into().unwrap();
        let plaintext: [u8; 32] = hex(concat!(
            "6bc1bee22e409f96e93d7e117393172a",
            "ae2d8a571e03ac9c9eb76fac45af8e51"
        ))
        .try_into()
        .unwrap();
        let ciphertext: [u8; 32] = hex(concat!(
            "7649abac8119b246cee98e9b12e9197d",
            "5086cb9b507219ee95db113a917678b2"
        ))
        .try_into()
        .unwrap();

        let mut buf = input("aes_encrypt", plaintext);
        let encrypted = AesCbcEncryptingKey::new(&AES_128, &key)
            .and_then(|k| k.encrypt_blocks(CbcIv::assume_unpredictable(iv), &mut buf));
        check("aes_encrypt", encrypted.is_ok() && buf == ciphertext)?;

        let mut buf = input("aes_decrypt", ciphertext);
        let decrypted =
            AesCbcDecryptingKey::new(&AES_128, &key).and_then(|k| k.decrypt_blocks(&iv, &mut buf));
        check("aes_decrypt", decrypted.is_ok() && buf == plaintext)
    }

    // McGrew and Viega's GCM test case 4: AES-128, with associated data.
    pub(super) fn aes_gcm() -> Result<(), &'static str> {
        use crate::aead::{AES_128_GCM, Key, Nonce};
        let key = Key::new(&AES_128_GCM, &hex("feffe9928665731c6d6a8f9467308308"));
        let Ok(key) = key else {
            return Err("aes_gcm_seal");
        };
        let nonce = || Nonce::assume_unique_for_key(hex_array("cafebabefacedbaddecaf888"));
        let aad = hex("feedfacedeadbeeffeedfacedeadbeefabaddad2");
        let plaintext = hex(concat!(
            "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72",
            "1c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39"
        ));
        let sealed = hex(concat!(
            "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e",
            "21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091",
            "5bc94fbc3221a5db94fae95ae7121a47"
        ));

        let mut buf = plaintext.clone();
        if broken("aes_gcm_seal") {
            buf[0] ^= 1;
        }
        let tag = key.seal_in_place_separate_tag(nonce(), &aad, &mut buf);
        let tag_matches = tag.is_ok_and(|tag| sealed[plaintext.len()..] == *tag.as_ref());
        check(
            "aes_gcm_seal",
            tag_matches && buf[..] == sealed[..plaintext.len()],
        )?;

        let mut buf = sealed;
        if broken("aes_gcm_open") {
            buf[0] ^= 1;
        }
        let opened = key.open_in_place(nonce(), &aad, &mut buf);
        check("aes_gcm_open", opened.is_ok_and(|p| *p == plaintext[..]))
    }

    // P-256 with SHA-256, signing with a fixed nonce source.
    pub(super) fn ecdsa() -> Result<(), &'static str> {
        use crate::high::curve::P256;
        use crate::high::ecdsa::{SigningKey, VerifyingKey};

        let Ok(key) =
            SigningKey::<P256>::from_pkcs8_der(include_bytes!("high/ecdsa/secp256r1.pkcs8.der"))
        else {
            return Err("ecdsa_sign");
        };
        let mut signature = [0u8; 64];
        let message = input("ecdsa_sign", *b"rind-fips ECDSA self-test");
        let signed = key.sign_with_random::<Sha256>(&message, &[0; 16], &mut signature);
        check(
            "ecdsa_sign",
            signed.is_ok() && sha256_of(&signature)[..] == hex(ECDSA_SIGNATURE_SHA256),
        )?;

        let message = input("ecdsa_verify", *b"rind-fips ECDSA self-test");
        let verified =
            VerifyingKey::<P256>::from_x962_uncompressed(key.public_key_uncompressed().as_ref())
                .and_then(|k| k.verify::<Sha256>(&message, &signature));
        check("ecdsa_verify", verified.is_ok())
    }

    // The first P-256 vector of CAVS's ECC CDH primitive tests.
    pub(super) fn ecdh() -> Result<(), &'static str> {
        use crate::high::agreement::{ECDH_P256, PrivateKey};
        let peer = hex(concat!(
            "04",
            "700c48f77f56584c5cc632ca65640db91b6bacce3a4df6b42ce7cc838833d287",
            "db71e509e3fd9b060ddb20ba5c51dcc5948d46fbf640dfe0441782cab85fa4ac"
        ));
        let scalar: [u8; 32] =
            hex_array("7d7dc5f71eb29ddaf80d6214632eeae03d9058af1fb6d22ed80badb62bc1a534");
        let secret = PrivateKey::from_scalar(&ECDH_P256, &input("ecdh", scalar))
            .and_then(|k| k.agree(&peer));
        check(
            "ecdh",
            secret.is_ok_and(|s| {
                known(s.as_ref())
                    == hex("46fc62106420ff012e54a434fbdd2d25ccc5852060561e68040dd7778997bd7b")
            }),
        )
    }

    // RFC 8032's test 1.
    pub(super) fn ed25519() -> Result<(), &'static str> {
        use crate::high::signature::{Ed25519KeyPair, PublicKey, verify::ED25519};
        let seed: [u8; 32] =
            hex_array("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
        let Ok(key) = Ed25519KeyPair::from_seed(&input("ed25519_sign", seed)) else {
            return Err("ed25519_sign");
        };
        let signature: [u8; 64] = hex_array(concat!(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155",
            "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
        ));
        check("ed25519_sign", key.sign(b"").as_ref() == signature)?;

        let public_key = hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
        let signature = input("ed25519_verify", signature);
        let verified =
            PublicKey::new(&ED25519, &public_key).and_then(|k| k.verify(b"", &signature));
        check("ed25519_verify", verified.is_ok())
    }

    // PKCS#1 v1.5 with SHA-256 under a 2048-bit key.
    pub(super) fn rsa() -> Result<(), &'static str> {
        use crate::high::signature::{PublicKey, RsaKeyPair, sign, verify};
        let Ok(key) = RsaKeyPair::from_pkcs8(include_bytes!("high/rsa/rsa2048.pkcs8.der")) else {
            return Err("rsa_sign");
        };
        let message = input("rsa_sign", *b"rind-fips RSA self-test");
        let signature = key.sign(&sign::RSA_PKCS1_SHA256, &message);
        let Ok(signature) = signature else {
            return Err("rsa_sign");
        };
        check(
            "rsa_sign",
            sha256_of(signature.as_ref())[..] == hex(RSA_SIGNATURE_SHA256),
        )?;

        let message = input("rsa_verify", *b"rind-fips RSA self-test");
        let public_key = key.public_key(&sign::RSA_PKCS1_SHA256);
        let verified = PublicKey::new(&verify::RSA_PKCS1_SHA256, public_key.as_ref())
            .and_then(|k| k.verify(&message, signature.as_ref()));
        check("rsa_verify", verified.is_ok())
    }

    // Key generation from the seed of ACVP's first ML-KEM-768 keyGen vector,
    // then encapsulation of a fixed message, and decapsulation of its
    // ciphertext and of that ciphertext corrupted, which implicit rejection
    // answers.
    pub(super) fn ml_kem() -> Result<(), &'static str> {
        use crate::mid::mlkem768::{Ciphertext, DecapKey, Message};

        let mut seed = [0u8; 64];
        seed[..32].copy_from_slice(&hex(ML_KEM_D));
        seed[32..].copy_from_slice(&hex(ML_KEM_Z));
        let key = DecapKey::keygen_internal(&input("ml_kem_keygen", seed));
        let ek = key.encapsulation_key();
        check(
            "ml_kem_keygen",
            sha256_of(&ek.as_bytes())[..] == hex(ML_KEM_EK_SHA256)
                && sha256_of(&key.as_bytes())[..] == hex(ML_KEM_DK_SHA256),
        )?;

        let (secret, ciphertext) = ek.encaps_internal(Message(input("ml_kem_encaps", [0x5a; 32])));
        check(
            "ml_kem_encaps",
            sha256_of(ciphertext.as_ref())[..] == hex(ML_KEM_CIPHERTEXT_SHA256)
                && sha256_of(secret.as_ref())[..] == hex(ML_KEM_SECRET_SHA256),
        )?;

        let ciphertext = input("ml_kem_decaps", *ciphertext.as_ref());
        let decapsulated = key.decaps(&Ciphertext::from(ciphertext));
        let mut corrupted = ciphertext;
        corrupted[1] ^= 1;
        let rejected = key.decaps(&Ciphertext::from(corrupted));
        check(
            "ml_kem_decaps",
            sha256_of(decapsulated.as_ref())[..] == hex(ML_KEM_SECRET_SHA256)
                && sha256_of(rejected.as_ref())[..] == hex(ML_KEM_REJECTED_SHA256),
        )
    }

    // Key generation from the seed of ACVP's first ML-DSA-44 keyGen vector,
    // then signing with a fixed `rnd`, and verifying.
    pub(super) fn ml_dsa() -> Result<(), &'static str> {
        use crate::mid::mldsa::{KeyPair, MlDsa44, verify};

        let seed: [u8; 32] = hex_array(ML_DSA_SEED);
        let key = KeyPair::<MlDsa44>::from_seed(&input("ml_dsa_keygen", seed));
        check(
            "ml_dsa_keygen",
            sha256_of(key.public_key().as_ref())[..] == hex(ML_DSA_PK_SHA256)
                && sha256_of(key.secret_key().as_ref())[..] == hex(ML_DSA_SK_SHA256),
        )?;

        let message = *b"rind-fips ML-DSA self-test";
        let signature = key
            .mu(b"", &input("ml_dsa_sign", message))
            .and_then(|mu| key.sign_internal(&mu, &[0; 32]));
        let Ok(signature) = signature else {
            return Err("ml_dsa_sign");
        };
        check(
            "ml_dsa_sign",
            sha256_of(signature.as_ref())[..] == hex(ML_DSA_SIGNATURE_SHA256),
        )?;

        let verified = verify::<MlDsa44>(
            key.public_key().as_ref(),
            key.tr(),
            b"",
            &input("ml_dsa_verify", message),
            signature.as_ref(),
        );
        check("ml_dsa_verify", verified.is_ok())
    }

    pub(super) const ECDSA_SIGNATURE_SHA256: &str =
        "93154e00ad14c4e7a48faf4cd36a11b2294bcc99a72bf9e166bab3db145a6c08";
    pub(super) const RSA_SIGNATURE_SHA256: &str =
        "2d4231a659a72edf02a0545bb7e6f9b43cc1fca1d4bc46e3881e56e72230fb7a";
    pub(super) const ML_KEM_D: &str =
        "e582b7d75e6c80b05ae392a1fc9f7153b12390fd99930368cc67a768baebc8a0";
    pub(super) const ML_KEM_Z: &str =
        "1cdacb8740c0b87c4a379575f187b367cbfa3b300bf591b109f79816e9cbe8f0";
    pub(super) const ML_KEM_EK_SHA256: &str =
        "4158f6afb5e516c99f1da07da8c651348422b17c1f4e9a08ad73fb1f91249b3e";
    pub(super) const ML_KEM_DK_SHA256: &str =
        "7aab35839207f72b310abe36e2daa1cc7ff6f7fa8941e439967cd47d9b437079";
    pub(super) const ML_KEM_CIPHERTEXT_SHA256: &str =
        "f0241042115f1f11a1ac98805db1d0ecd0ebe7826de65e5979516f9f46b70108";
    pub(super) const ML_KEM_SECRET_SHA256: &str =
        "4e689716554875744605303f68c4aa404953a510020ea00b16e2380995d4c99e";
    pub(super) const ML_KEM_REJECTED_SHA256: &str =
        "1f3f16b46cfa1d09d9c2ed5566e7dca46ad152a9f30fe23bcd14216711d2bed9";
    pub(super) const ML_DSA_SEED: &str =
        "7194b13c95231010afd2c909992bd2003ba6f437c3886bdbe3f6b867a14ba161";
    pub(super) const ML_DSA_PK_SHA256: &str =
        "838b88b6ac41e2c60698173e08ca173d0b0d2839205806e56a8a3d53195f3a03";
    pub(super) const ML_DSA_SK_SHA256: &str =
        "1c911d163cd0a5563e06f22403f7e16334fee17c2abb66f11ddf39ca6307ec58";
    pub(super) const ML_DSA_SIGNATURE_SHA256: &str =
        "b49c6c322ccbae40f7c758ed53d55e530ff4b303a7da4000706ebb68b5cc3afd";

    /// Decodes hex this module writes, so a typo fails its test.
    fn hex(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    fn hex_array<const N: usize>(s: &str) -> [u8; N] {
        hex(s).try_into().unwrap()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn self_tests_pass() {
        for test in SelfTest::ALL {
            assert_eq!(test.run(), Ok(()), "{test:?}");
        }
    }

    fn sha256_hex(data: &[u8]) -> String {
        use crate::high::hash::{Hash, Sha256};
        hex::encode(Sha256::hash(data).as_ref())
    }

    // The keys the ML-KEM and ML-DSA self-tests generate are those ACVP's
    // first vectors give for their seeds.
    #[test]
    fn ml_kem_and_ml_dsa_keys_match_acvp() {
        use crate::test::{Acvp, acvp};

        let group = acvp("ML-KEM-keyGen-FIPS203")
            .into_iter()
            .find(|g| g.str("parameterSet") == "ML-KEM-768")
            .unwrap();
        let test = &group.tests()[0];
        assert_eq!(test.hex("d"), hex::decode(kat::ML_KEM_D).unwrap());
        assert_eq!(test.hex("z"), hex::decode(kat::ML_KEM_Z).unwrap());
        assert_eq!(sha256_hex(&test.hex("ek")), kat::ML_KEM_EK_SHA256);
        assert_eq!(sha256_hex(&test.hex("dk")), kat::ML_KEM_DK_SHA256);

        let group = acvp("ML-DSA-keyGen-FIPS204")
            .into_iter()
            .find(|g| g.str("parameterSet") == "ML-DSA-44")
            .unwrap();
        let test = &group.tests()[0];
        assert_eq!(test.hex("seed"), hex::decode(kat::ML_DSA_SEED).unwrap());
        assert_eq!(sha256_hex(&test.hex("pk")), kat::ML_DSA_PK_SHA256);
        assert_eq!(sha256_hex(&test.hex("sk")), kat::ML_DSA_SK_SHA256);
    }

    // aws-lc signs PKCS#1 v1.5 deterministically, so it must give the RSA
    // self-test's answer, and verify the ECDSA self-test's.
    #[cfg(not(any(miri, target_family = "wasm")))]
    #[test]
    fn rsa_and_ecdsa_answers_match_aws_lc() {
        use aws_lc_rs::signature::{self, KeyPair};

        let key = signature::RsaKeyPair::from_pkcs8(include_bytes!("high/rsa/rsa2048.pkcs8.der"))
            .unwrap();
        let mut sig = vec![0; key.public_modulus_len()];
        key.sign(
            &signature::RSA_PKCS1_SHA256,
            &aws_lc_rs::rand::SystemRandom::new(),
            b"rind-fips RSA self-test",
            &mut sig,
        )
        .unwrap();
        assert_eq!(sha256_hex(&sig), kat::RSA_SIGNATURE_SHA256);

        let key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            include_bytes!("high/ecdsa/secp256r1.pkcs8.der"),
        )
        .unwrap();
        let mut sig = [0u8; 64];
        let rind_key = crate::high::ecdsa::SigningKey::<crate::high::curve::P256>::from_pkcs8_der(
            include_bytes!("high/ecdsa/secp256r1.pkcs8.der"),
        )
        .unwrap();
        rind_key
            .sign_with_random::<crate::high::hash::Sha256>(
                b"rind-fips ECDSA self-test",
                &[0; 16],
                &mut sig,
            )
            .unwrap();
        assert_eq!(sha256_hex(&sig), kat::ECDSA_SIGNATURE_SHA256);
        signature::UnparsedPublicKey::new(
            &signature::ECDSA_P256_SHA256_FIXED,
            key.public_key().as_ref(),
        )
        .verify(b"rind-fips ECDSA self-test", &sig)
        .unwrap();
    }

    #[test]
    fn error_codes_round_trip() {
        for (i, &error) in ERRORS.iter().enumerate() {
            let code = error_code(error);
            assert_eq!(code, i as u32 + 1);
            assert_eq!(error_from_code(code), Some(error));
        }
        assert_eq!(error_from_code(0), None);
        assert_eq!(error_from_code(ERRORS.len() as u32 + 1), None);
    }
}
