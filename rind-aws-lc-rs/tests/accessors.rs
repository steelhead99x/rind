//! What rind-aws-lc-rs's keys and errors report beside their operations,
//! checked against aws-lc-rs: the algorithm and TLS version each key was
//! made for, `Debug`, lengths, and the error conversions.

use aws_lc_rs as theirs;
use rind_aws_lc_rs as ours;

macro_rules! debug_eq {
    ($ours:expr, $theirs:expr) => {
        assert_eq!(format!("{:?}", $ours), format!("{:?}", $theirs))
    };
}

struct Counter(u64);

impl ours::aead::NonceSequence for Counter {
    fn advance(&mut self) -> Result<ours::aead::Nonce, ours::error::Unspecified> {
        self.0 += 1;
        let mut nonce = [0; 12];
        nonce[4..].copy_from_slice(&self.0.to_be_bytes());
        Ok(ours::aead::Nonce::assume_unique_for_key(nonce))
    }
}

/// `mut_fill`, which only `dev-tests-only` adds, fills as `fill` does.
#[cfg(feature = "dev-tests-only")]
#[test]
fn mut_fill_fills_like_fill() {
    use ours::rand::SecureRandom;

    let mut rng = ours::rand::SystemRandom::new();
    let mut a = [0u8; 32];
    let mut b = [0u8; 32];
    rng.mut_fill(&mut a).unwrap();
    rng.fill(&mut b).unwrap();
    // Each is all zero with probability 2^-256, and the two are equal with
    // the same.
    assert_ne!(a, [0u8; 32]);
    assert_ne!(b, [0u8; 32]);
    assert_ne!(a, b);
}

#[test]
fn nonces_convert_as_aws_lc_rs_does() {
    let bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
    assert_eq!(
        ours::aead::Nonce::from(&bytes).as_ref(),
        theirs::aead::Nonce::from(&bytes).as_ref()
    );
    let words = [0x0403_0201, 0x0807_0605, 0x0c0b_0a09];
    assert_eq!(
        ours::aead::Nonce::from(&words).as_ref(),
        theirs::aead::Nonce::from(&words).as_ref()
    );
    let ours_iv = ours::iv::FixedLength::<16>::from(&[7; 16]);
    let theirs_iv = theirs::iv::FixedLength::<16>::from(&[7; 16]);
    assert_eq!(ours_iv.as_ref(), theirs_iv.as_ref());
}

#[test]
fn aead_keys_report_what_they_were_made_for() {
    use ours::aead::BoundKey as _;

    let key = [7; 16];
    let unbound = || ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key).unwrap();
    let sealing = ours::aead::SealingKey::new(unbound(), Counter(0));
    let opening = ours::aead::OpeningKey::new(unbound(), Counter(0));
    assert_eq!(sealing.algorithm(), &ours::aead::AES_128_GCM);
    assert_eq!(opening.algorithm(), &ours::aead::AES_128_GCM);

    let randomized = ours::aead::RandomizedNonceKey::new(&ours::aead::AES_128_GCM, &key).unwrap();
    let reference =
        theirs::aead::RandomizedNonceKey::new(&theirs::aead::AES_128_GCM, &key).unwrap();
    debug_eq!(randomized, reference);

    for (version, theirs_version) in [
        (
            ours::aead::TlsProtocolId::TLS12,
            theirs::aead::TlsProtocolId::TLS12,
        ),
        (
            ours::aead::TlsProtocolId::TLS13,
            theirs::aead::TlsProtocolId::TLS13,
        ),
    ] {
        let sealing =
            ours::aead::TlsRecordSealingKey::new(&ours::aead::AES_128_GCM, version, &key).unwrap();
        let reference = theirs::aead::TlsRecordSealingKey::new(
            &theirs::aead::AES_128_GCM,
            theirs_version,
            &key,
        )
        .unwrap();
        assert_eq!(sealing.algorithm(), &ours::aead::AES_128_GCM);
        debug_eq!(sealing.tls_protocol_id(), reference.tls_protocol_id());
        debug_eq!(sealing, reference);

        let opening =
            ours::aead::TlsRecordOpeningKey::new(&ours::aead::AES_128_GCM, version, &key).unwrap();
        let reference = theirs::aead::TlsRecordOpeningKey::new(
            &theirs::aead::AES_128_GCM,
            theirs_version,
            &key,
        )
        .unwrap();
        assert_eq!(opening.algorithm(), &ours::aead::AES_128_GCM);
        debug_eq!(opening.tls_protocol_id(), reference.tls_protocol_id());
        debug_eq!(opening, reference);
    }
}

#[test]
fn quic_algorithms_match_aws_lc_rs() {
    let pairs = [
        (&ours::aead::quic::AES_128, &theirs::aead::quic::AES_128),
        (&ours::aead::quic::AES_256, &theirs::aead::quic::AES_256),
        (&ours::aead::quic::CHACHA20, &theirs::aead::quic::CHACHA20),
    ];
    for (algorithm, reference) in pairs {
        assert_eq!(algorithm.sample_len(), reference.sample_len());
        debug_eq!(algorithm, reference);
        let key = vec![7; algorithm.key_len()];
        let key = ours::aead::quic::HeaderProtectionKey::new(algorithm, &key).unwrap();
        assert_eq!(key.algorithm(), algorithm);
    }
    assert_ne!(ours::aead::quic::AES_128, ours::aead::quic::AES_256);
}

#[test]
fn agreement_keys_keep_their_bytes() {
    let bytes = vec![9; 32];
    let key = ours::agreement::UnparsedPublicKey::new(&ours::agreement::X25519, bytes.clone());
    assert_eq!(key.bytes(), &bytes);
}

#[test]
fn ciphers_report_their_algorithm_and_iv() {
    let key = ours::cipher::UnboundCipherKey::new(&ours::cipher::AES_128, &[7; 16]).unwrap();
    assert_eq!(key.algorithm(), &ours::cipher::AES_128);
    let key = ours::cipher::EncryptingKey::ctr(key).unwrap();
    let mut data = [0; 16];
    let context = key.encrypt(&mut data).unwrap();
    let iv: &[u8] = (&context).try_into().unwrap();
    assert_eq!(iv.len(), 16);
    let none: Result<&[u8], _> = (&ours::cipher::DecryptionContext::None).try_into();
    assert_eq!(
        none.err(),
        Some(ours::error::Unspecified),
        "{:?}",
        theirs::cipher::DecryptionContext::None
    );
}

#[test]
fn constant_time_compares_as_aws_lc_rs() {
    #[allow(deprecated)]
    let compare = ours::constant_time::verify_slices_are_equal;
    #[allow(deprecated)]
    let reference = theirs::constant_time::verify_slices_are_equal;
    for (a, b) in [
        (&b"abc"[..], &b"abc"[..]),
        (b"abc", b"abd"),
        (b"abc", b"ab"),
    ] {
        assert_eq!(compare(a, b).is_ok(), reference(a, b).is_ok());
    }
}

#[test]
#[allow(deprecated)]
fn digest_chaining_lengths_match_aws_lc_rs() {
    let pairs = [
        (
            &ours::digest::SHA1_FOR_LEGACY_USE_ONLY,
            &theirs::digest::SHA1_FOR_LEGACY_USE_ONLY,
        ),
        (&ours::digest::SHA256, &theirs::digest::SHA256),
        (&ours::digest::SHA384, &theirs::digest::SHA384),
        (&ours::digest::SHA512, &theirs::digest::SHA512),
        (&ours::digest::SHA512_256, &theirs::digest::SHA512_256),
    ];
    for (algorithm, reference) in pairs {
        assert_eq!(algorithm.chaining_len(), reference.chaining_len());
    }
}

#[test]
fn errors_convert_as_aws_lc_rs_does() {
    use std::error::Error as _;

    let too_big = u8::try_from(256u32).unwrap_err();
    assert_eq!(
        ours::error::Unspecified::from(too_big),
        ours::error::Unspecified
    );
    #[cfg(any(feature = "ring-io", feature = "ring-sig-verify"))]
    assert_eq!(
        ours::error::Unspecified::from(untrusted::EndOfInput),
        ours::error::Unspecified
    );
    assert_eq!(ours::error::Unspecified::from(()), ours::error::Unspecified);
    let () = ours::error::Unspecified.into();

    let rejected = ours::error::KeyRejected::from(too_big);
    let reference = theirs::error::KeyRejected::from(too_big);
    assert_eq!(rejected.to_string(), reference.to_string());
    #[allow(deprecated)]
    {
        assert!(rejected.cause().is_none());
    }
    let rejected = ours::error::KeyRejected::from(ours::error::Unspecified);
    let reference = theirs::error::KeyRejected::from(theirs::error::Unspecified);
    assert_eq!(rejected.to_string(), reference.to_string());
}

#[test]
fn kem_keys_report_their_algorithm() {
    use ours::kem::{DecapsulationKey, ML_KEM_512, ML_KEM_768, ML_KEM_1024};

    for (algorithm, reference) in [
        (&ML_KEM_512, &theirs::kem::ML_KEM_512),
        (&ML_KEM_768, &theirs::kem::ML_KEM_768),
        (&ML_KEM_1024, &theirs::kem::ML_KEM_1024),
    ] {
        debug_eq!(algorithm, reference);
        let key = DecapsulationKey::generate(algorithm).unwrap();
        let theirs_key = theirs::kem::DecapsulationKey::generate(reference).unwrap();
        assert_eq!(key.algorithm(), algorithm);
        debug_eq!(key, theirs_key);
        let public = key.encapsulation_key().unwrap();
        assert_eq!(public.algorithm(), algorithm);
        debug_eq!(public, theirs_key.encapsulation_key().unwrap());
    }
}

/// aws-lc-rs's own build seeds from CPU jitter, and says so; rind seeds from
/// the OS, and refuses as aws-lc-rs does when jitter entropy is off.
#[test]
fn fips_entropy_is_refused() {
    assert_eq!(
        ours::try_fips_cpu_jitter_entropy(),
        Err("FIPS CPU Jitter Entropy not enabled!")
    );
}

#[cfg(feature = "ring-io")]
#[test]
fn rsa_public_keys_match_aws_lc_rs() {
    use ours::signature::KeyPair as _;
    use theirs::signature::KeyPair as _;

    let pkcs8 = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");
    let key = ours::signature::RsaKeyPair::from_pkcs8(pkcs8).unwrap();
    let reference = theirs::signature::RsaKeyPair::from_pkcs8(pkcs8).unwrap();
    let (public, theirs_public) = (key.public_key(), reference.public_key());
    assert_eq!(public.modulus_len(), theirs_public.modulus_len());
    assert_eq!(
        public.exponent().first_byte(),
        theirs_public.exponent().first_byte()
    );
    assert_eq!(
        public.modulus().first_byte(),
        theirs_public.modulus().first_byte()
    );

    // Components convert to an encrypting key that OAEP-encrypts to the
    // private key.
    let components = ours::rsa::PublicKeyComponents::<Vec<u8>>::from(public);
    let encrypting: ours::rsa::PublicEncryptingKey = components.try_into().unwrap();
    let decrypting = ours::rsa::PrivateDecryptingKey::from_pkcs8(pkcs8).unwrap();
    let oaep = ours::rsa::OaepPublicEncryptingKey::new(encrypting).unwrap();
    let mut ciphertext = vec![0; oaep.ciphertext_size()];
    let ciphertext = oaep
        .encrypt(
            &ours::rsa::OAEP_SHA256_MGF1SHA256,
            b"message",
            &mut ciphertext,
            None,
        )
        .unwrap();
    let oaep = ours::rsa::OaepPrivateDecryptingKey::new(decrypting).unwrap();
    let mut plaintext = vec![0; oaep.min_output_size()];
    let plaintext = oaep
        .decrypt(
            &ours::rsa::OAEP_SHA256_MGF1SHA256,
            ciphertext,
            &mut plaintext,
            None,
        )
        .unwrap();
    assert_eq!(plaintext, b"message");
}

/// An X25519 private key's seed comes out as aws-lc-rs gives it.
#[test]
fn x25519_seed_encodes() {
    use ours::encoding::AsBigEndian as _;

    let seed = [5; 32];
    let key =
        ours::agreement::PrivateKey::from_private_key(&ours::agreement::X25519, &seed).unwrap();
    let encoded: ours::encoding::Curve25519SeedBin<'_> = key.as_be_bytes().unwrap();
    assert_eq!(encoded.as_ref(), seed);
    assert_eq!(format!("{encoded:?}"), "Curve25519SeedBin");
    assert_eq!(format!("{:?}", *encoded), "Buffer(...)");
}
