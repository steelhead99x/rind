//! Constant-time checks for the secret paths rind-aws-lc-rs adds over rind,
//! run under valgrind by `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. rind itself marks the private keys it
//! generates or parses.

use std::num::NonZeroU32;

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use rind_aws_lc_rs::aead::{self, quic};
use rind_aws_lc_rs::{cipher, hkdf, hmac, iv, key_wrap, pbkdf2};

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

struct Len(usize);

impl hkdf::KeyType for Len {
    fn len(&self) -> usize {
        self.0
    }
}

/// HKDF, built here on rind's HMAC, and the keys it fills.
#[test]
fn hkdf() {
    for algorithm in [
        hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
        hkdf::HKDF_SHA256,
        hkdf::HKDF_SHA384,
        hkdf::HKDF_SHA512,
    ] {
        let ikm = [0x0b; 22];
        let info: [&[u8]; 2] = [b"label", b"context"];
        let derive = |ikm: &[u8], out: &mut [u8]| {
            let prk = hkdf::Salt::new(algorithm, b"salt").extract(ikm);
            prk.expand(&info, Len(out.len()))
                .unwrap()
                .fill(out)
                .unwrap();
            hkdf::Prk::from(prk.expand(&info, algorithm).unwrap())
        };
        // Three blocks of the longest hash, and a partial one.
        let mut expected = [0u8; 200];
        derive(&ikm, &mut expected);

        secret(&ikm);
        let mut okm = [0u8; 200];
        let prk = derive(&ikm, &mut okm);
        public(&okm);
        assert_eq!(okm, expected, "{algorithm:?}");

        // Each key a secret `Okm` fills, used once, and its output declassified.
        let key = hmac::Key::from(prk.expand(&info, algorithm.hmac_algorithm()).unwrap());
        let tag = hmac::sign(&key, b"message");
        public(tag.as_ref());

        let key = aead::LessSafeKey::new(aead::UnboundKey::from(
            prk.expand(&info, &aead::AES_256_GCM).unwrap(),
        ));
        let nonce = aead::Nonce::assume_unique_for_key([0; 12]);
        let mut sealed = b"message".to_vec();
        key.seal_in_place_append_tag(nonce, aead::Aad::empty(), &mut sealed)
            .unwrap();
        public(&sealed[..]);

        let key = quic::HeaderProtectionKey::from(prk.expand(&info, &quic::AES_128).unwrap());
        let mask = key.new_mask(&[0; 16]).unwrap();
        public(&mask);

        let key = cipher::UnboundCipherKey::from(prk.expand(&info, &cipher::AES_128).unwrap());
        let key = cipher::EncryptingKey::ctr(key).unwrap();
        let mut in_out = *b"message";
        let context = cipher::EncryptionContext::Iv128(iv::FixedLength::from([0; 16]));
        key.less_safe_encrypt(&mut in_out, context).unwrap();
        public(&in_out);
    }
}

/// `open_within` moves the plaintext to the front of the buffer.
#[test]
fn open_within() {
    let key_bytes = [0x42; 16];
    let key = |key_bytes: &[u8]| {
        aead::LessSafeKey::new(aead::UnboundKey::new(&aead::AES_128_GCM, key_bytes).unwrap())
    };
    let nonce = || aead::Nonce::assume_unique_for_key([1; 12]);
    let mut sealed = b"prefix--message".to_vec();
    key(&key_bytes)
        .seal_in_place_append_tag(nonce(), aead::Aad::empty(), &mut sealed)
        .unwrap();

    secret(&key_bytes);
    let key = key(&key_bytes);
    let mut in_out = [&b"header"[..], &sealed].concat();
    let plaintext = key
        .open_within(nonce(), aead::Aad::empty(), &mut in_out, 6..)
        .unwrap();
    public(plaintext);
    assert_eq!(plaintext, b"prefix--message");
}

/// A stored PBKDF2 value shorter than the hash, which rind-aws-lc-rs
/// compares itself.
#[test]
fn pbkdf2_short() {
    let iterations = NonZeroU32::new(2).unwrap();
    let password = *b"password";
    let mut stored = [0u8; 16];
    pbkdf2::derive(
        pbkdf2::PBKDF2_HMAC_SHA256,
        iterations,
        b"salt",
        &password,
        &mut stored,
    );

    secret(&password);
    secret(&stored);
    let result = pbkdf2::verify(
        pbkdf2::PBKDF2_HMAC_SHA256,
        iterations,
        b"salt",
        &password,
        &stored,
    );
    public(&result);
    assert_eq!(result, Ok(()));
}

/// AES-CTR and AES-CBC, with and without padding, whose keys
/// rind-aws-lc-rs holds and whose blocks it drives.
#[test]
fn cipher() {
    for (algorithm, key_bytes) in [
        (&cipher::AES_128, &[0x24u8; 32][..16]),
        (&cipher::AES_192, &[0x24u8; 32][..24]),
        (&cipher::AES_256, &[0x24u8; 32][..]),
    ] {
        let context = || cipher::EncryptionContext::Iv128(iv::FixedLength::from([9; 16]));
        let key = || cipher::UnboundCipherKey::new(algorithm, key_bytes).unwrap();
        let mut expected = [0x42u8; 48];
        cipher::EncryptingKey::cbc(key())
            .unwrap()
            .less_safe_encrypt(&mut expected, context())
            .unwrap();

        secret(key_bytes);
        let mut message = [0x42u8; 48];
        secret(&message);
        let decryption = cipher::EncryptingKey::cbc(key())
            .unwrap()
            .less_safe_encrypt(&mut message, context())
            .unwrap();
        public(&message);
        assert_eq!(message, expected);
        let plaintext = cipher::DecryptingKey::cbc(key())
            .unwrap()
            .decrypt(&mut message, decryption)
            .unwrap();
        public(plaintext);
        assert_eq!(plaintext, [0x42; 48]);

        let mut message = b"a message not a multiple of the block".to_vec();
        secret(&message[..]);
        let decryption = cipher::PaddedBlockEncryptingKey::cbc_pkcs7(key())
            .unwrap()
            .less_safe_encrypt(&mut message, context())
            .unwrap();
        public(&message[..]);
        let plaintext = cipher::PaddedBlockDecryptingKey::cbc_pkcs7(key())
            .unwrap()
            .decrypt(&mut message, decryption)
            .unwrap();
        public(plaintext);
        assert_eq!(plaintext, b"a message not a multiple of the block");

        let mut message = [0x42u8; 37];
        secret(&message);
        cipher::EncryptingKey::ctr(key())
            .unwrap()
            .less_safe_encrypt(&mut message, context())
            .unwrap();
        public(&message);
        public(key_bytes);
    }
}

/// Key wrap, with and without padding, whose output buffers rind-aws-lc-rs
/// slices to rind's lengths.
#[test]
fn key_wrap() {
    use key_wrap::{KeyWrap, KeyWrapPadded};

    let kek_bytes = [0x11u8; 32];
    let key = [0x22u8; 24];
    let kek = |kek_bytes: &[u8]| key_wrap::AesKek::new(&key_wrap::AES_256, kek_bytes).unwrap();
    let (mut plain, mut padded) = ([0u8; 48], [0u8; 48]);
    let plain = kek(&kek_bytes).wrap(&key, &mut plain).unwrap().to_vec();
    let padded = kek(&kek_bytes)
        .wrap_with_padding(&key, &mut padded)
        .unwrap()
        .to_vec();

    secret(&kek_bytes);
    secret(&key);
    let mut out = [0u8; 48];
    let wrapped = kek(&kek_bytes).wrap(&key, &mut out).unwrap();
    public(wrapped);
    assert_eq!(wrapped, plain);
    let mut out = [0u8; 48];
    let wrapped = kek(&kek_bytes).wrap_with_padding(&key, &mut out).unwrap();
    public(wrapped);
    assert_eq!(wrapped, padded);
    // Unwrapping still runs on the secret key-encryption key.
    public(&key);

    let mut out = [0u8; 48];
    let unwrapped = kek(&kek_bytes).unwrap(&plain, &mut out).unwrap();
    public(unwrapped);
    assert_eq!(unwrapped, key);
    let mut out = [0u8; 48];
    let unwrapped = kek(&kek_bytes)
        .unwrap_with_padding(&padded, &mut out)
        .unwrap();
    public(unwrapped);
    assert_eq!(unwrapped, key);
}

/// An ML-DSA expanded key, which rind-aws-lc-rs wraps in PKCS#8 for rind to
/// load, and the seed.
#[test]
fn ml_dsa() {
    use aws_lc_rs::encoding::{AsRawBytes, PqdsaPrivateKeyRaw};
    use rind_aws_lc_rs::signature::{self, KeyPair, ML_DSA_65_SIGNING, PqdsaKeyPair};

    let seed = [0x33u8; 32];
    let raw: PqdsaPrivateKeyRaw<'static> = aws_lc_rs::signature::PqdsaKeyPair::from_seed(
        &aws_lc_rs::signature::ML_DSA_65_SIGNING,
        &seed,
    )
    .unwrap()
    .private_key()
    .as_raw_bytes()
    .unwrap();
    let raw = raw.as_ref().to_vec();

    secret(&seed);
    // The expanded key's first 32 bytes are the public seed `rho`.
    secret(&raw[32..]);
    let msg = b"message";
    for key in [
        PqdsaKeyPair::from_seed(&ML_DSA_65_SIGNING, &seed).unwrap(),
        PqdsaKeyPair::from_raw_private_key(&ML_DSA_65_SIGNING, &raw).unwrap(),
    ] {
        let public_key = key.public_key().as_ref().to_vec();
        public(public_key.as_slice());
        let mut sig = [0u8; 3309];
        key.sign(msg, &mut sig).unwrap();
        public(&sig);
        signature::UnparsedPublicKey::new(&signature::ML_DSA_65, &public_key)
            .verify(msg, &sig)
            .unwrap();
    }
}

/// `PqdsaKeyPair::from_pkcs8` parses an Ed25519 key before refusing it.
/// The seed is marked secret. The OID is public.
#[cfg(not(any(miri, target_family = "wasm")))]
#[test]
fn ml_dsa_other_private_key() {
    use rind_aws_lc_rs::signature;

    let seed = [3u8; 32];
    let doc = aws_lc_rs::signature::Ed25519KeyPair::from_seed_unchecked(&seed)
        .unwrap()
        .to_pkcs8v1()
        .unwrap();
    let pkcs8 = doc.as_ref();
    let at = pkcs8
        .windows(seed.len())
        .position(|window| window == seed)
        .unwrap();
    secret(&pkcs8[at..at + seed.len()]);
    let err =
        signature::PqdsaKeyPair::from_pkcs8(&signature::ML_DSA_44_SIGNING, pkcs8).unwrap_err();
    public(err.description_().as_bytes());
    assert_eq!(err.description_(), "WrongAlgorithm");
    public(&pkcs8[..at]);
    public(&pkcs8[at + seed.len()..]);
}

/// `PqdsaKeyPair::from_raw_private_key` loads an ML-DSA-65 expanded key,
/// and one with a flipped byte, as ML-DSA-44 before refusing it. The secret
/// bytes are marked. The first 32 bytes are the public seed `rho`.
#[cfg(not(any(miri, target_family = "wasm")))]
#[test]
fn ml_dsa_other_set() {
    use aws_lc_rs::encoding::{AsRawBytes, PqdsaPrivateKeyRaw};
    use rind_aws_lc_rs::signature::{ML_DSA_44_SIGNING, PqdsaKeyPair};

    let seed = [0x33u8; 32];
    let raw: PqdsaPrivateKeyRaw<'static> = aws_lc_rs::signature::PqdsaKeyPair::from_seed(
        &aws_lc_rs::signature::ML_DSA_65_SIGNING,
        &seed,
    )
    .unwrap()
    .private_key()
    .as_raw_bytes()
    .unwrap();
    let raw = raw.as_ref().to_vec();
    let mut corrupt = raw.clone();
    corrupt[100] ^= 0x01;

    // The expanded key's first 32 bytes are the public seed `rho`.
    secret(&raw[32..]);
    secret(&corrupt[32..]);

    let err = PqdsaKeyPair::from_raw_private_key(&ML_DSA_44_SIGNING, &raw).unwrap_err();
    public(err.description_().as_bytes());
    assert_eq!(err.description_(), "Unspecified");

    let err = PqdsaKeyPair::from_raw_private_key(&ML_DSA_44_SIGNING, &corrupt).unwrap_err();
    public(err.description_().as_bytes());
    assert_eq!(err.description_(), "InvalidEncoding");
}

/// `PqdsaKeyPair::from_pkcs8` loads an ML-DSA-65 key in full as ML-DSA-65
/// before refusing it as ML-DSA-44: its seed, its expanded key, one with a
/// flipped byte, and both together. The seed and the expanded key past its
/// public seed `rho` are marked secret; the framing is public.
#[cfg(not(any(miri, target_family = "wasm")))]
#[test]
fn ml_dsa_other_set_pkcs8() {
    use aws_lc_rs::encoding::{AsRawBytes, PqdsaPrivateKeyRaw};
    use rind_aws_lc_rs::signature::{ML_DSA_44_SIGNING, PqdsaKeyPair};

    let seed = [0x44u8; 32];
    let raw: PqdsaPrivateKeyRaw<'static> = aws_lc_rs::signature::PqdsaKeyPair::from_seed(
        &aws_lc_rs::signature::ML_DSA_65_SIGNING,
        &seed,
    )
    .unwrap()
    .private_key()
    .as_raw_bytes()
    .unwrap();
    let raw = raw.as_ref().to_vec();
    let mut flipped = raw.clone();
    flipped[100] ^= 0x01;

    let der = |tag: u8, body: &[u8]| {
        let mut out = vec![tag];
        match body.len() {
            0..0x80 => out.push(body.len() as u8),
            0x80..0x100 => out.extend([0x81, body.len() as u8]),
            n => out.extend([0x82, (n >> 8) as u8, n as u8]),
        }
        out.extend_from_slice(body);
        out
    };
    // id-ml-dsa-65, 2.16.840.1.101.3.4.3.18
    let algorithm = der(
        0x30,
        &der(
            0x06,
            &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12],
        ),
    );
    let pkcs8 = |private_key: &[u8]| {
        der(
            0x30,
            &[&[0x02, 0x01, 0x00][..], &algorithm, &der(0x04, private_key)].concat(),
        )
    };
    let both = |expanded: &[u8]| der(0x30, &[der(0x04, &seed), der(0x04, expanded)].concat());

    for (doc, expected) in [
        (pkcs8(&der(0x80, &seed)), "Unspecified"),
        (pkcs8(&der(0x04, &raw)), "Unspecified"),
        (pkcs8(&der(0x04, &flipped)), "InvalidEncoding"),
        (pkcs8(&both(&raw)), "Unspecified"),
        (pkcs8(&both(&flipped)), "InvalidEncoding"),
    ] {
        // Every needle is found before any is marked, so the search reads
        // only defined bytes.
        let found: Vec<_> = [&seed[..], &raw[32..], &flipped[32..]]
            .into_iter()
            .filter_map(|needle| {
                let at = doc.windows(needle.len()).position(|w| w == needle)?;
                Some(at..at + needle.len())
            })
            .collect();
        for range in found {
            secret(&doc[range]);
        }
        let err = PqdsaKeyPair::from_pkcs8(&ML_DSA_44_SIGNING, &doc).unwrap_err();
        public(err.description_().as_bytes());
        assert_eq!(err.description_(), expected);
    }
}
