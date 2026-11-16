// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Constant-time checks of the module as it ships, run under valgrind by
//! `admin/ctgrind fips`: its own optimized build of rind, its C ABI, its
//! pairwise consistency tests, and its DRBG.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index inside the module that depends on them. Outputs that are public by
//! design are marked defined before the test checks them. The module's build
//! of rind, with `rind/__ctgrind`, adds its own marks, such as on RSA's
//! private integers, and declassifies what it makes public. The DRBG's
//! output is not marked, so a key the module generates is checked only once
//! the test marks it, as `key_imports` marks each encoding.
#![cfg(rind_fips_module)]
#![cfg(feature = "__ctgrind")]

use std::num::NonZeroU32;

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use rind_fips::ecdsa::{KeyPair as EcdsaKeyPair, sign};
use rind_fips::ed25519::KeyPair as Ed25519KeyPair;
use rind_fips::key_wrap::{self, Mode};
use rind_fips::ml_dsa::{KeyPair as MlDsaKeyPair, MlDsa65};
use rind_fips::rsa::KeyPair as RsaKeyPair;
use rind_fips::{aead, agreement, cipher, hkdf, hmac, kem, pbkdf2, rand};

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

const MESSAGE: &[u8] = b"message";

#[test]
fn hmac_hkdf_and_pbkdf2() {
    let key_value = [0x0b; 32];
    let expected = rind::hmac::sign(
        &rind::hmac::Key::new(&rind::hmac::HMAC_SHA256, &key_value),
        MESSAGE,
    );
    secret(&key_value);
    let key = hmac::Key::new(&hmac::HMAC_SHA256, &key_value);
    let tag = hmac::sign(&key, MESSAGE);
    public(tag.as_ref());
    assert_eq!(tag.as_ref(), expected.as_ref());
    assert!(hmac::verify(&key, MESSAGE, tag.as_ref()).is_ok());

    // A streamed tag, and a clone forked partway, match the one-shot tag.
    let mut context = hmac::Context::with_key(&key);
    context.update(&MESSAGE[..3]);
    let mut forked = context.clone();
    context.update(&MESSAGE[3..]);
    forked.update(&MESSAGE[3..]);
    let (streamed, forked) = (context.sign(), forked.sign());
    public(streamed.as_ref());
    public(forked.as_ref());
    assert_eq!(streamed.as_ref(), expected.as_ref());
    assert_eq!(forked.as_ref(), expected.as_ref());

    let ikm = [0x0c; 32];
    secret(&ikm);
    let prk = hkdf::Salt::new(&hkdf::HKDF_SHA256, b"salt")
        .extract(&ikm)
        .unwrap();
    let mut okm = [0u8; 42];
    prk.fill(&[b"info"], &mut okm).unwrap();
    public(&okm);
    hkdf::Prk::new(&hkdf::HKDF_SHA256, &ikm)
        .clone()
        .fill(&[b"info"], &mut okm)
        .unwrap();
    public(&okm);
    let key = hmac::Key::from(prk.expand(&[b"info"], &hmac::HMAC_SHA256).unwrap());
    let tag = hmac::sign(&key, MESSAGE);
    public(tag.as_ref());

    let password = *b"correct horse battery staple";
    secret(&password);
    let iterations = NonZeroU32::new(1000).unwrap();
    let derived = pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA256, &password);
    let mut out = [0u8; 32];
    derived.derive(iterations, &[5; 16], &mut out).unwrap();
    secret(&out);
    assert!(derived.verify(iterations, &[5; 16], &out).is_ok());
}

#[test]
fn aes() {
    let key = [0x42; 32];
    let sealing = rind::aead::Key::new(&rind::aead::AES_256_GCM, &key).unwrap();
    let mut sealed = MESSAGE.to_vec();
    sealing
        .seal_in_place_append_tag(
            rind::aead::Nonce::assume_unique_for_key([1; 12]),
            b"aad",
            &mut sealed,
        )
        .unwrap();

    secret(&key);
    let opening = aead::Key::new(&aead::AES_256_GCM, &key).unwrap();
    let opened = opening
        .open_in_place(
            aead::Nonce::assume_unique_for_key([1; 12]),
            b"aad",
            &mut sealed,
        )
        .unwrap();
    public(&*opened);
    assert_eq!(opened, MESSAGE);

    // Sealing under a random nonce, and a TLS 1.3 record's, of a secret
    // message under the secret key.
    let random = aead::RandomizedNonceKey::new(&aead::AES_256_GCM, &key).unwrap();
    let mut message = MESSAGE.to_vec();
    secret(&message[..]);
    let nonce = random
        .seal_in_place_append_tag(b"aad", &mut message)
        .unwrap();
    public(&message[..]);
    let opened = random.open_in_place(nonce, b"aad", &mut message).unwrap();
    public(&*opened);
    assert_eq!(opened, MESSAGE);

    let mut tls =
        aead::TlsRecordSealingKey::new(&aead::AES_256_GCM, aead::TlsProtocolId::TLS13, &key)
            .unwrap();
    for seq in 0..2u8 {
        let mut nonce = [1; 12];
        nonce[11] ^= seq;
        let mut message = MESSAGE.to_vec();
        secret(&message[..]);
        let tag = tls
            .seal_in_place_separate_tag(
                aead::Nonce::assume_unique_for_key(nonce),
                b"aad",
                &mut message,
            )
            .unwrap();
        public(&message[..]);
        public(tag.as_ref());
        let opened = opening
            .open_in_place_separate_tag(
                aead::Nonce::assume_unique_for_key(nonce),
                b"aad",
                tag,
                &mut message,
            )
            .unwrap();
        public(&*opened);
        assert_eq!(opened, MESSAGE);
    }

    // GCM with a truncated tag and an IV that is not 96 bits, which GCM
    // hashes under the key into its counter.
    let iv = [9u8; 7];
    let reference = rind::aead::gcm::Key::new(
        &rind::cipher::AES_256,
        &[0x42; 32],
        rind::aead::gcm::TagLength::Truncated96,
    )
    .unwrap();
    let mut sealed = MESSAGE.to_vec();
    reference
        .seal_in_place_append_tag(
            rind::aead::gcm::Iv::assume_unique_for_key(&iv).unwrap(),
            b"aad",
            &mut sealed,
        )
        .unwrap();
    let gcm =
        aead::gcm::Key::new(&cipher::AES_256, &key, aead::gcm::TagLength::Truncated96).unwrap();
    let mut forged = sealed.clone();
    *forged.last_mut().unwrap() ^= 1;
    let opened = gcm
        .open_in_place(
            aead::gcm::Iv::assume_unique_for_key(&iv).unwrap(),
            b"aad",
            &mut sealed,
        )
        .unwrap();
    public(&*opened);
    assert_eq!(opened, MESSAGE);
    assert_eq!(
        gcm.open_in_place(
            aead::gcm::Iv::assume_unique_for_key(&iv).unwrap(),
            b"aad",
            &mut forged,
        )
        .err(),
        Some(rind_fips::Error::DecryptFailed),
    );

    let mut block = [7u8; 16];
    cipher::Aes::new(&cipher::AES_256, &key)
        .unwrap()
        .encrypt_block(&mut block);
    public(&block);

    let mut stream = [0u8; 40];
    cipher::AesCtr::new(&cipher::AES_256, &key, 32)
        .unwrap()
        .apply_keystream(&[0; 16], &mut stream)
        .unwrap();
    public(&stream);

    let mut padded = MESSAGE.to_vec();
    cipher::AesCbcEncryptingKey::new(&cipher::AES_256, &key)
        .unwrap()
        .encrypt(cipher::CbcIv::assume_unpredictable([3; 16]), &mut padded)
        .unwrap();
    public(&padded[..]);
    let plaintext = cipher::AesCbcDecryptingKey::new(&cipher::AES_256, &key)
        .unwrap()
        .decrypt(&[3; 16], &mut padded)
        .unwrap();
    public(&*plaintext);
    assert_eq!(plaintext, MESSAGE);

    let kek = key_wrap::AesKek::new(&key_wrap::AES_256, &key).unwrap();
    let wrapped_key = [0x24u8; 32];
    secret(&wrapped_key);
    let mut wrapped = [0u8; 40];
    kek.wrap_key(Mode::Kw, &wrapped_key, &mut wrapped).unwrap();
    public(&wrapped);
    let mut unwrapped = [0u8; 32];
    kek.unwrap_key(Mode::Kw, &wrapped, &mut unwrapped).unwrap();
    public(&unwrapped);
    assert_eq!(unwrapped, [0x24; 32]);
    wrapped[9] ^= 1;
    assert_eq!(
        kek.unwrap_key(Mode::Kw, &wrapped, &mut unwrapped)
            .map(|_| ()),
        Err(rind_fips::Error::DecryptFailed)
    );

    // RFC 5649's padding: a key of 8 bytes or fewer takes the single-block
    // path, and a longer one the wrapping loop, each unpadded after.
    for len in [5, 8, 20] {
        let wrapped_key = vec![0x42u8; len];
        secret(&wrapped_key[..]);
        let mut wrapped = vec![0u8; len.next_multiple_of(8) + 8];
        kek.wrap_key(Mode::Kwp, &wrapped_key, &mut wrapped).unwrap();
        public(&wrapped[..]);
        let mut unwrapped = vec![0u8; wrapped.len() - 8];
        let key = kek.unwrap_key(Mode::Kwp, &wrapped, &mut unwrapped).unwrap();
        public(key);
        assert_eq!(key, &vec![0x42; len][..], "{len}");
        wrapped[9] ^= 1;
        assert_eq!(
            kek.unwrap_key(Mode::Kwp, &wrapped, &mut unwrapped).err(),
            Some(rind_fips::Error::DecryptFailed),
            "{len}"
        );
    }
}

#[test]
fn agreement_and_kem() {
    let peer = agreement::PrivateKey::generate(&agreement::ECDH_P256).unwrap();
    let scalar = [0x11u8; 32];
    secret(&scalar);
    let ours = agreement::PrivateKey::from_scalar(&agreement::ECDH_P256, &scalar).unwrap();
    let shared = ours.agree(peer.public_key().as_ref()).unwrap();
    let theirs = peer.agree(ours.public_key().as_ref()).unwrap();
    public(shared.as_ref());
    public(theirs.as_ref());
    assert_eq!(shared.as_ref(), theirs.as_ref());

    kem_set::<kem::MlKem512>();
    kem_set::<kem::MlKem768>();
    kem_set::<kem::MlKem1024>();
}

fn kem_set<A: kem::Algorithm>() {
    let key = kem::DecapsulationKey::<A>::generate().unwrap();
    let (ciphertext, sent) = key.public_key().encapsulate().unwrap();
    let received = key.decapsulate(&ciphertext);
    public(sent.as_ref());
    public(received.as_ref());
    assert_eq!(sent.as_ref(), received.as_ref());
}

#[test]
fn signatures() {
    let ecdsa = EcdsaKeyPair::generate(&sign::P256_SHA256_ASN1).unwrap();
    let mut scalar = ecdsa.to_scalar().as_ref().to_vec();
    let public_key = ecdsa.public_key().as_ref().to_vec();
    secret(&scalar[..]);
    let loaded =
        EcdsaKeyPair::from_scalar_and_public_key(&sign::P256_SHA256_ASN1, &scalar, &public_key)
            .unwrap();
    scalar.fill(0);
    let signature = loaded.sign(MESSAGE).unwrap();
    public(signature.as_ref());
    assert!(
        loaded
            .public_key()
            .verify(MESSAGE, signature.as_ref())
            .is_ok()
    );

    let seed = [0x33u8; 32];
    secret(&seed);
    let ed25519 = Ed25519KeyPair::from_seed(&seed).unwrap();
    let signature = ed25519.sign(MESSAGE);
    public(signature.as_ref());
    assert!(
        ed25519
            .public_key()
            .verify(MESSAGE, signature.as_ref())
            .is_ok()
    );
    let signature = Ed25519KeyPair::generate().unwrap().sign(MESSAGE);
    public(signature.as_ref());

    let seed = [0x44u8; 32];
    secret(&seed);
    let ml_dsa = MlDsaKeyPair::<MlDsa65>::from_seed(&seed).unwrap();
    let signature = ml_dsa.sign(MESSAGE).unwrap();
    public(signature.as_ref());
    assert!(
        ml_dsa
            .public_key()
            .verify(MESSAGE, signature.as_ref())
            .is_ok()
    );
    let signature = MlDsaKeyPair::<MlDsa65>::generate()
        .unwrap()
        .sign(MESSAGE)
        .unwrap();
    public(signature.as_ref());

    let rsa = RsaKeyPair::generate(rind_fips::rsa::KeySize::Rsa2048).unwrap();
    let signature = rsa
        .sign(&rind_fips::rsa::sign::PSS_SHA256, MESSAGE)
        .unwrap();
    public(signature.as_ref());
    assert!(
        rsa.public_key()
            .verify(
                &rind_fips::rsa::verify::PSS_SHA256,
                MESSAGE,
                signature.as_ref()
            )
            .is_ok()
    );
}

/// Copies `der`, marking secret where it holds `private`.
fn with_secret(der: &[u8], private: &[u8]) -> Vec<u8> {
    // Searched for in copies the test may branch on.
    let (haystack, needle) = (der.to_vec(), private.to_vec());
    public(&haystack[..]);
    public(&needle[..]);
    let at = haystack
        .windows(needle.len())
        .position(|w| w == needle)
        .unwrap();
    let der = der.to_vec();
    secret(&der[at..at + private.len()]);
    der
}

/// Copies the PKCS#1 `RSAPrivateKey` `der`, marking secret every byte of
/// its private integers, d, p, q, dp, dq, and qinv.
fn rsa_with_secret(der: &[u8]) -> Vec<u8> {
    let der = der.to_vec();
    // The length of the element at `at`'s tag and length, and its length.
    let header = |at: usize| -> (usize, usize) {
        match der[at + 1] {
            len @ 0..=0x7f => (2, usize::from(len)),
            0x81 => (3, usize::from(der[at + 2])),
            0x82 => (
                4,
                usize::from(u16::from_be_bytes([der[at + 2], der[at + 3]])),
            ),
            _ => unreachable!(),
        }
    };
    let (mut at, _) = header(0);
    for index in 0..9 {
        let (head, len) = header(at);
        if index >= 3 {
            secret(&der[at + head..at + head + len]);
        }
        at += head + len;
    }
    der
}

/// Loads private keys from DER, marked secret where they hold the private
/// key and public in their framing and public key.
#[test]
fn key_imports() {
    let algorithm = &sign::P256_SHA256_ASN1;
    let ecdsa = EcdsaKeyPair::generate(algorithm).unwrap();
    let scalar = ecdsa.to_scalar().as_ref().to_vec();
    let public_key = ecdsa.public_key().as_ref().to_vec();
    let pkcs8 = with_secret(ecdsa.to_pkcs8().as_ref(), &scalar);
    let loaded = EcdsaKeyPair::from_pkcs8(algorithm, &pkcs8).unwrap();
    assert_eq!(loaded.public_key().as_ref(), public_key);
    let sec1 = with_secret(ecdsa.to_sec1().as_ref(), &scalar);
    let loaded = EcdsaKeyPair::from_sec1(algorithm, &sec1).unwrap();
    assert_eq!(loaded.public_key().as_ref(), public_key);

    // A public key that is not the private key's fails the consistency
    // check. Each encoding ends with it.
    let other = EcdsaKeyPair::generate(algorithm).unwrap();
    let mut mismatched = pkcs8;
    let at = mismatched.len() - public_key.len();
    assert_eq!(mismatched[at..], public_key);
    mismatched[at..].copy_from_slice(other.public_key().as_ref());
    assert!(EcdsaKeyPair::from_pkcs8(algorithm, &mismatched).is_err());

    let ed25519 = Ed25519KeyPair::generate().unwrap();
    let seed = ed25519.to_seed().as_ref().to_vec();
    let public_key = ed25519.public_key().as_ref().to_vec();
    for pkcs8 in [ed25519.to_pkcs8(), ed25519.to_pkcs8v1()] {
        let pkcs8 = with_secret(pkcs8.as_ref(), &seed);
        let loaded = Ed25519KeyPair::from_pkcs8(&pkcs8).unwrap();
        assert_eq!(loaded.public_key().as_ref(), public_key);
    }
    let mut mismatched = with_secret(ed25519.to_pkcs8().as_ref(), &seed);
    let at = mismatched.len() - public_key.len();
    assert_eq!(mismatched[at..], public_key);
    mismatched[at..].copy_from_slice(Ed25519KeyPair::generate().unwrap().public_key().as_ref());
    assert!(Ed25519KeyPair::from_pkcs8(&mismatched).is_err());

    let ml_dsa = MlDsaKeyPair::<MlDsa65>::generate().unwrap();
    let seed = ml_dsa.to_seed().unwrap().as_ref().to_vec();
    let pkcs8 = with_secret(ml_dsa.to_pkcs8().as_ref(), &seed);
    let loaded = MlDsaKeyPair::<MlDsa65>::from_pkcs8(&pkcs8).unwrap();
    assert_eq!(loaded.public_key().as_ref(), ml_dsa.public_key().as_ref());

    // PKCS#1's `RSAPrivateKey` is the OCTET STRING that ends PKCS#8's
    // 26-byte framing for a 2048-bit key.
    let rsa = RsaKeyPair::generate(rind_fips::rsa::KeySize::Rsa2048).unwrap();
    let public_key = rsa.public_key().to_spki();
    let pkcs8 = rsa.to_pkcs8();
    let pkcs8 = [
        &pkcs8.as_ref()[..26],
        &rsa_with_secret(&pkcs8.as_ref()[26..]),
    ]
    .concat();
    for loaded in [
        RsaKeyPair::from_pkcs8(&pkcs8),
        RsaKeyPair::from_pkcs1(&pkcs8[26..]),
    ] {
        assert_eq!(
            loaded.unwrap().public_key().to_spki().as_ref(),
            public_key.as_ref()
        );
    }
}

#[test]
fn random() {
    let mut out = [0u8; 48];
    rand::fill(&mut out).unwrap();
    public(&out);
    rand::fill(&mut out).unwrap();
    public(&out);
}
