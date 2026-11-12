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
use rind_aws_lc_rs::signature::KeyPair;
use rind_aws_lc_rs::{cipher, hkdf, hmac, iv, key_wrap, pbkdf2, signature};

/// Marks `value`'s bytes secret: memcheck flags any branch or index that
/// depends on them. `value` must be the bytes themselves, a slice or an
/// array. A `Vec`'s header is its pointer, capacity, and length, and the
/// length is public; marking the header taints every length derived from it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value`'s bytes public, so the test may branch on them. As with
/// [`secret`], pass the bytes, not a `Vec`.
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

/// The adapter's wrap of an expanded ML-DSA private key into PKCS#8, and
/// the seed-form export. Lengths are public; the key bytes are not.
#[test]
fn ml_dsa() {
    use aws_lc_rs::encoding::AsRawBytes;
    use aws_lc_rs::signature::{
        ML_DSA_44_SIGNING, ML_DSA_65_SIGNING, ML_DSA_87_SIGNING, PqdsaKeyPair,
    };
    use rind_aws_lc_rs::encoding::AsDer as _;

    for (ours_sign, theirs_sign) in [
        (&signature::ML_DSA_44_SIGNING, &ML_DSA_44_SIGNING),
        (&signature::ML_DSA_65_SIGNING, &ML_DSA_65_SIGNING),
        (&signature::ML_DSA_87_SIGNING, &ML_DSA_87_SIGNING),
    ] {
        let seed = [0x5au8; 32];
        let raw = {
            let key = PqdsaKeyPair::from_seed(theirs_sign, &seed).unwrap();
            key.private_key().as_raw_bytes().unwrap().as_ref().to_vec()
        };
        let expected = signature::PqdsaKeyPair::from_seed(ours_sign, &seed)
            .unwrap()
            .public_key()
            .as_ref()
            .to_vec();

        secret(&raw[..]);
        let key = signature::PqdsaKeyPair::from_raw_private_key(ours_sign, &raw).unwrap();
        let public_key = key.public_key().as_ref().to_vec();
        public(&public_key[..]);
        assert_eq!(public_key, expected);
        let mut signature_bytes = vec![0; ours_sign.signature_len()];
        key.sign(b"ct", &mut signature_bytes).unwrap();
        public(&signature_bytes[..]);

        secret(&seed);
        let key = signature::PqdsaKeyPair::from_seed(ours_sign, &seed).unwrap();
        let cloned = key.clone();
        let pkcs8 = key.to_pkcs8v1().unwrap();
        public(pkcs8.as_ref());
        let der = key.private_key().as_der().unwrap();
        public(der.as_ref());
        let mut signature_bytes = vec![0; ours_sign.signature_len()];
        cloned.sign(b"ct", &mut signature_bytes).unwrap();
        public(&signature_bytes[..]);
        let public_key = cloned.public_key().as_ref().to_vec();
        public(&public_key[..]);
        assert_eq!(public_key, expected);
    }
}

/// ML-DSA keys loaded from PKCS#8 in seed and expanded form, signing with
/// them, and exporting the seed form. The documents' headers and lengths are
/// public; their seed and expanded key are not.
#[test]
fn ml_dsa_pkcs8_sign_export() {
    use aws_lc_rs::encoding::{AsDer as _, AsRawBytes};
    use aws_lc_rs::signature::KeyPair as _;
    use aws_lc_rs::signature::{ML_DSA_65_SIGNING, PqdsaKeyPair};
    use rind_aws_lc_rs::encoding::{AsDer, Pkcs8V1Der};

    let seed = [0x6bu8; 32];
    let theirs = PqdsaKeyPair::from_seed(&ML_DSA_65_SIGNING, &seed).unwrap();
    let seed_form = theirs.private_key().as_der().unwrap().as_ref().to_vec();
    let raw = theirs
        .private_key()
        .as_raw_bytes()
        .unwrap()
        .as_ref()
        .to_vec();
    let expected = theirs.public_key().as_ref().to_vec();

    // Loading the ML-DSA-65 document as ML-DSA-44 refuses on the public
    // algorithm identifier. The seed stays secret.
    secret(&seed_form[seed_form.len() - 32..]);
    assert!(
        signature::PqdsaKeyPair::from_pkcs8(&signature::ML_DSA_44_SIGNING, &seed_form).is_err()
    );
    public(&seed_form[..seed_form.len() - 32]);

    // RFC 9881's expanded form: the raw key in an `OCTET STRING` inside
    // PKCS#8's, after the seed form's version and algorithm identifier.
    let header = &seed_form[2..2 + 3 + 13];
    let len = |n: usize| [0x82, (n >> 8) as u8, n as u8];
    let inner = [&[0x04][..], &len(raw.len()), &raw].concat();
    let body = [header, &[0x04], &len(inner.len()), &inner].concat();
    let expanded_form = [&[0x30][..], &len(body.len()), &body].concat();

    for (pkcs8, key_bytes) in [
        (&seed_form, seed_form.len() - 32..seed_form.len()),
        (
            &expanded_form,
            expanded_form.len() - raw.len()..expanded_form.len(),
        ),
    ] {
        secret(&pkcs8[key_bytes]);
        let key =
            signature::PqdsaKeyPair::from_pkcs8(&signature::ML_DSA_65_SIGNING, pkcs8).unwrap();
        let public_key = key.public_key().as_ref().to_vec();
        public(&public_key[..]);
        assert_eq!(public_key, expected);

        let mut sig = vec![0; signature::ML_DSA_65_SIGNING.signature_len()];
        let len = key.sign(b"message", &mut sig).unwrap();
        public(&sig[..]);
        assert!(
            aws_lc_rs::signature::UnparsedPublicKey::new(
                &aws_lc_rs::signature::ML_DSA_65,
                &expected
            )
            .verify(b"message", &sig[..len])
            .is_ok()
        );

        // The load and the signature have used the secret bytes. Declassify
        // the input document before comparing the export with it.
        public(&pkcs8[..]);
        // Only the seed form exports; the expanded form has no seed.
        match key.to_pkcs8v1() {
            Ok(doc) => {
                let der: Pkcs8V1Der<'static> = key.private_key().as_der().unwrap();
                public(doc.as_ref());
                public(der.as_ref());
                assert_eq!(doc.as_ref(), &seed_form[..]);
                assert_eq!(der.as_ref(), &seed_form[..]);
            }
            Err(_) => assert!(core::ptr::eq(pkcs8, &expanded_form)),
        }
    }
}

/// `PqdsaKeyPair::from_pkcs8` parses a non-ML-DSA key before refusing it.
/// The seed or scalar of an Ed25519, X25519, or ECDSA key is marked secret,
/// as is an RSA key's private exponent, primes, and CRT values.
///
/// Two parts of each RSA integer stay defined. The first two octets are the
/// DER sign check in `Integer::minimum_magnitude_check`, and the low octet of
/// each prime is the parity `RsaPrivateKey::new` branches on. The ECDSA
/// scalar parse is the same `sec1` decoder
/// `agreement::tests::loads_in_constant_time` checks.
#[test]
fn ml_dsa_other_private_key() {
    let load = |pkcs8: &[u8]| {
        let err =
            signature::PqdsaKeyPair::from_pkcs8(&signature::ML_DSA_44_SIGNING, pkcs8).unwrap_err();
        public(err.description_().as_bytes());
        assert_eq!(err.description_(), "WrongAlgorithm");
    };

    for (curve, len) in [
        (&[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07][..], 32),
        (&[0x2b, 0x81, 0x04, 0x00, 0x22][..], 48),
        (&[0x2b, 0x81, 0x04, 0x00, 0x23][..], 66),
    ] {
        let mut scalar = vec![0u8; len];
        scalar[len - 1] = 1;
        let pkcs8 = ec_pkcs8(curve, &scalar);
        let at = pkcs8
            .windows(len)
            .position(|window| window == scalar)
            .unwrap();
        secret(&pkcs8[at..at + len]);
        load(&pkcs8);
        public(&pkcs8[..at]);
        public(&pkcs8[at + len..]);
    }

    for (oid, seed) in [
        (&[0x2b, 0x65, 0x70][..], [3; 32]),
        (&[0x2b, 0x65, 0x6e][..], [0x11; 32]),
    ] {
        let pkcs8 = octet_string_pkcs8(oid, &seed);
        let at = pkcs8
            .windows(seed.len())
            .position(|window| window == seed)
            .unwrap();
        secret(&pkcs8[at..at + seed.len()]);
        load(&pkcs8);
        public(&pkcs8[..at]);
        public(&pkcs8[at + seed.len()..]);
    }

    use aws_lc_rs::encoding::AsDer as _;
    let rsa = aws_lc_rs::rsa::KeyPair::generate(aws_lc_rs::rsa::KeySize::Rsa2048)
        .unwrap()
        .as_der()
        .unwrap();
    let pkcs8 = rsa.as_ref().to_vec();
    mark_rsa_secrets(&pkcs8);
    load(&pkcs8);
    public(&pkcs8[..]);

    // RSASSA-PSS with no parameters is the same RSA key under another OID.
    // The integers are marked the same way.
    let (body, _) = der_contents(&pkcs8);
    let (_, body) = der_contents(body);
    let (_, body) = der_contents(body);
    let (pkcs1, _) = der_contents(body);
    let pss = der(
        0x30,
        &[
            der(0x02, &[0]),
            der(
                0x30,
                &der(
                    0x06,
                    &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a],
                ),
            ),
            der(0x04, pkcs1),
        ]
        .concat(),
    );
    mark_rsa_secrets(&pss);
    load(&pss);
    public(&pss[..]);

    // An ML-KEM-512 seed. Only its length is checked, so the seed bytes stay
    // secret through the refusal.
    let seed = [0x5au8; 64];
    let kem = der(
        0x30,
        &[
            der(0x02, &[0]),
            der(
                0x30,
                &der(
                    0x06,
                    &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x01],
                ),
            ),
            der(0x04, &der(0x80, &seed)),
        ]
        .concat(),
    );
    let at = kem
        .windows(seed.len())
        .position(|window| window == seed)
        .unwrap();
    secret(&kem[at..at + seed.len()]);
    load(&kem);
    public(&kem[at..at + seed.len()]);
}

/// Marks the private exponent, primes, and CRT values in an RSA PKCS#8
/// document. The first two octets of each integer are its DER sign check,
/// and the low octet of each prime is its parity.
fn mark_rsa_secrets(pkcs8: &[u8]) {
    let (body, _) = der_contents(pkcs8);
    let (_, body) = der_contents(body);
    let (_, body) = der_contents(body);
    let (octet, _) = der_contents(body);
    let (mut rest, _) = der_contents(octet);
    let mut which = 0;
    while !rest.is_empty() {
        let (integer, next) = der_contents(rest);
        if which >= 3 && integer.len() > 3 {
            let start = integer.as_ptr() as usize - pkcs8.as_ptr() as usize;
            let end = start + integer.len() - usize::from(which == 4 || which == 5);
            secret(&pkcs8[start + 2..end]);
        }
        which += 1;
        rest = next;
    }
}

fn der_contents(input: &[u8]) -> (&[u8], &[u8]) {
    let (len, rest) = match input[1] {
        len @ 0..=0x7f => (usize::from(len), &input[2..]),
        0x81 => (usize::from(input[2]), &input[3..]),
        0x82 => (
            usize::from(u16::from_be_bytes([input[2], input[3]])),
            &input[4..],
        ),
        _ => panic!("DER length is longer than two bytes"),
    };
    rest.split_at(len)
}

fn ec_pkcs8(curve: &[u8], scalar: &[u8]) -> Vec<u8> {
    let private_key = der(0x30, &[der(0x02, &[1]), der(0x04, scalar)].concat());
    let algorithm = [
        der(0x06, &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]),
        der(0x06, curve),
    ]
    .concat();
    der(
        0x30,
        &[
            der(0x02, &[0]),
            der(0x30, &algorithm),
            der(0x04, &private_key),
        ]
        .concat(),
    )
}

fn octet_string_pkcs8(oid: &[u8], seed: &[u8]) -> Vec<u8> {
    der(
        0x30,
        &[
            der(0x02, &[0]),
            der(0x30, &der(0x06, oid)),
            der(0x04, &der(0x04, seed)),
        ]
        .concat(),
    )
}

fn der(tag: u8, contents: &[u8]) -> Vec<u8> {
    let len = contents.len();
    let mut out = vec![tag];
    match len {
        0..=0x7f => out.push(len as u8),
        0x80..=0xff => out.extend([0x81, len as u8]),
        _ => out.extend([0x82, (len >> 8) as u8, len as u8]),
    }
    out.extend_from_slice(contents);
    out
}
