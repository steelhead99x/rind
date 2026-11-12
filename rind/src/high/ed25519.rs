// Written for Graviola by Joe Birr-Pixton, 2025.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use crate::Error;
use crate::error::KeyFormatError;
use crate::high::asn1::{self, Type, pkix};
use crate::high::pkcs8;
use crate::low::{self, Entry, ct};
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::{ed25519, util};

/// An Ed25519 verification public key.
#[derive(Debug)]
pub(crate) struct Ed25519VerifyingKey(ed25519::VerifyingKey);

impl Ed25519VerifyingKey {
    /// Encode in `SubjectPublicKeyInfo` DER format.
    ///
    /// The encoding is written to the start of `output`, and the used slice is
    /// returned.  [`Error::WrongLength`] is returned if `output` is not sufficient
    /// to contain the full encoding.
    pub(crate) fn to_spki_der<'a>(&self, output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let pub_key_buffer = self.as_bytes();

        let spki = pkix::SubjectPublicKeyInfo {
            algorithm: pkix::AlgorithmIdentifier {
                algorithm: asn1::oid::id_ed25519.clone(),
                parameters: None,
            },
            subjectPublicKey: asn1::BitString::new(&pub_key_buffer[..]),
        };

        let len = spki
            .encode(&mut asn1::Encoder::new(output))
            .map_err(|_| Error::WrongLength)?;
        Ok(&output[..len])
    }

    /// Decode from the 32-byte Ed25519 public key encoding, refusing a point
    /// of small order.
    ///
    /// aws-lc-rs takes one, but with the identity as the key, `R = identity`
    /// and `S = 0` verify any message. No honest key has small order, so
    /// rind refuses them all, as libsodium does.
    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        if has_small_order(bytes) {
            return Err(KeyFormatError::SmallOrder.into());
        }
        ed25519::VerifyingKey::from_bytes(bytes).map(Self)
    }

    /// Encode using compressed point encoding.
    pub(crate) fn as_bytes(&self) -> [u8; 32] {
        self.0.as_bytes()
    }

    /// Verify a `signature` against the given `message`.
    ///
    /// The signature must be precisely 64 bytes.
    ///
    /// Returns `Error::BadSignature` if the signature is invalid.
    pub(crate) fn verify(&self, signature: &[u8], message: &[u8]) -> Result<(), Error> {
        let _entry = Entry::new_public();

        self.0.verify(
            signature.try_into().map_err(|_| Error::BadSignature)?,
            message,
        )
    }
}

/// Whether `bytes` encodes a point of small order, canonically or not.
///
/// These are libsodium's `ge25519_has_small_order` encodings, compared, as
/// there, in constant time and without the sign bit of `x`: the eight points
/// of order dividing 8, then `y = p` and `y = p + 1`, the only `y` of a
/// small-order point whose non-canonical `y + p` fits in 255 bits. Each is
/// compared as little-endian limbs with s2n-bignum's proven `bignum_eq`.
pub(crate) fn has_small_order(bytes: &[u8]) -> bool {
    const SMALL_ORDER_Y: [[u64; 4]; 7] = [
        // `y = 0`, order 4.
        [0; 4],
        // `y = 1`, the identity.
        [1, 0, 0, 0],
        // Order 8.
        [
            0xb027b2c28f95e826,
            0xf098eff289f4c345,
            0x3933c6d305acdfd5,
            0x05fc536d880238b1,
        ],
        // Order 8.
        [
            0x4fd84d3d706a17c7,
            0x0f67100d760b3cba,
            0xc6cc392cfa53202a,
            0x7a03ac9277fdc74e,
        ],
        // `y = p - 1`, order 2, then `y = p` and `y = p + 1`.
        near_p(0xffffffffffffffec),
        near_p(0xffffffffffffffed),
        near_p(0xffffffffffffffee),
    ];

    /// `p = 2^255 - 19`, as limbs, with its lowest limb `low`.
    const fn near_p(low: u64) -> [u64; 4] {
        [low, u64::MAX, u64::MAX, u64::MAX >> 1]
    }

    let Some(mut y) = util::little_endian_slice_to_u64x4(bytes) else {
        return false;
    };
    y[3] &= u64::MAX >> 1;
    let mut found = false;
    for small in &SMALL_ORDER_Y {
        found |= low::bignum_eq(&y, small);
    }
    found
}

/// An Ed25519 signing private key.
pub(crate) struct Ed25519SigningKey(ed25519::SigningKey);

impl Ed25519SigningKey {
    /// Generate a new signing key.
    pub(crate) fn generate() -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let mut seed = [0u8; 32];
        SystemRandom.fill(&mut seed)?;
        Ok(Self(ed25519::SigningKey::from_seed(&seed)))
    }

    /// Sign `message`.
    pub(crate) fn sign(&self, message: &[u8]) -> [u8; 64] {
        let _entry = Entry::new_secret();
        self.0.sign(message)
    }

    /// Return the corresponding public key.
    pub(crate) fn public_key(&self) -> Ed25519VerifyingKey {
        let _entry = Entry::new_public();
        Ed25519VerifyingKey(self.0.verifying_key().clone())
    }

    /// Load an Ed25519 private key in PKCS#8 format.
    ///
    /// This supports PKCS#8 v1 (RFC 5208) and v2 (RFC 5958, which may include the public key).
    /// If the encoding includes the alleged public key, this is checked against the actual one.
    pub(crate) fn from_pkcs8_der(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();

        let p8 = pkcs8::Key::decode(bytes, &[&asn1::oid::id_ed25519], None)?;

        let key = asn1::OctetString::from_bytes(p8.private_key())
            .map_err(|e| Error::from(KeyFormatError::Asn1(e)))
            .and_then(|pk| Self::from_bytes(pk.as_octets()))?;

        if let Some(alleged_pub_key) = p8.public_key() {
            let actual_pub_key = key.public_key().as_bytes();
            if alleged_pub_key != actual_pub_key {
                return Err(KeyFormatError::MismatchedPkcs8PublicKey.into());
            }
        }

        Ok(key)
    }

    /// Encode this private key in PKCS#8 DER format: RFC 5958's "v2", with
    /// the public key, if `with_public_key`, and otherwise RFC 8410's v1.
    ///
    /// The encoding is written to the start of `output`, and the used slice is
    /// returned.  [`Error::WrongLength`] is returned if `output` is not sufficient
    /// to contain the full encoding.
    pub(crate) fn to_pkcs8_der<'a>(
        &self,
        with_public_key: bool,
        output: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();

        let mut private_key_buf = [0u8; 34];
        let private_key_len = asn1::OctetString::new(self.0.as_seed_bytes())
            .encode(&mut asn1::Encoder::new(&mut private_key_buf))
            .map_err(|_| Error::WrongLength)?;
        assert_eq!(private_key_len, private_key_buf.len());

        let public_key = self.public_key().as_bytes();

        match pkcs8::Key::construct(
            &private_key_buf[..],
            with_public_key.then_some(&public_key[..]),
            asn1::oid::id_ed25519.clone(),
            None,
        )
        .encode(output)
        {
            Ok(bytes) => {
                ct::public_slice(bytes);
                Ok(bytes)
            }
            Err(e) => Err(e),
        }
    }

    /// Load an Ed25519 private key from a 32-byte seed.
    pub(crate) fn from_bytes(seed: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        seed.try_into()
            .map(|seed| Self(ed25519::SigningKey::from_seed(&seed)))
            .map_err(|_| KeyFormatError::WrongLength.into())
    }

    /// Return the 32-byte seed, still secret, which [`Self::from_bytes`] loads.
    pub(crate) fn seed(&self) -> &[u8; 32] {
        self.0.as_seed_bytes()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::{Acvp, acvp};

    #[test]
    fn acvp_key_gen() {
        for group in acvp("EDDSA-KeyGen-1.0") {
            for test in group.tests() {
                let key = Ed25519SigningKey::from_bytes(&test.hex("d")).unwrap();
                assert_eq!(key.public_key().as_bytes(), &test.hex("q")[..]);
            }
        }
    }

    #[test]
    fn acvp_key_ver() {
        for group in acvp("EDDSA-KeyVer-1.0") {
            for test in group.tests() {
                let valid = Ed25519VerifyingKey::from_bytes(&test.hex("q")).is_ok();
                assert_eq!(valid, test.flag("testPassed"), "{}", test.str("reason"));
            }
        }
    }

    /// Ed25519 signing is deterministic, so each signature is checked whole:
    /// AFT groups sign messages, and BFT groups messages that differ in one bit.
    #[test]
    fn acvp_sig_gen() {
        for group in acvp("EDDSA-SigGen-1.0") {
            let key = Ed25519SigningKey::from_bytes(&group.hex("d")).unwrap();
            assert_eq!(key.public_key().as_bytes(), &group.hex("q")[..]);
            for test in group.tests() {
                assert_eq!(key.sign(&test.hex("message")), &test.hex("signature")[..]);
            }
        }
    }

    #[test]
    fn acvp_sig_ver() {
        for group in acvp("EDDSA-SigVer-1.0") {
            for test in group.tests() {
                let valid = Ed25519VerifyingKey::from_bytes(&test.hex("q"))
                    .and_then(|key| key.verify(&test.hex("signature"), &test.hex("message")))
                    .is_ok();
                assert_eq!(valid, test.flag("testPassed"), "{}", test.str("reason"));
            }
        }
    }

    #[test]
    fn pairwise() {
        for _ in 0..100 {
            let k = Ed25519SigningKey::generate().unwrap();
            let pk = k.public_key();
            let mut msg = [0u8; 128];
            SystemRandom.fill(&mut msg).unwrap();
            let sig = k.sign(&msg);

            pk.verify(&sig, &msg).unwrap();
        }
    }

    #[test]
    fn decode_pkcs8_v1() {
        let bytes = include_bytes!("asn1/testdata/ed25519-p8v1.bin");
        let key = Ed25519SigningKey::from_pkcs8_der(bytes).unwrap();

        let mut buf = vec![0; 128];
        let buf = key.to_pkcs8_der(true, &mut buf).unwrap();
        assert_ne!(bytes, buf);
        assert!(bytes.len() < buf.len());
    }

    #[test]
    fn round_trip_pkcs8_v2() {
        let bytes = include_bytes!("asn1/testdata/ed25519-p8v2.bin");
        let key = Ed25519SigningKey::from_pkcs8_der(bytes).unwrap();

        let mut buf = vec![0; bytes.len()];
        assert_eq!(
            key.to_pkcs8_der(true, &mut buf[..bytes.len() - 1]),
            Err(Error::WrongLength)
        );
        let buf = key.to_pkcs8_der(true, &mut buf).unwrap();
        assert_eq!(bytes, buf);
    }

    #[test]
    fn spki_encode_length() {
        let pk = Ed25519SigningKey::generate().unwrap().public_key();
        assert_eq!(
            pk.to_spki_der(&mut [0u8; 32]).unwrap_err(),
            Error::WrongLength
        );
    }

    #[test]
    fn pkcs8_public_key_wrong() {
        let mut bytes = include_bytes!("asn1/testdata/ed25519-p8v2.bin").to_vec();
        bytes[52] ^= 0x01;
        assert_eq!(
            Ed25519SigningKey::from_pkcs8_der(&bytes).err(),
            Some(KeyFormatError::MismatchedPkcs8PublicKey.into())
        );
    }

    #[test]
    fn verifying_key_from_bytes() {
        const GOOD: &[u8] = &[
            0x53, 0x0e, 0x81, 0x33, 0x75, 0x16, 0x14, 0xbe, 0x84, 0x26, 0x71, 0x59, 0x50, 0xc2,
            0x49, 0x71, 0x67, 0x0c, 0xb5, 0xd9, 0x89, 0x14, 0xc0, 0xf0, 0xbd, 0xb4, 0xd9, 0x49,
            0x05, 0xee, 0x0d, 0x9e,
        ];
        assert!(Ed25519VerifyingKey::from_bytes(GOOD).is_ok());
        assert_eq!(
            Ed25519VerifyingKey::from_bytes(&[0xff; 32]).err(),
            Some(KeyFormatError::NotOnCurve.into())
        );

        // Each point has one encoding, `y` below `p`. A sign on `x = 0` (where
        // `y = ±1`) and `y = p` or `p + 1` encode points of small order, which
        // `small_order` covers.
        let mut y_three = [0; 32];
        y_three[0] = 3;
        let mut y_p_plus_three = [0xff; 32];
        y_p_plus_three[0] = 0xf0;
        y_p_plus_three[31] = 0x7f;
        let mut y_two = [0; 32];
        y_two[0] = 2;
        for (y, ok) in [
            (y_three, true),
            (y_p_plus_three, false),
            // No `x` has `y = 2`.
            (y_two, false),
        ] {
            let result = Ed25519VerifyingKey::from_bytes(&y);
            assert_eq!(
                result.err(),
                (!ok).then_some(KeyFormatError::NotOnCurve.into()),
                "{y:x?}"
            );
        }

        assert_eq!(
            Ed25519VerifyingKey::from_bytes(&[0; 31]).err(),
            Some(KeyFormatError::WrongLength.into())
        );
        assert_eq!(
            Ed25519VerifyingKey::from_bytes(&[0; 33]).err(),
            Some(KeyFormatError::WrongLength.into())
        );
    }

    #[test]
    fn small_order() {
        // libsodium's list: each `y` of a small-order point that fits in 255
        // bits, with either sign, eight of them the canonical encodings of
        // the points of order dividing 8.
        let mut points = 0;
        for y in [
            "0000000000000000000000000000000000000000000000000000000000000000",
            "0100000000000000000000000000000000000000000000000000000000000000",
            "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
            "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
            "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            "eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        ] {
            for sign in [0, 0x80] {
                let mut bytes: [u8; 32] = hex::decode(y).unwrap().try_into().unwrap();
                bytes[31] |= sign;
                points += usize::from(ed25519::VerifyingKey::from_bytes(&bytes).is_ok());
                assert_eq!(
                    Ed25519VerifyingKey::from_bytes(&bytes).err(),
                    Some(KeyFormatError::SmallOrder.into()),
                    "{bytes:x?}"
                );
            }
        }
        assert_eq!(points, 8);
    }
}
