// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::asn1::{self, Type};
use super::curve::{
    Curve, MAX_SCALAR_LEN, MAX_UNCOMPRESSED_PUBLIC_KEY_LEN, PrivateKey, PublicKey, Scalar,
};
use super::hash::{Hash, SignatureHash};
use super::hmac_drbg::HmacDrbg;
use super::sec1;
use crate::error::{Error, KeyFormatError};
use crate::low::{Entry, ReuseCache};
use crate::mid::rng::{RandomSource, SystemRandom};

/// An ECDSA signing key, on curve `C`.
pub(crate) struct SigningKey<C: Curve> {
    // Private, so the scalar cannot be reused for ECDH.
    private_key: C::PrivateKey,
    // Deriving the public key costs a scalar multiplication, which signing
    // never needs, so it is done when the public key is first read.
    public_key: ReuseCache<EncodedPoint>,
}

/// A public key's X9.62 uncompressed encoding, on any curve.
#[derive(Clone, Copy)]
pub(crate) struct EncodedPoint {
    bytes: [u8; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN],
    len: usize,
}

impl Default for EncodedPoint {
    fn default() -> Self {
        Self {
            bytes: [0; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN],
            len: 0,
        }
    }
}

impl AsRef<[u8]> for EncodedPoint {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl<C: Curve> SigningKey<C> {
    fn new(private_key: C::PrivateKey) -> Self {
        Self {
            private_key,
            public_key: ReuseCache::new(),
        }
    }

    /// Generate a new random key.
    pub(crate) fn generate() -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        Ok(Self::new(C::generate_random_key(&mut SystemRandom)?))
    }

    /// Load an ECDSA private key in PKCS#8 format.
    pub(crate) fn from_pkcs8_der(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        Self::from_decoded(sec1::decode_pkcs8(bytes, &C::oid())?)
    }

    /// Encode this private key in PKCS#8 DER format.
    ///
    /// The encoding is written to the start of `output`, and the used span is
    /// returned.  [`Error::WrongLength`] is returned if `output` is not sufficient
    /// to contain the full encoding.
    pub(crate) fn to_pkcs8_der<'a>(&self, output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let mut private_key = [0u8; MAX_SCALAR_LEN];
        let private_key = self.private_key.encode(&mut private_key)?;
        sec1::encode_pkcs8(
            private_key,
            self.public_key_uncompressed().as_ref(),
            C::oid(),
            output,
        )
    }

    /// Load an ECDSA private key in SEC.1 format.
    pub(crate) fn from_sec1_der(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        Self::from_decoded(sec1::decode(bytes, &C::oid())?)
    }

    fn from_decoded(decoded: sec1::Decoded<'_>) -> Result<Self, Error> {
        let key = Self::new(C::PrivateKey::from_bytes(decoded.private_key)?);
        match decoded.public_key {
            Some(public_key) if !key.is_public_key(public_key) => {
                Err(KeyFormatError::MismatchedSec1PublicKey.into())
            }
            _ => Ok(key),
        }
    }

    /// Load an ECDSA private key from its fixed-length big-endian scalar,
    /// checking it against `public_key`, an X9.62 uncompressed or compressed
    /// point.
    pub(crate) fn from_private_key_and_public_key(
        private_key: &[u8],
        public_key: &[u8],
    ) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        if private_key.len() != C::Scalar::LEN_BYTES {
            return Err(KeyFormatError::WrongLength.into());
        }

        let key = Self::new(C::PrivateKey::from_bytes(private_key)?);
        match key.is_public_key(public_key) {
            true => Ok(key),
            false => Err(KeyFormatError::MismatchedPublicKey.into()),
        }
    }

    /// Whether `encoded`, an X9.62 uncompressed or compressed point, is this
    /// key's public key, as [`sec1::is_public_key`] decides, or for an
    /// uncompressed point the curve's `public_key_is_uncompressed` where it
    /// has one.
    fn is_public_key(&self, encoded: &[u8]) -> bool {
        // Kept as the public key once it matches, so it is not derived again.
        #[cfg(rind_backend = "x86_64")]
        if let [0x04, ..] = encoded
            && let Some(matches) = self.private_key.public_key_is_uncompressed(encoded)
        {
            if matches {
                self.public_key.get_or_build_now(|| {
                    let mut point = EncodedPoint::default();
                    point.bytes[..encoded.len()].copy_from_slice(encoded);
                    point.len = encoded.len();
                    point
                });
            }
            return matches;
        }
        sec1::is_public_key(self.public_key_uncompressed().as_ref(), encoded)
    }

    /// Encode this private key as its fixed-length big-endian scalar, still
    /// secret, which [`Self::from_private_key_and_public_key`] loads.
    pub(crate) fn to_scalar<'a>(&self, output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        self.private_key.encode(output)
    }

    /// This private key's public key, as an X9.62 uncompressed point.
    pub(crate) fn public_key_uncompressed(&self) -> EncodedPoint {
        self.public_key.get_or_build_now(|| {
            let mut point = EncodedPoint::default();
            point.len = self
                .private_key
                .public_key_encode_uncompressed(&mut point.bytes)
                .expect("sized for the largest curve")
                .len();
            point
        })
    }

    /// Encode this private key's corresponding public key in SubjectPublicKeyInfo DER format.
    ///
    /// The encoding is written to the start of `output`, and the used span is
    /// returned.  [`Error::WrongLength`] is returned if `output` is not sufficient
    /// to contain the full encoding.
    pub(crate) fn to_spki_der<'a>(&self, output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let point = self.public_key_uncompressed();
        let spki = asn1::pkix::SubjectPublicKeyInfo {
            algorithm: asn1::pkix::AlgorithmIdentifier {
                algorithm: asn1::oid::id_ecPublicKey.clone(),
                parameters: Some(asn1::Any::ObjectId(C::oid())),
            },
            subjectPublicKey: asn1::BitString::new(point.as_ref()),
        };

        let len = spki
            .encode(&mut asn1::Encoder::new(output))
            .map_err(|_| Error::WrongLength)?;
        Ok(&output[..len])
    }

    /// ECDSA signing, returning a fixed-length signature.
    ///
    /// The `message` is hashed using `H`.
    ///
    /// `signature` is the output buffer; `Error::WrongLength` is returned
    /// if it is not long enough.  The used prefix of this buffer is returned
    /// on success.
    pub(crate) fn sign<'a, H: SignatureHash>(
        &self,
        message: &[u8],
        signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let mut random = [0u8; 16];
        SystemRandom.fill(&mut random)?;
        self.rfc6979_sign_with_random::<H>(message, &random, signature)
    }

    /// [`Self::sign()`] with `random` in place of the system's, so the FIPS
    /// module's self-test knows its answer.
    #[cfg(any(test, rind_fips))]
    pub(crate) fn sign_with_random<'a, H: SignatureHash>(
        &self,
        message: &[u8],
        random: &[u8; 16],
        signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        self.rfc6979_sign_with_random::<H>(message, random, signature)
    }

    /// ECDSA signing, returning a DER-encoded ASN.1 signature.
    ///
    /// This calls [`Self::sign()`] and then does a straightforward conversion
    /// from fixed length to ASN.1 -- see that function's documentation for more.
    pub(crate) fn sign_asn1<'a, H: SignatureHash>(
        &self,
        message: &[u8],
        asn1_signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let mut fixed_sig = [0u8; MAX_SCALAR_LEN * 2];
        let fixed_sig = self.sign::<H>(message, &mut fixed_sig)?;

        Self::fixed_to_asn1(fixed_sig, asn1_signature)
    }

    /// ECDSA signing of `digest`, a hash of the message, returning a
    /// fixed-length signature, as [`Self::sign()`] does for a message.
    ///
    /// A `digest` longer than the scalar is truncated to its leftmost bytes,
    /// as FIPS 186-5 truncates it to bits for every digest rind makes, which
    /// are at most 64 bytes; see [`hash_to_scalar()`]. The nonce comes from HMAC_DRBG over `H`, which
    /// need not be the digest's hash: RFC 6979 uses the message's for its
    /// test vectors, but any PRF serves.
    pub(crate) fn sign_digest<'a, H: Hash>(
        &self,
        digest: &[u8],
        signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let mut random = [0u8; 16];
        SystemRandom.fill(&mut random)?;
        self.rfc6979_sign_digest_with_random::<H>(digest, &random, signature)
    }

    /// [`Self::sign_digest()`], returning a DER-encoded ASN.1 signature.
    pub(crate) fn sign_asn1_digest<'a, H: Hash>(
        &self,
        digest: &[u8],
        asn1_signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let mut fixed_sig = [0u8; MAX_SCALAR_LEN * 2];
        let fixed_sig = self.sign_digest::<H>(digest, &mut fixed_sig)?;

        Self::fixed_to_asn1(fixed_sig, asn1_signature)
    }

    fn fixed_to_asn1<'a>(
        fixed_signature: &[u8],
        asn1_signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let mut r = [0u8; MAX_SCALAR_LEN + 1];
        let mut s = [0u8; MAX_SCALAR_LEN + 1];
        let r = asn1::Integer::new_positive(&mut r, &fixed_signature[..C::Scalar::LEN_BYTES]);
        let s = asn1::Integer::new_positive(&mut s, &fixed_signature[C::Scalar::LEN_BYTES..]);

        let sig = asn1::pkix::EcdsaSigValue { r, s };
        let sig_len = sig
            .encode(&mut asn1::Encoder::new(asn1_signature))
            .map_err(|_| Error::WrongLength)?;
        Ok(&asn1_signature[..sig_len])
    }

    /// This is RFC6979 deterministic ECDSA signing, _with added randomness_.
    ///
    /// Rationale: deterministic ECDSA is good for implementation quality (we
    /// can test and validate the selection of `k` is good, and that is
    /// absolutely crucial), but theoretically behaves worse under fault attacks.
    ///
    /// The added randomness is non-critical, assuming the design of HMAC_DRBG
    /// is OK.
    ///
    /// RFC6979 allows for this: see section 3.6:
    /// <https://datatracker.ietf.org/doc/html/rfc6979#section-3.6>.  And HMAC_DRBG
    /// also allows for it, it is the `personalization_string` input.
    fn rfc6979_sign_with_random<'a, H: Hash>(
        &self,
        message: &[u8],
        random: &[u8],
        signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let Some(output) = signature.get_mut(..C::Scalar::LEN_BYTES * 2) else {
            return Err(Error::WrongLength);
        };

        let hash = H::hash(message);

        let mut encoded_private_key_buf = [0u8; MAX_SCALAR_LEN];
        let encoded_private_key = self.private_key.encode(&mut encoded_private_key_buf)?;

        let e = hash_to_scalar::<C>(hash.as_ref())?;
        let mut e_bytes = [0u8; MAX_SCALAR_LEN];
        e.write_bytes(&mut e_bytes[..C::Scalar::LEN_BYTES]);
        let mut rng = HmacDrbg::<H>::new(
            encoded_private_key,
            &e_bytes[..C::Scalar::LEN_BYTES],
            random,
        );

        let (r, s) = self.sign_with_nonces(&e, &mut rng)?;

        r.write_bytes(&mut output[..C::Scalar::LEN_BYTES]);
        s.write_bytes(&mut output[C::Scalar::LEN_BYTES..]);
        Ok(&output[..C::Scalar::LEN_BYTES * 2])
    }

    /// [`Self::rfc6979_sign_with_random()`] for a message already hashed.
    ///
    /// That function does not call this one, as `proofs/` checks its
    /// translation as it stands.
    fn rfc6979_sign_digest_with_random<'a, H: Hash>(
        &self,
        digest: &[u8],
        random: &[u8],
        signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let Some(output) = signature.get_mut(..C::Scalar::LEN_BYTES * 2) else {
            return Err(Error::WrongLength);
        };

        let mut encoded_private_key_buf = [0u8; MAX_SCALAR_LEN];
        let encoded_private_key = self.private_key.encode(&mut encoded_private_key_buf)?;

        let e = hash_to_scalar::<C>(digest)?;
        let mut e_bytes = [0u8; MAX_SCALAR_LEN];
        e.write_bytes(&mut e_bytes[..C::Scalar::LEN_BYTES]);
        let mut rng = HmacDrbg::<H>::new(
            encoded_private_key,
            &e_bytes[..C::Scalar::LEN_BYTES],
            random,
        );

        let (r, s) = self.sign_with_nonces(&e, &mut rng)?;

        r.write_bytes(&mut output[..C::Scalar::LEN_BYTES]);
        s.write_bytes(&mut output[C::Scalar::LEN_BYTES..]);
        Ok(&output[..C::Scalar::LEN_BYTES * 2])
    }

    /// Sign the message representative `e`, returning `(r, s)`.
    ///
    /// Draws nonces from `nonces` until both `r` and `s` are nonzero, as
    /// FIPS 186-5 section 6.4.1 requires.
    fn sign_with_nonces(
        &self,
        e: &C::Scalar,
        nonces: &mut impl RandomSource,
    ) -> Result<(C::Scalar, C::Scalar), Error> {
        loop {
            let k = C::generate_random_key(nonces)?;
            let r = k.public_key_x_scalar();
            if r.is_zero() {
                continue;
            }
            let s = self.private_key.raw_ecdsa_sign(&k, e, &r);
            if !s.is_zero() {
                return Ok((r, s));
            }
        }
    }
}

/// An ECDSA verification key, on curve `C`.
pub(crate) struct VerifyingKey<C: Curve> {
    public_key: C::PublicKey,
}

impl<C: Curve> Clone for VerifyingKey<C>
where
    C::PublicKey: Clone,
{
    fn clone(&self) -> Self {
        Self {
            public_key: self.public_key.clone(),
        }
    }
}

impl<C: Curve> VerifyingKey<C> {
    /// Create a `VerifyingKey` by decoding an X9.62 uncompressed point.
    pub(crate) fn from_x962_uncompressed(encoded: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        C::PublicKey::from_x962_uncompressed(encoded).map(|public_key| Self { public_key })
    }

    /// Verify an ECDSA fixed-length signature.
    ///
    /// The `message` is hashed with `H`.
    ///
    /// `signature` is the purported signature.
    ///
    /// Fails with [`Error::BadSignature`] unless the signature is valid.
    pub(crate) fn verify<H: SignatureHash>(
        &self,
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        if signature.len() != C::Scalar::LEN_BYTES * 2 {
            return Err(Error::BadSignature);
        }

        // 1. If r and s are not both integers in the interval [1, n − 1], output “invalid” and stop.
        let r = C::Scalar::from_bytes_checked(&signature[..C::Scalar::LEN_BYTES])
            .map_err(|_| Error::BadSignature)?;
        let s = C::Scalar::from_bytes_checked(&signature[C::Scalar::LEN_BYTES..])
            .map_err(|_| Error::BadSignature)?;

        // 2. Use the hash function established during the setup procedure to compute the hash value:
        let hash = H::hash(message);

        // 3. Derive an integer e from H as follows: (...)
        let e = hash_to_scalar::<C>(hash.as_ref())?;

        // 4. - 8. in `raw_ecdsa_verify`
        self.public_key.raw_ecdsa_verify(&r, &s, &e)
    }

    /// Verify an ECDSA ASN.1-encoded signature.
    ///
    /// This does a straightforward conversion from ASN.1 to fixed length,
    /// and then calls [`Self::verify()`] -- see the documentation for more.
    pub(crate) fn verify_asn1<H: SignatureHash>(
        &self,
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        let mut fixed = [0u8; MAX_SCALAR_LEN * 2];
        self.verify::<H>(message, Self::asn1_to_fixed(signature, &mut fixed)?)
    }

    /// Verify an ECDSA fixed-length signature over `digest`, a hash of the
    /// message, as [`Self::verify()`] does over a message.
    ///
    /// That function does not call this one, as `proofs/` checks its
    /// translation as it stands.
    pub(crate) fn verify_digest(&self, digest: &[u8], signature: &[u8]) -> Result<(), Error> {
        let _entry = Entry::new_public();
        if signature.len() != C::Scalar::LEN_BYTES * 2 {
            return Err(Error::BadSignature);
        }

        let r = C::Scalar::from_bytes_checked(&signature[..C::Scalar::LEN_BYTES])
            .map_err(|_| Error::BadSignature)?;
        let s = C::Scalar::from_bytes_checked(&signature[C::Scalar::LEN_BYTES..])
            .map_err(|_| Error::BadSignature)?;
        let e = hash_to_scalar::<C>(digest)?;
        self.public_key.raw_ecdsa_verify(&r, &s, &e)
    }

    /// [`Self::verify_digest()`] of an ASN.1-encoded signature.
    pub(crate) fn verify_asn1_digest(&self, digest: &[u8], signature: &[u8]) -> Result<(), Error> {
        let _entry = Entry::new_public();
        let mut fixed = [0u8; MAX_SCALAR_LEN * 2];
        self.verify_digest(digest, Self::asn1_to_fixed(signature, &mut fixed)?)
    }

    /// Converts an ASN.1 signature to fixed length in `fixed`, returning the
    /// used span.
    fn asn1_to_fixed<'a>(signature: &[u8], fixed: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let sig =
            asn1::pkix::EcdsaSigValue::from_bytes(signature).map_err(|_| Error::BadSignature)?;
        if sig.r.is_negative() || sig.s.is_negative() {
            return Err(Error::BadSignature);
        }

        let fixed = &mut fixed[..C::Scalar::LEN_BYTES * 2];
        write_fixed(&mut fixed[..C::Scalar::LEN_BYTES], sig.r.as_ref())?;
        write_fixed(&mut fixed[C::Scalar::LEN_BYTES..], sig.s.as_ref())?;
        Ok(fixed)
    }
}

/// FIPS 186-5's `e`: `hash`'s leftmost bits, as many as the order has,
/// reduced.
///
/// This truncates to bytes, so it is wrong only for a hash longer than P-521's
/// 66-byte scalar, whose order has 521 bits. No `Digest` is that long.
fn hash_to_scalar<C: Curve>(hash: &[u8]) -> Result<C::Scalar, Error> {
    let hash = if hash.len() > C::Scalar::LEN_BYTES {
        &hash[..C::Scalar::LEN_BYTES]
    } else {
        hash
    };
    Ok(C::Scalar::from_bytes_reduced(hash))
}

fn write_fixed(out: &mut [u8], mut value: &[u8]) -> Result<(), Error> {
    // strip (one) leading zero byte
    if !value.is_empty() && value[0] == 0x00 {
        value = &value[1..];
    }

    // if it doesn't fit, it is illegally larger than the largest scalar, so
    // cannot be an integer mod n.
    if out.len() < value.len() {
        return Err(Error::BadSignature);
    }

    let (prefix, suffix) = out.split_at_mut(out.len() - value.len());
    prefix.fill(0x00);
    suffix.copy_from_slice(value);
    Ok(())
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::high::curve::Curve;
    use crate::high::{curve, hash};
    use crate::mid::rng::SliceRandomSource;
    use crate::test::*;

    /// Calls `$f::<curve, hash>($args)` for an ACVP group's curve and hash.
    macro_rules! acvp_dispatch {
        ($group:expr, $f:ident($($args:expr),*)) => {
            match ($group.str("curve"), $group.str("hashAlg")) {
                ("P-256", "SHA2-256") => $f::<curve::P256, hash::Sha256>($($args),*),
                ("P-256", "SHA2-384") => $f::<curve::P256, hash::Sha384>($($args),*),
                ("P-256", "SHA2-512") => $f::<curve::P256, hash::Sha512>($($args),*),
                ("P-384", "SHA2-256") => $f::<curve::P384, hash::Sha256>($($args),*),
                ("P-384", "SHA2-384") => $f::<curve::P384, hash::Sha384>($($args),*),
                ("P-384", "SHA2-512") => $f::<curve::P384, hash::Sha512>($($args),*),
                ("P-521", "SHA2-256") => $f::<curve::P521, hash::Sha256>($($args),*),
                ("P-521", "SHA2-384") => $f::<curve::P521, hash::Sha384>($($args),*),
                ("P-521", "SHA2-512") => $f::<curve::P521, hash::Sha512>($($args),*),
                other => panic!("unexpected curve and hash {other:?}"),
            }
        };
    }

    /// `value` left-padded to `len` bytes, or `None` if it is longer.
    fn acvp_fixed(value: Vec<u8>, len: usize) -> Option<Vec<u8>> {
        let pad = len.checked_sub(value.len())?;
        Some([vec![0; pad], value].concat())
    }

    /// The X9.62 uncompressed encoding of a test's `qx` and `qy`, or `None`
    /// if either is too long for curve `C`.
    fn acvp_point<C: Curve>(test: &serde_json::Value) -> Option<Vec<u8>> {
        let x = acvp_fixed(test.hex("qx"), C::Scalar::LEN_BYTES)?;
        let y = acvp_fixed(test.hex("qy"), C::Scalar::LEN_BYTES)?;
        Some([vec![0x04], x, y].concat())
    }

    fn acvp_signing_key<C: Curve>(d: Vec<u8>) -> SigningKey<C> {
        let d = acvp_fixed(d, C::Scalar::LEN_BYTES).unwrap();
        SigningKey::new(C::PrivateKey::from_bytes(&d).unwrap())
    }

    /// `r || s`, each padded to curve `C`'s scalar length.
    fn acvp_signature<C: Curve>(test: &serde_json::Value) -> Option<Vec<u8>> {
        let r = acvp_fixed(test.hex("r"), C::Scalar::LEN_BYTES)?;
        let s = acvp_fixed(test.hex("s"), C::Scalar::LEN_BYTES)?;
        Some([r, s].concat())
    }

    #[test]
    fn acvp_key_gen() {
        fn check<C: Curve>(test: &serde_json::Value) {
            let key = acvp_signing_key::<C>(test.hex("d"));
            assert_eq!(
                key.public_key_uncompressed().as_ref(),
                acvp_point::<C>(test).unwrap()
            );
        }
        for group in acvp("ECDSA-KeyGen-FIPS186-5") {
            for test in group.tests() {
                match group.str("curve") {
                    "P-256" => check::<curve::P256>(test),
                    "P-384" => check::<curve::P384>(test),
                    "P-521" => check::<curve::P521>(test),
                    other => panic!("unexpected curve {other}"),
                }
            }
        }
    }

    #[test]
    fn acvp_key_ver() {
        fn valid<C: Curve>(test: &serde_json::Value) -> bool {
            acvp_point::<C>(test)
                .is_some_and(|point| VerifyingKey::<C>::from_x962_uncompressed(&point).is_ok())
        }
        for group in acvp("ECDSA-KeyVer-FIPS186-5") {
            for test in group.tests() {
                let valid = match group.str("curve") {
                    "P-256" => valid::<curve::P256>(test),
                    "P-384" => valid::<curve::P384>(test),
                    "P-521" => valid::<curve::P521>(test),
                    other => panic!("unexpected curve {other}"),
                };
                assert_eq!(valid, test.flag("testPassed"), "{}", test.str("reason"));
            }
        }
    }

    /// Signs with each test's nonce `k`, which ACVP gives with its answers.
    /// It skips the random nonce's mapping, which for P-521 keeps the top
    /// 521 bits of 66 bytes rather than reading `k` as given.
    #[test]
    fn acvp_sig_gen() {
        fn check<C: Curve, H: SignatureHash>(group: &serde_json::Value) {
            let key = acvp_signing_key::<C>(group.hex("d"));
            assert_eq!(
                key.public_key_uncompressed().as_ref(),
                acvp_point::<C>(group).unwrap()
            );
            for test in group.tests() {
                let e = hash_to_scalar::<C>(H::hash(&test.hex("message")).as_ref()).unwrap();
                let k = acvp_fixed(test.hex("k"), C::Scalar::LEN_BYTES).unwrap();
                let k = C::PrivateKey::from_bytes(&k).unwrap();
                let r = k.public_key_x_scalar();
                let s = key.private_key.raw_ecdsa_sign(&k, &e, &r);
                let mut signature = vec![0; C::Scalar::LEN_BYTES * 2];
                r.write_bytes(&mut signature[..C::Scalar::LEN_BYTES]);
                s.write_bytes(&mut signature[C::Scalar::LEN_BYTES..]);
                assert_eq!(signature, acvp_signature::<C>(test).unwrap());
            }
        }
        for group in acvp("ECDSA-SigGen-FIPS186-5") {
            assert!(!group.flag("componentTest"));
            acvp_dispatch!(group, check(&group));
        }
    }

    /// FIPS 186-5's deterministic ECDSA is RFC 6979's, which rind's signing
    /// is with no added randomness.
    #[test]
    fn acvp_det_sig_gen() {
        fn check<C: Curve, H: SignatureHash>(group: &serde_json::Value) {
            let key = acvp_signing_key::<C>(group.hex("d"));
            for test in group.tests() {
                let mut signature = vec![0; C::Scalar::LEN_BYTES * 2];
                key.rfc6979_sign_with_random::<H>(&test.hex("message"), &[], &mut signature)
                    .unwrap();
                assert_eq!(signature, acvp_signature::<C>(test).unwrap());
            }
        }
        for group in acvp("DetECDSA-SigGen-FIPS186-5") {
            assert!(!group.flag("componentTest"));
            acvp_dispatch!(group, check(&group));
        }
    }

    #[test]
    fn acvp_sig_ver() {
        fn check<C: Curve, H: SignatureHash>(group: &serde_json::Value) {
            for test in group.tests() {
                let valid = acvp_point::<C>(test)
                    .and_then(|point| VerifyingKey::<C>::from_x962_uncompressed(&point).ok())
                    .zip(acvp_signature::<C>(test))
                    .is_some_and(|(key, signature)| {
                        key.verify::<H>(&test.hex("message"), &signature).is_ok()
                    });
                assert_eq!(valid, test.flag("testPassed"), "{}", test.str("reason"));
            }
        }
        for group in acvp("ECDSA-SigVer-FIPS186-5") {
            acvp_dispatch!(group, check(&group));
        }
    }

    #[test]
    fn smoke_test_loading_keys() {
        check_sign_verify::<curve::P256>(
            SigningKey::<curve::P256>::from_pkcs8_der(include_bytes!("ecdsa/secp256r1.pkcs8.der"))
                .unwrap()
                .private_key,
        );
        check_pairwise_pkcs8::<curve::P256>(include_bytes!("ecdsa/secp256r1.pkcs8.der"));

        check_sign_verify::<curve::P256>(
            SigningKey::<curve::P256>::from_sec1_der(include_bytes!("ecdsa/secp256r1.der"))
                .unwrap()
                .private_key,
        );
        check_pairwise_sec1::<curve::P256>(include_bytes!("ecdsa/secp256r1.der"));

        assert_eq!(
            SigningKey::<curve::P256>::from_sec1_der(include_bytes!("ecdsa/secp384r1.der")).err(),
            Some(KeyFormatError::MismatchedSec1Curve.into()),
        );
        assert_eq!(
            SigningKey::<curve::P256>::from_sec1_der(include_bytes!(
                "ecdsa/secp256r1.wrong-public-key.der"
            ))
            .err(),
            Some(KeyFormatError::MismatchedSec1PublicKey.into()),
        );
        assert_eq!(
            SigningKey::<curve::P256>::from_sec1_der(include_bytes!(
                "ecdsa/secp256r1.wrong-version.der"
            ))
            .err(),
            Some(KeyFormatError::Asn1(asn1::Error::UnhandledEnumValue).into()),
        );

        check_sign_verify::<curve::P384>(
            SigningKey::<curve::P384>::from_pkcs8_der(include_bytes!("ecdsa/secp384r1.pkcs8.der"))
                .unwrap()
                .private_key,
        );
        check_pairwise_pkcs8::<curve::P384>(include_bytes!("ecdsa/secp384r1.pkcs8.der"));

        check_sign_verify::<curve::P384>(
            SigningKey::<curve::P384>::from_sec1_der(include_bytes!("ecdsa/secp384r1.der"))
                .unwrap()
                .private_key,
        );
        check_pairwise_sec1::<curve::P384>(include_bytes!("ecdsa/secp384r1.der"));

        assert_eq!(
            SigningKey::<curve::P384>::from_sec1_der(include_bytes!("ecdsa/secp256r1.der")).err(),
            Some(KeyFormatError::MismatchedSec1Curve.into()),
        );

        check_sign_verify::<curve::P521>(
            SigningKey::<curve::P521>::from_pkcs8_der(include_bytes!("ecdsa/secp521r1.pkcs8.der"))
                .unwrap()
                .private_key,
        );
        check_pairwise_pkcs8::<curve::P521>(include_bytes!("ecdsa/secp521r1.pkcs8.der"));

        check_sign_verify::<curve::P521>(
            SigningKey::<curve::P521>::from_sec1_der(include_bytes!("ecdsa/secp521r1.der"))
                .unwrap()
                .private_key,
        );
        check_pairwise_sec1::<curve::P521>(include_bytes!("ecdsa/secp521r1.der"));

        assert_eq!(
            SigningKey::<curve::P521>::from_sec1_der(include_bytes!("ecdsa/secp384r1.der")).err(),
            Some(KeyFormatError::MismatchedSec1Curve.into()),
        );
    }

    #[test]
    fn smoke_test_ecdsa_sign() {
        let k = SigningKey::<curve::P256>::generate().unwrap();
        check_sign_verify::<curve::P256>(k.private_key);

        let k = SigningKey::<curve::P384>::generate().unwrap();
        check_sign_verify::<curve::P384>(k.private_key);

        let k = SigningKey::<curve::P521>::generate().unwrap();
        check_sign_verify::<curve::P521>(k.private_key);
    }

    #[test]
    fn sign_retries_when_s_is_zero() {
        use crate::mid::p256::{Scalar, StaticPrivateKey};

        let k1 = [0x11u8; 32];
        let k2 = [0x22u8; 32];
        let e = Scalar::from_bytes_checked(&[0x33; 32]).unwrap();
        let r1 = StaticPrivateKey::from_bytes(&k1)
            .unwrap()
            .public_key_x_scalar();

        // d = -e / r1 zeroes s = (e + r1 * d) / k1 for the first nonce.
        // raw_ecdsa_sign computes d as (0 + (n - 1) * e) / r1.
        let n_minus_1 = Scalar::from_bytes_checked(
            &hex::decode("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550")
                .unwrap(),
        )
        .unwrap();
        let d = StaticPrivateKey::from_bytes(&e.as_bytes())
            .unwrap()
            .raw_ecdsa_sign(
                &StaticPrivateKey::from_bytes(&r1.as_bytes()).unwrap(),
                &Scalar::from_bytes_reduced(&[0; 32]).unwrap(),
                &n_minus_1,
            );
        let sk =
            SigningKey::<curve::P256>::new(StaticPrivateKey::from_bytes(&d.as_bytes()).unwrap());
        let k1_key = StaticPrivateKey::from_bytes(&k1).unwrap();
        assert!(sk.private_key.raw_ecdsa_sign(&k1_key, &e, &r1).is_zero());

        let nonces = [k1, k2].concat();
        let (r, s) = sk
            .sign_with_nonces(&e, &mut SliceRandomSource(&nonces))
            .unwrap();
        let r2 = StaticPrivateKey::from_bytes(&k2)
            .unwrap()
            .public_key_x_scalar();
        assert_eq!(r.as_bytes(), r2.as_bytes());
        VerifyingKey::<curve::P256>::from_x962_uncompressed(sk.public_key_uncompressed().as_ref())
            .unwrap()
            .public_key
            .raw_ecdsa_verify(&r, &s, &e)
            .unwrap();
    }

    fn check_sign_verify<C: Curve>(private_key: C::PrivateKey) {
        let mut public_key = [0u8; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN];
        let public_key = private_key
            .public_key_encode_uncompressed(&mut public_key)
            .unwrap();
        let sk = SigningKey::<C>::new(private_key);
        let vk = VerifyingKey::<C> {
            public_key: C::PublicKey::from_x962_uncompressed(public_key).unwrap(),
        };

        let mut buffer = [0u8; 256];
        let message = b"hello world";

        let signature = sk.sign::<hash::Sha256>(message, &mut buffer).unwrap();
        vk.verify::<hash::Sha256>(message, signature).unwrap();

        let signature = sk.sign::<hash::Sha384>(message, &mut buffer).unwrap();
        vk.verify::<hash::Sha384>(message, signature).unwrap();

        let signature = sk.sign::<hash::Sha512>(message, &mut buffer).unwrap();
        vk.verify::<hash::Sha512>(message, signature).unwrap();

        if std::env::var_os("SLOW_TESTS").is_some() {
            // check for invalid asn1 with p=1/256
            for _ in 0..1024 {
                let signature = sk.sign_asn1::<hash::Sha256>(message, &mut buffer).unwrap();
                vk.verify_asn1::<hash::Sha256>(message, signature).unwrap();
            }
        }

        let signature = sk.sign_asn1::<hash::Sha384>(message, &mut buffer).unwrap();
        vk.verify_asn1::<hash::Sha384>(message, signature).unwrap();

        let signature = sk.sign_asn1::<hash::Sha512>(message, &mut buffer).unwrap();
        vk.verify_asn1::<hash::Sha512>(message, signature).unwrap();

        assert_eq!(
            sk.sign_asn1::<hash::Sha256>(message, &mut [0u8; 8]),
            Err(Error::WrongLength)
        );
        assert_eq!(sk.to_spki_der(&mut [0u8; 8]), Err(Error::WrongLength));
    }

    fn check_pairwise_sec1<C: Curve>(sec1_der: &[u8]) {
        let loaded = SigningKey::<C>::from_sec1_der(sec1_der).unwrap();
        let mut buf = [0u8; 256];
        assert!(buf.len() > sec1_der.len());
        let mut scalar = [0u8; MAX_SCALAR_LEN];
        let scalar = loaded.to_scalar(&mut scalar).unwrap();
        let public_key = loaded.public_key_uncompressed();
        let public_key = public_key.as_ref();
        let encoded = sec1::encode(scalar, public_key, Some(C::oid()), &mut buf).unwrap();
        assert_eq!(sec1_der, encoded);
        assert_eq!(
            sec1::encode(
                scalar,
                public_key,
                Some(C::oid()),
                &mut buf[..sec1_der.len() - 1]
            ),
            Err(Error::WrongLength)
        );
    }

    fn check_pairwise_pkcs8<C: Curve>(pkcs8_der: &[u8]) {
        let loaded = SigningKey::<C>::from_pkcs8_der(pkcs8_der).unwrap();
        let mut buf = [0u8; 256];
        assert!(buf.len() > pkcs8_der.len());
        let encoded = loaded.to_pkcs8_der(&mut buf).unwrap();
        assert_eq!(pkcs8_der, encoded);
        assert_eq!(
            loaded.to_pkcs8_der(&mut buf[..pkcs8_der.len() - 1]),
            Err(Error::WrongLength)
        );
    }

    #[test]
    fn rejects_invalid_asn1_sigs() {
        let private_key =
            SigningKey::<curve::P256>::from_pkcs8_der(include_bytes!("ecdsa/secp256r1.pkcs8.der"))
                .unwrap()
                .private_key;

        let mut public_key_buf = [0u8; 128];
        let public_key_buf = private_key
            .public_key_encode_uncompressed(&mut public_key_buf)
            .unwrap();
        let verify = VerifyingKey::<curve::P256> {
            public_key: <curve::P256 as curve::Curve>::PublicKey::from_x962_uncompressed(
                public_key_buf,
            )
            .unwrap(),
        };

        // base case
        verify
            .verify_asn1::<hash::Sha256>(
                b"hello",
                &[
                    0x30, 0x43, 0x02, 0x1f, 0x40, 0x1a, 0x29, 0x85, 0xde, 0xb3, 0x75, 0xd4, 0x81,
                    0x70, 0x6f, 0x6c, 0x26, 0xea, 0x70, 0x44, 0x30, 0xcd, 0xf5, 0x94, 0x9a, 0x3c,
                    0xe3, 0x44, 0x18, 0xe9, 0xd6, 0x73, 0xf9, 0xb0, 0xe6, 0x02, 0x20, 0x4d, 0xd1,
                    0x81, 0x3c, 0xa2, 0xaa, 0x52, 0xc4, 0xff, 0xe0, 0xd6, 0x02, 0xf4, 0xde, 0x4e,
                    0x30, 0x85, 0x2a, 0xfd, 0x31, 0x87, 0xa6, 0x0f, 0xe4, 0xbc, 0x6d, 0x40, 0xff,
                    0x6c, 0x31, 0xb1, 0x9b,
                ],
            )
            .unwrap();

        // r has unnecessary zero
        assert_eq!(
            verify
                .verify_asn1::<hash::Sha256>(
                    b"hello",
                    &[
                        0x30, 0x44, 0x02, 0x20, 0x00, 0x40, 0x1a, 0x29, 0x85, 0xde, 0xb3, 0x75,
                        0xd4, 0x81, 0x70, 0x6f, 0x6c, 0x26, 0xea, 0x70, 0x44, 0x30, 0xcd, 0xf5,
                        0x94, 0x9a, 0x3c, 0xe3, 0x44, 0x18, 0xe9, 0xd6, 0x73, 0xf9, 0xb0, 0xe6,
                        0x02, 0x20, 0x4d, 0xd1, 0x81, 0x3c, 0xa2, 0xaa, 0x52, 0xc4, 0xff, 0xe0,
                        0xd6, 0x02, 0xf4, 0xde, 0x4e, 0x30, 0x85, 0x2a, 0xfd, 0x31, 0x87, 0xa6,
                        0x0f, 0xe4, 0xbc, 0x6d, 0x40, 0xff, 0x6c, 0x31, 0xb1, 0x9b,
                    ],
                )
                .unwrap_err(),
            Error::BadSignature,
        );
    }

    #[test]
    fn rfc6979_test_vectors() {
        // from A.2.5.
        let mut rng = SliceRandomSource(b"\xC9\xAF\xA9\xD8\x45\xBA\x75\x16\x6B\x5C\x21\x57\x67\xB1\xD6\x93\x4E\x50\xC3\xDB\x36\xE8\x9B\x12\x7B\x8A\x62\x2B\x12\x0F\x67\x21");
        let private_key = curve::P256::generate_random_key(&mut rng).unwrap();
        let mut public_key = [0u8; 128];
        let public_key = private_key
            .public_key_encode_uncompressed(&mut public_key)
            .unwrap();
        let k = SigningKey::<curve::P256>::new(private_key);
        let v = VerifyingKey::<curve::P256> {
            public_key: <curve::P256 as curve::Curve>::PublicKey::from_x962_uncompressed(
                public_key,
            )
            .unwrap(),
        };
        let mut signature = [0u8; 64];

        k.rfc6979_sign_with_random::<hash::Sha256>(b"sample", &[], &mut signature)
            .unwrap();
        assert_eq!(
            signature,
            [
                0xef, 0xd4, 0x8b, 0x2a, 0xac, 0xb6, 0xa8, 0xfd, 0x11, 0x40, 0xdd, 0x9c, 0xd4, 0x5e,
                0x81, 0xd6, 0x9d, 0x2c, 0x87, 0x7b, 0x56, 0xaa, 0xf9, 0x91, 0xc3, 0x4d, 0x0e, 0xa8,
                0x4e, 0xaf, 0x37, 0x16, 0xf7, 0xcb, 0x1c, 0x94, 0x2d, 0x65, 0x7c, 0x41, 0xd4, 0x36,
                0xc7, 0xa1, 0xb6, 0xe2, 0x9f, 0x65, 0xf3, 0xe9, 0x00, 0xdb, 0xb9, 0xaf, 0xf4, 0x06,
                0x4d, 0xc4, 0xab, 0x2f, 0x84, 0x3a, 0xcd, 0xa8,
            ]
        );
        v.verify::<hash::Sha256>(b"sample", &signature).unwrap();

        let mut asn1_sig = [0u8; 128];
        let asn1_sig = SigningKey::<curve::P256>::fixed_to_asn1(&signature, &mut asn1_sig).unwrap();
        v.verify_asn1::<hash::Sha256>(b"sample", asn1_sig).unwrap();

        k.rfc6979_sign_with_random::<hash::Sha256>(b"test", &[], &mut signature)
            .unwrap();
        assert_eq!(
            signature,
            [
                0xf1, 0xab, 0xb0, 0x23, 0x51, 0x83, 0x51, 0xcd, 0x71, 0xd8, 0x81, 0x56, 0x7b, 0x1e,
                0xa6, 0x63, 0xed, 0x3e, 0xfc, 0xf6, 0xc5, 0x13, 0x2b, 0x35, 0x4f, 0x28, 0xd3, 0xb0,
                0xb7, 0xd3, 0x83, 0x67, 0x01, 0x9f, 0x41, 0x13, 0x74, 0x2a, 0x2b, 0x14, 0xbd, 0x25,
                0x92, 0x6b, 0x49, 0xc6, 0x49, 0x15, 0x5f, 0x26, 0x7e, 0x60, 0xd3, 0x81, 0x4b, 0x4c,
                0x0c, 0xc8, 0x42, 0x50, 0xe4, 0x6f, 0x00, 0x83,
            ]
        );
        v.verify::<hash::Sha256>(b"test", &signature).unwrap();

        let mut asn1_sig = [0u8; 128];
        let asn1_sig = SigningKey::<curve::P256>::fixed_to_asn1(&signature, &mut asn1_sig).unwrap();
        v.verify_asn1::<hash::Sha256>(b"test", asn1_sig).unwrap();

        k.rfc6979_sign_with_random::<hash::Sha512>(b"sample", &[], &mut signature)
            .unwrap();
        assert_eq!(
            signature,
            [
                0x84, 0x96, 0xa6, 0x0b, 0x5e, 0x9b, 0x47, 0xc8, 0x25, 0x48, 0x88, 0x27, 0xe0, 0x49,
                0x5b, 0x0e, 0x3f, 0xa1, 0x09, 0xec, 0x45, 0x68, 0xfd, 0x3f, 0x8d, 0x10, 0x97, 0x67,
                0x8e, 0xb9, 0x7f, 0x00, 0x23, 0x62, 0xab, 0x1a, 0xdb, 0xe2, 0xb8, 0xad, 0xf9, 0xcb,
                0x9e, 0xda, 0xb7, 0x40, 0xea, 0x60, 0x49, 0xc0, 0x28, 0x11, 0x4f, 0x24, 0x60, 0xf9,
                0x65, 0x54, 0xf6, 0x1f, 0xae, 0x33, 0x02, 0xfe,
            ]
        );
        v.verify::<hash::Sha512>(b"sample", &signature).unwrap();

        let mut asn1_sig = [0u8; 128];
        let asn1_sig = SigningKey::<curve::P256>::fixed_to_asn1(&signature, &mut asn1_sig).unwrap();
        v.verify_asn1::<hash::Sha512>(b"sample", asn1_sig).unwrap();

        k.rfc6979_sign_with_random::<hash::Sha512>(b"test", &[], &mut signature)
            .unwrap();
        assert_eq!(
            signature,
            [
                0x46, 0x1d, 0x93, 0xf3, 0x1b, 0x65, 0x40, 0x89, 0x47, 0x88, 0xfd, 0x20, 0x6c, 0x07,
                0xcf, 0xa0, 0xcc, 0x35, 0xf4, 0x6f, 0xa3, 0xc9, 0x18, 0x16, 0xff, 0xf1, 0x04, 0x0a,
                0xd1, 0x58, 0x1a, 0x04, 0x39, 0xaf, 0x9f, 0x15, 0xde, 0x0d, 0xb8, 0xd9, 0x7e, 0x72,
                0x71, 0x9c, 0x74, 0x82, 0x0d, 0x30, 0x4c, 0xe5, 0x22, 0x6e, 0x32, 0xde, 0xda, 0xe6,
                0x75, 0x19, 0xe8, 0x40, 0xd1, 0x19, 0x4e, 0x55,
            ]
        );
        v.verify::<hash::Sha512>(b"test", &signature).unwrap();

        let mut asn1_sig = [0u8; 128];
        let asn1_sig = SigningKey::<curve::P256>::fixed_to_asn1(&signature, &mut asn1_sig).unwrap();
        v.verify_asn1::<hash::Sha512>(b"test", asn1_sig).unwrap();

        // This is an extra test vector from
        // <https://github.com/C2SP/CCTV/tree/main/RFC6979>
        // that exercises the rejection sampling in
        // `p256::PrivateKey::generate()`

        k.rfc6979_sign_with_random::<hash::Sha256>(b"wv[vnX", &[], &mut signature)
            .unwrap();
        assert_eq!(
            signature,
            [
                0xef, 0xd9, 0x07, 0x3b, 0x65, 0x2e, 0x76, 0xda, 0x1b, 0x5a, 0x01, 0x9c, 0x0e, 0x4a,
                0x2e, 0x3f, 0xa5, 0x29, 0xb0, 0x35, 0xa6, 0xab, 0xb9, 0x1e, 0xf6, 0x7f, 0x0e, 0xd7,
                0xa1, 0xf2, 0x12, 0x34, 0x3d, 0xb4, 0x70, 0x6c, 0x9d, 0x9f, 0x4a, 0x4f, 0xe1, 0x3b,
                0xb5, 0xe0, 0x8e, 0xf0, 0xfa, 0xb5, 0x3a, 0x57, 0xdb, 0xab, 0x20, 0x61, 0xc8, 0x3a,
                0x35, 0xfa, 0x41, 0x1c, 0x68, 0xd2, 0xba, 0x33
            ]
        );
        v.verify::<hash::Sha256>(b"wv[vnX", &signature).unwrap();
    }

    // The digest path repeats the message path, which `proofs/` checks as
    // it stands, so the two must agree, here on RFC 6979's A.2.5, A.2.6,
    // and A.2.7 keys and messages.
    #[test]
    fn digest_signing_matches_message_signing() {
        fn check<C: Curve>(private_key: &str) {
            let private_key =
                C::PrivateKey::from_bytes(&hex::decode(private_key).unwrap()).unwrap();
            let mut public_key = [0u8; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN];
            let public_key = private_key
                .public_key_encode_uncompressed(&mut public_key)
                .unwrap();
            let v = VerifyingKey::<C>::from_x962_uncompressed(public_key).unwrap();
            let k = SigningKey::<C>::new(private_key);
            for message in [&b"sample"[..], b"test"] {
                let (mut ours, mut wanted) = ([0u8; 132], [0u8; 132]);
                let wanted = k
                    .rfc6979_sign_with_random::<hash::Sha512>(message, &[], &mut wanted)
                    .unwrap();
                let digest = hash::Sha512::hash(message);
                let ours = k
                    .rfc6979_sign_digest_with_random::<hash::Sha512>(
                        digest.as_ref(),
                        &[],
                        &mut ours,
                    )
                    .unwrap();
                assert_eq!(ours, wanted);
                v.verify_digest(digest.as_ref(), ours).unwrap();
                v.verify::<hash::Sha512>(message, ours).unwrap();

                let mut asn1 = [0u8; 160];
                let asn1 = SigningKey::<C>::fixed_to_asn1(ours, &mut asn1).unwrap();
                v.verify_asn1_digest(digest.as_ref(), asn1).unwrap();
                assert_eq!(
                    v.verify_digest(hash::Sha512::hash(b"other").as_ref(), ours),
                    Err(Error::BadSignature)
                );
            }
        }

        check::<curve::P256>("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721");
        check::<curve::P384>(
            "6b9d3dad2e1b8c1c05b19875b6659f4de23c3b667bf297ba9aa47740787137d896d5724e4c70a825f872c9ea60d2edf5",
        );
        check::<curve::P521>(
            "00fad06daa62ba3b25d2fb40133da757205de67f5bb0018fee8c86e1b68c7e75caa896eb32f1f47c70855836a6d16fcc1466f6d8fbec67db89ec0c08b0e996b83538",
        );
    }

    #[test]
    fn rfc6979_p521_test_vectors() {
        // from A.2.7.  bits2int keeps the leftmost 521 of each 528 bits
        // HMAC_DRBG draws.
        let private_key = <curve::P521 as curve::Curve>::PrivateKey::from_bytes(&hex::decode("00fad06daa62ba3b25d2fb40133da757205de67f5bb0018fee8c86e1b68c7e75caa896eb32f1f47c70855836a6d16fcc1466f6d8fbec67db89ec0c08b0e996b83538").unwrap()).unwrap();
        let mut public_key = [0u8; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN];
        let public_key = private_key
            .public_key_encode_uncompressed(&mut public_key)
            .unwrap();
        let v = VerifyingKey::<curve::P521> {
            public_key: <curve::P521 as curve::Curve>::PublicKey::from_x962_uncompressed(
                public_key,
            )
            .unwrap(),
        };
        let k = SigningKey::<curve::P521>::new(private_key);
        let mut signature = [0u8; 132];

        k.rfc6979_sign_with_random::<hash::Sha256>(b"sample", &[], &mut signature)
            .unwrap();
        assert_eq!(
            hex::encode(signature),
            "01511bb4d675114fe266fc4372b87682baecc01d3cc62cf2303c92b3526012659d16876e25c7c1e57648f23b73564d67f61c6f14d527d54972810421e7d87589e1a7004a171143a83163d6df460aaf61522695f207a58b95c0644d87e52aa1a347916e4f7a72930b1bc06dbe22ce3f58264afd23704cbb63b29b931f7de6c9d949a7ecfc"
        );
        v.verify::<hash::Sha256>(b"sample", &signature).unwrap();

        k.rfc6979_sign_with_random::<hash::Sha512>(b"sample", &[], &mut signature)
            .unwrap();
        assert_eq!(
            hex::encode(signature),
            "00c328fafcbd79dd77850370c46325d987cb525569fb63c5d3bc53950e6d4c5f174e25a1ee9017b5d450606add152b534931d7d4e8455cc91f9b15bf05ec36e377fa00617cce7cf5064806c467f678d3b4080d6f1cc50af26ca209417308281b68af282623eaa63e5b5c0723d8b8c37ff0777b1a20f8ccb1dccc43997f1ee0e44da4a67a"
        );
        v.verify::<hash::Sha512>(b"sample", &signature).unwrap();

        let mut asn1_sig = [0u8; 160];
        let asn1_sig = SigningKey::<curve::P521>::fixed_to_asn1(&signature, &mut asn1_sig).unwrap();
        v.verify_asn1::<hash::Sha512>(b"sample", asn1_sig).unwrap();

        k.rfc6979_sign_with_random::<hash::Sha256>(b"test", &[], &mut signature)
            .unwrap();
        assert_eq!(
            hex::encode(signature),
            "000e871c4a14f993c6c7369501900c4bc1e9c7b0b4ba44e04868b30b41d8071042eb28c4c250411d0ce08cd197e4188ea4876f279f90b3d8d74a3c76e6f1e4656aa800cd52dbaa33b063c3a6cd8058a1fb0a46a4754b034fcc644766ca14da8ca5ca9fde00e88c1ad60ccba759025299079d7a427ec3cc5b619bfbc828e7769bcd694e86"
        );
        v.verify::<hash::Sha256>(b"test", &signature).unwrap();

        k.rfc6979_sign_with_random::<hash::Sha512>(b"test", &[], &mut signature)
            .unwrap();
        assert_eq!(
            hex::encode(signature),
            "013e99020abf5cee7525d16b69b229652ab6bdf2affcaef38773b4b7d08725f10cdb93482fdcc54edcee91eca4166b2a7c6265ef0ce2bd7051b7cef945babd47ee6d01fbd0013c674aa79cb39849527916ce301c66ea7ce8b80682786ad60f98f7e78a19ca69eff5c57400e3b3a0ad66ce0978214d13baf4e9ac60752f7b155e2de4dce3"
        );
        v.verify::<hash::Sha512>(b"test", &signature).unwrap();
    }

    /// `value` as `len` big-endian bytes, or `None` if it is larger.
    fn fixed(value: &[u8], len: usize) -> Option<Vec<u8>> {
        let start = value.iter().position(|b| *b != 0).unwrap_or(value.len());
        let value = &value[start..];
        (value.len() <= len).then(|| [vec![0; len - value.len()], value.to_vec()].concat())
    }

    // aws-lc's verification vectors give digests of every length, some
    // longer than the scalar. P-224 and secp256k1 rind doesn't offer, nor
    // digests over 64 bytes, which `hash_to_scalar` would truncate to bytes.
    #[test]
    fn aws_lc_verify() {
        fn check<C: Curve>(test: &file_test::Test) {
            if test.bytes("Digest").len() > 64 {
                return;
            }
            let len = C::Scalar::LEN_BYTES;
            let key = [vec![4], test.bytes("X"), test.bytes("Y")].concat();
            let result = C::PublicKey::from_x962_uncompressed(&key).and_then(|public_key| {
                match (fixed(&test.bytes("R"), len), fixed(&test.bytes("S"), len)) {
                    (Some(r), Some(s)) => VerifyingKey::<C> { public_key }
                        .verify_digest(&test.bytes("Digest"), &[r, s].concat()),
                    _ => Err(Error::BadSignature),
                }
            });
            match test.get("Invalid") {
                None => assert_eq!(result, Ok(()), "{test}"),
                Some(_) => assert!(result.is_err(), "{test}"),
            }
        }

        for test in file_test::tests("aws-lc/crypto/fipsmodule/ecdsa/ecdsa_verify_tests.txt") {
            match test.str("Curve") {
                "P-256" => check::<curve::P256>(&test),
                "P-384" => check::<curve::P384>(&test),
                "P-521" => check::<curve::P521>(&test),
                "P-224" | "secp256k1" | "secp160r1" => {}
                other => panic!("{test}: unexpected curve {other}"),
            }
        }
    }

    // aws-lc's signing vectors fix the nonce, which rind otherwise derives.
    // P-224, secp256k1, and digests over 64 bytes rind doesn't offer.
    #[test]
    fn aws_lc_sign() {
        fn check<C: Curve>(test: &file_test::Test) {
            if test.bytes("Digest").len() > 64 {
                return;
            }
            let len = C::Scalar::LEN_BYTES;
            let private = fixed(&test.bytes("Private"), len).unwrap();
            let private_key = C::PrivateKey::from_bytes(&private).unwrap();
            let mut public_key = [0u8; 133];
            let public_key = private_key
                .public_key_encode_uncompressed(&mut public_key)
                .unwrap();
            let expected = [vec![4], test.bytes("X"), test.bytes("Y")].concat();
            assert_eq!(public_key, expected, "{test}");

            let key = SigningKey::<C>::new(private_key);
            let e = hash_to_scalar::<C>(&test.bytes("Digest")).unwrap();
            // Nonces are drawn as RFC 6979's bits2int reads them: P-521's
            // from the leftmost 521 bits of 66 bytes.
            let k = fixed(&test.bytes("K"), len).unwrap();
            let excess = if len == 66 { 7 } else { 0 };
            let k: Vec<u8> = (0..len)
                .map(|i| {
                    let pair = u16::from_be_bytes([k[i], k.get(i + 1).copied().unwrap_or(0)]);
                    (pair << excess).to_be_bytes()[0]
                })
                .collect();
            let (r, s) = key
                .sign_with_nonces(&e, &mut SliceRandomSource(&k))
                .unwrap();
            let mut sig = [0u8; MAX_SCALAR_LEN * 2];
            r.write_bytes(&mut sig[..len]);
            s.write_bytes(&mut sig[len..len * 2]);
            let r = fixed(&test.bytes("R"), len).unwrap();
            let s = fixed(&test.bytes("S"), len).unwrap();
            assert_eq!(&sig[..len * 2], [r, s].concat(), "{test}");
        }

        for test in file_test::tests("aws-lc/crypto/fipsmodule/ecdsa/ecdsa_sign_tests.txt") {
            match test.str("Curve") {
                "P-256" => check::<curve::P256>(&test),
                "P-384" => check::<curve::P384>(&test),
                "P-521" => check::<curve::P521>(&test),
                "P-224" | "secp256k1" => {}
                other => panic!("{test}: unexpected curve {other}"),
            }
        }
    }

    #[test]
    fn cavp_sigver() {
        #[derive(Debug, Default)]
        struct State {
            param: String,
            msg: Vec<u8>,
            px: Vec<u8>,
            py: Vec<u8>,
            r: Vec<u8>,
            s: Vec<u8>,
        }

        impl CavpSink for State {
            fn on_meta(&mut self, meta: &str) {
                self.param = meta.to_string();
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "Msg" => self.msg = value.bytes(),
                    "Qx" => self.px = value.bytes(),
                    "Qy" => self.py = value.bytes(),
                    "R" => self.r = value.bytes(),
                    "S" => self.s = value.bytes(),
                    "Result" => {
                        match self.param.as_ref() {
                            "P-256,SHA-256" | "P-256,SHA-384" | "P-256,SHA-512" => {
                                pad(&mut self.px, 32);
                                pad(&mut self.py, 32);
                                pad(&mut self.r, 32);
                                pad(&mut self.s, 32);

                                let mut point = vec![0x04];
                                point.extend_from_slice(&self.px);
                                point.extend_from_slice(&self.py);

                                let mut sig = vec![];
                                sig.extend_from_slice(&self.r);
                                sig.extend_from_slice(&self.s);

                                let vkey =
                                    VerifyingKey::<curve::P256>::from_x962_uncompressed(&point)
                                        .unwrap();

                                let result = match self.param.as_ref() {
                                    "P-256,SHA-256" => vkey.verify::<hash::Sha256>(&self.msg, &sig),
                                    "P-256,SHA-384" => vkey.verify::<hash::Sha384>(&self.msg, &sig),
                                    "P-256,SHA-512" => vkey.verify::<hash::Sha512>(&self.msg, &sig),
                                    _ => todo!("unhandled param"),
                                };

                                match value.str().chars().next() {
                                    Some('F') => {
                                        result.unwrap_err();
                                    }
                                    Some('P') => {
                                        result.unwrap();
                                    }
                                    _ => todo!("unrecognised Result {:?}", value.str()),
                                };
                                println!("PASS: {}", value.str());
                            }
                            "P-384,SHA-256" | "P-384,SHA-384" | "P-384,SHA-512" => {
                                pad(&mut self.px, 48);
                                pad(&mut self.py, 48);
                                pad(&mut self.r, 48);
                                pad(&mut self.s, 48);

                                let mut point = vec![0x04];
                                point.extend_from_slice(&self.px);
                                point.extend_from_slice(&self.py);

                                let mut sig = vec![];
                                sig.extend_from_slice(&self.r);
                                sig.extend_from_slice(&self.s);

                                let vkey =
                                    VerifyingKey::<curve::P384>::from_x962_uncompressed(&point)
                                        .unwrap();

                                let result = match self.param.as_ref() {
                                    "P-384,SHA-256" => vkey.verify::<hash::Sha256>(&self.msg, &sig),
                                    "P-384,SHA-384" => vkey.verify::<hash::Sha384>(&self.msg, &sig),
                                    "P-384,SHA-512" => vkey.verify::<hash::Sha512>(&self.msg, &sig),
                                    _ => todo!("unhandled param"),
                                };

                                match value.str().chars().next() {
                                    Some('F') => {
                                        result.unwrap_err();
                                    }
                                    Some('P') => {
                                        result.unwrap();
                                    }
                                    _ => todo!("unrecognised Result {:?}", value.str()),
                                };
                                println!("PASS: {}", value.str());
                            }

                            "P-521,SHA-256" | "P-521,SHA-384" | "P-521,SHA-512" => {
                                pad(&mut self.px, 66);
                                pad(&mut self.py, 66);
                                pad(&mut self.r, 66);
                                pad(&mut self.s, 66);

                                let mut point = vec![0x04];
                                point.extend_from_slice(&self.px);
                                point.extend_from_slice(&self.py);

                                let mut sig = vec![];
                                sig.extend_from_slice(&self.r);
                                sig.extend_from_slice(&self.s);

                                let vkey =
                                    VerifyingKey::<curve::P521>::from_x962_uncompressed(&point)
                                        .unwrap();

                                let result = match self.param.as_ref() {
                                    "P-521,SHA-256" => vkey.verify::<hash::Sha256>(&self.msg, &sig),
                                    "P-521,SHA-384" => vkey.verify::<hash::Sha384>(&self.msg, &sig),
                                    "P-521,SHA-512" => vkey.verify::<hash::Sha512>(&self.msg, &sig),
                                    _ => todo!("unhandled param"),
                                };

                                match value.str().chars().next() {
                                    Some('F') => {
                                        result.unwrap_err();
                                    }
                                    Some('P') => {
                                        result.unwrap();
                                    }
                                    _ => todo!("unrecognised Result {:?}", value.str()),
                                };
                                println!("PASS: {}", value.str());
                            }

                            _ => {
                                println!("unhandled params {}", self.param);
                            }
                        };
                    }
                    _ => {}
                }
            }
        }

        process_cavp("../thirdparty/cavp/ecdsa/SigVer.rsp", &mut State::default());
    }

    fn pad(v: &mut Vec<u8>, l: usize) {
        while v.len() < l {
            v.insert(0, 0x00);
        }
    }
}
