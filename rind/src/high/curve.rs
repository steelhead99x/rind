// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use crate::Error;
use crate::high::asn1;
use crate::mid::p256;
use crate::mid::p384;
use crate::mid::p521;
use crate::mid::rng::RandomSource;

/// A generalisation of elliptic curves for use with ECDSA.
///
/// The key traits name the curve's scalar rather than the curve, so that no
/// two traits refer to each other, which Aeneas cannot translate.
pub(crate) trait Curve {
    /// Private key type for this curve.
    type PrivateKey: PrivateKey<Self::Scalar>;

    /// Public key type for this curve.
    type PublicKey: PublicKey<Self::Scalar>;

    /// Scalar type for this curve.
    type Scalar: Scalar;

    /// The curve's OID when used in PKCS#8 key formats.
    fn oid() -> asn1::ObjectId;

    /// Generate a random `PrivateKey`
    fn generate_random_key(rng: &mut impl RandomSource) -> Result<Self::PrivateKey, Error>;
}

/// A generic elliptic curve private key scalar, whose curve's scalars are `S`.
pub(crate) trait PrivateKey<S> {
    /// Decode a private key from `bytes`.
    ///
    /// `bytes` may be larger or smaller than the size of `n`: excess bytes
    /// must be zero.  If given a variable-sized input, this is deemed a
    /// non-secret property.  Prefer to use fixed-sized inputs.
    ///
    /// An error is returned if the magnitude of the value is larger than
    /// `n` (ie, the input is never reduced mod n),  or the value is zero.
    fn from_bytes(bytes: &[u8]) -> Result<Self, Error>
    where
        Self: Sized;

    /// Encode this private key's value into `out`, still secret.
    ///
    /// The written prefix of `out` is returned.
    fn encode<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error>;

    /// Return the x coordinate of this key's public half.
    ///
    /// Note this is returned as a scalar, so this may involve
    /// a `mod p` to `mod n` reduction.  This is not useful outside
    /// of ECDSA.
    fn public_key_x_scalar(&self) -> S;

    /// Output an uncompressed encoding of this key's public half.
    ///
    /// The return value is the written prefix of `out`.
    #[allow(dead_code)] // ??? false positive
    fn public_key_encode_uncompressed<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error>;

    /// Whether `encoded`, an X9.62 uncompressed point, is this key's public
    /// half, for a curve that checks it faster than it encodes its own;
    /// `None` for one that does not.
    #[cfg(rind_backend = "x86_64")]
    fn public_key_is_uncompressed(&self, _encoded: &[u8]) -> Option<bool> {
        None
    }

    /// The raw RSA signing operation: `(e + r * d) / k`, where self aka `d`.
    fn raw_ecdsa_sign(&self, k: &Self, e: &S, r: &S) -> S;
}

/// A generic elliptic curve public key point, whose curve's scalars are `S`.
pub(crate) trait PublicKey<S> {
    /// Decode a point from its uncompressed encoding.
    ///
    /// `bytes` must be precisely `LEN_BYTES` in length.
    ///
    /// An error is returned for the wrong length, wrong indicator
    /// byte, a coordinate not below the field prime, or if the
    /// resulting point is not on the curve.
    fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error>
    where
        Self: Sized;

    /// Raw ECDSA verification primitive.
    fn raw_ecdsa_verify(&self, r: &S, s: &S, e: &S) -> Result<(), Error>;
}

/// A generic elliptic curve scalar.
pub(crate) trait Scalar {
    /// Length of an encoded scalar.
    const LEN_BYTES: usize;

    /// Decode a scalar from `bytes`.
    ///
    /// `bytes` may be larger or smaller than the size of `n`: excess bytes
    /// must be zero.  If given a variable-sized input, this is deemed a
    /// non-secret property.  Prefer to use fixed-sized inputs.
    ///
    /// An error is returned if the magnitude of the value is larger than
    /// `n` (ie, the input is never reduced mod n),  or the value is zero.
    fn from_bytes_checked(bytes: &[u8]) -> Result<Self, Error>
    where
        Self: Sized;

    /// Decode a scalar from `bytes`, reducing it `mod n`.
    ///
    /// This may return a zero scalar (for any even multiple of `n`);
    /// this can be checked with `is_zero`.
    fn from_bytes_reduced(bytes: &[u8]) -> Self;

    /// Return true if this scalar is zero.
    fn is_zero(&self) -> bool;

    /// Write a fixed-length encoding of the scalar to the front of `target`.
    ///
    /// `Self::LEN_BYTES` gives the number of bytes written.
    fn write_bytes(&self, target: &mut [u8]);
}

// enough for p521
pub(crate) const MAX_SCALAR_LEN: usize = p521::Scalar::BYTES;
pub(crate) const MAX_UNCOMPRESSED_PUBLIC_KEY_LEN: usize = p521::PublicKey::BYTES;

/// This is the elliptic curve "P-256".
///
/// P-256 is also known as "NISTP256", "prime256v1", or "secp256r1".
///
/// See [SEC1](https://www.secg.org/sec1-v2.pdf) for one definition.
pub(crate) struct P256;

impl Curve for P256 {
    type PrivateKey = p256::StaticPrivateKey;
    type PublicKey = p256::VerifyingKey;
    type Scalar = p256::Scalar;

    fn oid() -> asn1::ObjectId {
        asn1::oid::id_prime256v1.clone()
    }

    fn generate_random_key(rng: &mut impl RandomSource) -> Result<p256::StaticPrivateKey, Error> {
        p256::StaticPrivateKey::generate(rng)
    }
}

impl PrivateKey<p256::Scalar> for p256::StaticPrivateKey {
    fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_bytes(bytes)
    }

    fn encode<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        if let Some(out) = out.get_mut(0..32) {
            out.copy_from_slice(&self.secret_bytes());
            Ok(out)
        } else {
            Err(Error::WrongLength)
        }
    }

    fn public_key_x_scalar(&self) -> p256::Scalar {
        self.public_key_x_scalar()
    }

    fn public_key_encode_uncompressed<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        if let Some(out) = out.get_mut(0..p256::PublicKey::BYTES) {
            out.copy_from_slice(&self.public_key_uncompressed());
            Ok(out)
        } else {
            Err(Error::WrongLength)
        }
    }

    #[cfg(rind_backend = "x86_64")]
    fn public_key_is_uncompressed(&self, encoded: &[u8]) -> Option<bool> {
        Some(self.public_key_is_uncompressed(encoded))
    }

    fn raw_ecdsa_sign(&self, k: &Self, e: &p256::Scalar, r: &p256::Scalar) -> p256::Scalar {
        self.raw_ecdsa_sign(k, e, r)
    }
}

impl PublicKey<p256::Scalar> for p256::VerifyingKey {
    fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_x962_uncompressed(bytes)
    }

    fn raw_ecdsa_verify(
        &self,
        r: &p256::Scalar,
        s: &p256::Scalar,
        e: &p256::Scalar,
    ) -> Result<(), Error> {
        self.raw_ecdsa_verify(r, s, e)
    }
}

impl Scalar for p256::Scalar {
    const LEN_BYTES: usize = Self::BYTES;

    fn from_bytes_checked(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_bytes_checked(bytes)
    }

    fn from_bytes_reduced(bytes: &[u8]) -> Self {
        Self::from_bytes_reduced(bytes).unwrap()
    }

    fn is_zero(&self) -> bool {
        self.is_zero()
    }

    fn write_bytes(&self, target: &mut [u8]) {
        target.copy_from_slice(&self.as_bytes());
    }
}

/// This is the elliptic curve "P-384".
///
/// P-384 is also known as "NISTP384", or "secp384r1".
///
/// See [SEC1](https://www.secg.org/sec1-v2.pdf) for one definition.
pub(crate) struct P384;

impl Curve for P384 {
    type PrivateKey = p384::StaticPrivateKey;
    type PublicKey = p384::VerifyingKey;
    type Scalar = p384::Scalar;

    fn oid() -> asn1::ObjectId {
        asn1::oid::secp384r1.clone()
    }

    fn generate_random_key(rng: &mut impl RandomSource) -> Result<p384::StaticPrivateKey, Error> {
        p384::StaticPrivateKey::generate(rng)
    }
}

impl PrivateKey<p384::Scalar> for p384::StaticPrivateKey {
    fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_bytes(bytes)
    }

    fn encode<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        if let Some(out) = out.get_mut(0..48) {
            out.copy_from_slice(&self.secret_bytes());
            Ok(out)
        } else {
            Err(Error::WrongLength)
        }
    }

    fn public_key_x_scalar(&self) -> p384::Scalar {
        self.public_key_x_scalar()
    }

    fn public_key_encode_uncompressed<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        if let Some(out) = out.get_mut(0..p384::PublicKey::BYTES) {
            out.copy_from_slice(&self.public_key_uncompressed());
            Ok(out)
        } else {
            Err(Error::WrongLength)
        }
    }

    fn raw_ecdsa_sign(&self, k: &Self, e: &p384::Scalar, r: &p384::Scalar) -> p384::Scalar {
        self.raw_ecdsa_sign(k, e, r)
    }
}

impl PublicKey<p384::Scalar> for p384::VerifyingKey {
    fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_x962_uncompressed(bytes)
    }

    fn raw_ecdsa_verify(
        &self,
        r: &p384::Scalar,
        s: &p384::Scalar,
        e: &p384::Scalar,
    ) -> Result<(), Error> {
        self.raw_ecdsa_verify(r, s, e)
    }
}

impl Scalar for p384::Scalar {
    const LEN_BYTES: usize = Self::BYTES;

    fn from_bytes_checked(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_bytes_checked(bytes)
    }

    fn from_bytes_reduced(bytes: &[u8]) -> Self {
        Self::from_bytes_reduced(bytes).unwrap()
    }

    fn is_zero(&self) -> bool {
        self.is_zero()
    }

    fn write_bytes(&self, target: &mut [u8]) {
        target.copy_from_slice(&self.as_bytes());
    }
}

/// This is the elliptic curve "P-521".
///
/// P-521 is also known as "NISTP521", or "secp521r1".
///
/// See [SEC1](https://www.secg.org/sec1-v2.pdf) for one definition.
pub(crate) struct P521;

impl Curve for P521 {
    type PrivateKey = p521::StaticPrivateKey;
    type PublicKey = p521::VerifyingKey;
    type Scalar = p521::Scalar;

    fn oid() -> asn1::ObjectId {
        asn1::oid::secp521r1.clone()
    }

    fn generate_random_key(rng: &mut impl RandomSource) -> Result<p521::StaticPrivateKey, Error> {
        p521::StaticPrivateKey::generate(rng)
    }
}

impl PrivateKey<p521::Scalar> for p521::StaticPrivateKey {
    fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_bytes(bytes)
    }

    fn encode<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        if let Some(out) = out.get_mut(0..p521::Scalar::BYTES) {
            out.copy_from_slice(&self.secret_bytes());
            Ok(out)
        } else {
            Err(Error::WrongLength)
        }
    }

    fn public_key_x_scalar(&self) -> p521::Scalar {
        self.public_key_x_scalar()
    }

    fn public_key_encode_uncompressed<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        if let Some(out) = out.get_mut(0..p521::PublicKey::BYTES) {
            out.copy_from_slice(&self.public_key_uncompressed());
            Ok(out)
        } else {
            Err(Error::WrongLength)
        }
    }

    fn raw_ecdsa_sign(&self, k: &Self, e: &p521::Scalar, r: &p521::Scalar) -> p521::Scalar {
        self.raw_ecdsa_sign(k, e, r)
    }
}

impl PublicKey<p521::Scalar> for p521::VerifyingKey {
    fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_x962_uncompressed(bytes)
    }

    fn raw_ecdsa_verify(
        &self,
        r: &p521::Scalar,
        s: &p521::Scalar,
        e: &p521::Scalar,
    ) -> Result<(), Error> {
        self.raw_ecdsa_verify(r, s, e)
    }
}

impl Scalar for p521::Scalar {
    const LEN_BYTES: usize = Self::BYTES;

    fn from_bytes_checked(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_bytes_checked(bytes)
    }

    fn from_bytes_reduced(bytes: &[u8]) -> Self {
        Self::from_bytes_reduced(bytes).unwrap()
    }

    fn is_zero(&self) -> bool {
        self.is_zero()
    }

    fn write_bytes(&self, target: &mut [u8]) {
        target.copy_from_slice(&self.as_bytes());
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::error::KeyFormatError;
    use crate::test::*;

    // Signing retries on a zero `r` or `s`, which only this tells it of.
    #[test]
    fn is_zero() {
        fn check<S: Scalar>() {
            assert!(S::from_bytes_reduced(&[0; 66][..S::LEN_BYTES]).is_zero());
            let mut one = [0; 66];
            one[S::LEN_BYTES - 1] = 1;
            assert!(!S::from_bytes_reduced(&one[..S::LEN_BYTES]).is_zero());
        }
        check::<p256::Scalar>();
        check::<p384::Scalar>();
        check::<p521::Scalar>();
    }

    #[test]
    fn private_key_encode_error() {
        let key = p256::StaticPrivateKey::new_random().unwrap();
        let mut out = [0; 31];
        assert!(key.encode(&mut out).is_err());
        let mut out = [0; 64];
        assert!(key.public_key_encode_uncompressed(&mut out).is_err());

        let key = p384::StaticPrivateKey::new_random().unwrap();
        let mut out = [0; 47];
        assert!(key.encode(&mut out).is_err());
        let mut out = [0; 96];
        assert!(key.public_key_encode_uncompressed(&mut out).is_err());

        let key = p521::StaticPrivateKey::new_random().unwrap();
        let mut out = [0; 65];
        assert!(key.encode(&mut out).is_err());
        let mut out = [0; 132];
        assert!(key.public_key_encode_uncompressed(&mut out).is_err());
    }

    #[test]
    fn cavp_pkv() {
        #[derive(Debug, Default)]
        struct State {
            curve: String,
            px: Vec<u8>,
            py: Vec<u8>,
        }

        impl CavpSink for State {
            fn on_meta(&mut self, meta: &str) {
                self.curve = meta.to_string();
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "Qx" => self.px = value.bytes(),
                    "Qy" => self.py = value.bytes(),
                    "Result" => match self.curve.as_ref() {
                        "P-256" => {
                            pad(&mut self.px, 32);
                            pad(&mut self.py, 32);
                            let mut point = vec![0x04];
                            point.extend_from_slice(&self.px);
                            point.extend_from_slice(&self.py);
                            let res = <P256 as Curve>::PublicKey::from_x962_uncompressed(&point);

                            match value.str().chars().next() {
                                Some('F') => {
                                    res.unwrap_err();
                                }
                                Some('P') => {
                                    res.unwrap();
                                }
                                _ => {}
                            };
                        }
                        "P-384" => {
                            pad(&mut self.px, 48);
                            pad(&mut self.py, 48);
                            let mut point = vec![0x04];
                            point.extend_from_slice(&self.px);
                            point.extend_from_slice(&self.py);
                            let res = <P384 as Curve>::PublicKey::from_x962_uncompressed(&point);

                            match value.str().chars().next() {
                                Some('F') => {
                                    res.unwrap_err();
                                }
                                Some('P') => {
                                    res.unwrap();
                                }
                                _ => {}
                            };
                        }
                        "P-521" => {
                            pad(&mut self.px, 66);
                            pad(&mut self.py, 66);
                            let mut point = vec![0x04];
                            point.extend_from_slice(&self.px);
                            point.extend_from_slice(&self.py);
                            let res = <P521 as Curve>::PublicKey::from_x962_uncompressed(&point);

                            match value.str().chars().next() {
                                Some('F') => {
                                    res.unwrap_err();
                                }
                                Some('P') => {
                                    res.unwrap();
                                }
                                _ => {}
                            };
                        }
                        _ => {
                            println!("unhandled curve {}", self.curve);
                        }
                    },
                    _ => {}
                }
            }
        }

        process_cavp(
            "../thirdparty/vectors/cavp/ecdsa/PKV.rsp",
            &mut State::default(),
        );
    }

    #[test]
    fn non_canonical_coordinates() {
        // Each point is on the curve with a coordinate small enough that
        // adding p still fits, so that encoding reduces to an on-curve point
        // and only a range check refuses it.
        fn check<C: Curve>(p: &str, small_x: &[(&str, &str)], small_y: (&str, &str)) {
            let p = hex::decode(p).unwrap();
            let coordinate = |hex: &str| {
                let bytes = hex::decode(hex).unwrap();
                [vec![0; p.len() - bytes.len()], bytes].concat()
            };
            let plus_p = |v: &[u8]| {
                let mut sum = v.to_vec();
                let mut carry = 0;
                for (s, p) in sum.iter_mut().zip(&p).rev() {
                    let t = *s as u16 + *p as u16 + carry;
                    *s = t as u8;
                    carry = t >> 8;
                }
                assert_eq!(carry, 0);
                sum
            };
            let decode = |x: &[u8], y: &[u8]| {
                C::PublicKey::from_x962_uncompressed(&[&[0x04], x, y].concat()).map(drop)
            };

            for (x, y) in small_x {
                let (x, y) = (coordinate(x), coordinate(y));
                decode(&x, &y).unwrap();
                assert_eq!(
                    decode(&plus_p(&x), &y),
                    Err(KeyFormatError::NotOnCurve.into())
                );
            }

            let (x, y) = (coordinate(small_y.0), coordinate(small_y.1));
            decode(&x, &y).unwrap();
            assert_eq!(
                decode(&x, &plus_p(&y)),
                Err(KeyFormatError::NotOnCurve.into())
            );
            assert_eq!(decode(&x, &p), Err(KeyFormatError::NotOnCurve.into()));
        }

        check::<P256>(
            "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
            &[
                (
                    "00",
                    "66485c780e2f83d72433bd5d84a06bb6541c2af31dae871728bf856a174f93f4",
                ),
                (
                    "05",
                    "459243b9aa581806fe913bce99817ade11ca503c64d9a3c533415c083248fbcc",
                ),
            ],
            (
                "d7325d7646cd60d80a92738ceb345f844cffaf35841022cab176f692de8de1d7",
                "05",
            ),
        );

        check::<P384>(
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff",
            &[
                (
                    "00",
                    "c306610fb0ae5a159cf45c06069f22a6c5eb3641c602d42dea2c4b4f75550793406d80d2b91ad54f9048bd487af1ade1",
                ),
                (
                    "02",
                    "8cdeadbbd04911a3c1931e26df3fa6439dca9c7eb286fbd46fc319f0e2bb780232baf57825fc0c1912ada2fefe84024c",
                ),
            ],
            (
                "2261b2bf605c22f2f3aef6338719b2c486388ad5240719a5257315969ef01ba27f0a104c89704773a81fdabee6ab5c78",
                "01",
            ),
        );

        // p is 2^521 - 1, so any coordinate plus p fits 66 bytes: the
        // generator serves.
        let g = (
            "00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66",
            "011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650",
        );
        check::<P521>(
            "01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            &[g],
            g,
        );
    }

    #[test]
    fn cavp_keypair() {
        #[derive(Debug, Default)]
        struct State {
            curve: String,
            d: Vec<u8>,
            px: Vec<u8>,
            py: Vec<u8>,
        }

        impl CavpSink for State {
            fn on_meta(&mut self, meta: &str) {
                // Curve sections, such as "P-521" or "K-163", not their
                // subsections.
                if meta.as_bytes().get(1) == Some(&b'-') {
                    self.curve = meta.to_string();
                }
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "d" => self.d = value.bytes(),
                    "Qx" => self.px = value.bytes(),
                    "Qy" => {
                        self.py = value.bytes();

                        match self.curve.as_ref() {
                            "P-256" => {
                                pad(&mut self.px, 32);
                                pad(&mut self.py, 32);
                                let mut point = vec![0x04];
                                point.extend_from_slice(&self.px);
                                point.extend_from_slice(&self.py);

                                let res = <P256 as Curve>::PrivateKey::from_bytes(&self.d).unwrap();
                                let mut buffer = [0u8; 65];
                                let got = res.public_key_encode_uncompressed(&mut buffer).unwrap();
                                assert_eq!(point, got);
                            }
                            "P-384" => {
                                pad(&mut self.px, 48);
                                pad(&mut self.py, 48);
                                let mut point = vec![0x04];
                                point.extend_from_slice(&self.px);
                                point.extend_from_slice(&self.py);

                                let res = <P384 as Curve>::PrivateKey::from_bytes(&self.d).unwrap();
                                let mut buffer = [0u8; 97];
                                let got = res.public_key_encode_uncompressed(&mut buffer).unwrap();
                                assert_eq!(point, got);
                            }
                            "P-521" => {
                                pad(&mut self.px, 66);
                                pad(&mut self.py, 66);
                                let mut point = vec![0x04];
                                point.extend_from_slice(&self.px);
                                point.extend_from_slice(&self.py);

                                let res = <P521 as Curve>::PrivateKey::from_bytes(&self.d).unwrap();
                                let mut buffer = [0u8; 133];
                                let got = res.public_key_encode_uncompressed(&mut buffer).unwrap();
                                assert_eq!(point, got);
                            }
                            _ => {
                                println!("unhandled curve {}", self.curve);
                            }
                        };
                    }
                    _ => {}
                }
            }
        }

        process_cavp(
            "../thirdparty/vectors/cavp/ecdsa/KeyPair.rsp",
            &mut State::default(),
        );
    }

    fn pad(v: &mut Vec<u8>, l: usize) {
        while v.len() < l {
            v.insert(0, 0x00);
        }
    }
}
