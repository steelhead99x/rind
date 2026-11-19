//! Key agreement: X25519, and ECDH on P-256, P-384, and P-521.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use crate::encoding::{
    AsBigEndian, AsDer, Curve25519SeedBin, EcPrivateKeyBin, EcPrivateKeyRfc5915Der,
    EcPublicKeyCompressedBin, EcPublicKeyUncompressedBin, Pkcs8V1Der, PublicKeyX509Der,
};
use crate::error::{KeyRejected, Unspecified, unspecified};
use crate::rand::SecureRandom;

#[derive(Clone, Copy, PartialEq, Eq)]
enum AlgorithmId {
    EcdhP256,
    EcdhP384,
    EcdhP521,
    X25519,
}

/// A key agreement algorithm.
#[derive(PartialEq, Eq)]
pub struct Algorithm {
    id: AlgorithmId,
}

impl Algorithm {
    fn rind(&self) -> &'static rind::agreement::Algorithm {
        match self.id {
            AlgorithmId::EcdhP256 => &rind::agreement::ECDH_P256,
            AlgorithmId::EcdhP384 => &rind::agreement::ECDH_P384,
            AlgorithmId::EcdhP521 => &rind::agreement::ECDH_P521,
            AlgorithmId::X25519 => &rind::agreement::X25519,
        }
    }

    fn from_rind(algorithm: &rind::agreement::Algorithm) -> &'static Self {
        [&ECDH_P256, &ECDH_P384, &ECDH_P521, &X25519]
            .into_iter()
            .find(|alg| alg.rind() == algorithm)
            .expect("every rind algorithm has an aws-lc-rs one")
    }

    /// The ECDSA algorithm on the same curve, through which a NIST key is
    /// encoded as SEC1.
    fn ecdsa(&self) -> Option<&'static rind::ecdsa::SigningAlgorithm> {
        use rind::ecdsa::sign;
        match self.id {
            AlgorithmId::EcdhP256 => Some(&sign::P256_SHA256_ASN1),
            AlgorithmId::EcdhP384 => Some(&sign::P384_SHA384_ASN1),
            AlgorithmId::EcdhP521 => Some(&sign::P521_SHA512_ASN1),
            AlgorithmId::X25519 => None,
        }
    }

    fn private_key_len(&self) -> usize {
        match self.id {
            AlgorithmId::EcdhP256 | AlgorithmId::X25519 => 32,
            AlgorithmId::EcdhP384 => 48,
            AlgorithmId::EcdhP521 => 66,
        }
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let curve = match self.id {
            AlgorithmId::EcdhP256 => "P256",
            AlgorithmId::EcdhP384 => "P384",
            AlgorithmId::EcdhP521 => "P521",
            AlgorithmId::X25519 => "Curve25519",
        };
        write!(f, "Algorithm {{ curve: {curve} }}")
    }
}

/// ECDH on P-256.
pub const ECDH_P256: Algorithm = Algorithm {
    id: AlgorithmId::EcdhP256,
};

/// ECDH on P-384.
pub const ECDH_P384: Algorithm = Algorithm {
    id: AlgorithmId::EcdhP384,
};

/// ECDH on P-521.
pub const ECDH_P521: Algorithm = Algorithm {
    id: AlgorithmId::EcdhP521,
};

/// X25519 (RFC 7748).
pub const X25519: Algorithm = Algorithm {
    id: AlgorithmId::X25519,
};

/// A private key for any number of key agreements; wiped on drop.
pub struct PrivateKey {
    key: rind::agreement::PrivateKey,
}

impl PrivateKey {
    /// Generates a private key for `alg` from the system random source.
    pub fn generate(alg: &'static Algorithm) -> Result<Self, Unspecified> {
        let key = rind::agreement::PrivateKey::generate(alg.rind()).map_err(unspecified)?;
        Ok(Self { key })
    }

    /// Loads a NIST curve's private key from PKCS#8 or a SEC1 (RFC 5915)
    /// `ECPrivateKey`. X25519 keys are refused, as aws-lc-rs refuses them.
    pub fn from_private_key_der(
        alg: &'static Algorithm,
        key_bytes: &[u8],
    ) -> Result<Self, KeyRejected> {
        if alg.id == AlgorithmId::X25519 {
            return Err(KeyRejected::invalid_encoding());
        }
        let key = rind::agreement::PrivateKey::from_pkcs8(alg.rind(), key_bytes)
            .or_else(|_| rind::agreement::PrivateKey::from_sec1(alg.rind(), key_bytes))
            .map_err(KeyRejected::rind)?;
        Ok(Self { key })
    }

    /// Loads a private key from its bytes: X25519's 32, or a NIST curve's
    /// big-endian scalar, exactly the curve's length.
    pub fn from_private_key(
        alg: &'static Algorithm,
        key_bytes: &[u8],
    ) -> Result<Self, KeyRejected> {
        if key_bytes.len() != alg.private_key_len() {
            return Err(KeyRejected::wrong_algorithm());
        }
        let key = rind::agreement::PrivateKey::from_scalar(alg.rind(), key_bytes)
            .map_err(KeyRejected::rind)?;
        Ok(Self { key })
    }

    /// The public key to send to the peer.
    pub fn compute_public_key(&self) -> Result<PublicKey, Unspecified> {
        Ok(PublicKey {
            key: self.key.public_key().clone(),
        })
    }

    /// The key's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static Algorithm {
        Algorithm::from_rind(self.key.algorithm())
    }
}

impl fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PrivateKey {{ algorithm: {:?} }}", self.algorithm())
    }
}

impl AsDer<EcPrivateKeyRfc5915Der<'static>> for PrivateKey {
    /// Encodes a NIST curve's key as a SEC1 (RFC 5915) `ECPrivateKey`
    /// naming its curve and holding its public key; X25519 is refused.
    fn as_der(&self) -> Result<EcPrivateKeyRfc5915Der<'static>, Unspecified> {
        let ecdsa = self.algorithm().ecdsa().ok_or(Unspecified)?;
        let pkcs8 = self.key.to_pkcs8();
        let pair = rind::ecdsa::KeyPair::from_pkcs8(ecdsa, pkcs8.as_ref()).map_err(unspecified)?;
        Ok(EcPrivateKeyRfc5915Der::new(
            pair.to_sec1().as_ref().to_vec(),
        ))
    }
}

impl AsDer<Pkcs8V1Der<'static>> for PrivateKey {
    /// Encodes a NIST curve's key as PKCS#8 v1; X25519 is refused.
    fn as_der(&self) -> Result<Pkcs8V1Der<'static>, Unspecified> {
        if self.algorithm().id == AlgorithmId::X25519 {
            return Err(Unspecified);
        }
        Ok(Pkcs8V1Der::new(self.key.to_pkcs8().as_ref().to_vec()))
    }
}

impl AsBigEndian<EcPrivateKeyBin<'static>> for PrivateKey {
    /// A NIST curve's big-endian scalar; X25519 is refused.
    fn as_be_bytes(&self) -> Result<EcPrivateKeyBin<'static>, Unspecified> {
        if self.algorithm().id == AlgorithmId::X25519 {
            return Err(Unspecified);
        }
        Ok(EcPrivateKeyBin::new(self.key.to_scalar().as_ref().to_vec()))
    }
}

impl AsBigEndian<Curve25519SeedBin<'static>> for PrivateKey {
    /// X25519's 32-byte private key; a NIST curve is refused.
    fn as_be_bytes(&self) -> Result<Curve25519SeedBin<'static>, Unspecified> {
        if self.algorithm().id != AlgorithmId::X25519 {
            return Err(Unspecified);
        }
        Ok(Curve25519SeedBin::new(
            self.key.to_scalar().as_ref().to_vec(),
        ))
    }
}

/// A public key for key agreement: X25519's 32 bytes, or an uncompressed
/// point.
#[derive(Clone)]
pub struct PublicKey {
    key: rind::agreement::PublicKey,
}

impl PublicKey {
    /// The key's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static Algorithm {
        Algorithm::from_rind(self.key.algorithm())
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PublicKey {{ algorithm: {:?}, bytes: ", self.algorithm())?;
        fmt::Debug::fmt(&crate::Hex(self.as_ref()), f)?;
        f.write_str(" }")
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.key.as_ref()
    }
}

impl AsDer<PublicKeyX509Der<'static>> for PublicKey {
    /// Encodes the key as a `SubjectPublicKeyInfo`.
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        Ok(PublicKeyX509Der::new(self.key.to_spki().as_ref().to_vec()))
    }
}

impl AsBigEndian<EcPublicKeyCompressedBin<'static>> for PublicKey {
    /// A NIST curve's compressed point; X25519 is refused.
    fn as_be_bytes(&self) -> Result<EcPublicKeyCompressedBin<'static>, Unspecified> {
        if self.algorithm().id == AlgorithmId::X25519 {
            return Err(Unspecified);
        }
        Ok(EcPublicKeyCompressedBin::new(compress(self.as_ref())))
    }
}

impl AsBigEndian<EcPublicKeyUncompressedBin<'static>> for PublicKey {
    /// A NIST curve's uncompressed point; X25519 is refused.
    fn as_be_bytes(&self) -> Result<EcPublicKeyUncompressedBin<'static>, Unspecified> {
        if self.algorithm().id == AlgorithmId::X25519 {
            return Err(Unspecified);
        }
        Ok(EcPublicKeyUncompressedBin::new(self.as_ref().to_vec()))
    }
}

/// Compresses an uncompressed X9.62 point, which is public.
pub(crate) fn compress(uncompressed: &[u8]) -> Vec<u8> {
    let coordinates = &uncompressed[1..];
    let (x, y) = coordinates.split_at(coordinates.len() / 2);
    let mut compressed = Vec::with_capacity(1 + x.len());
    compressed.push(0x02 | (y[y.len() - 1] & 1));
    compressed.extend_from_slice(x);
    compressed
}

/// A peer's encoded public key, parsed only when used.
#[derive(Clone)]
pub struct UnparsedPublicKey<B: AsRef<[u8]>> {
    alg: &'static Algorithm,
    bytes: B,
}

impl<B: Copy + AsRef<[u8]>> Copy for UnparsedPublicKey<B> {}

impl<B: fmt::Debug + AsRef<[u8]>> fmt::Debug for UnparsedPublicKey<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UnparsedPublicKey {{ algorithm: {:?}, bytes: ", self.alg)?;
        fmt::Debug::fmt(&crate::Hex(self.bytes.as_ref()), f)?;
        f.write_str(" }")
    }
}

impl<B: AsRef<[u8]>> UnparsedPublicKey<B> {
    /// Wraps the peer's encoded key for `algorithm`.
    pub fn new(algorithm: &'static Algorithm, bytes: B) -> Self {
        Self {
            alg: algorithm,
            bytes,
        }
    }

    /// The key's algorithm.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.alg
    }

    /// The encoded key.
    pub fn bytes(&self) -> &B {
        &self.bytes
    }

    fn parse(&self) -> Result<ParsedPublicKey, KeyRejected> {
        ParsedPublicKey::new(self.bytes.as_ref(), self.alg)
    }
}

/// A peer's public key, parsed and checked.
#[derive(Debug, Clone)]
pub struct ParsedPublicKey {
    format: ParsedPublicKeyFormat,
    key: rind::agreement::PublicKey,
    bytes: Box<[u8]>,
}

/// The format a public key was parsed from.
#[non_exhaustive]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ParsedPublicKeyFormat {
    /// An X.509 `SubjectPublicKeyInfo`.
    X509,
    /// An uncompressed X9.62 point.
    Uncompressed,
    /// A compressed X9.62 point.
    Compressed,
    /// A hybrid X9.62 point, which rind refuses.
    Hybrid,
    /// X25519's raw 32 bytes.
    Raw,
    /// Unknown.
    Unknown,
}

impl ParsedPublicKey {
    fn new(bytes: &[u8], algorithm: &'static Algorithm) -> Result<Self, KeyRejected> {
        if bytes.is_empty() {
            return Err(KeyRejected::unspecified());
        }
        let (format, key) = match rind::agreement::PublicKey::from_spki(algorithm.rind(), bytes) {
            Ok(key) => (ParsedPublicKeyFormat::X509, key),
            Err(_) => {
                let key = rind::agreement::PublicKey::new(algorithm.rind(), bytes)
                    .map_err(|_| KeyRejected::invalid_encoding())?;
                let format = match (algorithm.id, bytes[0]) {
                    (AlgorithmId::X25519, _) => ParsedPublicKeyFormat::Raw,
                    (_, 0x02 | 0x03) => ParsedPublicKeyFormat::Compressed,
                    (_, 0x04) => ParsedPublicKeyFormat::Uncompressed,
                    _ => ParsedPublicKeyFormat::Unknown,
                };
                (format, key)
            }
        };
        Ok(Self {
            format,
            key,
            bytes: bytes.into(),
        })
    }

    /// The format the key was parsed from.
    #[must_use]
    pub fn format(&self) -> ParsedPublicKeyFormat {
        self.format
    }

    /// The key's algorithm.
    #[must_use]
    pub fn alg(&self) -> &'static Algorithm {
        Algorithm::from_rind(self.key.algorithm())
    }
}

impl AsRef<[u8]> for ParsedPublicKey {
    /// The bytes the key was parsed from.
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<B: AsRef<[u8]>> TryFrom<&UnparsedPublicKey<B>> for ParsedPublicKey {
    type Error = KeyRejected;

    fn try_from(upk: &UnparsedPublicKey<B>) -> Result<Self, Self::Error> {
        upk.parse()
    }
}

impl<B: AsRef<[u8]>> TryFrom<UnparsedPublicKey<B>> for ParsedPublicKey {
    type Error = KeyRejected;

    fn try_from(upk: UnparsedPublicKey<B>) -> Result<Self, Self::Error> {
        upk.parse()
    }
}

/// Agrees on a secret with the peer's public key, keeping `my_private_key`
/// for more agreements, and returns `kdf` of it.
///
/// Returns `error_value` if the peer's key fails to parse, is for another
/// algorithm, or is off the curve, or if X25519 agrees on all zeros.
pub fn agree<B: TryInto<ParsedPublicKey>, F, R, E>(
    my_private_key: &PrivateKey,
    peer_public_key: B,
    error_value: E,
    kdf: F,
) -> Result<R, E>
where
    F: FnOnce(&[u8]) -> Result<R, E>,
{
    let Ok(peer) = peer_public_key.try_into() else {
        return Err(error_value);
    };
    if peer.key.algorithm() != my_private_key.key.algorithm() {
        return Err(error_value);
    }
    match my_private_key.key.agree(peer.key.as_ref()) {
        Ok(secret) => kdf(secret.as_ref()),
        Err(_) => Err(error_value),
    }
}

/// A private key for one key agreement; wiped on drop.
pub struct EphemeralPrivateKey(PrivateKey);

impl EphemeralPrivateKey {
    /// Generates a private key for `alg` from the system random source.
    ///
    /// rind draws from that source itself, which `rng`, the only
    /// [`SecureRandom`], also is.
    pub fn generate(alg: &'static Algorithm, rng: &dyn SecureRandom) -> Result<Self, Unspecified> {
        let _ = rng;
        PrivateKey::generate(alg).map(Self)
    }

    /// The public key to send to the peer.
    pub fn compute_public_key(&self) -> Result<PublicKey, Unspecified> {
        self.0.compute_public_key()
    }

    /// The key's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static Algorithm {
        self.0.algorithm()
    }
}

impl fmt::Debug for EphemeralPrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "EphemeralPrivateKey {{ algorithm: {:?} }}",
            self.algorithm()
        )
    }
}

/// Agrees on a secret with the peer's public key, consuming
/// `my_private_key`, and returns `kdf` of it, as [`agree`] does.
#[allow(clippy::needless_pass_by_value)]
pub fn agree_ephemeral<B: TryInto<ParsedPublicKey>, F, R, E>(
    my_private_key: EphemeralPrivateKey,
    peer_public_key: B,
    error_value: E,
    kdf: F,
) -> Result<R, E>
where
    F: FnOnce(&[u8]) -> Result<R, E>,
{
    agree(&my_private_key.0, peer_public_key, error_value, kdf)
}
