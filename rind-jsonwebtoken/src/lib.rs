//! <h1 align="center">rind-jsonwebtoken</h1>
//! <img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">
//!
//! This crate provides an integration between [jsonwebtoken](https://github.com/Keats/jsonwebtoken) and [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
//!
//! Use it like:
//!
//! ```rust
//! rind_jsonwebtoken::DEFAULT_PROVIDER
//!     .install_default()
//!     .unwrap();
//! ```
//!
//! And then use jsonwebtoken as normal.

use jsonwebtoken::crypto::{CryptoProvider, JwtSigner, JwtVerifier, KeyUtils};
use jsonwebtoken::errors::{Error, ErrorKind, Result};
use jsonwebtoken::jwk::{EllipticCurve, ThumbprintHash};
use jsonwebtoken::signature::{self, Signer, Verifier};
use jsonwebtoken::{Algorithm, DecodingKey, DecodingKeyKind, EncodingKey};
use pkcs1::der::Decode;
use rind::ecdsa::{KeyPair as EcdsaKeyPair, SigningAlgorithm as EcdsaSigningAlgorithm};
use rind::ed25519::KeyPair as Ed25519KeyPair;
use rind::rsa::{
    KeyPair as RsaKeyPair, PublicKeyComponents, SigningAlgorithm as RsaSigningAlgorithm,
    VerificationAlgorithm as RsaVerificationAlgorithm,
};
use rind::{digest, ecdsa, ed25519, hmac, rsa};

/// The jsonwebtoken [`CryptoProvider`] that signs and verifies every algorithm
/// with rind.
pub static DEFAULT_PROVIDER: CryptoProvider = CryptoProvider {
    signer_factory: new_signer,
    verifier_factory: new_verifier,
    key_utils: KeyUtils {
        rsa_pub_components_from_private_key,
        rsa_pub_components_from_public_key,
        ec_pub_components_from_private_key,
        ed_pub_components_from_private_key,
        compute_digest,
    },
};

type RindResult<T> = std::result::Result<T, rind::Error>;

/// A key that signs for exactly one algorithm.
trait Sign {
    fn sign_message(&self, message: &[u8]) -> RindResult<Vec<u8>>;
}

/// A key that verifies for exactly one algorithm.
trait Verify {
    fn verify_message(&self, message: &[u8], signature: &[u8]) -> RindResult<()>;
}

/// A key tagged with the algorithm jsonwebtoken asked for.
struct Keyed<K> {
    algorithm: Algorithm,
    key: K,
}

fn signer<K: Sign + 'static>(algorithm: Algorithm, key: K) -> Box<dyn JwtSigner> {
    Box::new(Keyed { algorithm, key })
}

fn verifier<K: Verify + 'static>(algorithm: Algorithm, key: K) -> Box<dyn JwtVerifier> {
    Box::new(Keyed { algorithm, key })
}

fn new_signer(algorithm: &Algorithm, key: &EncodingKey) -> Result<Box<dyn JwtSigner>> {
    if key.family() != algorithm.family() {
        return Err(ErrorKind::InvalidKeyFormat.into());
    }

    let algorithm = *algorithm;
    let der = key.as_bytes();
    let ecdsa = |signing: &'static EcdsaSigningAlgorithm| -> Result<Box<dyn JwtSigner>> {
        let key = EcdsaKeyPair::from_pkcs8(signing, der).map_err(|_| ErrorKind::InvalidEcdsaKey)?;
        Ok(signer(algorithm, key))
    };
    let rsa = |padding: &'static RsaSigningAlgorithm| -> Result<Box<dyn JwtSigner>> {
        let key = RsaKeyPair::from_pkcs1(der).map_err(invalid_rsa)?;
        Ok(signer(algorithm, (key, padding)))
    };

    Ok(match algorithm {
        // HMAC keeps the keyed state rather than a copy of the secret.
        Algorithm::HS256 => signer(algorithm, hmac::Key::new(&hmac::HMAC_SHA256, der)),
        Algorithm::HS384 => signer(algorithm, hmac::Key::new(&hmac::HMAC_SHA384, der)),
        Algorithm::HS512 => signer(algorithm, hmac::Key::new(&hmac::HMAC_SHA512, der)),
        Algorithm::ES256 => ecdsa(&ecdsa::sign::P256_SHA256_FIXED)?,
        Algorithm::ES384 => ecdsa(&ecdsa::sign::P384_SHA384_FIXED)?,
        Algorithm::EdDSA => signer(
            algorithm,
            Ed25519KeyPair::from_pkcs8(der).map_err(|_| ErrorKind::InvalidEddsaKey)?,
        ),
        Algorithm::RS256 => rsa(&rsa::sign::PKCS1_SHA256)?,
        Algorithm::RS384 => rsa(&rsa::sign::PKCS1_SHA384)?,
        Algorithm::RS512 => rsa(&rsa::sign::PKCS1_SHA512)?,
        Algorithm::PS256 => rsa(&rsa::sign::PSS_SHA256)?,
        Algorithm::PS384 => rsa(&rsa::sign::PSS_SHA384)?,
        Algorithm::PS512 => rsa(&rsa::sign::PSS_SHA512)?,
        _ => return Err(ErrorKind::InvalidAlgorithm.into()),
    })
}

fn new_verifier(algorithm: &Algorithm, key: &DecodingKey) -> Result<Box<dyn JwtVerifier>> {
    if key.family() != algorithm.family() {
        return Err(ErrorKind::InvalidKeyFormat.into());
    }

    // Parsing here refuses a malformed key before any token arrives.
    let algorithm = *algorithm;
    let ecdsa = |verification: &'static ecdsa::VerificationAlgorithm| {
        let der = key.try_get_as_bytes()?;
        // The point or SPKI, as aws-lc-rs's verifier takes either.
        let key = ecdsa::PublicKey::new(verification, der)
            .or_else(|_| ecdsa::PublicKey::from_spki(verification, der))
            .map_err(|_| ErrorKind::InvalidEcdsaKey)?;
        Ok::<_, Error>(verifier(algorithm, key))
    };
    let rsa = |verification: &'static RsaVerificationAlgorithm| -> Result<Box<dyn JwtVerifier>> {
        let key = match key.kind() {
            // PKCS#1 or SPKI, as aws-lc-rs's verifier takes either.
            DecodingKeyKind::SecretOrDer(der) => {
                rsa::PublicKey::new(der).or_else(|_| rsa::PublicKey::from_spki(der))
            }
            DecodingKeyKind::RsaModulusExponent { n, e } => {
                rsa::PublicKey::from_components(&PublicKeyComponents { n, e })
            }
        };
        Ok(verifier(
            algorithm,
            (key.map_err(invalid_rsa)?, verification),
        ))
    };

    let hmac = |hmac_algorithm| -> Result<Box<dyn JwtVerifier>> {
        let key = hmac::Key::new(hmac_algorithm, key.try_get_as_bytes()?);
        Ok(verifier(algorithm, key))
    };

    Ok(match algorithm {
        Algorithm::HS256 => hmac(&hmac::HMAC_SHA256)?,
        Algorithm::HS384 => hmac(&hmac::HMAC_SHA384)?,
        Algorithm::HS512 => hmac(&hmac::HMAC_SHA512)?,
        Algorithm::ES256 => ecdsa(&ecdsa::verify::P256_SHA256_FIXED)?,
        Algorithm::ES384 => ecdsa(&ecdsa::verify::P384_SHA384_FIXED)?,
        Algorithm::EdDSA => {
            // The raw key or SPKI, as aws-lc-rs's verifier takes either.
            let der = key.try_get_as_bytes()?;
            let key = ed25519::PublicKey::new(der)
                .or_else(|_| ed25519::PublicKey::from_spki(der))
                .map_err(|_| ErrorKind::InvalidEddsaKey)?;
            verifier(algorithm, key)
        }
        Algorithm::RS256 => rsa(&rsa::verify::PKCS1_SHA256)?,
        Algorithm::RS384 => rsa(&rsa::verify::PKCS1_SHA384)?,
        Algorithm::RS512 => rsa(&rsa::verify::PKCS1_SHA512)?,
        Algorithm::PS256 => rsa(&rsa::verify::PSS_SHA256)?,
        Algorithm::PS384 => rsa(&rsa::verify::PSS_SHA384)?,
        Algorithm::PS512 => rsa(&rsa::verify::PSS_SHA512)?,
        _ => return Err(ErrorKind::InvalidAlgorithm.into()),
    })
}

impl Sign for hmac::Key {
    fn sign_message(&self, message: &[u8]) -> RindResult<Vec<u8>> {
        Ok(hmac::sign(self, message).as_ref().to_vec())
    }
}

impl Verify for hmac::Key {
    fn verify_message(&self, message: &[u8], signature: &[u8]) -> RindResult<()> {
        hmac::verify(self, message, signature)
    }
}

impl Sign for EcdsaKeyPair {
    fn sign_message(&self, message: &[u8]) -> RindResult<Vec<u8>> {
        Ok(self.sign(message)?.as_ref().to_vec())
    }
}

impl Sign for Ed25519KeyPair {
    fn sign_message(&self, message: &[u8]) -> RindResult<Vec<u8>> {
        Ok(self.sign(message).as_ref().to_vec())
    }
}

// An RSA key serves six algorithms, so it carries the padding it was made for.
impl Sign for (RsaKeyPair, &'static RsaSigningAlgorithm) {
    fn sign_message(&self, message: &[u8]) -> RindResult<Vec<u8>> {
        let (key, padding) = self;
        Ok(key.sign(padding, message)?.as_ref().to_vec())
    }
}

impl Verify for ecdsa::PublicKey {
    fn verify_message(&self, message: &[u8], signature: &[u8]) -> RindResult<()> {
        self.verify(message, signature)
    }
}

impl Verify for ed25519::PublicKey {
    fn verify_message(&self, message: &[u8], signature: &[u8]) -> RindResult<()> {
        self.verify(message, signature)
    }
}

// An RSA public key serves six algorithms, so it carries the one it verifies.
impl Verify for (rsa::PublicKey, &'static RsaVerificationAlgorithm) {
    fn verify_message(&self, message: &[u8], signature: &[u8]) -> RindResult<()> {
        let (key, algorithm) = self;
        key.verify(algorithm, message, signature)
    }
}

impl<K: Sign> Signer<Vec<u8>> for Keyed<K> {
    fn try_sign(&self, message: &[u8]) -> std::result::Result<Vec<u8>, signature::Error> {
        self.key
            .sign_message(message)
            .map_err(signature::Error::from_source)
    }
}

impl<K: Verify> Verifier<Vec<u8>> for Keyed<K> {
    fn verify(
        &self,
        message: &[u8],
        signature: &Vec<u8>,
    ) -> std::result::Result<(), signature::Error> {
        self.key
            .verify_message(message, signature)
            .map_err(signature::Error::from_source)
    }
}

impl<K: Sign> JwtSigner for Keyed<K> {
    fn algorithm(&self) -> Algorithm {
        self.algorithm
    }
}

impl<K: Verify> JwtVerifier for Keyed<K> {
    fn algorithm(&self) -> Algorithm {
        self.algorithm
    }
}

fn invalid_rsa(error: impl std::fmt::Display) -> Error {
    ErrorKind::InvalidRsaKey(error.to_string()).into()
}

fn rsa_pub_components_from_private_key(der: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
    let key = RsaKeyPair::from_pkcs1(der).map_err(invalid_rsa)?;
    rsa_pub_components_from_public_key(key.public_key().as_ref())
}

fn rsa_pub_components_from_public_key(der: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
    // Refuses the keys rind cannot parse.
    rsa::PublicKey::new(der).map_err(invalid_rsa)?;
    let key = pkcs1::RsaPublicKeyRef::from_der(der).map_err(invalid_rsa)?;
    Ok((
        key.modulus.as_bytes().to_vec(),
        key.public_exponent.as_bytes().to_vec(),
    ))
}

fn ec_pub_components_from_private_key(
    der: &[u8],
    algorithm: Algorithm,
) -> Result<(EllipticCurve, Vec<u8>, Vec<u8>)> {
    let (curve, signing) = match algorithm {
        Algorithm::ES256 => (EllipticCurve::P256, &ecdsa::sign::P256_SHA256_FIXED),
        Algorithm::ES384 => (EllipticCurve::P384, &ecdsa::sign::P384_SHA384_FIXED),
        _ => return Err(ErrorKind::InvalidEcdsaKey.into()),
    };
    let key = EcdsaKeyPair::from_pkcs8(signing, der).map_err(|_| ErrorKind::InvalidEcdsaKey)?;

    // An uncompressed point is 0x04 || x || y.
    let point = &key.public_key().as_ref()[1..];
    let (x, y) = point.split_at(point.len() / 2);
    Ok((curve, x.to_vec(), y.to_vec()))
}

fn ed_pub_components_from_private_key(der: &[u8], curve: &EllipticCurve) -> Result<Vec<u8>> {
    match curve {
        EllipticCurve::Ed25519 => Ok(Ed25519KeyPair::from_pkcs8(der)
            .map_err(|_| ErrorKind::InvalidEddsaKey)?
            .public_key()
            .as_ref()
            .to_vec()),
        _ => Err(ErrorKind::InvalidAlgorithm.into()),
    }
}

fn compute_digest(data: &[u8], hash: ThumbprintHash) -> Result<Vec<u8>> {
    let algorithm = match hash {
        ThumbprintHash::SHA256 => &digest::SHA256,
        ThumbprintHash::SHA384 => &digest::SHA384,
        ThumbprintHash::SHA512 => &digest::SHA512,
        _ => return Err(ErrorKind::InvalidAlgorithm.into()),
    };
    Ok(digest::digest(algorithm, data).as_ref().to_vec())
}
