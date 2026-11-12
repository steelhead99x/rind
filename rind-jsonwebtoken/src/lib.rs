//! <h1 align="center">rind-jsonwebtoken</h1>
//! <img width="40%" align="right" src="https://raw.githubusercontent.com/moq-dev/rind/main/admin/logo.png">
//!
//! This crate provides an integration between [jsonwebtoken](https://github.com/Keats/jsonwebtoken) and [rind](https://github.com/moq-dev/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
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
use rind::rsa::PublicKeyComponents;
use rind::signature::{
    EcdsaKeyPair, EcdsaSigningAlgorithm, Ed25519KeyPair, PublicKey, RsaKeyPair,
    RsaSigningAlgorithm, RsaVerificationAlgorithm, VerificationAlgorithm, sign, verify,
};
use rind::{digest, hmac};

/// A jsonwebtoken [`CryptoProvider`] that signs and verifies every algorithm with rind.
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
        Algorithm::ES256 => ecdsa(&sign::ECDSA_P256_SHA256_FIXED)?,
        Algorithm::ES384 => ecdsa(&sign::ECDSA_P384_SHA384_FIXED)?,
        Algorithm::EdDSA => signer(
            algorithm,
            Ed25519KeyPair::from_pkcs8(der).map_err(|_| ErrorKind::InvalidEddsaKey)?,
        ),
        Algorithm::RS256 => rsa(&sign::RSA_PKCS1_SHA256)?,
        Algorithm::RS384 => rsa(&sign::RSA_PKCS1_SHA384)?,
        Algorithm::RS512 => rsa(&sign::RSA_PKCS1_SHA512)?,
        Algorithm::PS256 => rsa(&sign::RSA_PSS_SHA256)?,
        Algorithm::PS384 => rsa(&sign::RSA_PSS_SHA384)?,
        Algorithm::PS512 => rsa(&sign::RSA_PSS_SHA512)?,
        _ => return Err(ErrorKind::InvalidAlgorithm.into()),
    })
}

fn new_verifier(algorithm: &Algorithm, key: &DecodingKey) -> Result<Box<dyn JwtVerifier>> {
    if key.family() != algorithm.family() {
        return Err(ErrorKind::InvalidKeyFormat.into());
    }

    // Parsing here refuses a malformed key before any token arrives.
    let algorithm = *algorithm;
    let parse = |verification: &'static VerificationAlgorithm,
                 der: &[u8],
                 invalid: ErrorKind|
     -> Result<Box<dyn JwtVerifier>> {
        let key = PublicKey::new(verification, der).map_err(|_| invalid)?;
        Ok(verifier(algorithm, key))
    };
    let ecdsa = |verification: &'static VerificationAlgorithm| {
        parse(
            verification,
            key.try_get_as_bytes()?,
            ErrorKind::InvalidEcdsaKey,
        )
    };
    let rsa = |verification: &'static RsaVerificationAlgorithm| -> Result<Box<dyn JwtVerifier>> {
        let key = match key.kind() {
            DecodingKeyKind::SecretOrDer(der) => PublicKey::new(verification, der),
            DecodingKeyKind::RsaModulusExponent { n, e } => {
                PublicKey::from_components(verification, &PublicKeyComponents { n, e })
            }
        };
        Ok(verifier(algorithm, key.map_err(invalid_rsa)?))
    };

    let hmac = |hmac_algorithm| -> Result<Box<dyn JwtVerifier>> {
        let key = hmac::Key::new(hmac_algorithm, key.try_get_as_bytes()?);
        Ok(verifier(algorithm, key))
    };

    Ok(match algorithm {
        Algorithm::HS256 => hmac(&hmac::HMAC_SHA256)?,
        Algorithm::HS384 => hmac(&hmac::HMAC_SHA384)?,
        Algorithm::HS512 => hmac(&hmac::HMAC_SHA512)?,
        Algorithm::ES256 => ecdsa(&verify::ECDSA_P256_SHA256_FIXED)?,
        Algorithm::ES384 => ecdsa(&verify::ECDSA_P384_SHA384_FIXED)?,
        Algorithm::EdDSA => parse(
            &verify::ED25519,
            key.try_get_as_bytes()?,
            ErrorKind::InvalidEddsaKey,
        )?,
        Algorithm::RS256 => rsa(&verify::RSA_PKCS1_SHA256)?,
        Algorithm::RS384 => rsa(&verify::RSA_PKCS1_SHA384)?,
        Algorithm::RS512 => rsa(&verify::RSA_PKCS1_SHA512)?,
        Algorithm::PS256 => rsa(&verify::RSA_PSS_SHA256)?,
        Algorithm::PS384 => rsa(&verify::RSA_PSS_SHA384)?,
        Algorithm::PS512 => rsa(&verify::RSA_PSS_SHA512)?,
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

impl Verify for PublicKey {
    fn verify_message(&self, message: &[u8], signature: &[u8]) -> RindResult<()> {
        self.verify(message, signature)
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
    // Every RSA algorithm's public key has the same encoding.
    rsa_pub_components_from_public_key(key.public_key(&sign::RSA_PKCS1_SHA256).as_ref())
}

fn rsa_pub_components_from_public_key(der: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
    // Any RSA algorithm refuses the keys rind cannot verify with.
    PublicKey::new(&verify::RSA_PKCS1_SHA256, der).map_err(invalid_rsa)?;
    let key = pkcs1::RsaPublicKey::from_der(der).map_err(invalid_rsa)?;
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
        Algorithm::ES256 => (EllipticCurve::P256, &sign::ECDSA_P256_SHA256_FIXED),
        Algorithm::ES384 => (EllipticCurve::P384, &sign::ECDSA_P384_SHA384_FIXED),
        _ => return Err(ErrorKind::InvalidEcdsaKey.into()),
    };
    let key = EcdsaKeyPair::from_pkcs8(signing, der).map_err(|_| ErrorKind::InvalidEcdsaKey)?;

    // An uncompressed point is 0x04 || x || y.
    let public_key = key.public_key();
    let point = &public_key.as_ref()[1..];
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
