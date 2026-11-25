//! <h1 align="center">rind-rcgen</h1>
//! <img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">
//!
//! This crate provides rcgen's [`KeyPair`](https://docs.rs/rcgen/0.14/rcgen/struct.KeyPair.html)
//! for [rcgen](https://github.com/rustls/rcgen), backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
//! It generates and loads ECDSA P-256 and P-384, Ed25519, and RSA keys, as
//! rcgen's `aws_lc_rs` backend does.
//!
//! Build rcgen with `default-features = false` so it compiles no other crypto backend,
//! and use `rind_rcgen::KeyPair` where rcgen's `crypto` feature would give `rcgen::KeyPair`.
//! Without that feature, rcgen needs each certificate's serial number set explicitly,
//! and leaves its key identifiers empty unless `key_identifier_method` is set.
//!
//! ```rust
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use rind_rcgen::KeyPair;
//!
//! let key = KeyPair::generate()?;
//!
//! let mut params = rcgen::CertificateParams::new(["localhost".to_string()])?;
//! params.serial_number = Some(rcgen::SerialNumber::from(1));
//!
//! let cert = params.self_signed(&key)?;
//! let key = key.serialize_der();
//! # Ok(())
//! # }
//! ```
#![cfg_attr(docsrs, feature(doc_cfg))]

use core::fmt;

use rcgen::{
    Error, PKCS_ECDSA_P256_SHA256, PKCS_ECDSA_P384_SHA384, PKCS_ED25519, PKCS_RSA_SHA256,
    PKCS_RSA_SHA384, PKCS_RSA_SHA512, PublicKeyData, SignatureAlgorithm,
};
use rind::ecdsa::{KeyPair as EcdsaKeyPair, SigningAlgorithm as EcdsaSigningAlgorithm};
use rind::ed25519::KeyPair as Ed25519KeyPair;
use rind::rsa::{KeyPair as RsaKeyPair, SigningAlgorithm as RsaSigningAlgorithm};
use rind::{ecdsa, rsa};
use rustls_pki_types::{PrivateKeyDer, PrivatePkcs8KeyDer};

#[cfg(feature = "pem")]
mod pem;

/// A key pair used to sign certificates and CSRs.
pub struct KeyPair {
    key: Key,
    algorithm: &'static SignatureAlgorithm,
    serialized_der: Wiped,
}

#[allow(clippy::large_enum_variant)]
enum Key {
    Ecdsa(EcdsaKeyPair),
    Ed25519(Ed25519KeyPair),
    Rsa(RsaKeyPair, &'static RsaSigningAlgorithm),
}

impl KeyPair {
    /// Generates a random ECDSA P-256 key pair.
    pub fn generate() -> Result<Self, Error> {
        Self::generate_for(&PKCS_ECDSA_P256_SHA256)
    }

    /// Generates a random key pair for `alg`: ECDSA P-256 or P-384, Ed25519,
    /// or RSA, whose modulus is then 2048 bits.
    pub fn generate_for(alg: &'static SignatureAlgorithm) -> Result<Self, Error> {
        let key = match signer(alg)? {
            Signer::Ecdsa(signing) => EcdsaKeyPair::generate(signing).map(Key::Ecdsa),
            Signer::Ed25519 => Ed25519KeyPair::generate().map(Key::Ed25519),
            Signer::Rsa(padding) => {
                RsaKeyPair::generate(rsa::KeySize::Rsa2048).map(|key| Key::Rsa(key, padding))
            }
        };
        Self::generated(key, alg)
    }

    /// Generates a random RSA key pair of `key_size` for `alg`, which must be
    /// an RSA algorithm.
    pub fn generate_rsa_for(
        alg: &'static SignatureAlgorithm,
        key_size: RsaKeySize,
    ) -> Result<Self, Error> {
        let Ok(Signer::Rsa(padding)) = signer(alg) else {
            return Err(Error::KeyGenerationUnavailable);
        };
        let size = match key_size {
            RsaKeySize::_2048 => rsa::KeySize::Rsa2048,
            RsaKeySize::_3072 => rsa::KeySize::Rsa3072,
            RsaKeySize::_4096 => rsa::KeySize::Rsa4096,
        };
        let key = RsaKeyPair::generate(size).map(|key| Key::Rsa(key, padding));
        Self::generated(key, alg)
    }

    /// Returns the key pair's signature algorithm.
    pub fn algorithm(&self) -> &'static SignatureAlgorithm {
        self.algorithm
    }

    /// Loads a PKCS#8 private key that signs with `alg`: ECDSA P-256 or P-384,
    /// Ed25519, or RSA PKCS#1 v1.5.
    pub fn from_pkcs8_der_and_sign_algo(
        pkcs8: &PrivatePkcs8KeyDer<'_>,
        alg: &'static SignatureAlgorithm,
    ) -> Result<Self, Error> {
        let der = pkcs8.secret_pkcs8_der();
        let key = match signer(alg)? {
            Signer::Ecdsa(signing) => EcdsaKeyPair::from_pkcs8(signing, der).map(Key::Ecdsa),
            Signer::Ed25519 => Ed25519KeyPair::from_pkcs8(der).map(Key::Ed25519),
            Signer::Rsa(padding) => RsaKeyPair::from_pkcs8(der).map(|key| Key::Rsa(key, padding)),
        };
        Ok(Self::new(key.map_err(rejected)?, alg, der.to_vec()))
    }

    /// Loads a private key that signs with `alg`: PKCS#8, or SEC1 for ECDSA
    /// and PKCS#1 for RSA. Its serialized DER is then the key as given.
    pub fn from_der_and_sign_algo(
        key: &PrivateKeyDer<'_>,
        alg: &'static SignatureAlgorithm,
    ) -> Result<Self, Error> {
        let der = key.secret_der();
        let loaded = match signer(alg)? {
            // As aws-lc-rs, which reads either for ECDSA whatever the key's
            // label, and PKCS#1 for RSA unless it is labeled PKCS#8.
            Signer::Ecdsa(signing) => EcdsaKeyPair::from_pkcs8(signing, der)
                .or_else(|_| EcdsaKeyPair::from_sec1(signing, der))
                .map(Key::Ecdsa),
            Signer::Ed25519 => Ed25519KeyPair::from_pkcs8(der).map(Key::Ed25519),
            Signer::Rsa(padding) => match key {
                PrivateKeyDer::Pkcs8(_) => RsaKeyPair::from_pkcs8(der),
                _ => RsaKeyPair::from_pkcs1(der),
            }
            .map(|key| Key::Rsa(key, padding)),
        };
        Ok(Self::new(loaded.map_err(rejected)?, alg, der.to_vec()))
    }

    /// Parses a PEM private key, PKCS#8, SEC1, or PKCS#1, finding its algorithm.
    #[cfg(feature = "pem")]
    pub fn from_pem(pem_str: &str) -> Result<Self, Error> {
        Self::try_from(pem::decode(pem_str)?.as_slice())
    }

    /// Parses a PEM PKCS#8 private key that signs with `alg`.
    #[cfg(feature = "pem")]
    pub fn from_pkcs8_pem_and_sign_algo(
        pem_str: &str,
        alg: &'static SignatureAlgorithm,
    ) -> Result<Self, Error> {
        let pem = pem::decode(pem_str)?;
        Self::from_pkcs8_der_and_sign_algo(&PrivatePkcs8KeyDer::from(pem.as_slice()), alg)
    }

    /// Parses a PEM private key that signs with `alg`: PKCS#8, or SEC1 for
    /// ECDSA and PKCS#1 for RSA.
    #[cfg(feature = "pem")]
    pub fn from_pem_and_sign_algo(
        pem_str: &str,
        alg: &'static SignatureAlgorithm,
    ) -> Result<Self, Error> {
        let pem = pem::decode(pem_str)?;
        let key =
            PrivateKeyDer::try_from(pem.as_slice()).map_err(|_| Error::CouldNotParseKeyPair)?;
        Self::from_der_and_sign_algo(&key, alg)
    }

    /// Returns the raw public key, as `der_bytes` does.
    pub fn public_key_raw(&self) -> &[u8] {
        self.der_bytes()
    }

    /// Returns whether this key pair signs with `signature_algorithm`.
    pub fn is_compatible(&self, signature_algorithm: &SignatureAlgorithm) -> bool {
        self.algorithm == signature_algorithm
    }

    /// Returns the signature algorithms this key pair signs with.
    pub fn compatible_algs(&self) -> impl Iterator<Item = &'static SignatureAlgorithm> {
        std::iter::once(self.algorithm)
    }

    /// Encodes the public key as a PEM SubjectPublicKeyInfo.
    #[cfg(feature = "pem")]
    pub fn public_key_pem(&self) -> String {
        pem::encode("PUBLIC KEY", &self.subject_public_key_info())
    }

    /// Returns a copy of the key pair's DER: the key as loaded, or PKCS#8
    /// for a generated one.
    pub fn serialize_der(&self) -> Vec<u8> {
        self.serialized_der.0.clone()
    }

    /// Returns the key pair's DER: the key as loaded, or PKCS#8 for a
    /// generated one.
    pub fn serialized_der(&self) -> &[u8] {
        &self.serialized_der.0
    }

    /// Encodes the key pair's DER as PEM labeled `PRIVATE KEY`, as rcgen
    /// does, even when that DER is a loaded SEC1 or PKCS#1 key.
    #[cfg(feature = "pem")]
    pub fn serialize_pem(&self) -> String {
        pem::encode("PRIVATE KEY", self.serialized_der())
    }

    /// A key pair just generated, whose serialized DER is its PKCS#8.
    fn generated(
        key: Result<Key, rind::Error>,
        algorithm: &'static SignatureAlgorithm,
    ) -> Result<Self, Error> {
        let key = key.map_err(|_| Error::RingUnspecified)?;
        let pkcs8 = match &key {
            Key::Ecdsa(key) => key.to_pkcs8(),
            Key::Ed25519(key) => key.to_pkcs8(),
            Key::Rsa(key, _) => key.to_pkcs8(),
        };
        let serialized_der = pkcs8.as_ref().to_vec();
        Ok(Self::new(key, algorithm, serialized_der))
    }

    fn new(key: Key, algorithm: &'static SignatureAlgorithm, serialized_der: Vec<u8>) -> Self {
        Self {
            key,
            algorithm,
            serialized_der: Wiped(serialized_der),
        }
    }
}

/// The modulus size of an RSA key [`KeyPair::generate_rsa_for`] generates.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RsaKeySize {
    /// 2048 bits.
    _2048,
    /// 3072 bits.
    _3072,
    /// 4096 bits.
    _4096,
}

/// The key pair's DER, wiped on drop, as rind wipes the key itself.
struct Wiped(Vec<u8>);

impl Drop for Wiped {
    fn drop(&mut self) {
        zeroize::Zeroize::zeroize(&mut self.0);
    }
}

/// Clears the key pair's DER copy, as rcgen's `zeroize` feature does; the
/// rind key it wraps is wiped on drop.
#[cfg(feature = "zeroize")]
impl zeroize::Zeroize for KeyPair {
    fn zeroize(&mut self) {
        self.serialized_der.0.zeroize();
    }
}

/// How rind signs for an rcgen algorithm.
enum Signer {
    Ecdsa(&'static EcdsaSigningAlgorithm),
    Ed25519,
    Rsa(&'static RsaSigningAlgorithm),
}

/// Finds how rind signs for `algorithm`, refusing one it doesn't support.
fn signer(algorithm: &SignatureAlgorithm) -> Result<Signer, Error> {
    // rcgen's algorithms are statics compared by value, so this can't match on them.
    Ok(if *algorithm == PKCS_ECDSA_P256_SHA256 {
        Signer::Ecdsa(&ecdsa::sign::P256_SHA256_ASN1)
    } else if *algorithm == PKCS_ECDSA_P384_SHA384 {
        Signer::Ecdsa(&ecdsa::sign::P384_SHA384_ASN1)
    } else if *algorithm == PKCS_ED25519 {
        Signer::Ed25519
    } else if *algorithm == PKCS_RSA_SHA256 {
        Signer::Rsa(&rsa::sign::PKCS1_SHA256)
    } else if *algorithm == PKCS_RSA_SHA384 {
        Signer::Rsa(&rsa::sign::PKCS1_SHA384)
    } else if *algorithm == PKCS_RSA_SHA512 {
        Signer::Rsa(&rsa::sign::PKCS1_SHA512)
    } else {
        return Err(Error::UnsupportedSignatureAlgorithm);
    })
}

/// Keeps rind's reason for refusing a key, as rcgen does for its backends.
fn rejected(err: rind::Error) -> Error {
    match err {
        rind::Error::KeyRejected(reason) => Error::RingKeyRejected(reason.to_string()),
        other => Error::RingKeyRejected(other.to_string()),
    }
}

impl PublicKeyData for KeyPair {
    // rcgen takes the uncompressed point for ECDSA, the 32 bytes for Ed25519,
    // and PKCS#1 `RSAPublicKey` DER for RSA, which is rind's encoding of each.
    fn der_bytes(&self) -> &[u8] {
        match &self.key {
            Key::Ecdsa(key) => key.public_key().as_ref(),
            Key::Ed25519(key) => key.public_key().as_ref(),
            Key::Rsa(key, _) => key.public_key().as_ref(),
        }
    }

    fn algorithm(&self) -> &'static SignatureAlgorithm {
        self.algorithm
    }
}

impl rcgen::SigningKey for KeyPair {
    fn sign(&self, msg: &[u8]) -> Result<Vec<u8>, Error> {
        let signature = match &self.key {
            Key::Ecdsa(key) => key.sign(msg).map(|s| s.as_ref().to_vec()),
            Key::Ed25519(key) => Ok(key.sign(msg).as_ref().to_vec()),
            Key::Rsa(key, padding) => key.sign(padding, msg).map(|s| s.as_ref().to_vec()),
        };
        signature.map_err(|_| Error::RingUnspecified)
    }
}

impl TryFrom<&[u8]> for KeyPair {
    type Error = Error;

    /// Loads a private key, finding its algorithm and encoding as
    /// `rustls_pki_types` does; RSA keys sign with SHA-256.
    fn try_from(key: &[u8]) -> Result<Self, Error> {
        let key = PrivateKeyDer::try_from(key).map_err(|_| Error::CouldNotParseKeyPair)?;
        Self::try_from(&key)
    }
}

impl TryFrom<Vec<u8>> for KeyPair {
    type Error = Error;

    /// Loads a private key, finding its algorithm and encoding as
    /// `rustls_pki_types` does; RSA keys sign with SHA-256.
    fn try_from(key: Vec<u8>) -> Result<Self, Error> {
        Self::try_from(key.as_slice())
    }
}

impl TryFrom<&PrivatePkcs8KeyDer<'_>> for KeyPair {
    type Error = Error;

    /// Loads a PKCS#8 private key, finding its algorithm; RSA keys sign with SHA-256.
    fn try_from(key: &PrivatePkcs8KeyDer<'_>) -> Result<Self, Error> {
        Self::try_from(key.secret_pkcs8_der())
    }
}

impl TryFrom<&PrivateKeyDer<'_>> for KeyPair {
    type Error = Error;

    /// Loads a private key, finding its algorithm: PKCS#8, or SEC1 for ECDSA
    /// and PKCS#1 for RSA, whose keys sign with SHA-256. Its serialized DER
    /// is then the key as given.
    fn try_from(key: &PrivateKeyDer<'_>) -> Result<Self, Error> {
        let der = key.secret_der();
        let pkcs8 = matches!(key, PrivateKeyDer::Pkcs8(_));
        // As aws-lc-rs: PKCS#8 for Ed25519 and ECDSA, then SEC1 for ECDSA,
        // whatever the key's label, and for RSA PKCS#8 or PKCS#1 by its label.
        let (key, alg) = match rind::KeyPair::from_pkcs8(der) {
            Ok(rind::KeyPair::Ed25519(key)) => (Key::Ed25519(key), &PKCS_ED25519),
            Ok(rind::KeyPair::EcdsaP256(key)) => (Key::Ecdsa(key), &PKCS_ECDSA_P256_SHA256),
            Ok(rind::KeyPair::EcdsaP384(key)) => (Key::Ecdsa(key), &PKCS_ECDSA_P384_SHA384),
            Ok(rind::KeyPair::Rsa(key)) if pkcs8 => {
                (Key::Rsa(key, &rsa::sign::PKCS1_SHA256), &PKCS_RSA_SHA256)
            }
            // rcgen names P-521 only with its `aws_lc_rs` feature.
            Ok(rind::KeyPair::EcdsaP521(_)) => return Err(Error::CouldNotParseKeyPair),
            _ => {
                let sec1 = |alg| EcdsaKeyPair::from_sec1(alg, der).map(Key::Ecdsa);
                if let Ok(key) = sec1(&ecdsa::sign::P256_SHA256_ASN1) {
                    (key, &PKCS_ECDSA_P256_SHA256)
                } else if let Ok(key) = sec1(&ecdsa::sign::P384_SHA384_ASN1) {
                    (key, &PKCS_ECDSA_P384_SHA384)
                } else if let (false, Ok(key)) = (pkcs8, RsaKeyPair::from_pkcs1(der)) {
                    (Key::Rsa(key, &rsa::sign::PKCS1_SHA256), &PKCS_RSA_SHA256)
                } else {
                    return Err(Error::CouldNotParseKeyPair);
                }
            }
        };
        Ok(Self::new(key, alg, der.to_vec()))
    }
}

impl From<KeyPair> for PrivatePkcs8KeyDer<'static> {
    fn from(key: KeyPair) -> Self {
        key.serialize_der().into()
    }
}

impl From<KeyPair> for PrivateKeyDer<'static> {
    fn from(key: KeyPair) -> Self {
        Self::from(PrivatePkcs8KeyDer::from(key))
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("algorithm", self.algorithm)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// rcgen requires `Debug`, which shows the algorithm but no key.
    #[test]
    fn debug_shows_the_algorithm_without_the_key() {
        let key = KeyPair::generate_for(&rcgen::PKCS_ED25519).unwrap();
        assert_eq!(
            format!("{key:?}"),
            format!("KeyPair {{ algorithm: {:?}, .. }}", rcgen::PKCS_ED25519)
        );
    }
}
