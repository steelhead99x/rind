//! <h1 align="center">rind-rcgen</h1>
//! <img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">
//!
//! This crate provides rcgen's [`KeyPair`](https://docs.rs/rcgen/0.14/rcgen/struct.KeyPair.html)
//! for [rcgen](https://github.com/rustls/rcgen), backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
//! It generates and loads ECDSA P-256 and P-384 and Ed25519 keys, and loads RSA keys.
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

    /// Generates a random key pair for `alg`: ECDSA P-256 or P-384, or Ed25519.
    ///
    /// RSA fails with [`Error::KeyGenerationUnavailable`], as on rcgen's `ring` backend.
    pub fn generate_for(alg: &'static SignatureAlgorithm) -> Result<Self, Error> {
        let key = match signer(alg)? {
            Signer::Ecdsa(signing) => {
                Key::Ecdsa(EcdsaKeyPair::generate(signing).map_err(|_| Error::RingUnspecified)?)
            }
            Signer::Ed25519 => {
                Key::Ed25519(Ed25519KeyPair::generate().map_err(|_| Error::RingUnspecified)?)
            }
            Signer::Rsa(_) => return Err(Error::KeyGenerationUnavailable),
        };
        let pkcs8 = match &key {
            Key::Ecdsa(key) => key.to_pkcs8(),
            Key::Ed25519(key) => key.to_pkcs8(),
            Key::Rsa(key, _) => key.to_pkcs8(),
        };
        let serialized_der = pkcs8.as_ref().to_vec();
        Ok(Self::new(key, alg, serialized_der))
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
        let signer = signer(alg)?;
        ring_pkcs8_version(der, matches!(signer, Signer::Ed25519))?;
        let key = match signer {
            Signer::Ecdsa(signing) => {
                Key::Ecdsa(EcdsaKeyPair::from_pkcs8(signing, der).map_err(rejected)?)
            }
            Signer::Ed25519 => Key::Ed25519(Ed25519KeyPair::from_pkcs8(der).map_err(rejected)?),
            Signer::Rsa(padding) => {
                Key::Rsa(RsaKeyPair::from_pkcs8(der).map_err(rejected)?, padding)
            }
        };
        Ok(Self::new(key, alg, der.to_vec()))
    }

    /// Loads a private key that signs with `alg`, which must be PKCS#8, as on
    /// rcgen's `ring` backend.
    pub fn from_der_and_sign_algo(
        key: &PrivateKeyDer<'_>,
        alg: &'static SignatureAlgorithm,
    ) -> Result<Self, Error> {
        match key {
            PrivateKeyDer::Pkcs8(key) => Self::from_pkcs8_der_and_sign_algo(key, alg),
            _ => Err(Error::CouldNotParseKeyPair),
        }
    }

    /// Parses a PEM private key, which must be PKCS#8, finding its algorithm.
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

    /// Parses a PEM private key that signs with `alg`, which must be PKCS#8.
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

    /// Encodes the key pair as PKCS#8 DER.
    pub fn serialize_der(&self) -> Vec<u8> {
        self.serialized_der.0.clone()
    }

    /// Returns the key pair's PKCS#8 DER encoding.
    pub fn serialized_der(&self) -> &[u8] {
        &self.serialized_der.0
    }

    /// Encodes the key pair as PEM PKCS#8.
    #[cfg(feature = "pem")]
    pub fn serialize_pem(&self) -> String {
        pem::encode("PRIVATE KEY", self.serialized_der())
    }

    fn new(key: Key, algorithm: &'static SignatureAlgorithm, serialized_der: Vec<u8>) -> Self {
        Self {
            key,
            algorithm,
            serialized_der: Wiped(serialized_der),
        }
    }
}

/// The key pair's PKCS#8 encoding, wiped on drop under the `wipe` feature, as
/// rind wipes the key itself.
struct Wiped(Vec<u8>);

impl Drop for Wiped {
    fn drop(&mut self) {
        // `cfg!` keeps the wipe type-checked in every build.
        if cfg!(feature = "wipe") {
            zeroize::Zeroize::zeroize(&mut self.0);
        }
    }
}

/// Clears the key pair's PKCS#8 copy, as rcgen's `zeroize` feature does; the
/// rind key it wraps is wiped on drop under the `wipe` feature.
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

/// Refuses the PKCS#8 v2 documents ring does, which rind takes as aws-lc-rs
/// does: any for ECDSA and RSA, and for Ed25519 one without its public key.
fn ring_pkcs8_version(der: &[u8], ed25519: bool) -> Result<(), Error> {
    /// The tag, body, and remainder of the DER element starting `der`, for
    /// lengths up to 0xffff; anything else is left for rind to refuse.
    fn element(der: &[u8]) -> Option<(u8, &[u8], &[u8])> {
        let (&tag, rest) = der.split_first()?;
        let (&len, rest) = rest.split_first()?;
        let (len, rest) = match len {
            0..=0x7f => (usize::from(len), rest),
            0x81 => (usize::from(*rest.first()?), rest.get(1..)?),
            0x82 => (
                usize::from(u16::from_be_bytes([*rest.first()?, *rest.get(1)?])),
                rest.get(2..)?,
            ),
            _ => return None,
        };
        rest.split_at_checked(len)
            .map(|(body, rest)| (tag, body, rest))
    }

    let Some((_, body, _)) = element(der) else {
        return Ok(());
    };
    let v2 = element(body).is_some_and(|(tag, version, _)| (tag, version) == (0x02, &[1][..]));
    let mut public_key = false;
    let mut fields = body;
    while let Some((tag, _, rest)) = element(fields) {
        public_key |= tag == 0x81;
        fields = rest;
    }
    match (v2, ed25519, public_key) {
        (true, false, _) => Err(Error::RingKeyRejected("VersionNotSupported".into())),
        (true, true, false) => Err(Error::RingKeyRejected("PublicKeyIsMissing".into())),
        _ => Ok(()),
    }
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

    /// Loads a PKCS#8 private key, finding its algorithm; RSA keys sign with SHA-256.
    fn try_from(key: &[u8]) -> Result<Self, Error> {
        let key = PrivateKeyDer::try_from(key).map_err(|_| Error::CouldNotParseKeyPair)?;
        Self::try_from(&key)
    }
}

impl TryFrom<Vec<u8>> for KeyPair {
    type Error = Error;

    /// Loads a PKCS#8 private key, finding its algorithm; RSA keys sign with SHA-256.
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

    /// Loads a PKCS#8 private key, finding its algorithm; RSA keys sign with SHA-256.
    fn try_from(key: &PrivateKeyDer<'_>) -> Result<Self, Error> {
        let PrivateKeyDer::Pkcs8(key) = key else {
            return Err(Error::CouldNotParseKeyPair);
        };
        // rcgen's `ring` backend tries the algorithms in this order.
        [
            &PKCS_ED25519,
            &PKCS_ECDSA_P256_SHA256,
            &PKCS_ECDSA_P384_SHA384,
            &PKCS_RSA_SHA256,
        ]
        .into_iter()
        .find_map(|alg| Self::from_pkcs8_der_and_sign_algo(key, alg).ok())
        .ok_or(Error::CouldNotParseKeyPair)
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

    /// `pkcs8` with its version set to `version`.
    fn with_version(pkcs8: &[u8], version: u8) -> Vec<u8> {
        let mut der = pkcs8.to_vec();
        let at = match der[1] {
            0x81 => 3,
            0x82 => 4,
            _ => 2,
        };
        assert_eq!(der[at..at + 2], [0x02, 0x01]);
        der[at + 2] = version;
        der
    }

    fn load(der: &[u8], alg: &'static SignatureAlgorithm) -> Result<KeyPair, Error> {
        KeyPair::from_pkcs8_der_and_sign_algo(&PrivatePkcs8KeyDer::from(der), alg)
    }

    /// ring refuses a v2 document that rind takes: any for ECDSA and RSA,
    /// and for Ed25519 one without its public key.
    #[test]
    fn pkcs8_v2_as_ring() {
        let rejected = |reason: &str| Some(Error::RingKeyRejected(reason.into()));

        let ecdsa = EcdsaKeyPair::generate(&ecdsa::sign::P256_SHA256_ASN1)
            .unwrap()
            .to_pkcs8();
        let rsa = RsaKeyPair::from_pkcs1(include_bytes!("../../rind/src/high/rsa/rsa2048.der"))
            .unwrap()
            .to_pkcs8();
        for (pkcs8, alg) in [
            (ecdsa.as_ref(), &PKCS_ECDSA_P256_SHA256),
            (rsa.as_ref(), &PKCS_RSA_SHA256),
        ] {
            assert!(load(pkcs8, alg).is_ok());
            let v2 = with_version(pkcs8, 1);
            assert_eq!(load(&v2, alg).err(), rejected("VersionNotSupported"));
        }

        let ed25519 = Ed25519KeyPair::generate().unwrap();
        assert!(load(ed25519.to_pkcs8().as_ref(), &PKCS_ED25519).is_ok());
        let v1 = ed25519.to_pkcs8v1();
        assert!(load(v1.as_ref(), &PKCS_ED25519).is_ok());
        let v2 = with_version(v1.as_ref(), 1);
        assert!(Ed25519KeyPair::from_pkcs8(&v2).is_ok());
        assert_eq!(
            load(&v2, &PKCS_ED25519).err(),
            rejected("PublicKeyIsMissing")
        );
    }
}
