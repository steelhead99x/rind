//! Where a key agreement key lives: rind, or with `fips` rind-fips's module
//! for ECDH, which it approves. X25519 stays in rind, as aws-lc-rs's FIPS
//! build keeps it callable.

use alloc::vec::Vec;

use super::{Algorithm, AlgorithmId};
use crate::error::{KeyRejected, Unspecified, unspecified};
use crate::wipe::Wiped;

/// Runs `$body` with `$key` bound to whichever backend's key `$engine` holds.
macro_rules! dispatch {
    ($engine:expr, $key:ident => $body:expr) => {
        match $engine {
            Self::Rind($key) => $body,
            #[cfg(feature = "fips")]
            Self::Module($key) => $body,
        }
    };
}

/// A private key, wiped on drop by whichever backend holds it.
pub(super) enum PrivateEngine {
    Rind(rind::agreement::PrivateKey),
    #[cfg(feature = "fips")]
    Module(rind_fips::agreement::PrivateKey),
}

impl PrivateEngine {
    pub(super) fn generate(alg: &Algorithm) -> Result<Self, Unspecified> {
        #[cfg(feature = "fips")]
        if let Some(module) = alg.module() {
            return rind_fips::agreement::PrivateKey::generate(module)
                .map(Self::Module)
                .map_err(unspecified);
        }
        rind::agreement::PrivateKey::generate(alg.rind())
            .map(Self::Rind)
            .map_err(unspecified)
    }

    /// Loads PKCS#8, or SEC1 if `sec1`.
    pub(super) fn from_der(alg: &Algorithm, der: &[u8], sec1: bool) -> Result<Self, KeyRejected> {
        #[cfg(feature = "fips")]
        if let Some(module) = alg.module() {
            return rind_fips::agreement::PrivateKey::from_pkcs8(module, der)
                .or_else(|error| {
                    if sec1 {
                        rind_fips::agreement::PrivateKey::from_sec1(module, der)
                    } else {
                        Err(error)
                    }
                })
                .map(Self::Module)
                .map_err(KeyRejected::rind);
        }
        rind::agreement::PrivateKey::from_pkcs8(alg.rind(), der)
            .or_else(|error| {
                if sec1 {
                    rind::agreement::PrivateKey::from_sec1(alg.rind(), der)
                } else {
                    Err(error)
                }
            })
            .map(Self::Rind)
            .map_err(KeyRejected::rind)
    }

    pub(super) fn from_scalar(alg: &Algorithm, scalar: &[u8]) -> Result<Self, KeyRejected> {
        #[cfg(feature = "fips")]
        if let Some(module) = alg.module() {
            return rind_fips::agreement::PrivateKey::from_scalar(module, scalar)
                .map(Self::Module)
                .map_err(KeyRejected::rind);
        }
        rind::agreement::PrivateKey::from_scalar(alg.rind(), scalar)
            .map(Self::Rind)
            .map_err(KeyRejected::rind)
    }

    pub(super) fn public_key(&self) -> PublicEngine {
        match self {
            Self::Rind(key) => PublicEngine::Rind(key.public_key().clone()),
            #[cfg(feature = "fips")]
            Self::Module(key) => PublicEngine::Module(key.public_key().clone()),
        }
    }

    /// Agrees with the peer's encoded public key, returning `kdf` of the
    /// secret, or `None` if the agreement fails.
    pub(super) fn agree<R>(&self, peer: &[u8], kdf: impl FnOnce(&[u8]) -> R) -> Option<R> {
        dispatch!(self, key => key.agree(peer).ok().map(|secret| kdf(secret.as_ref())))
    }

    pub(super) fn to_pkcs8(&self) -> Vec<u8> {
        dispatch!(self, key => key.to_pkcs8().as_ref().to_vec())
    }

    pub(super) fn to_scalar(&self) -> Vec<u8> {
        dispatch!(self, key => key.to_scalar().as_ref().to_vec())
    }

    /// The key as a SEC1 `ECPrivateKey`, through the ECDSA key pair on its
    /// curve; `None` for X25519.
    pub(super) fn to_sec1(&self, id: AlgorithmId) -> Result<Vec<u8>, Unspecified> {
        let pkcs8 = Wiped::new(self.to_pkcs8());
        #[cfg(feature = "fips")]
        if let Self::Module(_) = self {
            use rind_fips::ecdsa::sign;
            let algorithm = match id {
                AlgorithmId::EcdhP256 => &sign::P256_SHA256_ASN1,
                AlgorithmId::EcdhP384 => &sign::P384_SHA384_ASN1,
                AlgorithmId::EcdhP521 => &sign::P521_SHA512_ASN1,
                AlgorithmId::X25519 => return Err(Unspecified),
            };
            let pair =
                rind_fips::ecdsa::KeyPair::from_pkcs8(algorithm, &pkcs8).map_err(unspecified)?;
            return Ok(pair.to_sec1().as_ref().to_vec());
        }
        use rind::ecdsa::sign;
        let algorithm = match id {
            AlgorithmId::EcdhP256 => &sign::P256_SHA256_ASN1,
            AlgorithmId::EcdhP384 => &sign::P384_SHA384_ASN1,
            AlgorithmId::EcdhP521 => &sign::P521_SHA512_ASN1,
            AlgorithmId::X25519 => return Err(Unspecified),
        };
        let pair = rind::ecdsa::KeyPair::from_pkcs8(algorithm, &pkcs8).map_err(unspecified)?;
        Ok(pair.to_sec1().as_ref().to_vec())
    }
}

/// A public key, in the backend its private key lives in.
#[derive(Clone)]
pub(super) enum PublicEngine {
    Rind(rind::agreement::PublicKey),
    #[cfg(feature = "fips")]
    Module(rind_fips::agreement::PublicKey),
}

impl PublicEngine {
    pub(super) fn from_spki(alg: &Algorithm, der: &[u8]) -> Option<Self> {
        #[cfg(feature = "fips")]
        if let Some(module) = alg.module() {
            return rind_fips::agreement::PublicKey::from_spki(module, der)
                .ok()
                .map(Self::Module);
        }
        rind::agreement::PublicKey::from_spki(alg.rind(), der)
            .ok()
            .map(Self::Rind)
    }

    pub(super) fn new(alg: &Algorithm, bytes: &[u8]) -> Option<Self> {
        #[cfg(feature = "fips")]
        if let Some(module) = alg.module() {
            return rind_fips::agreement::PublicKey::new(module, bytes)
                .ok()
                .map(Self::Module);
        }
        rind::agreement::PublicKey::new(alg.rind(), bytes)
            .ok()
            .map(Self::Rind)
    }

    pub(super) fn to_spki(&self) -> Vec<u8> {
        dispatch!(self, key => key.to_spki().as_ref().to_vec())
    }
}

impl AsRef<[u8]> for PublicEngine {
    fn as_ref(&self) -> &[u8] {
        dispatch!(self, key => key.as_ref())
    }
}

impl core::fmt::Debug for PublicEngine {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        dispatch!(self, key => core::fmt::Debug::fmt(key, f))
    }
}

/// With `fips`, ECDH keys live in the module and X25519's in rind.
#[cfg(all(test, feature = "fips"))]
mod fips_tests {
    use super::*;
    use crate::agreement::{ECDH_P256, ECDH_P384, ECDH_P521, X25519};

    #[test]
    fn ecdh_is_in_the_module_and_x25519_in_rind() {
        for algorithm in [&ECDH_P256, &ECDH_P384, &ECDH_P521] {
            let key = PrivateEngine::generate(algorithm).unwrap();
            assert!(matches!(key, PrivateEngine::Module(_)));
            assert!(matches!(key.public_key(), PublicEngine::Module(_)));
        }
        let key = PrivateEngine::generate(&X25519).unwrap();
        assert!(matches!(key, PrivateEngine::Rind(_)));
    }
}
