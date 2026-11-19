//! An RSA public key, with the module verifying where it approves.
//!
//! rind validates every key and holds it. With `fips`, a key of a modulus the
//! module approves is also loaded into it, which then verifies: 1024 bits
//! (for legacy verification), or an even number of bits from 2048 to 8192. A
//! public key holds no secret, so a key outside that, or a PSS salt the
//! module does not take, verifies in rind, as aws-lc-rs verifies them.

use alloc::vec::Vec;

use super::{PssHash, RsaPssSaltLength, Verification};
use crate::der;
use crate::error::{KeyRejected, Unspecified, unspecified};

/// The PKCS#1 v1.5 verification algorithms, each a hash and a modulus floor.
#[derive(Clone, Copy)]
pub(super) enum Pkcs1 {
    Sha1,
    Sha1From1024,
    Sha256From1024,
    Sha512From1024,
    Sha256,
    Sha384,
    Sha512,
    Sha384From3072,
}

impl Pkcs1 {
    fn rind(self) -> &'static rind::rsa::VerificationAlgorithm {
        use rind::rsa::verify::{self, legacy};
        match self {
            Self::Sha1 => &legacy::PKCS1_SHA1,
            Self::Sha1From1024 => &legacy::PKCS1_1024_SHA1,
            Self::Sha256From1024 => &legacy::PKCS1_1024_SHA256,
            Self::Sha512From1024 => &legacy::PKCS1_1024_SHA512,
            Self::Sha256 => &verify::PKCS1_SHA256,
            Self::Sha384 => &verify::PKCS1_SHA384,
            Self::Sha512 => &verify::PKCS1_SHA512,
            Self::Sha384From3072 => &legacy::PKCS1_3072_SHA384,
        }
    }

    #[cfg(feature = "fips")]
    fn module(self) -> &'static rind_fips::rsa::VerificationAlgorithm {
        use rind_fips::rsa::verify::{self, legacy};
        match self {
            Self::Sha1 => &legacy::PKCS1_SHA1,
            Self::Sha1From1024 => &legacy::PKCS1_1024_SHA1,
            Self::Sha256From1024 => &legacy::PKCS1_1024_SHA256,
            Self::Sha512From1024 => &legacy::PKCS1_1024_SHA512,
            Self::Sha256 => &verify::PKCS1_SHA256,
            Self::Sha384 => &verify::PKCS1_SHA384,
            Self::Sha512 => &verify::PKCS1_SHA512,
            Self::Sha384From3072 => &legacy::PKCS1_3072_SHA384,
        }
    }
}

/// Whether the module takes a key of a modulus this many bits long.
#[cfg(feature = "fips")]
fn module_approves(bits: usize) -> bool {
    bits == 1024 || ((2048..=8192).contains(&bits) && bits.is_multiple_of(2))
}

/// A public key rind validated, and with `fips` the module holds when it approves.
#[derive(Clone)]
pub(crate) struct PublicEngine {
    rind: rind::rsa::PublicKey,
    #[cfg(feature = "fips")]
    module: Option<rind_fips::rsa::PublicKey>,
}

impl PublicEngine {
    fn new(rind: rind::rsa::PublicKey) -> Result<Self, KeyRejected> {
        #[cfg(feature = "fips")]
        let module = {
            let (n, _) = der::rsa_public_key(rind.as_ref()).map_err(KeyRejected::from)?;
            if module_approves(der::bits(n)) {
                Some(rind_fips::rsa::PublicKey::new(rind.as_ref()).map_err(KeyRejected::rind)?)
            } else {
                None
            }
        };
        Ok(Self {
            rind,
            #[cfg(feature = "fips")]
            module,
        })
    }

    /// Loads a PKCS#1 `RSAPublicKey` or an `rsaEncryption` `SubjectPublicKeyInfo`
    /// with a modulus of 1024 to 8192 bits, refusing what AWS-LC's
    /// `RSA_check_key` does, such as an even modulus or an exponent of 1.
    pub(crate) fn from_der(der: &[u8]) -> Result<Self, KeyRejected> {
        if der::is_spki(der) {
            rind::rsa::PublicKey::from_spki(der)
        } else {
            rind::rsa::PublicKey::new(der)
        }
        .map_err(KeyRejected::rind)
        .and_then(Self::new)
    }

    pub(crate) fn from_components(n: &[u8], e: &[u8]) -> Result<Self, KeyRejected> {
        rind::rsa::PublicKey::from_components(&rind::rsa::PublicKeyComponents { n, e })
            .map_err(KeyRejected::rind)
            .and_then(Self::new)
    }

    /// The key as a PKCS#1 `RSAPublicKey`.
    pub(crate) fn pkcs1(&self) -> &[u8] {
        self.rind.as_ref()
    }

    /// The key as a `SubjectPublicKeyInfo`.
    pub(crate) fn to_spki(&self) -> Vec<u8> {
        self.rind.to_spki().as_ref().to_vec()
    }

    /// Verifies `signature` over `message` with the algorithm `verification`
    /// and `salt` name.
    pub(super) fn verify(
        &self,
        verification: Verification,
        salt: RsaPssSaltLength,
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        #[cfg(feature = "fips")]
        if let Some(module) = &self.module {
            return match (verification, salt) {
                (Verification::Pkcs1(algorithm), _) => {
                    module.verify(algorithm.module(), message, signature)
                }
                (Verification::Pss(hash), RsaPssSaltLength::Digest) => {
                    use rind_fips::rsa::verify;
                    let algorithm = match hash {
                        PssHash::Sha256 => &verify::PSS_SHA256,
                        PssHash::Sha384 => &verify::PSS_SHA384,
                        PssHash::Sha512 => &verify::PSS_SHA512,
                    };
                    module.verify(algorithm, message, signature)
                }
                // A salt the module does not take.
                (Verification::Pss(_), _) => {
                    return self.verify_in_rind(verification, salt, message, signature);
                }
            }
            .map_err(unspecified);
        }
        self.verify_in_rind(verification, salt, message, signature)
    }

    fn verify_in_rind(
        &self,
        verification: Verification,
        salt: RsaPssSaltLength,
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        use rind::rsa::{VerificationAlgorithm as Alg, verify};
        let algorithm = match (verification, salt.rind()) {
            (Verification::Pkcs1(algorithm), _) => {
                return self
                    .rind
                    .verify(algorithm.rind(), message, signature)
                    .map_err(unspecified);
            }
            (Verification::Pss(PssHash::Sha256), None) => {
                return self
                    .rind
                    .verify(&verify::PSS_SHA256, message, signature)
                    .map_err(unspecified);
            }
            (Verification::Pss(PssHash::Sha384), None) => {
                return self
                    .rind
                    .verify(&verify::PSS_SHA384, message, signature)
                    .map_err(unspecified);
            }
            (Verification::Pss(PssHash::Sha512), None) => {
                return self
                    .rind
                    .verify(&verify::PSS_SHA512, message, signature)
                    .map_err(unspecified);
            }
            (Verification::Pss(PssHash::Sha256), Some(salt)) => Alg::pss_sha256(salt),
            (Verification::Pss(PssHash::Sha384), Some(salt)) => Alg::pss_sha384(salt),
            (Verification::Pss(PssHash::Sha512), Some(salt)) => Alg::pss_sha512(salt),
        };
        self.rind
            .verify(&algorithm, message, signature)
            .map_err(unspecified)
    }
}

/// With `fips`, the module verifies with the moduli it approves, and rind
/// with the rest.
#[cfg(all(test, feature = "fips"))]
mod fips_tests {
    use super::*;

    #[test]
    fn module_approves_even_2048_to_8192_and_1024() {
        for bits in [1024, 2048, 2050, 3072, 4096, 8192] {
            assert!(module_approves(bits), "{bits}");
        }
        for bits in [512, 1025, 2047, 2049, 2303, 8194] {
            assert!(!module_approves(bits), "{bits}");
        }
    }

    #[test]
    fn a_generated_key_is_held_by_the_module() {
        let pair = rind_fips::rsa::KeyPair::generate(rind_fips::rsa::KeySize::Rsa2048).unwrap();
        let key = PublicEngine::from_der(pair.public_key().as_ref()).unwrap();
        assert!(key.module.is_some());
    }
}
