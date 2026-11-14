//! Key encapsulation: ML-KEM-768.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use core::fmt;

use crate::buffer::generated_encodings;
use crate::error::{KeyRejected, Unspecified, unspecified};
use crate::wipe::Wiped;

/// ML-KEM-768, as standardised by FIPS 203.
pub const ML_KEM_768: Algorithm<AlgorithmId> = Algorithm {
    id: AlgorithmId::MlKem768,
    decapsulate_key_size: 2400,
    encapsulate_key_size: 1184,
};

/// An identifier for a KEM algorithm.
pub trait AlgorithmIdentifier:
    Copy + Clone + fmt::Debug + PartialEq + crate::sealed::Sealed + 'static
{
    /// The algorithm's AWS-LC NID.
    fn nid(self) -> i32;
}

/// A KEM algorithm.
#[derive(PartialEq)]
pub struct Algorithm<Id = AlgorithmId>
where
    Id: AlgorithmIdentifier,
{
    id: Id,
    #[allow(dead_code)]
    decapsulate_key_size: usize,
    encapsulate_key_size: usize,
}

impl<Id: AlgorithmIdentifier> Algorithm<Id> {
    /// The algorithm's identifier.
    #[must_use]
    pub fn id(&self) -> Id {
        self.id
    }
}

impl<Id: AlgorithmIdentifier> fmt::Debug for Algorithm<Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.id, f)
    }
}

/// A KEM algorithm's identifier.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AlgorithmId {
    /// ML-KEM-768, as standardised by FIPS 203.
    // aws-lc-rs declares ML-KEM-512 first, so `as` casts see 1.
    MlKem768 = 1,
}

/// AWS-LC's `NID_MLKEM768`.
const NID_MLKEM768: i32 = 989;

impl AlgorithmIdentifier for AlgorithmId {
    fn nid(self) -> i32 {
        match self {
            Self::MlKem768 => NID_MLKEM768,
        }
    }
}

impl crate::sealed::Sealed for AlgorithmId {}

impl<Id: AlgorithmIdentifier> Algorithm<Id> {
    /// rind's algorithm; only [`AlgorithmId`] implements the sealed
    /// [`AlgorithmIdentifier`], so its NID names one this module backs.
    fn rind(&self) -> &'static rind::kem::Algorithm {
        match self.id.nid() {
            NID_MLKEM768 => &rind::kem::ML_KEM_768,
            nid => unreachable!("no KEM has NID {nid}"),
        }
    }
}

generated_encodings!((EncapsulationKeyBytes, EncapsulationKeyBytesType, false));

/// A decapsulation key, which decapsulates any number of ciphertexts, wiped
/// on drop under the `wipe` feature.
pub struct DecapsulationKey<Id = AlgorithmId>
where
    Id: AlgorithmIdentifier,
{
    algorithm: &'static Algorithm<Id>,
    key: rind::kem::DecapsulationKey,
}

impl<Id: AlgorithmIdentifier> DecapsulationKey<Id> {
    /// Generates a decapsulation key for `alg`.
    pub fn generate(alg: &'static Algorithm<Id>) -> Result<Self, Unspecified> {
        let key = rind::kem::DecapsulationKey::generate(alg.rind()).map_err(unspecified)?;
        Ok(Self {
            algorithm: alg,
            key,
        })
    }

    /// The key's encapsulation key.
    pub fn encapsulation_key(&self) -> Result<EncapsulationKey<Id>, Unspecified> {
        Ok(EncapsulationKey {
            algorithm: self.algorithm,
            key: self.key.public_key(),
        })
    }

    /// Decapsulates `ciphertext`, which fails only if it is the wrong
    /// length: a ciphertext altered or made for another key yields an
    /// unrelated secret (FIPS 203's implicit rejection).
    #[allow(clippy::needless_pass_by_value)]
    pub fn decapsulate(&self, ciphertext: Ciphertext<'_>) -> Result<SharedSecret, Unspecified> {
        let secret = self
            .key
            .decapsulate(ciphertext.as_ref())
            .map_err(unspecified)?;
        Ok(SharedSecret(Wiped::new(secret.as_ref().into())))
    }

    /// The key's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static Algorithm<Id> {
        self.algorithm
    }
}

impl<Id: AlgorithmIdentifier> fmt::Debug for DecapsulationKey<Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecapsulationKey")
            .field("algorithm", &self.algorithm)
            .finish_non_exhaustive()
    }
}

/// An encapsulation key, made from a decapsulation key or from its bytes.
pub struct EncapsulationKey<Id = AlgorithmId>
where
    Id: AlgorithmIdentifier,
{
    algorithm: &'static Algorithm<Id>,
    key: rind::kem::EncapsulationKey,
}

impl<Id: AlgorithmIdentifier> EncapsulationKey<Id> {
    /// Parses an encapsulation key for `alg` from its bytes.
    pub fn new(alg: &'static Algorithm<Id>, bytes: &[u8]) -> Result<Self, KeyRejected> {
        match bytes.len().cmp(&alg.encapsulate_key_size) {
            core::cmp::Ordering::Less => return Err(KeyRejected::too_small()),
            core::cmp::Ordering::Greater => return Err(KeyRejected::too_large()),
            core::cmp::Ordering::Equal => {}
        }
        let key = rind::kem::EncapsulationKey::new(alg.rind(), bytes).map_err(KeyRejected::rind)?;
        Ok(Self {
            algorithm: alg,
            key,
        })
    }

    /// Encapsulates a fresh shared secret, returning the ciphertext to send
    /// and the secret.
    pub fn encapsulate(&self) -> Result<(Ciphertext<'static>, SharedSecret), Unspecified> {
        let (ciphertext, secret) = self.key.encapsulate().map_err(unspecified)?;
        Ok((
            Ciphertext(Cow::Owned(ciphertext.as_ref().to_vec())),
            SharedSecret(Wiped::new(secret.as_ref().into())),
        ))
    }

    /// The key's bytes.
    pub fn key_bytes(&self) -> Result<EncapsulationKeyBytes<'static>, Unspecified> {
        Ok(EncapsulationKeyBytes::new(self.key.as_ref().to_vec()))
    }

    /// The key's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static Algorithm<Id> {
        self.algorithm
    }
}

impl<Id: AlgorithmIdentifier> fmt::Debug for EncapsulationKey<Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EncapsulationKey")
            .field("algorithm", &self.algorithm)
            .finish_non_exhaustive()
    }
}

/// A KEM ciphertext.
pub struct Ciphertext<'a>(Cow<'a, [u8]>);

impl AsRef<[u8]> for Ciphertext<'_> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<'a> From<&'a [u8]> for Ciphertext<'a> {
    fn from(value: &'a [u8]) -> Self {
        Self(Cow::Borrowed(value))
    }
}

/// The shared secret encapsulation and decapsulation agree on, wiped on drop
/// under the `wipe` feature.
pub struct SharedSecret(Wiped<Box<[u8]>>);

impl AsRef<[u8]> for SharedSecret {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
