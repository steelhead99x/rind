//! Key encapsulation: ML-KEM-512, ML-KEM-768, and ML-KEM-1024.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use core::fmt;

use rind::kem::{MlKem512, MlKem768, MlKem1024};

use crate::buffer::generated_encodings;
use crate::error::{KeyRejected, Unspecified, unspecified};
use crate::wipe::Wiped;

/// ML-KEM-512, as standardised by FIPS 203.
pub const ML_KEM_512: Algorithm<AlgorithmId> = Algorithm {
    id: AlgorithmId::MlKem512,
    decapsulate_key_size: 1632,
    encapsulate_key_size: 800,
};

/// ML-KEM-768, as standardised by FIPS 203.
pub const ML_KEM_768: Algorithm<AlgorithmId> = Algorithm {
    id: AlgorithmId::MlKem768,
    decapsulate_key_size: 2400,
    encapsulate_key_size: 1184,
};

/// ML-KEM-1024, as standardised by FIPS 203.
pub const ML_KEM_1024: Algorithm<AlgorithmId> = Algorithm {
    id: AlgorithmId::MlKem1024,
    decapsulate_key_size: 3168,
    encapsulate_key_size: 1568,
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
    /// ML-KEM-512, as standardised by FIPS 203.
    MlKem512,
    /// ML-KEM-768, as standardised by FIPS 203.
    MlKem768,
    /// ML-KEM-1024, as standardised by FIPS 203.
    MlKem1024,
}

/// AWS-LC's `NID_MLKEM512`, `NID_MLKEM768`, and `NID_MLKEM1024`.
const NID_MLKEM512: i32 = 988;
const NID_MLKEM768: i32 = 989;
const NID_MLKEM1024: i32 = 990;

impl AlgorithmIdentifier for AlgorithmId {
    fn nid(self) -> i32 {
        match self {
            Self::MlKem512 => NID_MLKEM512,
            Self::MlKem768 => NID_MLKEM768,
            Self::MlKem1024 => NID_MLKEM1024,
        }
    }
}

impl crate::sealed::Sealed for AlgorithmId {}

/// One of rind's keys, of each parameter set: rind types a key by its set,
/// where aws-lc-rs picks the set at run time.
///
/// Each set's key has its own allocation: held inline, a smaller set's key
/// would sit in the largest's space, whose slack a move fills with stale
/// stack bytes, a seed among them, that the key's wipe never reaches.
enum BySet<T512, T768, T1024> {
    MlKem512(Box<T512>),
    MlKem768(Box<T768>),
    MlKem1024(Box<T1024>),
}

/// Rind's key type `$ty` of whichever set.
macro_rules! by_set {
    ($ty:ident) => {
        BySet<rind::kem::$ty<MlKem512>, rind::kem::$ty<MlKem768>, rind::kem::$ty<MlKem1024>>
    };
}

/// `$body` with `$key` bound to the key `$value` holds, of whichever set.
macro_rules! each {
    ($value:expr, $key:ident => $body:expr) => {
        match $value {
            BySet::MlKem512(key) => {
                let $key = &**key;
                $body
            }
            BySet::MlKem768(key) => {
                let $key = &**key;
                $body
            }
            BySet::MlKem1024(key) => {
                let $key = &**key;
                $body
            }
        }
    };
}

/// `$body` in the variant of `BySet` that `$alg` names, with `$set` bound
/// to rind's parameter set; only [`AlgorithmId`] implements the sealed
/// [`AlgorithmIdentifier`], so its NID names a set rind has.
macro_rules! for_set {
    ($alg:expr, $set:ident => $body:expr) => {
        match $alg.id.nid() {
            NID_MLKEM512 => {
                type $set = MlKem512;
                BySet::MlKem512(Box::new($body))
            }
            NID_MLKEM768 => {
                type $set = MlKem768;
                BySet::MlKem768(Box::new($body))
            }
            NID_MLKEM1024 => {
                type $set = MlKem1024;
                BySet::MlKem1024(Box::new($body))
            }
            nid => unreachable!("no KEM has NID {nid}"),
        }
    };
}

generated_encodings!((EncapsulationKeyBytes, EncapsulationKeyBytesType, false));

/// A decapsulation key, which decapsulates any number of ciphertexts, wiped
/// on drop under the `wipe` feature.
pub struct DecapsulationKey<Id = AlgorithmId>
where
    Id: AlgorithmIdentifier,
{
    algorithm: &'static Algorithm<Id>,
    key: by_set!(DecapsulationKey),
}

impl<Id: AlgorithmIdentifier> DecapsulationKey<Id> {
    /// Generates a decapsulation key for `alg`.
    pub fn generate(alg: &'static Algorithm<Id>) -> Result<Self, Unspecified> {
        let key = for_set!(alg, Set => {
            rind::kem::DecapsulationKey::<Set>::generate().map_err(unspecified)?
        });
        Ok(Self {
            algorithm: alg,
            key,
        })
    }

    /// The key's encapsulation key.
    pub fn encapsulation_key(&self) -> Result<EncapsulationKey<Id>, Unspecified> {
        let key = match &self.key {
            BySet::MlKem512(key) => BySet::MlKem512(Box::new(key.public_key().clone())),
            BySet::MlKem768(key) => BySet::MlKem768(Box::new(key.public_key().clone())),
            BySet::MlKem1024(key) => BySet::MlKem1024(Box::new(key.public_key().clone())),
        };
        Ok(EncapsulationKey {
            algorithm: self.algorithm,
            key,
        })
    }

    /// Decapsulates `ciphertext`, which fails only if it is the wrong
    /// length: a ciphertext altered or made for another key yields an
    /// unrelated secret (FIPS 203's implicit rejection).
    #[allow(clippy::needless_pass_by_value)]
    pub fn decapsulate(&self, ciphertext: Ciphertext<'_>) -> Result<SharedSecret, Unspecified> {
        let secret: Box<[u8]> = each!(&self.key, key => {
            let ciphertext = rind::kem::Ciphertext::new(ciphertext.as_ref()).map_err(unspecified)?;
            key.decapsulate(&ciphertext).as_ref().into()
        });
        Ok(SharedSecret(Wiped::new(secret)))
    }

    /// The key's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static Algorithm<Id> {
        self.algorithm
    }
}

// SAFETY: `AlgorithmIdentifier` is sealed, and for its only implementor,
// `AlgorithmId`, the `Algorithm` the keys point to is `Send` and `Sync`, as
// rind's keys are (checked below).
// aws-lc-rs bounds these impls by `AlgorithmIdentifier`, not by `Id: Sync` as
// the inferred ones would be, so these match its API.
unsafe impl<Id: AlgorithmIdentifier> Send for DecapsulationKey<Id> {}
// SAFETY: as for `Send` above.
unsafe impl<Id: AlgorithmIdentifier> Sync for DecapsulationKey<Id> {}
// SAFETY: as for `DecapsulationKey`.
unsafe impl<Id: AlgorithmIdentifier> Send for EncapsulationKey<Id> {}
// SAFETY: as for `DecapsulationKey`.
unsafe impl<Id: AlgorithmIdentifier> Sync for EncapsulationKey<Id> {}

const _: () = {
    const fn send_sync<T: Send + Sync>() {}
    send_sync::<Algorithm<AlgorithmId>>();
    send_sync::<rind::kem::DecapsulationKey<MlKem512>>();
    send_sync::<rind::kem::DecapsulationKey<MlKem768>>();
    send_sync::<rind::kem::DecapsulationKey<MlKem1024>>();
    send_sync::<rind::kem::EncapsulationKey<MlKem512>>();
    send_sync::<rind::kem::EncapsulationKey<MlKem768>>();
    send_sync::<rind::kem::EncapsulationKey<MlKem1024>>();
};

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
    key: by_set!(EncapsulationKey),
}

impl<Id: AlgorithmIdentifier> EncapsulationKey<Id> {
    /// Parses an encapsulation key for `alg` from its bytes.
    pub fn new(alg: &'static Algorithm<Id>, bytes: &[u8]) -> Result<Self, KeyRejected> {
        match bytes.len().cmp(&alg.encapsulate_key_size) {
            core::cmp::Ordering::Less => return Err(KeyRejected::too_small()),
            core::cmp::Ordering::Greater => return Err(KeyRejected::too_large()),
            core::cmp::Ordering::Equal => {}
        }
        let key = for_set!(alg, Set => {
            rind::kem::EncapsulationKey::<Set>::new(bytes).map_err(KeyRejected::rind)?
        });
        Ok(Self {
            algorithm: alg,
            key,
        })
    }

    /// Encapsulates a fresh shared secret, returning the ciphertext to send
    /// and the secret.
    pub fn encapsulate(&self) -> Result<(Ciphertext<'static>, SharedSecret), Unspecified> {
        each!(&self.key, key => {
            let (ciphertext, secret) = key.encapsulate().map_err(unspecified)?;
            Ok((
                Ciphertext(Cow::Owned(ciphertext.as_ref().to_vec())),
                SharedSecret(Wiped::new(secret.as_ref().into())),
            ))
        })
    }

    /// The key's bytes.
    pub fn key_bytes(&self) -> Result<EncapsulationKeyBytes<'static>, Unspecified> {
        Ok(EncapsulationKeyBytes::new(
            each!(&self.key, key => key.as_ref().to_vec()),
        ))
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
