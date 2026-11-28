//! `kem` 0.3's traits on rind: ML-KEM-512, ML-KEM-768 and ML-KEM-1024 as
//! [`kem::Kem`], with `Encapsulate`, `Decapsulate`, `Generate` and
//! `KeyInit` from a 64-byte seed, under RustCrypto's `ml-kem` crate's names,
//! paths, and re-exports.
//!
//! Every type is a thin wrapper that calls rind; nothing here is a
//! primitive. The README lists what rind cannot back.
#![no_std]

use core::fmt;
use core::marker::PhantomData;

pub use hybrid_array::{self as array, ArraySize};
pub use kem::{
    self, Ciphertext, Decapsulate, Encapsulate, FromSeed, Generate, InvalidKey, Kem, Key,
    KeyExport, KeyInit, KeySizeUser, TryKeyInit,
};
pub use ml_kem_512::MlKem512;
pub use ml_kem_768::MlKem768;
pub use ml_kem_1024::MlKem1024;

use hybrid_array::Array;
use hybrid_array::sizes::{U32, U64};
use kem::common::rand_core::{CryptoRng, TryCryptoRng};
use kem::{Decapsulator, SharedKey as KemSharedKey};

/// A 32-byte array, such as an encapsulation's random message.
pub type B32 = Array<u8, U32>;

/// A shared key, 32 bytes for every parameter set.
pub type SharedKey = Array<u8, U32>;

/// The 64-byte seed `d || z` a decapsulation key is made from.
pub type Seed = Array<u8, U64>;

/// A parameter set: its rind algorithm and its encodings' sizes. Sealed: only
/// [`MlKem512`], [`MlKem768`] and [`MlKem1024`] implement it, so a set's sizes
/// always match its rind algorithm's encodings, which the conversions rely on.
pub trait ParameterSet:
    sealed::Sealed
    + kem::Kem<
        DecapsulationKey = DecapsulationKey<Self>,
        EncapsulationKey = EncapsulationKey<Self>,
        SharedKeySize = U32,
    >
{
    /// rind's algorithm for this set.
    type Rind: rind::kem::Algorithm;
    /// The encapsulation key's length.
    type EncapsulationKeySize: ArraySize;
}

mod sealed {
    pub trait Sealed {}
}

macro_rules! sets {
    ($($(#[$meta:meta])* $name:ident, $module:ident, $dk:ident, $ek:ident, $eksize:ty, $ct:ty;)*) => {$(
        #[doc = concat!("`", stringify!($name), "` and its aliases, as `ml-kem`'s `", stringify!($module), "` module names them.")]
        pub mod $module {
            use hybrid_array::sizes::*;

            $(#[$meta])*
            #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
            pub struct $name;

            impl crate::sealed::Sealed for $name {}

            impl crate::ParameterSet for $name {
                type Rind = rind::kem::$name;
                type EncapsulationKeySize = $eksize;
            }

            impl kem::Kem for $name {
                type DecapsulationKey = DecapsulationKey;
                type EncapsulationKey = EncapsulationKey;
                type SharedKeySize = crate::U32;
                type CiphertextSize = $ct;
            }

            /// The decapsulation key.
            pub type DecapsulationKey = crate::DecapsulationKey<$name>;
            /// The encapsulation key.
            pub type EncapsulationKey = crate::EncapsulationKey<$name>;
            /// The ciphertext.
            pub type Ciphertext = kem::Ciphertext<$name>;
        }

        #[doc = concat!("The ", stringify!($name), " decapsulation key.")]
        pub type $dk = $module::DecapsulationKey;
        #[doc = concat!("The ", stringify!($name), " encapsulation key.")]
        pub type $ek = $module::EncapsulationKey;
    )*};
}

sets! {
    /// ML-KEM-512, FIPS 203's parameter set for security category 1.
    MlKem512, ml_kem_512, DecapsulationKey512, EncapsulationKey512, U800, U768;
    /// ML-KEM-768, FIPS 203's parameter set for security category 3.
    MlKem768, ml_kem_768, DecapsulationKey768, EncapsulationKey768, U1184, U1088;
    /// ML-KEM-1024, FIPS 203's parameter set for security category 5.
    MlKem1024, ml_kem_1024, DecapsulationKey1024, EncapsulationKey1024, U1568, U1568;
}

/// An encapsulation key: rind's, which checks FIPS 203's modulus as it
/// loads.
#[repr(transparent)]
pub struct EncapsulationKey<P: ParameterSet> {
    key: rind::kem::EncapsulationKey<P::Rind>,
    set: PhantomData<P>,
}

impl<P: ParameterSet> Clone for EncapsulationKey<P> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            set: PhantomData,
        }
    }
}

impl<P: ParameterSet> EncapsulationKey<P> {
    /// A key from its encoding, refused if rind refuses it: FIPS 203's modulus
    /// check.
    pub fn new(encapsulation_key: &Key<Self>) -> Result<Self, InvalidKey> {
        let key = rind::kem::EncapsulationKey::new(encapsulation_key.as_slice())
            .map_err(|_| InvalidKey)?;
        Ok(Self {
            key,
            set: PhantomData,
        })
    }

    /// Encapsulates with the caller's 32 random bytes `m`, for known-answer
    /// tests. Reusing `m` with one key gives the same secret.
    #[cfg_attr(not(feature = "hazmat"), doc(hidden))]
    #[must_use]
    pub fn encapsulate_deterministic(&self, m: &B32) -> (Ciphertext<P>, SharedKey) {
        let mut m: [u8; 32] = (*m).into();
        self.encapsulate_message(&mut m)
    }

    /// Encapsulates `m` through rind's `kem::Message`, which zeroes it.
    fn encapsulate_message(&self, m: &mut [u8; 32]) -> (Ciphertext<P>, SharedKey) {
        let (ciphertext, secret) = rind::kem::Message::new(m).encapsulate(&self.key);
        (
            Array::try_from(ciphertext.as_ref()).expect("the set's ciphertext length"),
            Array::try_from(secret.as_ref()).expect("a 32-byte shared secret"),
        )
    }

    /// rind's key as this wrapper, borrowed rather than copied, so a
    /// decapsulation key's encapsulation key is the one inside rind's
    /// decapsulation key, which that key wipes on drop.
    fn from_rind(key: &rind::kem::EncapsulationKey<P::Rind>) -> &Self {
        // SAFETY: `EncapsulationKey` is `repr(transparent)` over rind's key
        // (`set` is zero-sized), so the two share a layout and the borrow's
        // lifetime carries over.
        unsafe { &*(key as *const rind::kem::EncapsulationKey<P::Rind>).cast::<Self>() }
    }
}

impl<P: ParameterSet> fmt::Debug for EncapsulationKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.key, f)
    }
}

// Public bytes, so a plain comparison.
impl<P: ParameterSet> PartialEq for EncapsulationKey<P> {
    fn eq(&self, other: &Self) -> bool {
        self.key.as_ref() == other.key.as_ref()
    }
}

impl<P: ParameterSet> Eq for EncapsulationKey<P> {}

impl<P: ParameterSet> KeySizeUser for EncapsulationKey<P> {
    type KeySize = P::EncapsulationKeySize;
}

impl<P: ParameterSet> TryKeyInit for EncapsulationKey<P> {
    /// Fails if rind refuses the key: FIPS 203's modulus check.
    fn new(key: &Key<Self>) -> Result<Self, InvalidKey> {
        Self::new(key)
    }
}

impl<P: ParameterSet> KeyExport for EncapsulationKey<P> {
    fn to_bytes(&self) -> Key<Self> {
        Array::try_from(self.key.as_ref()).expect("the set's encapsulation key length")
    }
}

impl<P: ParameterSet> Encapsulate for EncapsulationKey<P> {
    type Kem = P;

    /// Encapsulates a secret from 32 bytes of `rng`, through rind's
    /// `kem::Message`, which zeroes the bytes it takes.
    fn encapsulate_with_rng<R>(&self, rng: &mut R) -> (Ciphertext<P>, KemSharedKey<P>)
    where
        R: CryptoRng + ?Sized,
    {
        let mut m = [0u8; 32];
        rng.fill_bytes(&mut m);
        self.encapsulate_message(&mut m)
    }
}

/// A decapsulation key, made from its 64-byte seed as `ml-kem`'s is: rind's,
/// which wipes its whole value, encapsulation key included, on drop. The
/// wrapper is only that key: it holds no other copy of either.
#[repr(transparent)]
pub struct DecapsulationKey<P: ParameterSet> {
    key: rind::kem::DecapsulationKey<P::Rind>,
    set: PhantomData<P>,
}

impl<P: ParameterSet> DecapsulationKey<P> {
    /// The key `seed` makes, FIPS 203's `ML-KEM.KeyGen_internal(d, z)`.
    #[must_use]
    pub fn from_seed(seed: Seed) -> Self {
        Self::from_seed_slice(seed.as_slice())
    }

    /// The key's seed, which rind holds for every key made here, so this is
    /// never `None`.
    #[must_use]
    pub fn to_seed(&self) -> Option<Seed> {
        let seed = self.key.to_seed()?;
        Some(Array::try_from(seed.as_ref()).expect("a 64-byte seed"))
    }

    /// The encapsulation key, the one inside rind's key.
    #[must_use]
    pub fn encapsulation_key(&self) -> &EncapsulationKey<P> {
        EncapsulationKey::from_rind(self.key.public_key())
    }

    fn from_seed_slice(seed: &[u8]) -> Self {
        let key = rind::kem::DecapsulationKey::<P::Rind>::from_seed(seed)
            .expect("a 64-byte seed is a key");
        Self {
            key,
            set: PhantomData,
        }
    }
}

impl<P: ParameterSet> From<Seed> for DecapsulationKey<P> {
    fn from(seed: Seed) -> Self {
        Self::from_seed(seed)
    }
}

impl<P: ParameterSet> fmt::Debug for DecapsulationKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecapsulationKey").finish_non_exhaustive()
    }
}

impl<P: ParameterSet> KeySizeUser for DecapsulationKey<P> {
    type KeySize = U64;
}

impl<P: ParameterSet> KeyInit for DecapsulationKey<P> {
    /// The key `seed` makes, FIPS 203's `ML-KEM.KeyGen_internal(d, z)`.
    fn new(seed: &Seed) -> Self {
        Self::from_seed_slice(seed.as_slice())
    }
}

impl<P: ParameterSet> KeyExport for DecapsulationKey<P> {
    /// The key's seed, which rind holds for every key made here.
    fn to_bytes(&self) -> Seed {
        self.to_seed().expect("made from a seed")
    }
}

impl<P: ParameterSet> Generate for DecapsulationKey<P> {
    /// A key from a seed of 64 bytes of `rng`. The seed is a stack temporary
    /// inside this call, which rind's policy leaves unwiped; the key rind
    /// makes from it holds its own copy and wipes that on drop.
    fn try_generate_from_rng<R>(rng: &mut R) -> Result<Self, R::Error>
    where
        R: TryCryptoRng + ?Sized,
    {
        let mut seed = [0u8; 64];
        rng.try_fill_bytes(&mut seed)?;
        Ok(Self::from_seed_slice(&seed))
    }
}

impl<P: ParameterSet> Decapsulator for DecapsulationKey<P> {
    type Kem = P;

    fn encapsulation_key(&self) -> &EncapsulationKey<P> {
        DecapsulationKey::encapsulation_key(self)
    }
}

impl<P: ParameterSet> Decapsulate for DecapsulationKey<P> {
    /// FIPS 203's `ML-KEM.Decaps`: an altered ciphertext gives the implicit
    /// rejection secret, never an error.
    fn decapsulate(&self, ct: &Ciphertext<P>) -> KemSharedKey<P> {
        let ct = rind::kem::Ciphertext::<P::Rind>::new(ct.as_slice())
            .expect("the set's ciphertext length");
        let secret = self.key.decapsulate(&ct);
        Array::try_from(secret.as_ref()).expect("a 32-byte shared secret")
    }
}
