//! HMAC as `digest`'s `Mac`, over the hashes rind keys it with, as `hmac`
//! names its types: [`Hmac`], and [`HmacReset`], which can also be reset.

use core::fmt;
use core::marker::PhantomData;

pub use digest::{self, KeyInit, Mac};
use digest::{
    FixedOutput, FixedOutputReset, InvalidLength, MacMarker, Output, OutputSizeUser, Reset, Update,
    common::{AlgorithmName, BlockSizeUser, KeySizeUser},
};

use crate::sha2::{Sha256, Sha384, Sha512};

/// A hash rind can key HMAC with: [`Sha256`], [`Sha384`], and [`Sha512`].
pub trait HmacHash: sealed::Sealed + OutputSizeUser + BlockSizeUser + AlgorithmName {
    #[doc(hidden)]
    fn algorithm() -> &'static rind::hmac::Algorithm;
}

mod sealed {
    pub trait Sealed {}
}

macro_rules! hmac_hash {
    ($($hash:ident => $algorithm:ident;)*) => {$(
        impl sealed::Sealed for $hash {}
        impl HmacHash for $hash {
            fn algorithm() -> &'static rind::hmac::Algorithm {
                &rind::hmac::$algorithm
            }
        }
    )*};
}

hmac_hash! {
    Sha256 => HMAC_SHA256;
    Sha384 => HMAC_SHA384;
    Sha512 => HMAC_SHA512;
}

// What `Hmac` and `HmacReset` share: any key length, `Clone`, and `Mac`.
macro_rules! mac {
    ($name:ident) => {
        impl<D: HmacHash> fmt::Debug for $name<D> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(concat!(stringify!($name), " { ... }"))
            }
        }

        impl<D: HmacHash> AlgorithmName for $name<D> {
            fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("Hmac<")?;
                D::write_alg_name(f)?;
                f.write_str(">")
            }
        }

        impl<D: HmacHash> KeySizeUser for $name<D> {
            type KeySize = <D as BlockSizeUser>::BlockSize;
        }

        impl<D: HmacHash> BlockSizeUser for $name<D> {
            type BlockSize = <D as BlockSizeUser>::BlockSize;
        }

        impl<D: HmacHash> KeyInit for $name<D> {
            fn new(key: &digest::Key<Self>) -> Self {
                Self::from_key(key.as_slice())
            }

            // HMAC takes a key of any length, as RustCrypto's does.
            fn new_from_slice(key: &[u8]) -> Result<Self, InvalidLength> {
                Ok(Self::from_key(key))
            }
        }

        impl<D: HmacHash> MacMarker for $name<D> {}

        impl<D: HmacHash> OutputSizeUser for $name<D> {
            type OutputSize = <D as OutputSizeUser>::OutputSize;
        }

        impl<D: HmacHash> Update for $name<D> {
            fn update(&mut self, data: &[u8]) {
                self.context.update(data);
            }
        }

        impl<D: HmacHash> FixedOutput for $name<D> {
            fn finalize_into(mut self, out: &mut Output<Self>) {
                out.copy_from_slice(self.context.sign().as_ref());
            }
        }
    };
}

/// HMAC over `D`, as `hmac::Hmac<D>`.
///
/// It holds only rind's running [`rind::hmac::Context`], which wipes itself on
/// drop; the key it starts from is wiped as it drops once the context is made.
pub struct Hmac<D: HmacHash> {
    context: rind::hmac::Context,
    hash: PhantomData<D>,
}

impl<D: HmacHash> Clone for Hmac<D> {
    fn clone(&self) -> Self {
        Self {
            context: self.context.clone(),
            hash: PhantomData,
        }
    }
}

impl<D: HmacHash> Hmac<D> {
    fn from_key(key: &[u8]) -> Self {
        let key = rind::hmac::Key::new(D::algorithm(), key);
        Self {
            context: rind::hmac::Context::with_key(&key),
            hash: PhantomData,
        }
    }
}

mac!(Hmac);

/// HMAC over `D` that can also be reset, as `hmac::HmacReset<D>`.
///
/// It keeps rind's [`rind::hmac::Key`] to restart from, and the running state;
/// both wipe themselves on drop, and no other copy of the key is made.
pub struct HmacReset<D: HmacHash> {
    key: rind::hmac::Key,
    context: rind::hmac::Context,
    hash: PhantomData<D>,
}

impl<D: HmacHash> Clone for HmacReset<D> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            context: self.context.clone(),
            hash: PhantomData,
        }
    }
}

impl<D: HmacHash> HmacReset<D> {
    fn from_key(key: &[u8]) -> Self {
        let key = rind::hmac::Key::new(D::algorithm(), key);
        let context = rind::hmac::Context::with_key(&key);
        Self {
            key,
            context,
            hash: PhantomData,
        }
    }
}

mac!(HmacReset);

impl<D: HmacHash> Reset for HmacReset<D> {
    fn reset(&mut self) {
        self.context = rind::hmac::Context::with_key(&self.key);
    }
}

impl<D: HmacHash> FixedOutputReset for HmacReset<D> {
    fn finalize_into_reset(&mut self, out: &mut Output<Self>) {
        // Signing starts a new message under the same key, which is the reset.
        out.copy_from_slice(self.context.sign().as_ref());
    }
}
