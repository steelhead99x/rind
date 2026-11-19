//! HMAC as `digest`'s `Mac`, over the hashes rind keys it with.

use core::fmt;
use core::marker::PhantomData;

use digest::{
    FixedOutput, FixedOutputReset, InvalidLength, KeyInit, MacMarker, Output, OutputSizeUser,
    Reset, Update, common::KeySizeUser,
};

use crate::sha2::{Sha256, Sha384, Sha512};

/// A hash rind can key HMAC with: [`Sha256`], [`Sha384`], and [`Sha512`].
pub trait HmacHash: sealed::Sealed + OutputSizeUser + digest::common::BlockSizeUser {
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

/// HMAC over `D`, as `hmac::Hmac<D>`: any key length, `Clone`, resettable.
///
/// The key is rind's [`rind::hmac::Key`], which wipes itself on drop, and so
/// does the running state; no other copy of the key is made.
pub struct Hmac<D: HmacHash> {
    key: rind::hmac::Key,
    context: rind::hmac::Context,
    hash: PhantomData<D>,
}

impl<D: HmacHash> Clone for Hmac<D> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            context: self.context.clone(),
            hash: PhantomData,
        }
    }
}

impl<D: HmacHash> fmt::Debug for Hmac<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Hmac { .. }")
    }
}

impl<D: HmacHash> KeySizeUser for Hmac<D> {
    type KeySize = <D as digest::common::BlockSizeUser>::BlockSize;
}

impl<D: HmacHash> KeyInit for Hmac<D> {
    fn new(key: &digest::Key<Self>) -> Self {
        Self::from_key(key.as_slice())
    }

    // HMAC takes a key of any length, as RustCrypto's does.
    fn new_from_slice(key: &[u8]) -> Result<Self, InvalidLength> {
        Ok(Self::from_key(key))
    }
}

impl<D: HmacHash> Hmac<D> {
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

impl<D: HmacHash> MacMarker for Hmac<D> {}

impl<D: HmacHash> OutputSizeUser for Hmac<D> {
    type OutputSize = <D as OutputSizeUser>::OutputSize;
}

impl<D: HmacHash> Update for Hmac<D> {
    fn update(&mut self, data: &[u8]) {
        self.context.update(data);
    }
}

impl<D: HmacHash> FixedOutput for Hmac<D> {
    fn finalize_into(self, out: &mut Output<Self>) {
        out.copy_from_slice(self.context.sign().as_ref());
    }
}

impl<D: HmacHash> Reset for Hmac<D> {
    fn reset(&mut self) {
        self.context = rind::hmac::Context::with_key(&self.key);
    }
}

impl<D: HmacHash> FixedOutputReset for Hmac<D> {
    fn finalize_into_reset(&mut self, out: &mut Output<Self>) {
        let context =
            core::mem::replace(&mut self.context, rind::hmac::Context::with_key(&self.key));
        out.copy_from_slice(context.sign().as_ref());
    }
}
