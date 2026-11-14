// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};

use super::{PublicKey, PublicKeyHandle, Verification, load, pkcs8};
use crate::Error;
use crate::encoding::{Encoded, Pkcs8};
use crate::ffi::{self, Handle, Status, ids, opaque};

opaque! {
    MlDsaHandle => rind_fips_ml_dsa_free,
}

unsafe extern "C" {
    fn rind_fips_ml_dsa_generate(set: u32, out: *mut *mut MlDsaHandle) -> Status;
    fn rind_fips_ml_dsa_from_seed(
        set: u32,
        seed: *const u8,
        len: usize,
        out: *mut *mut MlDsaHandle,
    ) -> Status;
    fn rind_fips_ml_dsa_from_pkcs8(
        set: u32,
        der: *const u8,
        len: usize,
        out: *mut *mut MlDsaHandle,
    ) -> Status;
    fn rind_fips_ml_dsa_to_seed(key: *const MlDsaHandle) -> *mut ffi::Encoded;
    fn rind_fips_ml_dsa_to_pkcs8(key: *const MlDsaHandle) -> *mut ffi::Encoded;
    fn rind_fips_ml_dsa_public_key(key: *const MlDsaHandle) -> *mut PublicKeyHandle;
    fn rind_fips_ml_dsa_sign(
        key: *const MlDsaHandle,
        message: *const u8,
        len: usize,
        out: *mut u8,
        cap: usize,
        out_len: *mut usize,
    ) -> Status;
}

/// ML-DSA-44, as standardised by FIPS 204.
#[derive(Debug)]
pub enum MlDsa44 {}

/// ML-DSA-65, as standardised by FIPS 204.
#[derive(Debug)]
pub enum MlDsa65 {}

/// ML-DSA-87, as standardised by FIPS 204.
#[derive(Debug)]
pub enum MlDsa87 {}

/// An ML-DSA parameter set, as FIPS 204 standardises them: [`MlDsa44`],
/// [`MlDsa65`], or [`MlDsa87`], which fixes the sizes of its keys and
/// signatures.
pub trait MlDsaParameterSet:
    fmt::Debug + Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static
{
    /// The parameter set's number in the module's C ABI.
    #[doc(hidden)]
    const ID: u32;
    /// FIPS 204's name for it.
    #[doc(hidden)]
    const NAME: &'static str;
    /// `sigma`, FIPS 204's signature encoding.
    #[doc(hidden)]
    type Signature: Array;
}

/// A byte array of a parameter set's length.
pub trait Array:
    Clone
    + fmt::Debug
    + AsRef<[u8]>
    + AsMut<[u8]>
    + Send
    + Sync
    + Unpin
    + UnwindSafe
    + RefUnwindSafe
    + 'static
{
    /// Every byte zero.
    #[doc(hidden)]
    fn zeroed() -> Self;
}

impl<const LEN: usize> Array for [u8; LEN] {
    fn zeroed() -> Self {
        [0; LEN]
    }
}

impl MlDsaParameterSet for MlDsa44 {
    const ID: u32 = ids::ml_dsa::ML_DSA_44;
    const NAME: &'static str = "ML-DSA-44";
    type Signature = [u8; 2420];
}

impl MlDsaParameterSet for MlDsa65 {
    const ID: u32 = ids::ml_dsa::ML_DSA_65;
    const NAME: &'static str = "ML-DSA-65";
    type Signature = [u8; 3309];
}

impl MlDsaParameterSet for MlDsa87 {
    const ID: u32 = ids::ml_dsa::ML_DSA_87;
    const NAME: &'static str = "ML-DSA-87";
    type Signature = [u8; 4627];
}

/// An ML-DSA private key and its public key, of parameter set `P`; held in
/// the module, which wipes it on drop.
///
/// It signs pure ML-DSA (FIPS 204) with the empty context, as TLS and X.509
/// use it, hedged with fresh randomness, as [`verify::ML_DSA_44`],
/// [`verify::ML_DSA_65`], and [`verify::ML_DSA_87`] verify.
///
/// [`verify::ML_DSA_44`]: super::verify::ML_DSA_44
/// [`verify::ML_DSA_65`]: super::verify::ML_DSA_65
/// [`verify::ML_DSA_87`]: super::verify::ML_DSA_87
pub struct MlDsaKeyPair<P: MlDsaParameterSet> {
    handle: Handle<MlDsaHandle>,
    set: PhantomData<P>,
}

impl<P: MlDsaParameterSet> MlDsaKeyPair<P> {
    fn load(load_with: impl FnOnce(*mut *mut MlDsaHandle) -> Status) -> Result<Self, Error> {
        load(load_with).map(|handle| Self {
            handle,
            set: PhantomData,
        })
    }

    /// Generates a key pair from the module's random generator, then checks
    /// that it signs what its public key verifies.
    pub fn generate() -> Result<Self, Error> {
        // SAFETY: `out` is writable.
        Self::load(|out| unsafe { rind_fips_ml_dsa_generate(P::ID, out) })
    }

    /// Expands a 32-byte seed, FIPS 204's `xi`, into its key pair.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        // SAFETY: `seed` is readable, and `out` writable.
        Self::load(|out| unsafe {
            rind_fips_ml_dsa_from_seed(P::ID, seed.as_ptr(), seed.len(), out)
        })
    }

    /// Returns the private key's 32-byte seed, which [`Self::from_seed`]
    /// loads, unless the key was loaded from its expanded form, which has
    /// none.
    pub fn to_seed(&self) -> Option<MlDsaSeed> {
        // SAFETY: the handle is live.
        let seed = unsafe { rind_fips_ml_dsa_to_seed(self.handle.ptr()) };
        (!seed.is_null()).then(|| MlDsaSeed(Encoded::new(seed)))
    }

    /// Loads a PKCS#8 ML-DSA key (RFC 9881), refused if it carries a public
    /// key (v2, RFC 5958) that does not match.
    ///
    /// Its private key may be any of RFC 9881's forms: the seed, the expanded
    /// key, which must be consistent as FIPS 204's key generation writes it,
    /// or both, which must agree.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        Self::load(|out| unsafe {
            rind_fips_ml_dsa_from_pkcs8(P::ID, der.as_ptr(), der.len(), out)
        })
    }

    /// Encodes the private key as PKCS#8 v1 (RFC 9881): its seed, as aws-lc
    /// writes it, or its expanded form if it was loaded from that and has no
    /// seed.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        // SAFETY: the handle is live.
        pkcs8(unsafe { rind_fips_ml_dsa_to_pkcs8(self.handle.ptr()) })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> PublicKey {
        // SAFETY: the handle is live.
        let handle = unsafe { rind_fips_ml_dsa_public_key(self.handle.ptr()) };
        PublicKey::from_handle(handle, Verification::MlDsa(P::NAME))
    }

    /// Signs `message`, with fresh randomness from the module's random
    /// generator.
    pub fn sign(&self, message: &[u8]) -> Result<MlDsaSignature<P>, Error> {
        let mut signature = P::Signature::zeroed();
        let out = signature.as_mut();
        let mut len = 0;
        // SAFETY: the handle is live, `message` readable, and `out`
        // writable for its length.
        ffi::check(unsafe {
            rind_fips_ml_dsa_sign(
                self.handle.ptr(),
                message.as_ptr(),
                message.len(),
                out.as_mut_ptr(),
                out.len(),
                &mut len,
            )
        })?;
        Ok(MlDsaSignature(signature))
    }
}

impl<P: MlDsaParameterSet> fmt::Debug for MlDsaKeyPair<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MlDsaKeyPair")
            .field("algorithm", &format_args!("{}", P::NAME))
            .finish_non_exhaustive()
    }
}

/// An ML-DSA signature of parameter set `P`, FIPS 204's encoding.
pub struct MlDsaSignature<P: MlDsaParameterSet>(P::Signature);

impl<P: MlDsaParameterSet> Clone for MlDsaSignature<P> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<P: MlDsaParameterSet> AsRef<[u8]> for MlDsaSignature<P> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<P: MlDsaParameterSet> fmt::Debug for MlDsaSignature<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MlDsaSignature")
            .field(&self.as_ref())
            .finish()
    }
}

/// An ML-DSA private key's 32-byte seed, held in the module, which wipes it
/// on drop.
pub struct MlDsaSeed(Encoded);

impl AsRef<[u8]> for MlDsaSeed {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for MlDsaSeed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MlDsaSeed").finish_non_exhaustive()
    }
}
