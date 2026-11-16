// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};

use super::{Key, PublicKeyHandle, load, pkcs8};
use crate::Error;
use crate::encoding::{Encoded, Pkcs8, Spki};
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
    fn rind_fips_ml_dsa_has_seed(key: *const MlDsaHandle) -> bool;
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

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::MlDsa44 {}
    impl Sealed for super::MlDsa65 {}
    impl Sealed for super::MlDsa87 {}
}

/// An ML-DSA parameter set, as FIPS 204 standardises them: [`MlDsa44`],
/// [`MlDsa65`], or [`MlDsa87`], which fixes the sizes of its keys and
/// signatures.
pub trait ParameterSet:
    sealed::Sealed + fmt::Debug + Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static
{
    /// The parameter set's number in the module's C ABI.
    #[doc(hidden)]
    const ID: u32;
    /// Its verification algorithm's number in the module's C ABI.
    #[doc(hidden)]
    const VERIFICATION: u32;
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

impl ParameterSet for MlDsa44 {
    const ID: u32 = ids::ml_dsa::ML_DSA_44;
    const VERIFICATION: u32 = ids::signature::ML_DSA_44;
    const NAME: &'static str = "ML-DSA-44";
    type Signature = [u8; 2420];
}

impl ParameterSet for MlDsa65 {
    const ID: u32 = ids::ml_dsa::ML_DSA_65;
    const VERIFICATION: u32 = ids::signature::ML_DSA_65;
    const NAME: &'static str = "ML-DSA-65";
    type Signature = [u8; 3309];
}

impl ParameterSet for MlDsa87 {
    const ID: u32 = ids::ml_dsa::ML_DSA_87;
    const VERIFICATION: u32 = ids::signature::ML_DSA_87;
    const NAME: &'static str = "ML-DSA-87";
    type Signature = [u8; 4627];
}

/// An ML-DSA public key of parameter set `P`: FIPS 204's encoding.
pub struct PublicKey<P: ParameterSet> {
    key: Key,
    set: PhantomData<P>,
}

impl<P: ParameterSet> PublicKey<P> {
    fn from_key(key: Key) -> Self {
        Self {
            key,
            set: PhantomData,
        }
    }

    /// Parses FIPS 204's encoding of a public key: any bytes of the
    /// parameter set's length are one.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        Key::new(P::VERIFICATION, bytes).map(Self::from_key)
    }

    /// Parses a public key from its `SubjectPublicKeyInfo` DER, which names
    /// the parameter set's OID (RFC 9881).
    pub fn from_spki(der: &[u8]) -> Result<Self, Error> {
        Key::from_spki(P::VERIFICATION, der).map(Self::from_key)
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo` naming its
    /// parameter set.
    pub fn to_spki(&self) -> Spki {
        self.key.to_spki()
    }

    /// Verifies `signature` over `message`: pure ML-DSA with the empty
    /// context, as TLS and X.509 sign.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        self.key.verify(message, signature)
    }
}

impl<P: ParameterSet> Clone for PublicKey<P> {
    fn clone(&self) -> Self {
        Self::from_key(self.key.clone())
    }
}

impl<P: ParameterSet> AsRef<[u8]> for PublicKey<P> {
    fn as_ref(&self) -> &[u8] {
        self.key.bytes()
    }
}

impl<P: ParameterSet> fmt::Debug for PublicKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("algorithm", &format_args!("{}", P::NAME))
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// An ML-DSA private key and its public key, of parameter set `P`; held in
/// the module, which wipes it on drop.
///
/// It signs pure ML-DSA (FIPS 204) with the empty context, as TLS and X.509
/// use it, hedged with fresh randomness, as [`PublicKey::verify`] verifies.
pub struct KeyPair<P: ParameterSet> {
    handle: Handle<MlDsaHandle>,
    public: PublicKey<P>,
}

impl<P: ParameterSet> KeyPair<P> {
    fn load(load_with: impl FnOnce(*mut *mut MlDsaHandle) -> Status) -> Result<Self, Error> {
        let handle = load(load_with)?;
        // SAFETY: the handle is live.
        let public = unsafe { rind_fips_ml_dsa_public_key(handle.ptr()) };
        Ok(Self {
            handle,
            public: PublicKey::from_key(Key::from_handle(public)),
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
    pub fn to_seed(&self) -> Option<Seed> {
        // SAFETY: the handle is live.
        let seed = unsafe { rind_fips_ml_dsa_to_seed(self.handle.ptr()) };
        (!seed.is_null()).then(|| Seed(Encoded::new(seed)))
    }

    /// Whether the key pair has its seed, which it lacks when loaded from its
    /// expanded form.
    pub fn has_seed(&self) -> bool {
        // SAFETY: the handle is live.
        unsafe { rind_fips_ml_dsa_has_seed(self.handle.ptr()) }
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
    pub fn public_key(&self) -> &PublicKey<P> {
        &self.public
    }

    /// Signs `message`, with fresh randomness from the module's random
    /// generator.
    pub fn sign(&self, message: &[u8]) -> Result<Signature<P>, Error> {
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
        Ok(Signature(signature))
    }
}

impl<P: ParameterSet> fmt::Debug for KeyPair<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("algorithm", &format_args!("{}", P::NAME))
            .finish_non_exhaustive()
    }
}

/// An ML-DSA signature of parameter set `P`, FIPS 204's encoding.
pub struct Signature<P: ParameterSet>(P::Signature);

impl<P: ParameterSet> Clone for Signature<P> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<P: ParameterSet> AsRef<[u8]> for Signature<P> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<P: ParameterSet> fmt::Debug for Signature<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

/// An ML-DSA private key's 32-byte seed, held in the module, which wipes it
/// on drop.
pub struct Seed(Encoded);

impl AsRef<[u8]> for Seed {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for Seed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Seed").finish_non_exhaustive()
    }
}
