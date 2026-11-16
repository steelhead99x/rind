// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};

use crate::Error;
use crate::encoding::Encoded;
use crate::ffi::{self, Handle, Status, ids, opaque};
use crate::signature::ml_dsa::Array;

opaque! {
    KemDecapsulationKey => rind_fips_kem_decapsulation_key_free,
    KemEncapsulationKey => rind_fips_kem_encapsulation_key_free,
}

unsafe extern "C" {
    fn rind_fips_kem_generate(id: u32, out: *mut *mut KemDecapsulationKey) -> Status;
    fn rind_fips_kem_public_key(
        key: *const KemDecapsulationKey,
        out: *mut u8,
        len: usize,
    ) -> *mut KemEncapsulationKey;
    fn rind_fips_kem_decapsulate(
        key: *const KemDecapsulationKey,
        ciphertext: *const u8,
        len: usize,
        out: *mut *mut ffi::Encoded,
    ) -> Status;
    fn rind_fips_kem_encapsulation_key_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut KemEncapsulationKey,
    ) -> Status;
    fn rind_fips_kem_encapsulation_key_clone(
        key: *const KemEncapsulationKey,
    ) -> *mut KemEncapsulationKey;
    fn rind_fips_kem_encapsulate(
        key: *const KemEncapsulationKey,
        ciphertext: *mut u8,
        len: usize,
        out: *mut *mut ffi::Encoded,
    ) -> Status;
}

/// ML-KEM-512, as standardised by FIPS-203.
#[derive(Debug)]
pub enum MlKem512 {}

/// ML-KEM-768, as standardised by FIPS-203.
#[derive(Debug)]
pub enum MlKem768 {}

/// ML-KEM-1024, as standardised by FIPS-203.
#[derive(Debug)]
pub enum MlKem1024 {}

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::MlKem512 {}
    impl Sealed for super::MlKem768 {}
    impl Sealed for super::MlKem1024 {}
}

/// An ML-KEM parameter set: [`MlKem512`], [`MlKem768`], or [`MlKem1024`].
///
/// Each key, ciphertext, and secret names its set, so a ciphertext of one
/// set fails to compile against a key of another.
pub trait Algorithm:
    sealed::Sealed + fmt::Debug + Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static
{
    /// The parameter set's number in the module's C ABI.
    #[doc(hidden)]
    const ID: u32;
    /// An encoded encapsulation key.
    #[doc(hidden)]
    type EncapKeyBytes: Array;
    /// A ciphertext.
    #[doc(hidden)]
    type CiphertextBytes: Array;
}

impl Algorithm for MlKem512 {
    const ID: u32 = ids::kem::ML_KEM_512;
    type EncapKeyBytes = [u8; 800];
    type CiphertextBytes = [u8; 768];
}

impl Algorithm for MlKem768 {
    const ID: u32 = ids::kem::ML_KEM_768;
    type EncapKeyBytes = [u8; 1184];
    type CiphertextBytes = [u8; 1088];
}

impl Algorithm for MlKem1024 {
    const ID: u32 = ids::kem::ML_KEM_1024;
    type EncapKeyBytes = [u8; 1568];
    type CiphertextBytes = [u8; 1568];
}

/// A decapsulation key, which decapsulates any number of ciphertexts; held
/// in the module, which wipes it on drop.
pub struct DecapsulationKey<A: Algorithm>(Handle<KemDecapsulationKey>, PhantomData<A>);

impl<A: Algorithm> DecapsulationKey<A> {
    /// Generates a decapsulation key from the module's DRBG, after checking
    /// that a secret encapsulated to it decapsulates.
    pub fn generate() -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: `out` is writable.
        let status = unsafe { rind_fips_kem_generate(A::ID, &mut out) };
        Handle::from_status(status, out).map(|handle| Self(handle, PhantomData))
    }

    /// Returns the encapsulation key to send to the peer.
    pub fn public_key(&self) -> EncapsulationKey<A> {
        let mut bytes = A::EncapKeyBytes::zeroed();
        let out = bytes.as_mut();
        // SAFETY: the handle is live, of set `A`, and `out` holds its
        // encapsulation key's length in writable bytes.
        let handle = unsafe { rind_fips_kem_public_key(self.0.ptr(), out.as_mut_ptr(), out.len()) };
        EncapsulationKey {
            handle: Handle::new(handle),
            bytes,
        }
    }

    /// Recovers the secret the peer encapsulated in `ciphertext`.
    ///
    /// A tampered ciphertext yields an unrelated secret (FIPS-203's implicit
    /// rejection), so the peer learns nothing until the secret is used.
    pub fn decapsulate(&self, ciphertext: &Ciphertext<A>) -> SharedSecret<A> {
        let ciphertext = ciphertext.0.as_ref();
        let mut out = core::ptr::null_mut();
        // SAFETY: the handle is live, `ciphertext` readable, and `out`
        // writable.
        let status = unsafe {
            rind_fips_kem_decapsulate(
                self.0.ptr(),
                ciphertext.as_ptr(),
                ciphertext.len(),
                &mut out,
            )
        };
        let secret = Encoded::from_status(status, out)
            .expect("the module decapsulates any ciphertext of the key's set");
        SharedSecret(secret, PhantomData)
    }
}

impl<A: Algorithm> fmt::Debug for DecapsulationKey<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecapsulationKey").finish_non_exhaustive()
    }
}

/// An encapsulation key, which anyone may encapsulate a secret to.
pub struct EncapsulationKey<A: Algorithm> {
    handle: Handle<KemEncapsulationKey>,
    bytes: A::EncapKeyBytes,
}

impl<A: Algorithm> EncapsulationKey<A> {
    /// Parses a peer's encapsulation key.
    ///
    /// Fails with [`Error::KeyRejected`] for the wrong length, or if it fails
    /// FIPS-203's modulus check.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: `bytes` is readable, and `out` writable.
        let status = unsafe {
            rind_fips_kem_encapsulation_key_new(A::ID, bytes.as_ptr(), bytes.len(), &mut out)
        };
        let handle = Handle::from_status(status, out)?;
        let mut copy = A::EncapKeyBytes::zeroed();
        copy.as_mut().copy_from_slice(bytes);
        Ok(Self {
            handle,
            bytes: copy,
        })
    }

    /// Encapsulates a fresh random secret, returning the ciphertext to send
    /// to the key's holder and the secret.
    pub fn encapsulate(&self) -> Result<(Ciphertext<A>, SharedSecret<A>), Error> {
        let mut ciphertext = A::CiphertextBytes::zeroed();
        let sealed = ciphertext.as_mut();
        let mut out = core::ptr::null_mut();
        // SAFETY: the handle is live, of set `A`, `sealed` holds its
        // ciphertext length in writable bytes, and `out` is writable.
        let status = unsafe {
            rind_fips_kem_encapsulate(
                self.handle.ptr(),
                sealed.as_mut_ptr(),
                sealed.len(),
                &mut out,
            )
        };
        let secret = Encoded::from_status(status, out)?;
        Ok((Ciphertext(ciphertext), SharedSecret(secret, PhantomData)))
    }
}

impl<A: Algorithm> Clone for EncapsulationKey<A> {
    fn clone(&self) -> Self {
        Self {
            // SAFETY: the handle is live.
            handle: Handle::new(unsafe {
                rind_fips_kem_encapsulation_key_clone(self.handle.ptr())
            }),
            bytes: self.bytes.clone(),
        }
    }
}

impl<A: Algorithm> AsRef<[u8]> for EncapsulationKey<A> {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl<A: Algorithm> fmt::Debug for EncapsulationKey<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EncapsulationKey")
            .field(&self.as_ref())
            .finish()
    }
}

/// A ciphertext carrying an encapsulated secret, to send to the key's holder.
pub struct Ciphertext<A: Algorithm>(A::CiphertextBytes);

impl<A: Algorithm> Ciphertext<A> {
    /// Takes a ciphertext the peer sent.
    ///
    /// Fails with [`Error::WrongLength`] unless it is the parameter set's
    /// length.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        let mut ciphertext = A::CiphertextBytes::zeroed();
        if bytes.len() != ciphertext.as_ref().len() {
            return Err(Error::WrongLength);
        }
        ciphertext.as_mut().copy_from_slice(bytes);
        Ok(Self(ciphertext))
    }
}

impl<A: Algorithm> Clone for Ciphertext<A> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

// As rind prints its own.
impl<A: Algorithm> fmt::Debug for Ciphertext<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Ciphertext").field(&self.0).finish()
    }
}

impl<A: Algorithm> AsRef<[u8]> for Ciphertext<A> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

/// The secret both parties share; held in the module, which wipes it on
/// drop.
pub struct SharedSecret<A: Algorithm>(Encoded, PhantomData<A>);

impl<A: Algorithm> AsRef<[u8]> for SharedSecret<A> {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl<A: Algorithm> fmt::Debug for SharedSecret<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SharedSecret").finish_non_exhaustive()
    }
}
