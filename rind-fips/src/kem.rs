// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::encoding::Encoded;
use crate::ffi::{self, Handle, Status, ids, opaque};

opaque! {
    KemDecapsulationKey => rind_fips_kem_decapsulation_key_free,
    KemEncapsulationKey => rind_fips_kem_encapsulation_key_free,
}

unsafe extern "C" {
    fn rind_fips_kem_generate(id: u32, out: *mut *mut KemDecapsulationKey) -> Status;
    fn rind_fips_kem_public_key(
        key: *const KemDecapsulationKey,
        out: *mut u8,
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
        out: *mut *mut ffi::Encoded,
    ) -> Status;
}

/// An encapsulation key's length.
const ENCAPSULATION_KEY_LEN: usize = 1184;

/// A ciphertext's length.
const CIPHERTEXT_LEN: usize = 1088;

/// A key encapsulation mechanism.
pub struct Algorithm {
    id: u32,
    name: &'static str,
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)
    }
}

/// ML-KEM-768, as standardised by FIPS-203.
pub static ML_KEM_768: Algorithm = Algorithm {
    id: ids::kem::ML_KEM_768,
    name: "MlKem768",
};

/// A decapsulation key, which decapsulates any number of ciphertexts; held
/// in the module, which wipes it on drop.
pub struct DecapsulationKey(Handle<KemDecapsulationKey>);

impl DecapsulationKey {
    /// Generates a decapsulation key for `algorithm` from the module's DRBG,
    /// after checking that a secret encapsulated to it decapsulates.
    pub fn generate(algorithm: &'static Algorithm) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: `out` is writable.
        let status = unsafe { rind_fips_kem_generate(algorithm.id, &mut out) };
        Handle::from_status(status, out).map(Self)
    }

    /// Returns the encapsulation key to send to the peer.
    pub fn public_key(&self) -> EncapsulationKey {
        let mut bytes = [0; ENCAPSULATION_KEY_LEN];
        // SAFETY: the handle is live, and `bytes` holds 1184 writable bytes.
        let handle = unsafe { rind_fips_kem_public_key(self.0.ptr(), bytes.as_mut_ptr()) };
        EncapsulationKey {
            handle: Handle::new(handle),
            bytes,
        }
    }

    /// Recovers the secret the peer encapsulated in `ciphertext`.
    ///
    /// A ciphertext of the wrong length is refused. Any other tampering
    /// yields an unrelated secret (FIPS-203's implicit rejection), so the
    /// peer learns nothing until the secret is used.
    pub fn decapsulate(&self, ciphertext: &[u8]) -> Result<SharedSecret, Error> {
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
        Encoded::from_status(status, out).map(SharedSecret)
    }
}

impl fmt::Debug for DecapsulationKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecapsulationKey").finish_non_exhaustive()
    }
}

/// An encapsulation key, which anyone may encapsulate a secret to.
pub struct EncapsulationKey {
    handle: Handle<KemEncapsulationKey>,
    bytes: [u8; ENCAPSULATION_KEY_LEN],
}

impl EncapsulationKey {
    /// Parses a peer's encapsulation key for `algorithm`.
    ///
    /// Fails with [`Error::KeyRejected`] for the wrong length, or if it fails
    /// FIPS-203's modulus check.
    pub fn new(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: `bytes` is readable, and `out` writable.
        let status = unsafe {
            rind_fips_kem_encapsulation_key_new(algorithm.id, bytes.as_ptr(), bytes.len(), &mut out)
        };
        let handle = Handle::from_status(status, out)?;
        Ok(Self {
            handle,
            bytes: bytes
                .try_into()
                .expect("the module takes only an encapsulation key's length"),
        })
    }

    /// Encapsulates a fresh random secret, returning the ciphertext to send
    /// to the key's holder and the secret.
    pub fn encapsulate(&self) -> Result<(Ciphertext, SharedSecret), Error> {
        let mut ciphertext = [0; CIPHERTEXT_LEN];
        let mut out = core::ptr::null_mut();
        // SAFETY: the handle is live, `ciphertext` holds 1088 writable
        // bytes, and `out` is writable.
        let status = unsafe {
            rind_fips_kem_encapsulate(self.handle.ptr(), ciphertext.as_mut_ptr(), &mut out)
        };
        let secret = Encoded::from_status(status, out).map(SharedSecret)?;
        Ok((Ciphertext(ciphertext), secret))
    }
}

impl Clone for EncapsulationKey {
    fn clone(&self) -> Self {
        Self {
            // SAFETY: the handle is live.
            handle: Handle::new(unsafe {
                rind_fips_kem_encapsulation_key_clone(self.handle.ptr())
            }),
            bytes: self.bytes,
        }
    }
}

impl AsRef<[u8]> for EncapsulationKey {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl fmt::Debug for EncapsulationKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EncapsulationKey")
            .field(&self.as_ref())
            .finish()
    }
}

/// A ciphertext carrying an encapsulated secret, to send to the key's holder.
#[derive(Clone)]
pub struct Ciphertext([u8; CIPHERTEXT_LEN]);

impl AsRef<[u8]> for Ciphertext {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

// As rind derives it, around its own `Ciphertext`.
impl fmt::Debug for Ciphertext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Inner<'a>(&'a [u8; CIPHERTEXT_LEN]);
        impl fmt::Debug for Inner<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple("Ciphertext").field(self.0).finish()
            }
        }
        f.debug_tuple("Ciphertext").field(&Inner(&self.0)).finish()
    }
}

/// The secret both parties share; held in the module, which wipes it on
/// drop.
pub struct SharedSecret(Encoded);

impl AsRef<[u8]> for SharedSecret {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for SharedSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SharedSecret").finish_non_exhaustive()
    }
}
