// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::{PublicKey, PublicKeyHandle, SIGNATURE_MAX_LEN, Signature, Verification, load, pkcs8};
use crate::Error;
use crate::encoding::{Encoded, Pkcs8, Spki};
use crate::ffi::{self, Handle, Status, opaque};

opaque! {
    Ed25519Handle => rind_fips_ed25519_free,
}

unsafe extern "C" {
    fn rind_fips_ed25519_generate(out: *mut *mut Ed25519Handle) -> Status;
    fn rind_fips_ed25519_from_pkcs8(
        der: *const u8,
        len: usize,
        out: *mut *mut Ed25519Handle,
    ) -> Status;
    fn rind_fips_ed25519_from_seed(
        seed: *const u8,
        len: usize,
        out: *mut *mut Ed25519Handle,
    ) -> Status;
    fn rind_fips_ed25519_from_seed_and_public_key(
        seed: *const u8,
        seed_len: usize,
        public_key: *const u8,
        public_key_len: usize,
        out: *mut *mut Ed25519Handle,
    ) -> Status;
    fn rind_fips_ed25519_public_key(key: *const Ed25519Handle) -> *mut PublicKeyHandle;
    fn rind_fips_ed25519_sign(
        key: *const Ed25519Handle,
        message: *const u8,
        len: usize,
        out: *mut u8,
    );
    fn rind_fips_ed25519_to_pkcs8(key: *const Ed25519Handle, v1: bool) -> *mut ffi::Encoded;
    fn rind_fips_ed25519_to_seed(key: *const Ed25519Handle) -> *mut ffi::Encoded;
    fn rind_fips_ed25519_to_spki(key: *const Ed25519Handle) -> *mut ffi::Encoded;
}

/// An Ed25519 private key and its public key; held in the module, which
/// wipes it on drop.
pub struct Ed25519KeyPair {
    handle: Handle<Ed25519Handle>,
}

impl Ed25519KeyPair {
    /// Generates a key pair from the module's random generator, then checks
    /// that it signs what its public key verifies.
    pub fn generate() -> Result<Self, Error> {
        // SAFETY: `out` is writable.
        load(|out| unsafe { rind_fips_ed25519_generate(out) }).map(|handle| Self { handle })
    }

    /// Loads a PKCS#8 Ed25519 key, refused if it carries a public key
    /// (v2, RFC 5958) that does not match.
    ///
    /// This also takes PKCS#8 v1, which carries no public key: common tools
    /// write v1, and such a key is no less valid.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        load(|out| unsafe { rind_fips_ed25519_from_pkcs8(der.as_ptr(), der.len(), out) })
            .map(|handle| Self { handle })
    }

    /// Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public
    /// key.
    ///
    /// Prefer [`Self::from_seed_and_public_key`] when the public key is at
    /// hand, which checks it.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        // SAFETY: `seed` is readable, and `out` writable.
        load(|out| unsafe { rind_fips_ed25519_from_seed(seed.as_ptr(), seed.len(), out) })
            .map(|handle| Self { handle })
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    ///
    /// This suits a JWK's `d` and `x`.
    pub fn from_seed_and_public_key(seed: &[u8], public_key: &[u8]) -> Result<Self, Error> {
        load(|out| {
            // SAFETY: `seed` and `public_key` are readable, and `out`
            // writable.
            unsafe {
                rind_fips_ed25519_from_seed_and_public_key(
                    seed.as_ptr(),
                    seed.len(),
                    public_key.as_ptr(),
                    public_key.len(),
                    out,
                )
            }
        })
        .map(|handle| Self { handle })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> PublicKey {
        // SAFETY: the handle is live.
        let handle = unsafe { rind_fips_ed25519_public_key(self.handle.ptr()) };
        PublicKey::from_handle(handle, Verification::Ed25519)
    }

    /// Signs `message`.
    pub fn sign(&self, message: &[u8]) -> Signature {
        let mut signature = Signature {
            bytes: [0; SIGNATURE_MAX_LEN],
            len: 64,
        };
        // SAFETY: the handle is live, `message` readable, and the
        // signature's bytes writable for 64.
        unsafe {
            rind_fips_ed25519_sign(
                self.handle.ptr(),
                message.as_ptr(),
                message.len(),
                signature.bytes.as_mut_ptr(),
            )
        };
        signature
    }

    /// Encodes the key pair as PKCS#8 v2 (RFC 5958).
    pub fn to_pkcs8(&self) -> Pkcs8 {
        // SAFETY: the handle is live.
        pkcs8(unsafe { rind_fips_ed25519_to_pkcs8(self.handle.ptr(), false) })
    }

    /// Encodes the private key as PKCS#8 v1 (RFC 8410), its seed without its
    /// public key, as OpenSSL and BoringSSL write it.
    pub fn to_pkcs8v1(&self) -> Pkcs8 {
        // SAFETY: the handle is live.
        pkcs8(unsafe { rind_fips_ed25519_to_pkcs8(self.handle.ptr(), true) })
    }

    /// Returns the private key's 32-byte seed, as a JWK's `d` holds it.
    ///
    /// This is what [`Self::from_seed_and_public_key`] loads; prefer
    /// [`Self::to_pkcs8`] for stored keys.
    pub fn to_seed(&self) -> Ed25519Seed {
        // SAFETY: the handle is live.
        Ed25519Seed(Encoded::new(unsafe {
            rind_fips_ed25519_to_seed(self.handle.ptr())
        }))
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        // SAFETY: the handle is live.
        Spki::from(Encoded::new(unsafe {
            rind_fips_ed25519_to_spki(self.handle.ptr())
        }))
    }
}

impl fmt::Debug for Ed25519KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let public_key = self.public_key();
        f.debug_struct("Ed25519KeyPair")
            .field("public_key", &public_key.as_ref())
            .finish_non_exhaustive()
    }
}

/// An Ed25519 private key's 32-byte seed, held in the module, which wipes
/// it on drop.
pub struct Ed25519Seed(Encoded);

impl AsRef<[u8]> for Ed25519Seed {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for Ed25519Seed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Ed25519Seed").finish_non_exhaustive()
    }
}
