// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::{Key, PublicKeyHandle, load, pkcs8};
use crate::Error;
use crate::encoding::{Encoded, Pkcs8, Spki};
use crate::ffi::{self, Handle, Status, ids, opaque};

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
}

/// An Ed25519 public key: its 32-byte encoding.
#[derive(Clone)]
pub struct PublicKey(Key);

impl PublicKey {
    /// Parses a 32-byte public key, refusing a malformed key, or a point of
    /// small order, which verifies signatures nobody made, before any
    /// signature arrives.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        Key::new(ids::signature::ED25519, bytes).map(Self)
    }

    /// Parses a public key from its `SubjectPublicKeyInfo` DER, naming
    /// `id-Ed25519`.
    pub fn from_spki(der: &[u8]) -> Result<Self, Error> {
        Key::from_spki(ids::signature::ED25519, der).map(Self)
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo` naming
    /// `id-Ed25519`.
    pub fn to_spki(&self) -> Spki {
        self.0.to_spki()
    }

    /// Verifies `signature` over `message`, refusing a malformed signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        self.0.verify(message, signature)
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey").field(&self.as_ref()).finish()
    }
}

/// An Ed25519 signature: 64 bytes.
#[derive(Clone, Copy)]
pub struct Signature([u8; 64]);

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

/// An Ed25519 private key's 32-byte seed, held in the module, which wipes
/// it on drop.
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

/// An Ed25519 private key and its public key; held in the module, which
/// wipes it on drop.
pub struct KeyPair {
    handle: Handle<Ed25519Handle>,
    public: PublicKey,
}

impl KeyPair {
    fn load(load_with: impl FnOnce(*mut *mut Ed25519Handle) -> Status) -> Result<Self, Error> {
        let handle = load(load_with)?;
        // SAFETY: the handle is live.
        let public = unsafe { rind_fips_ed25519_public_key(handle.ptr()) };
        Ok(Self {
            handle,
            public: PublicKey(Key::from_handle(public)),
        })
    }

    /// Generates a key pair from the module's random generator, then checks
    /// that it signs what its public key verifies.
    pub fn generate() -> Result<Self, Error> {
        // SAFETY: `out` is writable.
        Self::load(|out| unsafe { rind_fips_ed25519_generate(out) })
    }

    /// Loads a PKCS#8 Ed25519 key, refused if it carries a public key
    /// (v2, RFC 5958) that does not match.
    ///
    /// This also takes PKCS#8 v1, which carries no public key: common tools
    /// write v1, and such a key is no less valid.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        Self::load(|out| unsafe { rind_fips_ed25519_from_pkcs8(der.as_ptr(), der.len(), out) })
    }

    /// Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public
    /// key.
    ///
    /// Prefer [`Self::from_seed_and_public_key`] when the public key is at
    /// hand, which checks it.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        // SAFETY: `seed` is readable, and `out` writable.
        Self::load(|out| unsafe { rind_fips_ed25519_from_seed(seed.as_ptr(), seed.len(), out) })
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    ///
    /// This suits a JWK's `d` and `x`.
    pub fn from_seed_and_public_key(seed: &[u8], public_key: &[u8]) -> Result<Self, Error> {
        Self::load(|out| {
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
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Signs `message`.
    pub fn sign(&self, message: &[u8]) -> Signature {
        let mut signature = [0; 64];
        // SAFETY: the handle is live, `message` readable, and `signature`
        // writable for 64.
        unsafe {
            rind_fips_ed25519_sign(
                self.handle.ptr(),
                message.as_ptr(),
                message.len(),
                signature.as_mut_ptr(),
            )
        };
        Signature(signature)
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
    pub fn to_seed(&self) -> Seed {
        // SAFETY: the handle is live.
        Seed(Encoded::new(unsafe {
            rind_fips_ed25519_to_seed(self.handle.ptr())
        }))
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("public_key", &self.public.as_ref())
            .finish_non_exhaustive()
    }
}
