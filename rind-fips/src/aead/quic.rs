// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::cipher::new_handle;
use crate::ffi::{Bytes, Handle, Status, ids, opaque};
use crate::{Error, hkdf};

opaque! {
    QuicHpKey => rind_fips_quic_hp_free,
}

unsafe extern "C" {
    fn rind_fips_quic_hp_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut QuicHpKey,
    ) -> Status;
    fn rind_fips_quic_hp_mask(
        key: *const QuicHpKey,
        sample: *const [u8; SAMPLE_LEN],
        mask: *mut [u8; 5],
    );
    fn rind_fips_hkdf_expand_quic_hp(
        prk: *const hkdf::HkdfPrk,
        info: *const Bytes,
        info_len: usize,
        id: u32,
    ) -> *mut QuicHpKey;
}

/// The length of a header-protection sample, in bytes, for every algorithm.
pub const SAMPLE_LEN: usize = 16;

/// A header-protection cipher, which fixes the key length a key must have.
pub struct Algorithm {
    id: u32,
    name: &'static str,
    key_len: usize,
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Algorithm")
            .field("id", &format_args!("{}", self.name))
            .finish()
    }
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        self.key_len
    }
}

/// AES-128 header protection, which QUIC pairs with AES-128-GCM.
pub static AES_128: Algorithm = Algorithm {
    id: ids::aes::AES_128,
    name: "Aes128",
    key_len: 16,
};

/// AES-256 header protection, which QUIC pairs with AES-256-GCM.
pub static AES_256: Algorithm = Algorithm {
    id: ids::aes::AES_256,
    name: "Aes256",
    key_len: 32,
};

/// A header-protection key, expanded once for its algorithm; held in the
/// module, which wipes it on drop.
pub struct HeaderProtectionKey {
    algorithm: &'static Algorithm,
    handle: Handle<QuicHpKey>,
}

impl HeaderProtectionKey {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not [`Algorithm::key_len`] bytes.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe { rind_fips_quic_hp_new(algorithm.id, key.as_ptr(), key.len(), out) }
        })?;
        Ok(Self { algorithm, handle })
    }

    /// Computes the mask for `sample`: its first byte masks the packet's first
    /// byte, and the rest mask the packet number.
    pub fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5] {
        let mut mask = [0; 5];
        // SAFETY: the handle is live, `sample` is `SAMPLE_LEN` readable
        // bytes, and `mask` 5 writable bytes.
        unsafe { rind_fips_quic_hp_mask(self.handle.ptr(), sample, &mut mask) };
        mask
    }
}

impl fmt::Debug for HeaderProtectionKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HeaderProtectionKey")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}

/// A key of the algorithm's [`Algorithm::key_len`].
impl hkdf::sealed::Sealed for &'static Algorithm {
    fn len(&self) -> usize {
        self.key_len()
    }
}
impl hkdf::KeyType for &'static Algorithm {}

impl From<hkdf::Okm<'_, &'static Algorithm>> for HeaderProtectionKey {
    fn from(okm: hkdf::Okm<'_, &'static Algorithm>) -> Self {
        let info = okm.info();
        // SAFETY: the handle is live, and `info` lists readable strings.
        let handle = unsafe {
            rind_fips_hkdf_expand_quic_hp(
                okm.prk.handle.ptr(),
                info.as_ptr(),
                info.len(),
                okm.len.id,
            )
        };
        Self {
            algorithm: okm.len,
            handle: Handle::new(handle),
        }
    }
}
