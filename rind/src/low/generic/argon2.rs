// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's 1 KiB block and its compression function, RFC 9106 section 3.6.
//!
//! The mixing function is BlaMka, not BLAKE2b's. The rotations are BLAKE2b's.
//! This is the portable permutation. A backend may replace [`compress`].

use core::alloc::Layout;
use core::ptr;
use std::alloc::{alloc, dealloc};

use super::zeroise::{Zeroable, zeroise, zeroise_value};
use crate::Error;

/// One memory block: 128 little-endian 64-bit words, 1024 bytes.
///
/// Aligned to 64 so a vector permutation can load it.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub(crate) struct Block(pub(crate) [u64; 128]);

impl Block {
    pub(crate) const fn zero() -> Self {
        Self([0; 128])
    }
}

/// `G(prev, reference)`, optionally XORed with the block it replaces.
///
/// `next` may alias `prev` or `reference`: both are read before `next` is written.
///
/// aarch64's release build runs the NEON permutation instead. The scalar one
/// stays in test builds, which compare the two.
#[cfg(any(test, not(rind_backend = "aarch64")))]
pub(crate) fn compress(next: &mut Block, prev: &Block, reference: &Block, with_xor: bool) {
    let mut r = [0u64; 128];
    let mut tmp = [0u64; 128];
    for i in 0..128 {
        r[i] = prev.0[i] ^ reference.0[i];
        tmp[i] = r[i];
        if with_xor {
            tmp[i] ^= next.0[i];
        }
    }
    // Columns: eight independent 16-word permutations.
    for col in 0..8 {
        let mut v = [0u64; 16];
        v.copy_from_slice(&r[col * 16..col * 16 + 16]);
        round(&mut v);
        r[col * 16..col * 16 + 16].copy_from_slice(&v);
    }
    // Rows: word 2*row of each column, then the word beside it.
    for row in 0..8 {
        let mut v = [0u64; 16];
        for k in 0..16 {
            v[k] = r[row * 2 + (k % 2) + 16 * (k / 2)];
        }
        round(&mut v);
        for k in 0..16 {
            r[row * 2 + (k % 2) + 16 * (k / 2)] = v[k];
        }
    }
    for i in 0..128 {
        next.0[i] = tmp[i] ^ r[i];
    }
}

/// BLAKE2b's round with no message, using BlaMka in place of addition.
#[cfg(any(test, not(rind_backend = "aarch64")))]
fn round(v: &mut [u64; 16]) {
    g(v, 0, 4, 8, 12);
    g(v, 1, 5, 9, 13);
    g(v, 2, 6, 10, 14);
    g(v, 3, 7, 11, 15);
    g(v, 0, 5, 10, 15);
    g(v, 1, 6, 11, 12);
    g(v, 2, 7, 8, 13);
    g(v, 3, 4, 9, 14);
}

#[cfg(any(test, not(rind_backend = "aarch64")))]
fn g(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize) {
    v[a] = blamka(v[a], v[b]);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = blamka(v[c], v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = blamka(v[a], v[b]);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = blamka(v[c], v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

/// `x + y + 2 * (x mod 2^32) * (y mod 2^32)`.
#[cfg(any(test, not(rind_backend = "aarch64")))]
fn blamka(x: u64, y: u64) -> u64 {
    let product = (x & 0xFFFF_FFFF).wrapping_mul(y & 0xFFFF_FFFF);
    x.wrapping_add(y)
        .wrapping_add(product.wrapping_add(product))
}

/// A password, or any other owned secret bytes, wiped on drop under `wipe`.
///
/// All-zero is an empty buffer, so [`zeroise_value`] leaves a value `Drop` accepts.
#[repr(C)]
pub(crate) struct OwnedSecret {
    ptr: *mut u8,
    len: usize,
    cap: usize,
}

impl Zeroable for OwnedSecret {}

// SAFETY: the buffer is owned by this value and not aliased. `as_slice` only
// reads it, and `drop` frees it once, so it can move and be shared.
unsafe impl Send for OwnedSecret {}
// SAFETY: as above. A shared reference cannot drop the buffer.
unsafe impl Sync for OwnedSecret {}

impl OwnedSecret {
    /// Copies `bytes`. Fails with [`Error::OutOfRange`] when the copy cannot be allocated.
    pub(crate) fn new(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.is_empty() {
            return Ok(Self {
                ptr: ptr::null_mut(),
                len: 0,
                cap: 0,
            });
        }
        let layout = Layout::from_size_align(bytes.len(), 1).map_err(|_| Error::OutOfRange)?;
        // SAFETY: `layout` has a non-zero size, which `from_size_align` guaranteed.
        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            return Err(Error::OutOfRange);
        }
        // SAFETY: `ptr` is `bytes.len()` writable bytes the allocator just returned,
        // and `bytes` is that many readable bytes. The regions do not overlap.
        unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, bytes.len()) };
        Ok(Self {
            ptr,
            len: bytes.len(),
            cap: bytes.len(),
        })
    }

    pub(crate) fn as_slice(&self) -> &[u8] {
        if self.len == 0 {
            return &[];
        }
        // SAFETY: `new` allocated `len` bytes at `ptr` and nothing has freed them.
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}

impl Drop for OwnedSecret {
    fn drop(&mut self) {
        if self.cap != 0 {
            // SAFETY: `new` allocated `cap` bytes, of which the first `len` are
            // initialized, at `ptr`, and this is the only free.
            unsafe {
                zeroise(core::slice::from_raw_parts_mut(self.ptr, self.len));
                let layout = Layout::from_size_align(self.cap, 1).unwrap();
                dealloc(self.ptr, layout);
            }
        }
        zeroise_value(self);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn owned_secret_round_trips_and_empties() {
        let empty = OwnedSecret::new(b"").unwrap();
        assert!(empty.as_slice().is_empty());
        let owned = OwnedSecret::new(b"password").unwrap();
        assert_eq!(owned.as_slice(), b"password");
    }
}
