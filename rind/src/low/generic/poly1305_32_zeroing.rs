// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The wipe-on-drop test for `poly1305_32::Poly1305`, in a file of its own:
//! it needs `unsafe` to read the dropped bytes, and the file with the
//! type's assertions must not hold any
//! (`low::tests::no_debug_assert_beside_unsafe`).

#![cfg_attr(coverage_nightly, coverage(off))]

use super::Poly1305;

// Dropping wipes the whole value, padding included, whether or not any
// input was buffered. The drop runs in place and the bytes are read
// before the storage goes, as `rind/tests/zeroing.rs` does for the
// public key types, which cannot reach this crate-internal type.
#[test]
fn zeroes_on_drop() {
    use core::mem::{ManuallyDrop, size_of};

    for buffered in [0usize, 5, 16, 40] {
        let mut p = ManuallyDrop::new(Poly1305::new(&[0xff; 32]));
        p.add_bytes(&[0xff; 40][..buffered]);
        // SAFETY: `p` is dropped once, here, and only its bytes are
        // read afterwards.
        unsafe { ManuallyDrop::drop(&mut p) };
        // SAFETY: `p` still owns `size_of::<Poly1305>()` initialized bytes.
        let bytes: &[u8] = unsafe {
            core::slice::from_raw_parts((&raw const *p).cast::<u8>(), size_of::<Poly1305>())
        };
        assert!(bytes.iter().all(|&b| b == 0), "{buffered}: {bytes:?}");
    }
}
