// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Zeroization of the heap: the module's allocator zeroes every block it
//! frees, so heap scratch, such as RSA's CRT intermediates, and every key
//! handle, is wiped however the code that held it ends.

use std::alloc::{GlobalAlloc, Layout, System};

pub(crate) struct Zeroing;

// SAFETY: defers to `System`, only zeroing a block before freeing it.
unsafe impl GlobalAlloc for Zeroing {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's contract is `System`'s.
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: as for `alloc`.
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: the caller passes a live block of `layout`'s size.
        unsafe {
            zero(ptr, layout.size());
            System.dealloc(ptr, layout);
        }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // `System.realloc` may move the block and free the old one unwiped,
        // so the move is done here.
        // SAFETY: the caller's contract guarantees `new_size` is valid for
        // `layout`'s alignment.
        let new_layout = unsafe { Layout::from_size_align_unchecked(new_size, layout.align()) };
        // SAFETY: as for `alloc`.
        let new = unsafe { self.alloc(new_layout) };
        if !new.is_null() {
            // SAFETY: both blocks are live and at least this long.
            unsafe {
                core::ptr::copy_nonoverlapping(ptr, new, layout.size().min(new_size));
                self.dealloc(ptr, layout);
            }
        }
        new
    }
}

/// Zeroes `len` bytes at `ptr`, which the compiler cannot drop as dead
/// although the block is freed next.
///
/// # Safety
/// `ptr` must be `len` writable bytes.
pub(crate) unsafe fn zero(ptr: *mut u8, len: usize) {
    // SAFETY: the caller's contract.
    unsafe { core::ptr::write_bytes(ptr, 0, len) };
    // SAFETY: an empty instruction sequence, which may read `ptr`.
    unsafe {
        core::arch::asm!("/* {0} */", in(reg) ptr, options(nostack, readonly, preserves_flags));
    }
}
