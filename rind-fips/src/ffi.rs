// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The module's C ABI (`module/src/abi.rs` describes its conventions), and
//! the handles that own what it allocates.

use core::ptr::NonNull;

use crate::Error;

#[path = "../module/src/ids.rs"]
#[allow(dead_code)]
pub(crate) mod ids;

pub(crate) type Status = u32;

/// Zeroes `bytes` with writes the compiler cannot drop as dead, though the
/// value holding them is freed next.
pub(crate) fn wipe(bytes: &mut [u8]) {
    for byte in bytes {
        // SAFETY: `byte` is a valid, aligned `u8`.
        unsafe { core::ptr::write_volatile(byte, 0) };
    }
}

/// `status` as a result.
pub(crate) fn check(status: Status) -> Result<(), Error> {
    match status {
        0 => Ok(()),
        status => Err(Error::from_status(status)),
    }
}

/// A byte string within a list, as `module/src/abi.rs`'s `Bytes`.
#[repr(C)]
pub(crate) struct Bytes {
    ptr: *const u8,
    len: usize,
}

impl Bytes {
    pub(crate) fn list(list: &[&[u8]]) -> Vec<Self> {
        list.iter()
            .map(|b| Self {
                ptr: b.as_ptr(),
                len: b.len(),
            })
            .collect()
    }
}

/// A type of handle the module allocates, and the function that frees it.
pub(crate) trait Opaque {
    /// # Safety
    /// `handle` must be a live handle of this type, not used again.
    unsafe fn free(handle: *mut Self);
}

/// An owned handle to a value in the module, freed on drop. The value never
/// leaves the module, so moving a handle moves only its pointer.
pub(crate) struct Handle<T: Opaque>(NonNull<T>);

impl<T: Opaque> Handle<T> {
    /// Takes ownership of `handle`, which the module allocated.
    pub(crate) fn new(handle: *mut T) -> Self {
        // The module aborts rather than return null on allocation failure.
        Self(NonNull::new(handle).expect("the module returned no handle"))
    }

    /// Takes ownership of what a service wrote to `out` if `status` is 0.
    pub(crate) fn from_status(status: Status, out: *mut T) -> Result<Self, Error> {
        check(status).map(|()| Self::new(out))
    }

    pub(crate) fn ptr(&self) -> *mut T {
        self.0.as_ptr()
    }

    /// Gives up ownership, for a service that frees the handle itself.
    pub(crate) fn into_ptr(self) -> *mut T {
        core::mem::ManuallyDrop::new(self).0.as_ptr()
    }
}

impl<T: Opaque> Drop for Handle<T> {
    fn drop(&mut self) {
        // SAFETY: the handle is live, and this is its last use.
        unsafe { T::free(self.0.as_ptr()) }
    }
}

// SAFETY: every value the module holds behind a handle is `Send` and `Sync`
// in rind: plain data, used through `&` for shared calls.
unsafe impl<T: Opaque> Send for Handle<T> {}
// SAFETY: as for `Send`.
unsafe impl<T: Opaque> Sync for Handle<T> {}

/// Declares opaque handle types, and the extern functions that free them,
/// in the calling module.
macro_rules! opaque {
    ($($name:ident => $free:ident),* $(,)?) => {
        $(
            #[repr(C)]
            pub(crate) struct $name {
                _private: [u8; 0],
                _not_send: core::marker::PhantomData<*mut u8>,
            }

            impl $crate::ffi::Opaque for $name {
                unsafe fn free(handle: *mut Self) {
                    // SAFETY: the caller's contract.
                    unsafe { $free(handle) }
                }
            }
        )*

        unsafe extern "C" {
            $(fn $free(handle: *mut $name);)*
        }
    };
}
pub(crate) use opaque;

opaque! {
    Encoded => rind_fips_encoded_free,
}

unsafe extern "C" {
    pub(crate) fn rind_fips_version(len: *mut usize) -> *const u8;
    pub(crate) fn rind_fips_self_test();
    pub(crate) fn rind_fips_error_message(status: Status, out: *mut u8, cap: usize) -> usize;
    pub(crate) fn rind_fips_rand_fill(out: *mut u8, len: usize) -> Status;
    pub(crate) fn rind_fips_cpu_check(len: *mut usize) -> *const u8;
    pub(crate) fn rind_fips_has_aes_hardware() -> bool;
    pub(crate) fn rind_fips_constant_time_verify(
        a: *const u8,
        a_len: usize,
        b: *const u8,
        b_len: usize,
    ) -> Status;
    pub(crate) fn rind_fips_encoded_bytes(encoded: *const Encoded, len: *mut usize) -> *const u8;
}
