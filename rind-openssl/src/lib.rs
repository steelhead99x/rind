// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! An OpenSSL 3 provider backed by rind, for the algorithms where rind is
//! faster than OpenSSL's default provider: X25519 and Ed25519.
//!
//! OpenSSL loads the shared library this crate builds through
//! `openssl.cnf`, as the README shows. Its one export is
//! [`OSSL_provider_init`]; everything else is OpenSSL's provider ABI.
#![allow(clippy::missing_safety_doc)]
#![warn(clippy::undocumented_unsafe_blocks, unreachable_pub)]

use core::ffi::{c_int, c_void};

mod ed25519;
mod ffi;
mod keymgmt;
mod params;
mod provider;
mod x25519;

/// The entry point OpenSSL calls when it loads the provider.
///
/// # Safety
///
/// OpenSSL calls it with its core's handle and dispatch table, and two
/// outputs to write: the provider's table and its context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn OSSL_provider_init(
    handle: *const c_void,
    core: *const c_void,
    out: *mut *const c_void,
    provctx: *mut *mut c_void,
) -> c_int {
    // SAFETY: per the caller; the pointers are OpenSSL's, cast to its types.
    unsafe { provider::init(handle.cast(), core.cast(), out.cast(), provctx) }
}
