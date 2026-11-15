// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! The provider itself: its entry point, its parameters, the algorithms it
//! registers, and the errors it raises on OpenSSL's queue.

use core::ffi::{CStr, c_int, c_void};
use std::ffi::CString;
use std::sync::Arc;

use crate::ffi::{
    Algorithm, CORE_NEW_ERROR, CORE_VSET_ERROR, CoreHandle, CoreNewError, CoreVsetError, Dispatch,
    INTEGER, Item, OP_KEYEXCH, OP_KEYMGMT, OP_SIGNATURE, PROVIDER_GET_PARAMS,
    PROVIDER_GET_REASON_STRINGS, PROVIDER_GETTABLE_PARAMS, PROVIDER_QUERY_OPERATION,
    PROVIDER_TEARDOWN, Param, ProviderGetParams, ProviderGetReasonStrings, ProviderGettableParams,
    ProviderQueryOperation, ProviderTeardown, UTF8_PTR, entry,
};
use crate::params::ParamsMut;
use crate::{ed25519, x25519};

/// One activation of the provider, in one OpenSSL library context: the
/// core's handle and the functions that raise errors through it.
pub(crate) struct Provider {
    handle: *const CoreHandle,
    new_error: CoreNewError,
    vset_error: CoreVsetError,
}

// SAFETY: the core's handle and functions serve every thread for as long as
// the provider is active, which every object holding a `Provider` keeps it;
// the error queue they write is the calling thread's.
unsafe impl Send for Provider {}
// SAFETY: as for `Send`; a `Provider` is never written after it is made.
unsafe impl Sync for Provider {}

impl Provider {
    /// Raises `reason` on the calling thread's error queue, with `detail`.
    pub(crate) fn raise(&self, reason: Reason, detail: &str) {
        raise(self.handle, self.new_error, self.vset_error, reason, detail);
    }

    /// The provider whose context OpenSSL passes, which the caller now holds
    /// a reference to as well.
    ///
    /// # Safety
    ///
    /// `provctx` is the context [`OSSL_provider_init`] returned, which
    /// OpenSSL has not torn down.
    pub(crate) unsafe fn from_context(provctx: *mut c_void) -> Arc<Self> {
        let provider = provctx.cast_const().cast::<Self>();
        // SAFETY: the context is a live `Arc<Provider>`, per the caller.
        unsafe {
            Arc::increment_strong_count(provider);
            Arc::from_raw(provider)
        }
    }

    /// 1 on success; otherwise 0, having raised the failure's error if it
    /// has one.
    pub(crate) fn status(&self, result: Result<(), Failure>) -> c_int {
        match result {
            Ok(()) => 1,
            Err(Failure::Raise(reason, detail)) => {
                self.raise(reason, &detail);
                0
            }
            Err(Failure::Quiet) => 0,
        }
    }
}

/// Why a call failed.
pub(crate) enum Failure {
    /// An error to raise on OpenSSL's queue, with its detail.
    Raise(Reason, String),
    /// A failure OpenSSL's default provider reports without an error, such
    /// as a signature that does not verify.
    Quiet,
}

impl Failure {
    pub(crate) fn invalid(detail: &str) -> Self {
        Self::Raise(Reason::InvalidArgument, detail.into())
    }

    pub(crate) fn unsupported(detail: &str) -> Self {
        Self::Raise(Reason::Unsupported, detail.into())
    }
}

impl From<rind::Error> for Failure {
    fn from(error: rind::Error) -> Self {
        let reason = match error {
            rind::Error::KeyRejected(_) => Reason::KeyRejected,
            rind::Error::Unsupported => Reason::Unsupported,
            _ => Reason::Failed,
        };
        Self::Raise(reason, error.to_string())
    }
}

/// The reasons this provider raises errors for, which OpenSSL prints with
/// [`REASONS`]'s strings.
#[derive(Clone, Copy)]
#[repr(u32)]
pub(crate) enum Reason {
    /// rind refuses a key, such as one whose halves do not match.
    KeyRejected = 1,
    /// rind cannot back what the caller asks, such as Ed25519ph.
    Unsupported = 2,
    /// An argument OpenSSL's default provider refuses too.
    InvalidArgument = 3,
    /// rind failed, as when the system's random source does.
    Failed = 4,
}

static REASONS: [Item; 5] = [
    reason(Reason::KeyRejected, c"key rejected"),
    reason(Reason::Unsupported, c"unsupported by rind"),
    reason(Reason::InvalidArgument, c"invalid argument"),
    reason(Reason::Failed, c"operation failed"),
    Item {
        id: 0,
        ptr: core::ptr::null(),
    },
];

const fn reason(reason: Reason, string: &'static CStr) -> Item {
    Item {
        id: reason as u32,
        ptr: string.as_ptr().cast(),
    }
}

/// Raises `reason` with `detail` through the core, as `ERR_raise_data` would.
fn raise(
    handle: *const CoreHandle,
    new_error: CoreNewError,
    vset_error: CoreVsetError,
    reason: Reason,
    detail: &str,
) {
    // OpenSSL formats the detail as printf does: doubling each `%` leaves no
    // conversion, so it reads none of the arguments.
    let format =
        CString::new(detail.replace('%', "%%").replace('\0', "")).expect("every NUL was removed");
    // A zeroed stand-in for the `va_list` the format never reads, larger and
    // more aligned than any target's.
    let mut arguments = [0u64; 4];
    // SAFETY: the core's functions take its handle, and `vset_error` reads
    // the format, a C string, and none of the arguments.
    unsafe {
        new_error(handle);
        vset_error(
            handle,
            reason as u32,
            format.as_ptr(),
            arguments.as_mut_ptr().cast(),
        );
    }
}

/// Starts the provider.
///
/// # Safety
///
/// As for [`OSSL_provider_init`].
pub(crate) unsafe fn init(
    handle: *const CoreHandle,
    core: *const Dispatch,
    out: *mut *const Dispatch,
    provctx: *mut *mut c_void,
) -> c_int {
    let (mut new_error, mut vset_error) = (None, None);
    let mut at = core;
    while !at.is_null() {
        // SAFETY: the core's table runs to an entry with id 0.
        let entry = unsafe { &*at };
        if entry.id == 0 {
            break;
        }
        // SAFETY: the core gives each function with the signature its id
        // names.
        unsafe {
            match (entry.id, entry.function) {
                (CORE_NEW_ERROR, Some(function)) => {
                    new_error =
                        Some(core::mem::transmute::<unsafe extern "C" fn(), CoreNewError>(function))
                }
                (CORE_VSET_ERROR, Some(function)) => {
                    vset_error = Some(
                        core::mem::transmute::<unsafe extern "C" fn(), CoreVsetError>(function),
                    )
                }
                _ => {}
            }
        }
        // SAFETY: the table has not ended.
        at = unsafe { at.add(1) };
    }
    // Every OpenSSL 3 core offers both.
    let (Some(new_error), Some(vset_error)) = (new_error, vset_error) else {
        return 0;
    };
    let provider = Arc::new(Provider {
        handle,
        new_error,
        vset_error,
    });
    // SAFETY: the core passes both outputs to write.
    unsafe {
        *out = FUNCTIONS.as_ptr();
        *provctx = Arc::into_raw(provider).cast_mut().cast();
    }
    1
}

static FUNCTIONS: [Dispatch; 6] = [
    entry!(PROVIDER_TEARDOWN, teardown, ProviderTeardown),
    entry!(
        PROVIDER_GETTABLE_PARAMS,
        gettable_params,
        ProviderGettableParams
    ),
    entry!(PROVIDER_GET_PARAMS, get_params, ProviderGetParams),
    entry!(
        PROVIDER_QUERY_OPERATION,
        query_operation,
        ProviderQueryOperation
    ),
    entry!(
        PROVIDER_GET_REASON_STRINGS,
        reason_strings,
        ProviderGetReasonStrings
    ),
    Dispatch::END,
];

unsafe extern "C" fn teardown(provctx: *mut c_void) {
    if !provctx.is_null() {
        // SAFETY: the context is the `Arc` init made, which OpenSSL now
        // gives back.
        drop(unsafe { Arc::from_raw(provctx.cast_const().cast::<Provider>()) });
    }
}

const VERSION: &CStr =
    match CStr::from_bytes_with_nul(concat!(env!("CARGO_PKG_VERSION"), "\0").as_bytes()) {
        Ok(version) => version,
        Err(_) => panic!("the version holds no NUL"),
    };

static GETTABLE_PARAMS: [Param; 5] = [
    Param::describe(Some(c"name"), UTF8_PTR, 0),
    Param::describe(Some(c"version"), UTF8_PTR, 0),
    Param::describe(Some(c"buildinfo"), UTF8_PTR, 0),
    Param::describe(Some(c"status"), INTEGER, size_of::<c_int>()),
    Param::END,
];

unsafe extern "C" fn gettable_params(_provctx: *mut c_void) -> *const Param {
    GETTABLE_PARAMS.as_ptr()
}

unsafe extern "C" fn get_params(_provctx: *mut c_void, params: *mut Param) -> c_int {
    // SAFETY: OpenSSL passes a writable array.
    let mut params = unsafe { ParamsMut::new(params) };
    for (name, value) in [
        (c"name", c"rind"),
        (c"version", VERSION),
        (c"buildinfo", VERSION),
    ] {
        if let Some(param) = params.find(name)
            && !param.set_utf8_ptr(value)
        {
            return 0;
        }
    }
    if let Some(param) = params.find(c"status")
        && !param.set_int(1)
    {
        return 0;
    }
    1
}

static KEYMGMT: [Algorithm; 3] = [
    Algorithm::new(c"X25519:1.3.101.110", &x25519::KEYMGMT),
    Algorithm::new(c"ED25519:1.3.101.112", &ed25519::KEYMGMT),
    Algorithm::END,
];

static KEYEXCH: [Algorithm; 2] = [
    Algorithm::new(c"X25519:1.3.101.110", &x25519::KEYEXCH),
    Algorithm::END,
];

static SIGNATURE: [Algorithm; 2] = [
    Algorithm::new(c"ED25519:1.3.101.112", &ed25519::SIGNATURE),
    Algorithm::END,
];

unsafe extern "C" fn query_operation(
    _provctx: *mut c_void,
    operation: c_int,
    no_store: *mut c_int,
) -> *const Algorithm {
    if !no_store.is_null() {
        // SAFETY: OpenSSL passes a flag to write. The lists never change, so
        // it may cache what they hold.
        unsafe { *no_store = 0 };
    }
    match operation {
        OP_KEYMGMT => KEYMGMT.as_ptr(),
        OP_KEYEXCH => KEYEXCH.as_ptr(),
        OP_SIGNATURE => SIGNATURE.as_ptr(),
        _ => core::ptr::null(),
    }
}

unsafe extern "C" fn reason_strings(_provctx: *mut c_void) -> *const Item {
    REASONS.as_ptr()
}
