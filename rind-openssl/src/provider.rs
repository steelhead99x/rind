// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! The provider itself: its entry point, its parameters, the algorithms it
//! registers, and the errors it raises on OpenSSL's queue.

use core::ffi::{CStr, c_char, c_int, c_uint, c_void};
use std::ffi::CString;
use std::sync::Arc;

use crate::ffi::{
    Algorithm, CORE_GET_PARAMS, CORE_NEW_ERROR, CORE_VSET_ERROR, Callback, CoreGetParams,
    CoreHandle, CoreNewError, CoreVsetError, Dispatch, INTEGER, Item, OP_KEYEXCH, OP_KEYMGMT,
    OP_SIGNATURE, PROVIDER_GET_CAPABILITIES, PROVIDER_GET_PARAMS, PROVIDER_GET_REASON_STRINGS,
    PROVIDER_GETTABLE_PARAMS, PROVIDER_QUERY_OPERATION, PROVIDER_TEARDOWN, Param,
    ProviderGetCapabilities, ProviderGetParams, ProviderGetReasonStrings, ProviderGettableParams,
    ProviderQueryOperation, ProviderTeardown, UNMODIFIED, UTF8_PTR, entry,
};
use crate::params::ParamsMut;
use crate::{ec, ecdh, ecdsa, ed25519, x25519};

/// One activation of the provider, in one OpenSSL library context: the
/// core's handle and the functions that raise errors through it.
pub(crate) struct Provider {
    handle: *const CoreHandle,
    new_error: CoreNewError,
    vset_error: CoreVsetError,
    /// Whether the configuration section sets `ec = 1`, which registers the
    /// `EC` key type, ECDSA, and ECDH.
    ec: bool,
}

// SAFETY: the core's handle and functions serve every thread for as long as
// the provider is active, which every object holding a `Provider` keeps it;
// the error queue they write is the calling thread's.
unsafe impl Send for Provider {}
// SAFETY: as for `Send`; a `Provider` is never written after it is made.
unsafe impl Sync for Provider {}

#[cfg(test)]
impl Provider {
    /// A provider with no core behind it, for unit tests that raise nothing.
    pub(crate) fn for_tests() -> Arc<Self> {
        unsafe extern "C" fn new_error(_: *const CoreHandle) {}
        unsafe extern "C" fn vset_error(
            _: *const CoreHandle,
            _: u32,
            _: *const c_char,
            _: *mut c_void,
        ) {
        }
        Arc::new(Self {
            handle: core::ptr::null(),
            new_error,
            vset_error,
            ec: true,
        })
    }
}

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
    let (mut new_error, mut vset_error, mut get_params) = (None, None, None);
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
                (CORE_GET_PARAMS, Some(function)) => {
                    get_params = Some(
                        core::mem::transmute::<unsafe extern "C" fn(), CoreGetParams>(function),
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
    let ec = match config_flag(handle, get_params, c"ec") {
        Ok(ec) => ec,
        Err(detail) => {
            raise(
                handle,
                new_error,
                vset_error,
                Reason::InvalidArgument,
                &detail,
            );
            return 0;
        }
    };
    let provider = Arc::new(Provider {
        handle,
        new_error,
        vset_error,
        ec,
    });
    // SAFETY: the core passes both outputs to write.
    unsafe {
        *out = FUNCTIONS.as_ptr();
        *provctx = Arc::into_raw(provider).cast_mut().cast();
    }
    1
}

/// The flag `name` the provider's configuration section sets: `1` for on, `0`
/// or no such line for off, and anything else an error, since a misspelled
/// switch left off would read as a working one.
///
/// OpenSSL hands the section's lines it does not use itself to the provider
/// through the core, as strings.
fn config_flag(
    handle: *const CoreHandle,
    get_params: Option<CoreGetParams>,
    name: &CStr,
) -> Result<bool, String> {
    let Some(get_params) = get_params else {
        return Ok(false);
    };
    let mut value: *const c_char = core::ptr::null();
    let mut params = [
        Param {
            key: name.as_ptr(),
            data_type: UTF8_PTR,
            data: (&raw mut value).cast(),
            data_size: 0,
            return_size: UNMODIFIED,
        },
        Param::END,
    ];
    // SAFETY: the core's function takes its handle and a terminated array,
    // and writes the pointer to the section's own string.
    if unsafe { get_params(handle, params.as_mut_ptr()) } != 1 {
        return Err(format!("OpenSSL cannot read the configuration's {name:?}"));
    }
    if params[0].return_size == UNMODIFIED || value.is_null() {
        return Ok(false);
    }
    // SAFETY: the core points at a C string that lives as long as the
    // provider's configuration.
    match unsafe { CStr::from_ptr(value) }.to_bytes() {
        b"1" => Ok(true),
        b"0" => Ok(false),
        other => Err(format!(
            "{name:?} must be 0 or 1 in the rind section, not {:?}",
            String::from_utf8_lossy(other)
        )),
    }
}

static FUNCTIONS: [Dispatch; 7] = [
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
        PROVIDER_GET_CAPABILITIES,
        get_capabilities,
        ProviderGetCapabilities
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

// The same lists with the NIST curves, for `ec = 1`.
static KEYMGMT_EC: [Algorithm; 4] = [
    Algorithm::new(c"X25519:1.3.101.110", &x25519::KEYMGMT),
    Algorithm::new(c"ED25519:1.3.101.112", &ed25519::KEYMGMT),
    Algorithm::new(c"EC:id-ecPublicKey:1.2.840.10045.2.1", &ec::KEYMGMT),
    Algorithm::END,
];

static KEYEXCH_EC: [Algorithm; 3] = [
    Algorithm::new(c"X25519:1.3.101.110", &x25519::KEYEXCH),
    Algorithm::new(c"ECDH", &ecdh::KEYEXCH),
    Algorithm::END,
];

static SIGNATURE_EC: [Algorithm; 3] = [
    Algorithm::new(c"ED25519:1.3.101.112", &ed25519::SIGNATURE),
    Algorithm::new(c"ECDSA", &ecdsa::SIGNATURE),
    Algorithm::END,
];

unsafe extern "C" fn query_operation(
    provctx: *mut c_void,
    operation: c_int,
    no_store: *mut c_int,
) -> *const Algorithm {
    if !no_store.is_null() {
        // SAFETY: OpenSSL passes a flag to write. The lists never change
        // for a provider context, whose `ec` is fixed at its start, so
        // OpenSSL may cache what they hold.
        unsafe { *no_store = 0 };
    }
    // SAFETY: OpenSSL passes the context `init` made, which it has not torn
    // down.
    let ec = unsafe { provctx.cast_const().cast::<Provider>().as_ref() }.is_some_and(|p| p.ec);
    match (operation, ec) {
        (OP_KEYMGMT, false) => KEYMGMT.as_ptr(),
        (OP_KEYEXCH, false) => KEYEXCH.as_ptr(),
        (OP_SIGNATURE, false) => SIGNATURE.as_ptr(),
        (OP_KEYMGMT, true) => KEYMGMT_EC.as_ptr(),
        (OP_KEYEXCH, true) => KEYEXCH_EC.as_ptr(),
        (OP_SIGNATURE, true) => SIGNATURE_EC.as_ptr(),
        _ => core::ptr::null(),
    }
}

// The X25519 TLS group, as OpenSSL's default provider describes it. Through
// OpenSSL 3.4 a group is offered only when the provider that lists it also
// backs its algorithm, so with rind preferred, as in the README's
// configuration, the default provider's X25519 group is dropped and TLS has
// none unless rind lists it.
static GROUP_ID: c_uint = 29;
static GROUP_SECURITY_BITS: c_uint = 128;
/// `TLS1_VERSION`.
static GROUP_MIN_TLS: c_int = 0x0301;
/// No maximum.
static GROUP_NO_MAX: c_int = 0;
/// `DTLS1_VERSION`.
static GROUP_MIN_DTLS: c_int = 0xFEFF;

static TLS_GROUP: [Param; 10] = [
    Param::text(c"tls-group-name", c"x25519"),
    Param::text(c"tls-group-name-internal", c"X25519"),
    Param::text(c"tls-group-alg", c"X25519"),
    Param::unsigned(c"tls-group-id", &GROUP_ID),
    Param::unsigned(c"tls-group-sec-bits", &GROUP_SECURITY_BITS),
    Param::signed(c"tls-min-tls", &GROUP_MIN_TLS),
    Param::signed(c"tls-max-tls", &GROUP_NO_MAX),
    Param::signed(c"tls-min-dtls", &GROUP_MIN_DTLS),
    Param::signed(c"tls-max-dtls", &GROUP_NO_MAX),
    Param::END,
];

/// The NIST curves' TLS groups, as OpenSSL's default provider describes them,
/// which `ec = 1` lists beside X25519's for the reason given there.
static P256_ID: c_uint = 23;
static P384_ID: c_uint = 24;
static P521_ID: c_uint = 25;
static P256_BITS: c_uint = 128;
static P384_BITS: c_uint = 192;
static P521_BITS: c_uint = 256;

macro_rules! ec_group {
    ($name:expr, $internal:expr, $id:expr, $bits:expr) => {
        [
            Param::text(c"tls-group-name", $name),
            Param::text(c"tls-group-name-internal", $internal),
            Param::text(c"tls-group-alg", c"EC"),
            Param::unsigned(c"tls-group-id", &$id),
            Param::unsigned(c"tls-group-sec-bits", &$bits),
            Param::signed(c"tls-min-tls", &GROUP_MIN_TLS),
            Param::signed(c"tls-max-tls", &GROUP_NO_MAX),
            Param::signed(c"tls-min-dtls", &GROUP_MIN_DTLS),
            Param::signed(c"tls-max-dtls", &GROUP_NO_MAX),
            Param::END,
        ]
    };
}

static EC_GROUPS: [[Param; 10]; 3] = [
    ec_group!(c"secp256r1", c"prime256v1", P256_ID, P256_BITS),
    ec_group!(c"secp384r1", c"secp384r1", P384_ID, P384_BITS),
    ec_group!(c"secp521r1", c"secp521r1", P521_ID, P521_BITS),
];

unsafe extern "C" fn get_capabilities(
    provctx: *mut c_void,
    capability: *const c_char,
    callback: Callback,
    arg: *mut c_void,
) -> c_int {
    // SAFETY: OpenSSL passes a C string.
    if unsafe { CStr::from_ptr(capability) } != c"TLS-GROUP" {
        // Nothing to give for any other, which is how a provider without
        // this function answers.
        return 1;
    }
    // SAFETY: the callback is OpenSSL's, and takes the parameters it is
    // given to read for the call.
    if unsafe { callback(TLS_GROUP.as_ptr(), arg) } != 1 {
        return 0;
    }
    // SAFETY: OpenSSL passes the context `init` made, which it has not torn
    // down.
    if !unsafe { provctx.cast_const().cast::<Provider>().as_ref() }.is_some_and(|p| p.ec) {
        return 1;
    }
    for group in &EC_GROUPS {
        // SAFETY: as above.
        if unsafe { callback(group.as_ptr(), arg) } != 1 {
            return 0;
        }
    }
    1
}

unsafe extern "C" fn reason_strings(_provctx: *mut c_void) -> *const Item {
    REASONS.as_ptr()
}
