// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! The parts of OpenSSL's provider ABI this provider uses, from
//! `openssl/core.h`, `core_dispatch.h`, and `core_names.h`.
//!
//! The ABI is stable across OpenSSL 3, and this provider links no OpenSSL
//! library: the core hands it every function it calls.

use core::ffi::{CStr, c_char, c_int, c_uint, c_void};

/// `OSSL_CORE_HANDLE`: the core's handle to this provider, opaque to it.
#[repr(C)]
pub(crate) struct CoreHandle {
    _opaque: [u8; 0],
}

/// `OSSL_DISPATCH`: one function of a table, named by its id.
#[repr(C)]
pub(crate) struct Dispatch {
    pub(crate) id: c_int,
    pub(crate) function: Option<unsafe extern "C" fn()>,
}

impl Dispatch {
    /// `OSSL_DISPATCH_END`.
    pub(crate) const END: Self = Self {
        id: 0,
        function: None,
    };
}

/// `OSSL_ALGORITHM`: an implementation, its names, and its properties.
#[repr(C)]
pub(crate) struct Algorithm {
    pub(crate) names: *const c_char,
    pub(crate) properties: *const c_char,
    pub(crate) implementation: *const Dispatch,
    pub(crate) description: *const c_char,
}

impl Algorithm {
    /// The `OSSL_ALGORITHM` that ends a list.
    pub(crate) const END: Self = Self {
        names: core::ptr::null(),
        properties: core::ptr::null(),
        implementation: core::ptr::null(),
        description: core::ptr::null(),
    };

    /// `implementation`, under `names`, as rind's.
    pub(crate) const fn new(names: &'static CStr, implementation: &'static [Dispatch]) -> Self {
        Self {
            names: names.as_ptr(),
            properties: c"provider=rind".as_ptr(),
            implementation: implementation.as_ptr(),
            description: core::ptr::null(),
        }
    }
}

/// `OSSL_PARAM`: a named, typed value, one of an array ending at a null key.
#[repr(C)]
pub(crate) struct Param {
    pub(crate) key: *const c_char,
    pub(crate) data_type: c_uint,
    pub(crate) data: *mut c_void,
    pub(crate) data_size: usize,
    pub(crate) return_size: usize,
}

impl Param {
    /// `OSSL_PARAM_END`.
    pub(crate) const END: Self = Self::describe(None, 0, 0);

    /// A parameter that describes one a function takes or gives, as the
    /// gettable and settable lists do: its name, type, and size, with no
    /// data.
    pub(crate) const fn describe(
        key: Option<&'static CStr>,
        data_type: c_uint,
        size: usize,
    ) -> Self {
        Self {
            key: match key {
                Some(key) => key.as_ptr(),
                None => core::ptr::null(),
            },
            data_type,
            data: core::ptr::null_mut(),
            data_size: size,
            return_size: UNMODIFIED,
        }
    }
}

/// `OSSL_ITEM`: a number and a pointer, here a reason code and its string.
#[repr(C)]
pub(crate) struct Item {
    pub(crate) id: c_uint,
    pub(crate) ptr: *const c_void,
}

// SAFETY: these hold only pointers to static data, and no one writes through
// a shared instance: OpenSSL treats the tables and lists as read-only.
unsafe impl Sync for Dispatch {}
// SAFETY: as for `Dispatch`.
unsafe impl Sync for Algorithm {}
// SAFETY: as for `Dispatch`; only the static lists of parameter descriptions
// are shared.
unsafe impl Sync for Param {}
// SAFETY: as for `Dispatch`.
unsafe impl Sync for Item {}

/// `OSSL_PARAM_UNMODIFIED`: the `return_size` of a parameter no one set.
pub(crate) const UNMODIFIED: usize = usize::MAX;

// `OSSL_PARAM` data types.
pub(crate) const INTEGER: c_uint = 1;
pub(crate) const UNSIGNED_INTEGER: c_uint = 2;
pub(crate) const REAL: c_uint = 3;
pub(crate) const UTF8_STRING: c_uint = 4;
pub(crate) const OCTET_STRING: c_uint = 5;
pub(crate) const UTF8_PTR: c_uint = 6;

// Operations.
pub(crate) const OP_KEYMGMT: c_int = 10;
pub(crate) const OP_KEYEXCH: c_int = 11;
pub(crate) const OP_SIGNATURE: c_int = 12;

// Key selections.
pub(crate) const SELECT_PRIVATE_KEY: c_int = 0x01;
pub(crate) const SELECT_PUBLIC_KEY: c_int = 0x02;
pub(crate) const SELECT_KEYPAIR: c_int = SELECT_PRIVATE_KEY | SELECT_PUBLIC_KEY;

// The core's functions.
pub(crate) const CORE_NEW_ERROR: c_int = 5;
pub(crate) const CORE_VSET_ERROR: c_int = 7;

// The provider's functions.
pub(crate) const PROVIDER_TEARDOWN: c_int = 1024;
pub(crate) const PROVIDER_GETTABLE_PARAMS: c_int = 1025;
pub(crate) const PROVIDER_GET_PARAMS: c_int = 1026;
pub(crate) const PROVIDER_QUERY_OPERATION: c_int = 1027;
pub(crate) const PROVIDER_GET_REASON_STRINGS: c_int = 1029;

// Key management.
pub(crate) const KEYMGMT_NEW: c_int = 1;
pub(crate) const KEYMGMT_GEN_INIT: c_int = 2;
pub(crate) const KEYMGMT_GEN_SET_PARAMS: c_int = 4;
pub(crate) const KEYMGMT_GEN_SETTABLE_PARAMS: c_int = 5;
pub(crate) const KEYMGMT_GEN: c_int = 6;
pub(crate) const KEYMGMT_GEN_CLEANUP: c_int = 7;
pub(crate) const KEYMGMT_FREE: c_int = 10;
pub(crate) const KEYMGMT_GET_PARAMS: c_int = 11;
pub(crate) const KEYMGMT_GETTABLE_PARAMS: c_int = 12;
pub(crate) const KEYMGMT_SET_PARAMS: c_int = 13;
pub(crate) const KEYMGMT_SETTABLE_PARAMS: c_int = 14;
pub(crate) const KEYMGMT_HAS: c_int = 21;
pub(crate) const KEYMGMT_VALIDATE: c_int = 22;
pub(crate) const KEYMGMT_MATCH: c_int = 23;
pub(crate) const KEYMGMT_IMPORT: c_int = 40;
pub(crate) const KEYMGMT_IMPORT_TYPES: c_int = 41;
pub(crate) const KEYMGMT_EXPORT: c_int = 42;
pub(crate) const KEYMGMT_EXPORT_TYPES: c_int = 43;
pub(crate) const KEYMGMT_DUP: c_int = 44;

// Key exchange.
pub(crate) const KEYEXCH_NEWCTX: c_int = 1;
pub(crate) const KEYEXCH_INIT: c_int = 2;
pub(crate) const KEYEXCH_DERIVE: c_int = 3;
pub(crate) const KEYEXCH_SET_PEER: c_int = 4;
pub(crate) const KEYEXCH_FREECTX: c_int = 5;
pub(crate) const KEYEXCH_DUPCTX: c_int = 6;
pub(crate) const KEYEXCH_GET_CTX_PARAMS: c_int = 9;
pub(crate) const KEYEXCH_GETTABLE_CTX_PARAMS: c_int = 10;

// Signatures.
pub(crate) const SIGNATURE_NEWCTX: c_int = 1;
pub(crate) const SIGNATURE_SIGN_INIT: c_int = 2;
pub(crate) const SIGNATURE_SIGN: c_int = 3;
pub(crate) const SIGNATURE_VERIFY_INIT: c_int = 4;
pub(crate) const SIGNATURE_VERIFY: c_int = 5;
pub(crate) const SIGNATURE_DIGEST_SIGN_INIT: c_int = 8;
pub(crate) const SIGNATURE_DIGEST_SIGN: c_int = 11;
pub(crate) const SIGNATURE_DIGEST_VERIFY_INIT: c_int = 12;
pub(crate) const SIGNATURE_DIGEST_VERIFY: c_int = 15;
pub(crate) const SIGNATURE_FREECTX: c_int = 16;
pub(crate) const SIGNATURE_DUPCTX: c_int = 17;
pub(crate) const SIGNATURE_GET_CTX_PARAMS: c_int = 18;
pub(crate) const SIGNATURE_GETTABLE_CTX_PARAMS: c_int = 19;
pub(crate) const SIGNATURE_SET_CTX_PARAMS: c_int = 20;
pub(crate) const SIGNATURE_SETTABLE_CTX_PARAMS: c_int = 21;
pub(crate) const SIGNATURE_QUERY_KEY_TYPES: c_int = 26;
pub(crate) const SIGNATURE_SIGN_MESSAGE_INIT: c_int = 27;
pub(crate) const SIGNATURE_VERIFY_MESSAGE_INIT: c_int = 30;

/// `OSSL_CALLBACK`: a function the core passes, called with parameters.
pub(crate) type Callback = unsafe extern "C" fn(params: *const Param, arg: *mut c_void) -> c_int;

// The signature of each function this provider gives or takes, by id, as
// `core_dispatch.h` declares it. `entry!` casts a function through its alias,
// so one whose signature differs fails to compile.
pub(crate) type CoreNewError = unsafe extern "C" fn(*const CoreHandle);
/// `core_vset_error`, whose last parameter is a `va_list`. Every target's C
/// ABI passes one as a single pointer-sized value: a pointer, a pointer to the
/// caller's copy of a larger structure (AArch64), or a one-pointer structure
/// in a register (32-bit Arm).
pub(crate) type CoreVsetError =
    unsafe extern "C" fn(*const CoreHandle, u32, *const c_char, *mut c_void);

pub(crate) type ProviderTeardown = unsafe extern "C" fn(*mut c_void);
pub(crate) type ProviderGettableParams = unsafe extern "C" fn(*mut c_void) -> *const Param;
pub(crate) type ProviderGetParams = unsafe extern "C" fn(*mut c_void, *mut Param) -> c_int;
pub(crate) type ProviderQueryOperation =
    unsafe extern "C" fn(*mut c_void, c_int, *mut c_int) -> *const Algorithm;
pub(crate) type ProviderGetReasonStrings = unsafe extern "C" fn(*mut c_void) -> *const Item;

pub(crate) type KeymgmtNew = unsafe extern "C" fn(*mut c_void) -> *mut c_void;
pub(crate) type KeymgmtGenInit =
    unsafe extern "C" fn(*mut c_void, c_int, *const Param) -> *mut c_void;
pub(crate) type KeymgmtGenSetParams = unsafe extern "C" fn(*mut c_void, *const Param) -> c_int;
pub(crate) type KeymgmtGenSettableParams =
    unsafe extern "C" fn(*mut c_void, *mut c_void) -> *const Param;
pub(crate) type KeymgmtGen =
    unsafe extern "C" fn(*mut c_void, Option<Callback>, *mut c_void) -> *mut c_void;
pub(crate) type KeymgmtGenCleanup = unsafe extern "C" fn(*mut c_void);
pub(crate) type KeymgmtFree = unsafe extern "C" fn(*mut c_void);
pub(crate) type KeymgmtGetParams = unsafe extern "C" fn(*mut c_void, *mut Param) -> c_int;
pub(crate) type KeymgmtGettableParams = unsafe extern "C" fn(*mut c_void) -> *const Param;
pub(crate) type KeymgmtSetParams = unsafe extern "C" fn(*mut c_void, *const Param) -> c_int;
pub(crate) type KeymgmtSettableParams = unsafe extern "C" fn(*mut c_void) -> *const Param;
pub(crate) type KeymgmtHas = unsafe extern "C" fn(*const c_void, c_int) -> c_int;
pub(crate) type KeymgmtValidate = unsafe extern "C" fn(*const c_void, c_int, c_int) -> c_int;
pub(crate) type KeymgmtMatch = unsafe extern "C" fn(*const c_void, *const c_void, c_int) -> c_int;
pub(crate) type KeymgmtImport = unsafe extern "C" fn(*mut c_void, c_int, *const Param) -> c_int;
pub(crate) type KeymgmtTypes = unsafe extern "C" fn(c_int) -> *const Param;
pub(crate) type KeymgmtExport =
    unsafe extern "C" fn(*mut c_void, c_int, Option<Callback>, *mut c_void) -> c_int;
pub(crate) type KeymgmtDup = unsafe extern "C" fn(*const c_void, c_int) -> *mut c_void;

pub(crate) type KeyexchNewctx = unsafe extern "C" fn(*mut c_void) -> *mut c_void;
pub(crate) type KeyexchInit = unsafe extern "C" fn(*mut c_void, *mut c_void, *const Param) -> c_int;
pub(crate) type KeyexchDerive =
    unsafe extern "C" fn(*mut c_void, *mut u8, *mut usize, usize) -> c_int;
pub(crate) type KeyexchSetPeer = unsafe extern "C" fn(*mut c_void, *mut c_void) -> c_int;

pub(crate) type SignatureNewctx = unsafe extern "C" fn(*mut c_void, *const c_char) -> *mut c_void;
pub(crate) type SignatureInit =
    unsafe extern "C" fn(*mut c_void, *mut c_void, *const Param) -> c_int;
pub(crate) type SignatureDigestInit =
    unsafe extern "C" fn(*mut c_void, *const c_char, *mut c_void, *const Param) -> c_int;
pub(crate) type SignatureSign =
    unsafe extern "C" fn(*mut c_void, *mut u8, *mut usize, usize, *const u8, usize) -> c_int;
pub(crate) type SignatureVerify =
    unsafe extern "C" fn(*mut c_void, *const u8, usize, *const u8, usize) -> c_int;
pub(crate) type SignatureQueryKeyTypes = unsafe extern "C" fn() -> *const *const c_char;

// What the key exchange and signature contexts share.
pub(crate) type CtxFree = unsafe extern "C" fn(*mut c_void);
pub(crate) type CtxDup = unsafe extern "C" fn(*mut c_void) -> *mut c_void;
pub(crate) type CtxGetParams = unsafe extern "C" fn(*mut c_void, *mut Param) -> c_int;
pub(crate) type CtxSetParams = unsafe extern "C" fn(*mut c_void, *const Param) -> c_int;
pub(crate) type CtxParamList = unsafe extern "C" fn(*mut c_void, *mut c_void) -> *const Param;

/// A dispatch table entry: `$function`, which must have the signature
/// `$signature` names, under `$id`.
macro_rules! entry {
    ($id:expr, $function:expr, $signature:ty) => {
        $crate::ffi::Dispatch {
            id: $id,
            // SAFETY: a function pointer round-trips through the generic one
            // OpenSSL's tables hold, and OpenSSL casts it back to the
            // signature `$id` names, which `$signature` is.
            function: Some(unsafe {
                core::mem::transmute::<$signature, unsafe extern "C" fn()>($function as $signature)
            }),
        }
    };
}

pub(crate) use entry;
