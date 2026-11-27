// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! ML-DSA key management and signatures, as OpenSSL 3.5's default provider
//! offers them under `ML-DSA-44`, `ML-DSA-65`, and `ML-DSA-87`.
//!
//! rind signs and verifies pure ML-DSA with the empty context, hedged with
//! fresh randomness, as TLS and X.509 use it, so it refuses a context
//! string, deterministic or test randomness, external mu, and the raw
//! message encoding, which OpenSSL also takes.

use core::ffi::{c_char, c_int, c_uint, c_void};
use core::marker::PhantomData;
use core::slice;
use std::sync::Arc;

use rind::ml_dsa::{KeyPair, MlDsa44, MlDsa65, MlDsa87, ParameterSet, PublicKey};
use zeroize::Zeroizing;

use crate::ffi::{
    Callback, CtxDup, CtxFree, CtxGetParams, CtxParamList, CtxSetParams, Dispatch, INTEGER,
    OCTET_STRING, Param, SIGNATURE_DIGEST_SIGN, SIGNATURE_DIGEST_SIGN_INIT,
    SIGNATURE_DIGEST_VERIFY, SIGNATURE_DIGEST_VERIFY_INIT, SIGNATURE_DUPCTX, SIGNATURE_FREECTX,
    SIGNATURE_GET_CTX_PARAMS, SIGNATURE_GETTABLE_CTX_PARAMS, SIGNATURE_NEWCTX,
    SIGNATURE_SET_CTX_PARAMS, SIGNATURE_SETTABLE_CTX_PARAMS, SIGNATURE_SIGN,
    SIGNATURE_SIGN_MESSAGE_INIT, SIGNATURE_VERIFY, SIGNATURE_VERIFY_MESSAGE_INIT,
    SignatureDigestInit, SignatureInit, SignatureNewctx, SignatureSign, SignatureVerify,
    UNSIGNED_INTEGER, entry,
};
use crate::params::{Params, ParamsMut};
use crate::pq_keymgmt::{self, Key, KeyData, Scheme, Secret};
use crate::provider::{Failure, Provider};

/// The longest context string FIPS 204 allows.
const MAX_CONTEXT_LEN: usize = 255;
/// The bytes of randomness OpenSSL takes as `test-entropy`.
const TEST_ENTROPY_LEN: usize = 32;

/// ML-DSA with parameter set `P`.
pub(crate) struct MlDsa<P>(PhantomData<P>);

/// What tells the parameter sets apart, beyond rind's own types.
pub(crate) trait Set: ParameterSet + Send + Sync + 'static {
    const NAME: &'static str;
    const TAG: u8;
    const PRIVATE_LEN: usize;
    const PUBLIC_LEN: usize;
    const SIGNATURE_LEN: usize;
    const SECURITY_BITS: c_int;
    /// The last byte of the parameter set's OID, under
    /// 2.16.840.1.101.3.4.3 (RFC 9881).
    const OID_ARC: u8;
}

impl Set for MlDsa44 {
    const NAME: &'static str = "ML-DSA-44";
    const TAG: u8 = 19;
    const PRIVATE_LEN: usize = 2560;
    const PUBLIC_LEN: usize = 1312;
    const SIGNATURE_LEN: usize = 2420;
    const SECURITY_BITS: c_int = 128;
    const OID_ARC: u8 = 17;
}

impl Set for MlDsa65 {
    const NAME: &'static str = "ML-DSA-65";
    const TAG: u8 = 20;
    const PRIVATE_LEN: usize = 4032;
    const PUBLIC_LEN: usize = 1952;
    const SIGNATURE_LEN: usize = 3309;
    const SECURITY_BITS: c_int = 192;
    const OID_ARC: u8 = 18;
}

impl Set for MlDsa87 {
    const NAME: &'static str = "ML-DSA-87";
    const TAG: u8 = 21;
    const PRIVATE_LEN: usize = 4896;
    const PUBLIC_LEN: usize = 2592;
    const SIGNATURE_LEN: usize = 4627;
    const SECURITY_BITS: c_int = 256;
    const OID_ARC: u8 = 19;
}

/// The DER `AlgorithmIdentifier` of parameter set `P`: its OID, with no
/// parameters (RFC 9881).
fn algorithm_id<P: Set>() -> [u8; 13] {
    [
        0x30,
        0x0b,
        0x06,
        0x09,
        0x60,
        0x86,
        0x48,
        0x01,
        0x65,
        0x03,
        0x04,
        0x03,
        P::OID_ARC,
    ]
}

/// DER's `tag`, the length of `content`'s parts, and the parts in turn,
/// in a buffer sized once, since growing one would free a copy of the key
/// unwiped.
fn der(tag: u8, content: &[&[u8]]) -> Secret {
    let len = content.iter().map(|part| part.len()).sum::<usize>();
    let mut out = Zeroizing::new(Vec::with_capacity(len + 4));
    out.push(tag);
    match len {
        0..0x80 => out.push(len as u8),
        0x80..0x100 => out.extend([0x81, len as u8]),
        _ => out.extend([0x82, (len >> 8) as u8, len as u8]),
    }
    for part in content {
        out.extend_from_slice(part);
    }
    out
}

/// PKCS#8 v1 holding `private`, an ML-DSA private key's DER (RFC 9881),
/// which is how rind loads an expanded key.
fn pkcs8<P: Set>(private: &[u8]) -> Secret {
    der(
        0x30,
        &[
            &[0x02, 0x01, 0x00],
            &algorithm_id::<P>(),
            &der(0x04, &[private]),
        ],
    )
}

impl<P: Set> Scheme for MlDsa<P> {
    type Private = KeyPair<P>;
    type Public = PublicKey<P>;

    const NAME: &'static str = P::NAME;
    const TAG: u8 = P::TAG;
    const SEED_LEN: usize = 32;
    const PRIVATE_LEN: usize = P::PRIVATE_LEN;
    const PUBLIC_LEN: usize = P::PUBLIC_LEN;
    const BITS: c_int = 8 * P::PUBLIC_LEN as c_int;
    const SECURITY_BITS: c_int = P::SECURITY_BITS;
    const MAX_SIZE: c_int = P::SIGNATURE_LEN as c_int;
    const ENCODED_PUBLIC: bool = false;
    const SEED_ONCE: bool = false;

    fn generate() -> Result<Self::Private, rind::Error> {
        KeyPair::generate()
    }

    fn from_seed(seed: &[u8]) -> Result<Self::Private, rind::Error> {
        KeyPair::from_seed(seed)
    }

    /// rind loads an expanded key, alone or beside its seed, only from
    /// PKCS#8, so this wraps it in the PKCS#8 that holds it so.
    fn load(seed: Option<&[u8]>, expanded: Option<&[u8]>) -> Result<Self::Private, Failure> {
        let private = match (seed, expanded) {
            (Some(seed), None) => return Ok(KeyPair::from_seed(seed)?),
            (None, Some(expanded)) => der(0x04, &[expanded]),
            (Some(seed), Some(expanded)) => {
                der(0x30, &[&der(0x04, &[seed]), &der(0x04, &[expanded])])
            }
            (None, None) => return Err(Failure::invalid("neither seed nor priv is given")),
        };
        Ok(KeyPair::from_pkcs8(&pkcs8::<P>(&private))?)
    }

    fn parse_public(bytes: &[u8]) -> Result<Self::Public, rind::Error> {
        PublicKey::new(bytes)
    }

    fn public_bytes(public: &Self::Public) -> &[u8] {
        public.as_ref()
    }

    fn public_of(private: &Self::Private) -> &[u8] {
        private.public_key().as_ref()
    }

    fn seed(private: &Self::Private) -> Option<Secret> {
        private
            .to_seed()
            .map(|seed| Zeroizing::new(seed.as_ref().to_vec()))
    }

    /// The expanded key of a key loaded from it alone, which has no seed to
    /// give instead: rind gives it only inside PKCS#8, which then ends in
    /// it. rind gives no expanded form of a key with a seed.
    fn expanded(private: &Self::Private) -> Option<Secret> {
        if private.has_seed() {
            return None;
        }
        let pkcs8 = private.to_pkcs8();
        let der = pkcs8.as_ref();
        let start = der.len().checked_sub(P::PRIVATE_LEN)?;
        let header = [
            0x04,
            0x82,
            (P::PRIVATE_LEN >> 8) as u8,
            P::PRIVATE_LEN as u8,
        ];
        (der.get(start.checked_sub(header.len())?..start)? == header)
            .then(|| Zeroizing::new(der[start..].to_vec()))
    }
}

pub(crate) static KEYMGMT_44: [Dispatch; 20] = pq_keymgmt::functions!(MlDsa<MlDsa44>);
pub(crate) static KEYMGMT_65: [Dispatch; 20] = pq_keymgmt::functions!(MlDsa<MlDsa65>);
pub(crate) static KEYMGMT_87: [Dispatch; 20] = pq_keymgmt::functions!(MlDsa<MlDsa87>);

/// The signature functions for parameter set `$set`, as a dispatch table.
macro_rules! signature_functions {
    ($set:ty) => {
        [
            entry!(SIGNATURE_NEWCTX, newctx::<$set>, SignatureNewctx),
            entry!(
                SIGNATURE_SIGN_MESSAGE_INIT,
                message_init::<$set>,
                SignatureInit
            ),
            entry!(SIGNATURE_SIGN, sign::<$set>, SignatureSign),
            entry!(
                SIGNATURE_VERIFY_MESSAGE_INIT,
                message_init::<$set>,
                SignatureInit
            ),
            entry!(SIGNATURE_VERIFY, verify::<$set>, SignatureVerify),
            entry!(
                SIGNATURE_DIGEST_SIGN_INIT,
                digest_init::<$set>,
                SignatureDigestInit
            ),
            entry!(SIGNATURE_DIGEST_SIGN, sign::<$set>, SignatureSign),
            entry!(
                SIGNATURE_DIGEST_VERIFY_INIT,
                digest_init::<$set>,
                SignatureDigestInit
            ),
            entry!(SIGNATURE_DIGEST_VERIFY, verify::<$set>, SignatureVerify),
            entry!(SIGNATURE_FREECTX, freectx::<$set>, CtxFree),
            entry!(SIGNATURE_DUPCTX, dupctx::<$set>, CtxDup),
            entry!(
                SIGNATURE_GET_CTX_PARAMS,
                get_ctx_params::<$set>,
                CtxGetParams
            ),
            entry!(
                SIGNATURE_GETTABLE_CTX_PARAMS,
                gettable_ctx_params,
                CtxParamList
            ),
            entry!(
                SIGNATURE_SET_CTX_PARAMS,
                set_ctx_params::<$set>,
                CtxSetParams
            ),
            entry!(
                SIGNATURE_SETTABLE_CTX_PARAMS,
                settable_ctx_params,
                CtxParamList
            ),
            Dispatch::END,
        ]
    };
}

pub(crate) static SIGNATURE_44: [Dispatch; 16] = signature_functions!(MlDsa44);
pub(crate) static SIGNATURE_65: [Dispatch; 16] = signature_functions!(MlDsa65);
pub(crate) static SIGNATURE_87: [Dispatch; 16] = signature_functions!(MlDsa87);

/// A signature or verification under way.
struct Signing<P: Set> {
    provider: Arc<Provider>,
    key: Option<Arc<Key<MlDsa<P>>>>,
    /// Why a signature would not be hedged with fresh randomness, which
    /// refuses signing but not verification, which these flags do not
    /// change.
    unhedged: Unhedged,
}

/// The signing flags rind refuses, as a context's parameters last set them.
#[derive(Clone, Copy, Default)]
struct Unhedged {
    deterministic: bool,
    test_entropy: bool,
}

impl<P: Set> Clone for Signing<P> {
    fn clone(&self) -> Self {
        Self {
            provider: self.provider.clone(),
            key: self.key.clone(),
            unhedged: self.unhedged,
        }
    }
}

impl<P: Set> Signing<P> {
    /// # Safety
    ///
    /// `ctx` is null or a context `newctx` or `dupctx` made, which OpenSSL
    /// has not freed, and no one else uses for `'a`.
    unsafe fn from_ptr<'a>(ctx: *mut c_void) -> Option<&'a mut Self> {
        // SAFETY: per the caller.
        unsafe { ctx.cast::<Self>().as_mut() }
    }

    /// Begins an operation with the key of `keydata`, or the key it began
    /// with before if that is null, then sets `params`.
    ///
    /// # Safety
    ///
    /// As for [`KeyData::from_ptr`], and `params` as for [`Params::new`].
    unsafe fn init(&mut self, keydata: *mut c_void, params: *const Param) -> Result<(), Failure> {
        if !keydata.is_null() || self.key.is_none() {
            // SAFETY: per the caller.
            let key = unsafe { KeyData::<MlDsa<P>>::from_ptr(keydata) }
                .ok_or_else(|| Failure::invalid("no key is set"))?
                .operand()?;
            self.key = Some(key);
        }
        // SAFETY: per the caller.
        set_params(unsafe { Params::new(params) }, &mut self.unhedged)
    }

    fn key(&self) -> Result<&Key<MlDsa<P>>, Failure> {
        self.key
            .as_deref()
            .ok_or_else(|| Failure::invalid("no key is set"))
    }

    fn sign(
        &self,
        signature: *mut u8,
        signature_len: *mut usize,
        size: usize,
        message: &[u8],
    ) -> Result<(), Failure> {
        if signature_len.is_null() {
            return Err(Failure::invalid("no length to write"));
        }
        // OpenSSL refuses a public key even for the size query.
        let Some(pair) = self.key()?.private() else {
            return Err(Failure::invalid("the key is not a private key"));
        };
        if !signature.is_null() {
            if size < P::SIGNATURE_LEN {
                return Err(Failure::invalid("the output buffer is too small"));
            }
            if self.unhedged.deterministic {
                return Err(Failure::unsupported(
                    "rind signs ML-DSA hedged, not deterministically",
                ));
            }
            if self.unhedged.test_entropy {
                return Err(Failure::unsupported(
                    "rind signs ML-DSA only with fresh randomness, not test-entropy",
                ));
            }
            let signed = pair.sign(message)?;
            // SAFETY: OpenSSL passes `size` writable bytes at `signature`.
            unsafe {
                core::ptr::copy_nonoverlapping(
                    signed.as_ref().as_ptr(),
                    signature,
                    P::SIGNATURE_LEN,
                )
            };
        }
        // SAFETY: OpenSSL passes a length to write.
        unsafe { *signature_len = P::SIGNATURE_LEN };
        Ok(())
    }

    fn verify(&self, signature: &[u8], message: &[u8]) -> Result<(), Failure> {
        let public = match self.key()? {
            Key::Public(public) => public,
            Key::Private(pair) => pair.public_key(),
        };
        // OpenSSL's default provider raises no error for a signature that
        // fails, whatever its length or content.
        public
            .verify(message, signature)
            .map_err(|_| Failure::Quiet)
    }
}

/// The value of an integer parameter of up to eight bytes, as
/// `OSSL_PARAM_get_int` reads it.
fn integer(param: &Param) -> Option<i64> {
    if param.data.is_null() || !matches!(param.data_type, INTEGER | UNSIGNED_INTEGER) {
        return None;
    }
    // SAFETY: a parameter's data is valid for its size.
    let bytes = unsafe { slice::from_raw_parts(param.data.cast::<u8>(), param.data_size) };
    let value = match bytes.len() {
        1 => i64::from(bytes[0] as i8),
        2 => i64::from(i16::from_ne_bytes(bytes.try_into().ok()?)),
        4 => i64::from(i32::from_ne_bytes(bytes.try_into().ok()?)),
        8 => i64::from_ne_bytes(bytes.try_into().ok()?),
        _ => return None,
    };
    match param.data_type {
        // An unsigned value read as signed is negative only if it is too
        // large for any flag.
        UNSIGNED_INTEGER if value < 0 => None,
        UNSIGNED_INTEGER if bytes.len() == 1 => Some(i64::from(bytes[0])),
        _ => Some(value),
    }
}

/// The parameters an operation takes, each of which rind accepts only at
/// the value pure ML-DSA with the empty context has, but for those that
/// change only signing, which `unhedged` records for signing to refuse.
fn set_params(params: Params<'_>, unhedged: &mut Unhedged) -> Result<(), Failure> {
    if let Some(context) = params.find(c"context-string") {
        match context.octets() {
            Some([]) => {}
            Some(context) if context.len() <= MAX_CONTEXT_LEN => {
                return Err(Failure::unsupported(
                    "rind signs ML-DSA only with the empty context string",
                ));
            }
            Some(_) => {
                return Err(Failure::invalid(
                    "the context string is longer than 255 bytes",
                ));
            }
            None => {
                return Err(Failure::invalid(
                    "the context string must be an octet string",
                ));
            }
        }
    }
    // OpenSSL stores these two as it reads each, in this order, so a call it
    // refuses later keeps them, and drops a test entropy of the wrong size.
    match params.find(c"test-entropy").map(|param| param.octets()) {
        Some(Some(entropy)) if entropy.len() == TEST_ENTROPY_LEN => unhedged.test_entropy = true,
        Some(_) => {
            unhedged.test_entropy = false;
            return Err(Failure::invalid("the test entropy must be 32 bytes"));
        }
        None => {}
    }
    // OpenSSL reads it as an `int` and signs deterministically only at 1.
    if let Some(param) = params.find(c"deterministic") {
        match integer(param).map(i32::try_from) {
            Some(Ok(value)) => unhedged.deterministic = value == 1,
            _ => return Err(Failure::invalid("deterministic must be an int")),
        }
    }
    // Each integer and the value pure ML-DSA has.
    let flags = [
        (
            c"message-encoding",
            1,
            "rind signs ML-DSA only with the pure message encoding",
        ),
        (
            c"mu",
            0,
            "rind signs ML-DSA only from the message, not from an external mu",
        ),
    ];
    for (name, pure, unsupported) in flags {
        let Some(param) = params.find(name) else {
            continue;
        };
        match integer(param) {
            Some(value) if value == pure => {}
            Some(_) => return Err(Failure::unsupported(unsupported)),
            None => {
                return Err(Failure::invalid(&format!(
                    "{} must be an integer",
                    name.to_string_lossy()
                )));
            }
        }
    }
    Ok(())
}

/// The bytes at `data`, which may be null when there are none.
///
/// # Safety
///
/// `data` is valid for `len` bytes, unless `len` is 0.
unsafe fn bytes<'a>(data: *const u8, len: usize) -> Option<&'a [u8]> {
    match (data.is_null(), len) {
        (_, 0) => Some(&[]),
        (true, _) => None,
        // SAFETY: per the caller.
        (false, _) => Some(unsafe { slice::from_raw_parts(data, len) }),
    }
}

unsafe extern "C" fn newctx<P: Set>(provctx: *mut c_void, _propq: *const c_char) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    Box::into_raw(Box::new(Signing::<P> {
        provider,
        key: None,
        unhedged: Unhedged::default(),
    }))
    .cast()
}

unsafe extern "C" fn message_init<P: Set>(
    ctx: *mut c_void,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature, a key object of
    // this provider's key management for its parameter set, and an array.
    let Some(ctx) = (unsafe { Signing::<P>::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = unsafe { ctx.init(keydata, params) };
    ctx.provider.status(result)
}

unsafe extern "C" fn digest_init<P: Set>(
    ctx: *mut c_void,
    mdname: *const c_char,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: as for `message_init`.
    let Some(ctx) = (unsafe { Signing::<P>::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: a digest name is a C string.
    if !mdname.is_null() && !unsafe { core::ffi::CStr::from_ptr(mdname) }.is_empty() {
        return ctx
            .provider
            .status(Err(Failure::invalid("ML-DSA takes no digest")));
    }
    // SAFETY: as for `message_init`.
    let result = unsafe { ctx.init(keydata, params) };
    ctx.provider.status(result)
}

unsafe extern "C" fn sign<P: Set>(
    ctx: *mut c_void,
    signature: *mut u8,
    signature_len: *mut usize,
    size: usize,
    message: *const u8,
    message_len: usize,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature.
    let Some(ctx) = (unsafe { Signing::<P>::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: OpenSSL passes `message_len` bytes at `message`.
    let result = match unsafe { bytes(message, message_len) } {
        Some(message) => ctx.sign(signature, signature_len, size, message),
        None => Err(Failure::invalid("no message")),
    };
    ctx.provider.status(result)
}

unsafe extern "C" fn verify<P: Set>(
    ctx: *mut c_void,
    signature: *const u8,
    signature_len: usize,
    message: *const u8,
    message_len: usize,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature.
    let Some(ctx) = (unsafe { Signing::<P>::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: OpenSSL passes the lengths of bytes at each pointer.
    let result = match unsafe { (bytes(signature, signature_len), bytes(message, message_len)) } {
        (Some(signature), Some(message)) => ctx.verify(signature, message),
        _ => Err(Failure::Quiet),
    };
    ctx.provider.status(result)
}

unsafe extern "C" fn freectx<P: Set>(ctx: *mut c_void) {
    if !ctx.is_null() {
        // SAFETY: OpenSSL frees a context `newctx` or `dupctx` made.
        drop(unsafe { Box::from_raw(ctx.cast::<Signing<P>>()) });
    }
}

unsafe extern "C" fn dupctx<P: Set>(ctx: *mut c_void) -> *mut c_void {
    // SAFETY: OpenSSL passes a context of this signature.
    match unsafe { Signing::<P>::from_ptr(ctx) } {
        Some(ctx) => Box::into_raw(Box::new(ctx.clone())).cast(),
        None => core::ptr::null_mut(),
    }
}

static GETTABLE_CTX: [Param; 2] = [
    Param::describe(Some(c"algorithm-id"), OCTET_STRING, 0),
    Param::END,
];

// Listed so that OpenSSL hands rind each of them, which it refuses, or
// refuses to sign with, unless at pure, hedged ML-DSA's value, rather than
// dropping them unread.
static SETTABLE_CTX: [Param; 6] = [
    Param::describe(Some(c"context-string"), OCTET_STRING, 0),
    Param::describe(Some(c"test-entropy"), OCTET_STRING, 0),
    Param::describe(Some(c"deterministic"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"mu"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"message-encoding"), INTEGER, size_of::<c_int>()),
    Param::END,
];

unsafe extern "C" fn get_ctx_params<P: Set>(ctx: *mut c_void, params: *mut Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature, and a writable
    // array.
    let (Some(ctx), mut params) = (unsafe { Signing::<P>::from_ptr(ctx) }, unsafe {
        ParamsMut::new(params)
    }) else {
        return 0;
    };
    // An X.509 signer reads the identifier to name the algorithm, which a
    // context knows once it has a key, as OpenSSL's does.
    match params.find(c"algorithm-id") {
        Some(param) => (ctx.key.is_some() && param.set_octets(&algorithm_id::<P>())).into(),
        None => 1,
    }
}

unsafe extern "C" fn gettable_ctx_params(_ctx: *mut c_void, _provctx: *mut c_void) -> *const Param {
    GETTABLE_CTX.as_ptr()
}

unsafe extern "C" fn set_ctx_params<P: Set>(ctx: *mut c_void, params: *const Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature, and an array.
    let Some(ctx) = (unsafe { Signing::<P>::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = set_params(unsafe { Params::new(params) }, &mut ctx.unhedged);
    ctx.provider.status(result)
}

unsafe extern "C" fn settable_ctx_params(_ctx: *mut c_void, _provctx: *mut c_void) -> *const Param {
    SETTABLE_CTX.as_ptr()
}

// ML-DSA's TLS 1.3 signature schemes, as OpenSSL 3.5's default provider
// describes them. TLS offers a provider's scheme only when that provider
// also backs its key type, so with rind preferred the default provider's are
// dropped, and an ML-DSA certificate has none unless rind lists them.
static SIGALG_CODE_POINTS: [c_uint; 3] = [0x0904, 0x0905, 0x0906];
static SIGALG_SECURITY_BITS: [c_uint; 3] = [128, 192, 256];
/// `TLS1_3_VERSION`.
static SIGALG_MIN_TLS: c_int = 0x0304;
/// No maximum.
static SIGALG_NO_MAX: c_int = 0;
/// No DTLS.
static SIGALG_NO_DTLS: c_int = -1;

macro_rules! sigalg {
    ($tls:literal, $name:literal, $oid:literal, $index:literal) => {
        [
            Param::text(c"tls-sigalg-iana-name", $tls),
            Param::text(c"tls-sigalg-name", $name),
            Param::text(c"tls-sigalg-oid", $oid),
            Param::unsigned(c"tls-sigalg-code-point", &SIGALG_CODE_POINTS[$index]),
            Param::unsigned(c"tls-sigalg-sec-bits", &SIGALG_SECURITY_BITS[$index]),
            Param::signed(c"tls-min-tls", &SIGALG_MIN_TLS),
            Param::signed(c"tls-max-tls", &SIGALG_NO_MAX),
            Param::signed(c"tls-min-dtls", &SIGALG_NO_DTLS),
            Param::signed(c"tls-max-dtls", &SIGALG_NO_DTLS),
            Param::END,
        ]
    };
}

static TLS_SIGALGS: [[Param; 10]; 3] = [
    sigalg!(c"mldsa44", c"ML-DSA-44", c"2.16.840.1.101.3.4.3.17", 0),
    sigalg!(c"mldsa65", c"ML-DSA-65", c"2.16.840.1.101.3.4.3.18", 1),
    sigalg!(c"mldsa87", c"ML-DSA-87", c"2.16.840.1.101.3.4.3.19", 2),
];

/// Hands OpenSSL's capability callback each of ML-DSA's TLS signature
/// schemes.
///
/// # Safety
///
/// `callback` and `arg` are those OpenSSL passes to `get_capabilities`.
pub(crate) unsafe fn tls_sigalgs(callback: Callback, arg: *mut c_void) -> c_int {
    for sigalg in &TLS_SIGALGS {
        // SAFETY: the callback is OpenSSL's, and takes the parameters it is
        // given to read for the call.
        if unsafe { callback(sigalg.as_ptr(), arg) } != 1 {
            return 0;
        }
    }
    1
}
