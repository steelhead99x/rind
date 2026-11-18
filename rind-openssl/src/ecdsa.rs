// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! ECDSA on P-256, P-384, and P-521, as OpenSSL's default provider offers it
//! under `ECDSA`, through `EVP_DigestSign` and `EVP_DigestVerify`.
//!
//! A context hashes the message as it is given, in a digest context of
//! constant size, and signs or verifies the digest, so it keeps no copy of
//! the message. It takes no digest the caller made: `EVP_PKEY_sign` and `EVP_PKEY_verify`, which hand
//! over one, fail as unsupported. rind signs each curve only with its own
//! hash, as aws-lc-rs's algorithms do, and verifies with SHA-256, SHA-384,
//! and SHA-512.

use core::ffi::{c_char, c_int, c_void};
use core::slice;
use std::sync::Arc;

use rind::digest;

use crate::ec::{Hash, Key, KeyData};
use crate::ffi::{
    CtxDup, CtxFree, CtxGetParams, CtxParamList, CtxSetParams, Dispatch, INTEGER, OCTET_STRING,
    Param, SIGNATURE_DIGEST_SIGN, SIGNATURE_DIGEST_SIGN_FINAL, SIGNATURE_DIGEST_SIGN_INIT,
    SIGNATURE_DIGEST_SIGN_UPDATE, SIGNATURE_DIGEST_VERIFY, SIGNATURE_DIGEST_VERIFY_FINAL,
    SIGNATURE_DIGEST_VERIFY_INIT, SIGNATURE_DIGEST_VERIFY_UPDATE, SIGNATURE_DUPCTX,
    SIGNATURE_FREECTX, SIGNATURE_GET_CTX_PARAMS, SIGNATURE_GETTABLE_CTX_PARAMS, SIGNATURE_NEWCTX,
    SIGNATURE_QUERY_KEY_TYPES, SIGNATURE_SET_CTX_PARAMS, SIGNATURE_SETTABLE_CTX_PARAMS,
    SIGNATURE_SIGN, SIGNATURE_SIGN_INIT, SIGNATURE_SIGN_MESSAGE_FINAL, SIGNATURE_SIGN_MESSAGE_INIT,
    SIGNATURE_SIGN_MESSAGE_UPDATE, SIGNATURE_VERIFY, SIGNATURE_VERIFY_INIT,
    SIGNATURE_VERIFY_MESSAGE_FINAL, SIGNATURE_VERIFY_MESSAGE_INIT, SIGNATURE_VERIFY_MESSAGE_UPDATE,
    SignatureDigestInit, SignatureInit, SignatureNewctx, SignatureQueryKeyTypes, SignatureSign,
    SignatureSignFinal, SignatureUpdate, SignatureVerify, SignatureVerifyFinal, UNSIGNED_INTEGER,
    UTF8_STRING, entry,
};
use crate::params::{Params, ParamsMut};
use crate::provider::{Failure, Provider};

pub(crate) static SIGNATURE: [Dispatch; 27] = [
    entry!(SIGNATURE_NEWCTX, newctx, SignatureNewctx),
    // `EVP_PKEY_sign` and `EVP_PKEY_verify` take a digest the caller made.
    entry!(SIGNATURE_SIGN_INIT, bare_init, SignatureInit),
    entry!(SIGNATURE_SIGN, sign, SignatureSign),
    entry!(SIGNATURE_VERIFY_INIT, bare_init, SignatureInit),
    entry!(SIGNATURE_VERIFY, verify, SignatureVerify),
    entry!(
        SIGNATURE_DIGEST_SIGN_INIT,
        digest_sign_init,
        SignatureDigestInit
    ),
    entry!(SIGNATURE_DIGEST_SIGN_UPDATE, update, SignatureUpdate),
    entry!(SIGNATURE_DIGEST_SIGN_FINAL, sign_final, SignatureSignFinal),
    entry!(SIGNATURE_DIGEST_SIGN, sign, SignatureSign),
    entry!(
        SIGNATURE_DIGEST_VERIFY_INIT,
        digest_verify_init,
        SignatureDigestInit
    ),
    entry!(SIGNATURE_DIGEST_VERIFY_UPDATE, update, SignatureUpdate),
    entry!(
        SIGNATURE_DIGEST_VERIFY_FINAL,
        verify_final,
        SignatureVerifyFinal
    ),
    entry!(SIGNATURE_DIGEST_VERIFY, verify, SignatureVerify),
    entry!(
        SIGNATURE_SIGN_MESSAGE_INIT,
        sign_message_init,
        SignatureInit
    ),
    entry!(SIGNATURE_SIGN_MESSAGE_UPDATE, update, SignatureUpdate),
    entry!(SIGNATURE_SIGN_MESSAGE_FINAL, sign_final, SignatureSignFinal),
    entry!(
        SIGNATURE_VERIFY_MESSAGE_INIT,
        verify_message_init,
        SignatureInit
    ),
    entry!(SIGNATURE_VERIFY_MESSAGE_UPDATE, update, SignatureUpdate),
    entry!(
        SIGNATURE_VERIFY_MESSAGE_FINAL,
        verify_final,
        SignatureVerifyFinal
    ),
    entry!(SIGNATURE_FREECTX, freectx, CtxFree),
    entry!(SIGNATURE_DUPCTX, dupctx, CtxDup),
    entry!(
        SIGNATURE_QUERY_KEY_TYPES,
        query_key_types,
        SignatureQueryKeyTypes
    ),
    entry!(SIGNATURE_GET_CTX_PARAMS, get_ctx_params, CtxGetParams),
    entry!(
        SIGNATURE_GETTABLE_CTX_PARAMS,
        gettable_ctx_params,
        CtxParamList
    ),
    entry!(SIGNATURE_SET_CTX_PARAMS, set_ctx_params, CtxSetParams),
    entry!(
        SIGNATURE_SETTABLE_CTX_PARAMS,
        settable_ctx_params,
        CtxParamList
    ),
    Dispatch::END,
];

/// A signature or verification under way.
#[derive(Clone)]
struct Signing {
    provider: Arc<Provider>,
    key: Option<Arc<Key>>,
    /// Whether the operation verifies, as its init says.
    verifying: bool,
    /// The hash the message is signed with, if the caller named one.
    hash: Option<Hash>,
    /// The hash of the message so far, which exists once an update has
    /// begun it, and then fixes the hash.
    hashing: Option<(Hash, digest::Context)>,
}

impl Signing {
    /// # Safety
    ///
    /// `ctx` is null or a context `newctx` or `dupctx` made, which OpenSSL
    /// has not freed, and no one else uses for `'a`.
    unsafe fn from_ptr<'a>(ctx: *mut c_void) -> Option<&'a mut Self> {
        // SAFETY: per the caller.
        unsafe { ctx.cast::<Self>().as_mut() }
    }

    /// Begins an operation with the key of `keydata`, named hash `mdname`,
    /// and `params`.
    ///
    /// # Safety
    ///
    /// `keydata` is null or as for [`KeyData::from_ptr`], `mdname` is null or
    /// a C string, and `params` is as for [`Params::new`].
    unsafe fn init(
        &mut self,
        keydata: *mut c_void,
        mdname: *const c_char,
        params: *const Param,
        verifying: bool,
    ) -> Result<(), Failure> {
        // OpenSSL begins again without a key to change only the parameters.
        if keydata.is_null() && self.key.is_some() && self.verifying == verifying {
            self.hashing = None;
        } else {
            // SAFETY: per the caller.
            let key = unsafe { KeyData::from_ptr(keydata) }
                .ok_or_else(|| Failure::invalid("no key is set"))?
                .operand()?;
            self.key = Some(key);
            self.verifying = verifying;
            self.hash = None;
            self.hashing = None;
        }
        if !mdname.is_null() {
            // SAFETY: a digest name is a C string.
            let name = unsafe { core::ffi::CStr::from_ptr(mdname) }.to_bytes();
            if !name.is_empty() {
                self.hash = Some(hash(name)?);
            }
        }
        // SAFETY: per the caller.
        self.set_params(unsafe { Params::new(params) })
    }

    fn set_params(&mut self, params: Params<'_>) -> Result<(), Failure> {
        if let Some(digest) = params.find(c"digest") {
            let name = digest
                .utf8()
                .ok_or_else(|| Failure::invalid("the digest must be a UTF-8 string"))?;
            let new = hash(name)?;
            if self
                .hashing
                .as_ref()
                .is_some_and(|(begun, _)| *begun != new)
            {
                return Err(Failure::invalid(
                    "the digest cannot change once the message has begun",
                ));
            }
            self.hash = Some(new);
        }
        // rind fetches nothing, so it has no use for a property query.
        if params
            .find(c"properties")
            .is_some_and(|properties| properties.utf8().is_none())
        {
            return Err(Failure::invalid("properties must be a UTF-8 string"));
        }
        // rind's nonces are random.
        if let Some(nonce) = params.find(c"nonce-type")
            && nonce.int() != Some(0)
        {
            return Err(Failure::unsupported(
                "rind signs with random nonces, not deterministic ones",
            ));
        }
        self.check_signing_digest()
    }

    /// Refuses a signing digest that is not the key's curve's own, as soon
    /// as both are known, so `EVP_DigestSignInit_ex` fails rather than a
    /// later call after the message has been hashed.
    fn check_signing_digest(&self) -> Result<(), Failure> {
        match (&self.key, self.hash) {
            (Some(key), Some(hash)) if !self.verifying && hash != key.curve.own_hash() => {
                Err(Failure::unsupported(&format!(
                    "rind signs a curve only with its own hash, not {hash:?} here"
                )))
            }
            _ => Ok(()),
        }
    }

    fn key(&self) -> Result<&Key, Failure> {
        self.key
            .as_deref()
            .ok_or_else(|| Failure::invalid("no key is set"))
    }

    /// The hash the operation uses: the one named, or the curve's own.
    fn hash(&self) -> Result<Hash, Failure> {
        Ok(self.hash.unwrap_or(self.key()?.curve.own_hash()))
    }

    /// Adds `data` to the message's hash, which the first of them begins.
    fn absorb(&mut self, data: &[u8]) -> Result<(), Failure> {
        let hash = self.hash()?;
        let (_, context) = self
            .hashing
            .get_or_insert_with(|| (hash, digest::Context::new(hash.digest())));
        context.update(data);
        Ok(())
    }

    /// The digest of the message the updates gave, which an operation with
    /// none takes as empty, and begins a new message.
    fn finish(&mut self) -> Result<digest::Digest, Failure> {
        let hash = self.hash()?;
        let (_, mut context) = self
            .hashing
            .take()
            .unwrap_or_else(|| (hash, digest::Context::new(hash.digest())));
        Ok(context.finish())
    }

    /// Checks a request to sign, and answers the length of the longest
    /// signature if it asks only that. Returns whether to sign.
    fn begin_sign(
        &self,
        signature: *mut u8,
        signature_len: *mut usize,
        size: usize,
    ) -> Result<bool, Failure> {
        if self.verifying {
            return Err(Failure::invalid("the operation verifies"));
        }
        if signature_len.is_null() {
            return Err(Failure::invalid("no length to write"));
        }
        let key = self.key()?;
        let max = key.curve.max_signature_len();
        if self.hash()? != key.curve.own_hash() {
            return Err(Failure::unsupported(&format!(
                "rind signs a curve only with its own hash, not {:?} here",
                self.hash()?
            )));
        }
        if signature.is_null() {
            // SAFETY: OpenSSL passes a length to write.
            unsafe { *signature_len = max };
            return Ok(false);
        }
        if size < max {
            return Err(Failure::invalid("the output buffer is too small"));
        }
        if key.private().is_none() {
            return Err(Failure::invalid("the key is not a private key"));
        }
        Ok(true)
    }

    /// Signs `digest` into `signature`, after [`Self::begin_sign`] agreed.
    ///
    /// # Safety
    ///
    /// `signature` is valid for the `size` that `begin_sign` checked, and
    /// `signature_len` for a write.
    unsafe fn write_signature(
        &self,
        signature: *mut u8,
        signature_len: *mut usize,
        digest: &digest::Digest,
    ) -> Result<(), Failure> {
        let private = self
            .key()?
            .private()
            .ok_or_else(|| Failure::invalid("the key is not a private key"))?;
        let signed = private.sign_digest(digest)?;
        let signed = signed.as_ref();
        // SAFETY: per the caller, and the signature is no longer than the
        // longest.
        unsafe {
            core::ptr::copy_nonoverlapping(signed.as_ptr(), signature, signed.len());
            *signature_len = signed.len();
        }
        Ok(())
    }

    fn sign_message(
        &self,
        signature: *mut u8,
        signature_len: *mut usize,
        size: usize,
        message: &[u8],
    ) -> Result<(), Failure> {
        if self.begin_sign(signature, signature_len, size)? {
            let digest = digest::digest(self.hash()?.digest(), message);
            // SAFETY: `begin_sign` checked `size`, and OpenSSL passes the
            // buffer and the length.
            unsafe { self.write_signature(signature, signature_len, &digest) }?;
        }
        Ok(())
    }

    fn sign_streamed(
        &mut self,
        signature: *mut u8,
        signature_len: *mut usize,
        size: usize,
    ) -> Result<(), Failure> {
        // A query for the size leaves the message to sign.
        if self.begin_sign(signature, signature_len, size)? {
            let digest = self.finish()?;
            // SAFETY: as for `sign_message`.
            unsafe { self.write_signature(signature, signature_len, &digest) }?;
        }
        Ok(())
    }

    fn verify_digest(&self, signature: &[u8], digest: &digest::Digest) -> Result<(), Failure> {
        if !self.verifying {
            return Err(Failure::invalid("the operation signs"));
        }
        let Some(verifier) = self.key()?.verifier() else {
            return Err(Failure::Quiet);
        };
        // OpenSSL's default provider raises no error for a signature that
        // fails, whether its encoding or its equation is wrong.
        verifier
            .verify_digest(digest, signature)
            .map_err(|_| Failure::Quiet)
    }

    fn verify_message(&self, signature: &[u8], message: &[u8]) -> Result<(), Failure> {
        if !self.verifying {
            return Err(Failure::invalid("the operation signs"));
        }
        let digest = digest::digest(self.hash()?.digest(), message);
        self.verify_digest(signature, &digest)
    }
}

/// The hash `name` means, or why rind cannot verify with it.
fn hash(name: &[u8]) -> Result<Hash, Failure> {
    Hash::from_name(name).ok_or_else(|| {
        Failure::unsupported(&format!(
            "rind's ECDSA takes SHA-256, SHA-384, and SHA-512, not {:?}",
            String::from_utf8_lossy(name)
        ))
    })
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

unsafe extern "C" fn newctx(provctx: *mut c_void, _propq: *const c_char) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    Box::into_raw(Box::new(Signing {
        provider,
        key: None,
        verifying: false,
        hash: None,
        hashing: None,
    }))
    .cast()
}

/// `EVP_PKEY_sign_init` and `EVP_PKEY_verify_init`, whose signatures are over
/// a digest the caller made, which rind's API does not take.
unsafe extern "C" fn bare_init(
    ctx: *mut c_void,
    _keydata: *mut c_void,
    _params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    ctx.provider.status(Err(Failure::unsupported(
        "rind's ECDSA takes a message, not a digest the caller made: \
         use EVP_DigestSign or EVP_DigestVerify",
    )))
}

unsafe fn init(
    ctx: *mut c_void,
    mdname: *const c_char,
    keydata: *mut c_void,
    params: *const Param,
    verifying: bool,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature, a key object of
    // this provider's EC key management, a digest name, and an array.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = unsafe { ctx.init(keydata, mdname, params, verifying) };
    ctx.provider.status(result)
}

unsafe extern "C" fn digest_sign_init(
    ctx: *mut c_void,
    mdname: *const c_char,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: as for `init`.
    unsafe { init(ctx, mdname, keydata, params, false) }
}

unsafe extern "C" fn digest_verify_init(
    ctx: *mut c_void,
    mdname: *const c_char,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: as for `init`.
    unsafe { init(ctx, mdname, keydata, params, true) }
}

unsafe extern "C" fn sign_message_init(
    ctx: *mut c_void,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: as for `init`.
    unsafe { init(ctx, core::ptr::null(), keydata, params, false) }
}

unsafe extern "C" fn verify_message_init(
    ctx: *mut c_void,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: as for `init`.
    unsafe { init(ctx, core::ptr::null(), keydata, params, true) }
}

unsafe extern "C" fn update(ctx: *mut c_void, data: *const u8, len: usize) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: OpenSSL passes `len` bytes at `data`.
    let result = match unsafe { bytes(data, len) } {
        Some(data) if ctx.key.is_some() => ctx.absorb(data),
        Some(_) => Err(Failure::invalid("no key is set")),
        None => Err(Failure::invalid("no message")),
    };
    ctx.provider.status(result)
}

/// A one-shot signature of the message given, or of the one the updates
/// gave if none is.
unsafe extern "C" fn sign(
    ctx: *mut c_void,
    signature: *mut u8,
    signature_len: *mut usize,
    size: usize,
    message: *const u8,
    message_len: usize,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: OpenSSL passes `message_len` bytes at `message`.
    let result = match unsafe { bytes(message, message_len) } {
        Some(message) => ctx.sign_message(signature, signature_len, size, message),
        None => Err(Failure::invalid("no message")),
    };
    ctx.provider.status(result)
}

unsafe extern "C" fn sign_final(
    ctx: *mut c_void,
    signature: *mut u8,
    signature_len: *mut usize,
    size: usize,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    let result = ctx.sign_streamed(signature, signature_len, size);
    ctx.provider.status(result)
}

unsafe extern "C" fn verify(
    ctx: *mut c_void,
    signature: *const u8,
    signature_len: usize,
    message: *const u8,
    message_len: usize,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: OpenSSL passes the lengths of bytes at each pointer.
    let result = match unsafe { (bytes(signature, signature_len), bytes(message, message_len)) } {
        (Some(signature), Some(message)) => ctx.verify_message(signature, message),
        _ => Err(Failure::Quiet),
    };
    ctx.provider.status(result)
}

unsafe extern "C" fn verify_final(ctx: *mut c_void, signature: *const u8, len: usize) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    let digest = ctx.finish();
    // SAFETY: OpenSSL passes `len` bytes at `signature`.
    let result = match (unsafe { bytes(signature, len) }, digest) {
        (Some(signature), Ok(digest)) => ctx.verify_digest(signature, &digest),
        (_, Err(failure)) => Err(failure),
        (None, _) => Err(Failure::Quiet),
    };
    ctx.provider.status(result)
}

unsafe extern "C" fn freectx(ctx: *mut c_void) {
    if !ctx.is_null() {
        // SAFETY: OpenSSL frees a context `newctx` or `dupctx` made.
        drop(unsafe { Box::from_raw(ctx.cast::<Signing>()) });
    }
}

unsafe extern "C" fn dupctx(ctx: *mut c_void) -> *mut c_void {
    // SAFETY: OpenSSL passes a context of this signature.
    match unsafe { Signing::from_ptr(ctx) } {
        Some(ctx) => Box::into_raw(Box::new(ctx.clone())).cast(),
        None => core::ptr::null_mut(),
    }
}

/// The key type a signature takes, as `EVP_SIGNATURE_get0_key_types`
/// answers it, null-terminated.
struct KeyTypes([*const c_char; 2]);

// SAFETY: it points only at a static C string, and no one writes it.
unsafe impl Sync for KeyTypes {}

static KEY_TYPES: KeyTypes = KeyTypes([c"EC".as_ptr(), core::ptr::null()]);

unsafe extern "C" fn query_key_types() -> *const *const c_char {
    KEY_TYPES.0.as_ptr()
}

static GETTABLE_CTX: [Param; 4] = [
    Param::describe(Some(c"algorithm-id"), OCTET_STRING, 0),
    Param::describe(Some(c"digest"), UTF8_STRING, 0),
    Param::describe(Some(c"digest-size"), UNSIGNED_INTEGER, size_of::<usize>()),
    Param::END,
];

static SETTABLE_CTX: [Param; 4] = [
    Param::describe(Some(c"digest"), UTF8_STRING, 0),
    Param::describe(Some(c"properties"), UTF8_STRING, 0),
    Param::describe(Some(c"nonce-type"), INTEGER, size_of::<c_int>()),
    Param::END,
];

unsafe extern "C" fn get_ctx_params(ctx: *mut c_void, params: *mut Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature, and a writable
    // array.
    let (Some(ctx), mut params) = (unsafe { Signing::from_ptr(ctx) }, unsafe {
        ParamsMut::new(params)
    }) else {
        return 0;
    };
    // An X.509 signer reads the identifier to name the algorithm, which a
    // context knows once it has a key, as OpenSSL's does.
    let Ok(hash) = ctx.hash() else {
        return (params.find(c"algorithm-id").is_none()
            && params.find(c"digest").is_none()
            && params.find(c"digest-size").is_none())
        .into();
    };
    if let Some(param) = params.find(c"algorithm-id")
        && !param.set_octets(&hash.algorithm_id())
    {
        return 0;
    }
    if let Some(param) = params.find(c"digest")
        && !param.set_utf8(hash.name())
    {
        return 0;
    }
    if let Some(param) = params.find(c"digest-size")
        && !param.set_size(hash.len())
    {
        return 0;
    }
    1
}

unsafe extern "C" fn gettable_ctx_params(_ctx: *mut c_void, _provctx: *mut c_void) -> *const Param {
    GETTABLE_CTX.as_ptr()
}

unsafe extern "C" fn set_ctx_params(ctx: *mut c_void, params: *const Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature, and an array.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = ctx.set_params(unsafe { Params::new(params) });
    ctx.provider.status(result)
}

unsafe extern "C" fn settable_ctx_params(_ctx: *mut c_void, _provctx: *mut c_void) -> *const Param {
    SETTABLE_CTX.as_ptr()
}
