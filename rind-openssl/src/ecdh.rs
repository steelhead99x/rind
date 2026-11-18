// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! ECDH on P-256, P-384, and P-521, as OpenSSL's default provider offers it
//! under `ECDH`: the x coordinate of the shared point, with no key
//! derivation.
//!
//! The X9.63 key derivation OpenSSL can add (`kdf-type`) is not backed, and
//! fails as unsupported. The cofactor of every curve here is 1, so its
//! `ecdh-cofactor-mode` changes nothing.

use core::ffi::{c_int, c_void};
use std::sync::Arc;

use crate::ec::{Key, KeyData};
use crate::ffi::{
    CtxDup, CtxFree, CtxGetParams, CtxParamList, CtxSetParams, Dispatch, INTEGER, KEYEXCH_DERIVE,
    KEYEXCH_DUPCTX, KEYEXCH_FREECTX, KEYEXCH_GET_CTX_PARAMS, KEYEXCH_GETTABLE_CTX_PARAMS,
    KEYEXCH_INIT, KEYEXCH_NEWCTX, KEYEXCH_SET_CTX_PARAMS, KEYEXCH_SET_PEER,
    KEYEXCH_SETTABLE_CTX_PARAMS, KeyexchDerive, KeyexchInit, KeyexchNewctx, KeyexchSetPeer, Param,
    UTF8_STRING, entry,
};
use crate::params::{Params, ParamsMut};
use crate::provider::{Failure, Provider};

pub(crate) static KEYEXCH: [Dispatch; 11] = [
    entry!(KEYEXCH_NEWCTX, newctx, KeyexchNewctx),
    entry!(KEYEXCH_INIT, init, KeyexchInit),
    entry!(KEYEXCH_SET_PEER, set_peer, KeyexchSetPeer),
    entry!(KEYEXCH_DERIVE, derive, KeyexchDerive),
    entry!(KEYEXCH_FREECTX, freectx, CtxFree),
    entry!(KEYEXCH_DUPCTX, dupctx, CtxDup),
    entry!(KEYEXCH_SET_CTX_PARAMS, set_ctx_params, CtxSetParams),
    entry!(
        KEYEXCH_SETTABLE_CTX_PARAMS,
        settable_ctx_params,
        CtxParamList
    ),
    entry!(KEYEXCH_GET_CTX_PARAMS, get_ctx_params, CtxGetParams),
    entry!(
        KEYEXCH_GETTABLE_CTX_PARAMS,
        gettable_ctx_params,
        CtxParamList
    ),
    Dispatch::END,
];

/// A key exchange: this side's private key and the peer's public key.
#[derive(Clone)]
struct Exchange {
    provider: Arc<Provider>,
    key: Option<Arc<Key>>,
    peer: Option<Arc<Key>>,
    /// The cofactor mode a caller set, which changes nothing as every
    /// curve's cofactor is 1, and is read back as OpenSSL's is: -1 asks for
    /// the key's, which is off.
    cofactor_mode: c_int,
}

impl Exchange {
    /// # Safety
    ///
    /// `ctx` is null or a context `newctx` or `dupctx` made, which OpenSSL
    /// has not freed, and no one else uses for `'a`.
    unsafe fn from_ptr<'a>(ctx: *mut c_void) -> Option<&'a mut Self> {
        // SAFETY: per the caller.
        unsafe { ctx.cast::<Self>().as_mut() }
    }

    /// The key of the key object OpenSSL passes.
    ///
    /// # Safety
    ///
    /// As for [`KeyData::from_ptr`].
    unsafe fn key(keydata: *mut c_void) -> Result<Arc<Key>, Failure> {
        // SAFETY: per the caller.
        unsafe { KeyData::from_ptr(keydata) }
            .ok_or_else(|| Failure::invalid("no key is set"))?
            .operand()
    }

    fn derive(&self, secret: *mut u8, secretlen: *mut usize, outlen: usize) -> Result<(), Failure> {
        let (Some(key), Some(peer)) = (self.key.as_deref(), self.peer.as_deref()) else {
            return Err(Failure::invalid(
                "the key exchange needs a private key and a peer key",
            ));
        };
        let Some(private) = key.private() else {
            return Err(Failure::invalid(
                "the key exchange needs a private key and a peer key",
            ));
        };
        if key.curve != peer.curve {
            return Err(Failure::invalid("the keys are on different curves"));
        }
        if secretlen.is_null() {
            return Err(Failure::invalid("no length to write"));
        }
        let len = key.curve.scalar_len();
        if !secret.is_null() {
            if outlen < len {
                return Err(Failure::invalid("the output buffer is too small"));
            }
            let shared = private.agree(key.curve)?.agree(peer.point())?;
            let shared = shared.as_ref();
            debug_assert_eq!(shared.len(), len);
            // SAFETY: OpenSSL passes `outlen` writable bytes at `secret`,
            // and the secret is `len`.
            unsafe { core::ptr::copy_nonoverlapping(shared.as_ptr(), secret, shared.len()) };
        }
        // SAFETY: OpenSSL passes a length to write.
        unsafe { *secretlen = len };
        Ok(())
    }

    fn set_params(&mut self, params: Params<'_>) -> Result<(), Failure> {
        // The cofactor of every curve here is 1.
        if let Some(mode) = params.find(c"ecdh-cofactor-mode") {
            match mode.int() {
                Some(mode @ -1..=1) => self.cofactor_mode = mode,
                _ => return Err(Failure::invalid("ecdh-cofactor-mode is -1, 0, or 1")),
            }
        }
        // None of the X9.63 key derivation's parameters has a use here.
        if let Some(kdf) = params.find(c"kdf-type")
            && kdf.utf8().is_some_and(|name| !name.is_empty())
        {
            return Err(Failure::unsupported(
                "rind's ECDH gives the shared secret, with no key derivation",
            ));
        }
        for name in [c"kdf-digest", c"kdf-outlen", c"kdf-ukm"] {
            if params.find(name).is_some() {
                return Err(Failure::unsupported(
                    "rind's ECDH gives the shared secret, with no key derivation",
                ));
            }
        }
        Ok(())
    }
}

unsafe extern "C" fn newctx(provctx: *mut c_void) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    Box::into_raw(Box::new(Exchange {
        provider,
        key: None,
        peer: None,
        cofactor_mode: -1,
    }))
    .cast()
}

unsafe extern "C" fn init(ctx: *mut c_void, keydata: *mut c_void, params: *const Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this exchange, a key object of
    // this provider's EC key management, and an array.
    let Some(ctx) = (unsafe { Exchange::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = unsafe { Exchange::key(keydata) }.and_then(|key| {
        ctx.key = Some(key);
        // SAFETY: as above.
        ctx.set_params(unsafe { Params::new(params) })
    });
    ctx.provider.status(result)
}

unsafe extern "C" fn set_peer(ctx: *mut c_void, keydata: *mut c_void) -> c_int {
    // SAFETY: as for `init`.
    let Some(ctx) = (unsafe { Exchange::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as for `init`.
    let result = unsafe { Exchange::key(keydata) }.and_then(|peer| {
        match ctx.key.as_deref() {
            Some(key) if key.curve != peer.curve => {
                return Err(Failure::invalid("the keys are on different curves"));
            }
            _ => {}
        }
        ctx.peer = Some(peer);
        Ok(())
    });
    ctx.provider.status(result)
}

unsafe extern "C" fn derive(
    ctx: *mut c_void,
    secret: *mut u8,
    secretlen: *mut usize,
    outlen: usize,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this exchange.
    let Some(ctx) = (unsafe { Exchange::from_ptr(ctx) }) else {
        return 0;
    };
    ctx.provider.status(ctx.derive(secret, secretlen, outlen))
}

unsafe extern "C" fn freectx(ctx: *mut c_void) {
    if !ctx.is_null() {
        // SAFETY: OpenSSL frees a context `newctx` or `dupctx` made.
        drop(unsafe { Box::from_raw(ctx.cast::<Exchange>()) });
    }
}

unsafe extern "C" fn dupctx(ctx: *mut c_void) -> *mut c_void {
    // SAFETY: OpenSSL passes a context of this exchange.
    match unsafe { Exchange::from_ptr(ctx) } {
        Some(ctx) => Box::into_raw(Box::new(ctx.clone())).cast(),
        None => core::ptr::null_mut(),
    }
}

static SETTABLE_CTX: [Param; 3] = [
    Param::describe(Some(c"ecdh-cofactor-mode"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"kdf-type"), UTF8_STRING, 0),
    Param::END,
];

static GETTABLE_CTX: [Param; 3] = [
    Param::describe(Some(c"ecdh-cofactor-mode"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"kdf-type"), UTF8_STRING, 0),
    Param::END,
];

unsafe extern "C" fn set_ctx_params(ctx: *mut c_void, params: *const Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this exchange, and an array.
    let Some(ctx) = (unsafe { Exchange::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = ctx.set_params(unsafe { Params::new(params) });
    ctx.provider.status(result)
}

unsafe extern "C" fn settable_ctx_params(_ctx: *mut c_void, _provctx: *mut c_void) -> *const Param {
    SETTABLE_CTX.as_ptr()
}

unsafe extern "C" fn get_ctx_params(ctx: *mut c_void, params: *mut Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this exchange, and a writable
    // array.
    let (Some(ctx), mut params) = (unsafe { Exchange::from_ptr(ctx) }, unsafe {
        ParamsMut::new(params)
    }) else {
        return 0;
    };
    // The cofactor mode, which OpenSSL's default provider starts at off,
    // and no key derivation.
    if let Some(param) = params.find(c"ecdh-cofactor-mode")
        && !param.set_int(ctx.cofactor_mode.max(0))
    {
        return 0;
    }
    if let Some(param) = params.find(c"kdf-type")
        && !param.set_utf8(c"")
    {
        return 0;
    }
    1
}

unsafe extern "C" fn gettable_ctx_params(_ctx: *mut c_void, _provctx: *mut c_void) -> *const Param {
    GETTABLE_CTX.as_ptr()
}
