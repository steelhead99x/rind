// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! X25519 key management and key exchange, as OpenSSL's default provider
//! offers them under `X25519`.

use core::ffi::{c_int, c_void};
use std::sync::Arc;

use rind::agreement::{self, PrivateKey};
use rind::hpke;
use zeroize::Zeroizing;

use crate::ffi::{
    CtxDup, CtxFree, CtxGetParams, CtxParamList, Dispatch, INTEGER, KEYEXCH_DERIVE, KEYEXCH_DUPCTX,
    KEYEXCH_FREECTX, KEYEXCH_GET_CTX_PARAMS, KEYEXCH_GETTABLE_CTX_PARAMS, KEYEXCH_INIT,
    KEYEXCH_NEWCTX, KEYEXCH_SET_PEER, KeyexchDerive, KeyexchInit, KeyexchNewctx, KeyexchSetPeer,
    OCTET_STRING, Param, UTF8_STRING, entry,
};
use crate::keymgmt::{self, Key, KeyData, Kind, LEN};
use crate::params::{Params, ParamsMut};
use crate::provider::{Failure, Provider};

pub(crate) struct X25519;

impl Kind for X25519 {
    type Private = PrivateKey;
    type Public = Zeroizing<[u8; LEN]>;
    type Secret = agreement::Scalar;

    const BITS: c_int = 253;
    const SECURITY_BITS: c_int = 128;
    const MAX_SIZE: c_int = LEN as c_int;
    const GROUP: Option<&'static [u8]> = Some(b"x25519");
    const TAG: u8 = 1;

    fn generate(ikm: Option<&[u8]>) -> Result<PrivateKey, Failure> {
        let mut scalar = [0u8; LEN];
        match ikm {
            Some(ikm) if ikm.len() < LEN => {
                return Err(Failure::invalid("dhkem-ikm must hold at least 32 bytes"));
            }
            Some(ikm) => {
                let derived = hpke::PrivateKey::derive(&hpke::DHKEM_X25519_HKDF_SHA256, ikm)?;
                scalar.copy_from_slice(derived.to_scalar().as_ref());
            }
            None => rind::rand::fill(&mut scalar[..])?,
        }
        // Clamped, as OpenSSL stores a key it makes, so `priv` gives the same
        // bytes its default provider would.
        scalar[0] &= 248;
        scalar[LEN - 1] &= 127;
        scalar[LEN - 1] |= 64;
        Ok(PrivateKey::from_scalar(&agreement::X25519, &scalar[..])?)
    }

    fn load(private: &[u8]) -> Result<PrivateKey, rind::Error> {
        PrivateKey::from_scalar(&agreement::X25519, private)
    }

    fn public(bytes: [u8; LEN]) -> Self::Public {
        Zeroizing::new(bytes)
    }

    fn public_bytes(public: &Self::Public) -> &[u8] {
        &public[..]
    }

    fn public_of(private: &PrivateKey) -> &[u8] {
        private.public_key().as_ref()
    }

    fn private_bytes(private: &PrivateKey) -> agreement::Scalar {
        private.to_scalar()
    }

    fn get_params(key: Option<&Key<Self>>, params: &mut ParamsMut<'_>) -> bool {
        match (key, params.find(c"encoded-pub-key")) {
            (Some(key), Some(param)) => param.set_octets(key.public()),
            _ => true,
        }
    }

    fn set_params(data: &mut KeyData<Self>, params: Params<'_>) -> bool {
        // TLS gives a peer's key this way, into an empty key.
        if let Some(param) = params.find(c"encoded-pub-key") {
            let Some(public) = param
                .octets()
                .and_then(|bytes| <[u8; LEN]>::try_from(bytes).ok())
            else {
                return false;
            };
            data.set(Key::Public(Zeroizing::new(public)));
        }
        // rind fetches nothing, so it has no use for a property query.
        params
            .find(c"properties")
            .is_none_or(|properties| properties.utf8().is_some())
    }

    fn gettable() -> &'static [Param] {
        &GETTABLE
    }

    fn settable() -> &'static [Param] {
        &SETTABLE
    }
}

static GETTABLE: [Param; 7] = [
    Param::describe(Some(c"bits"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"security-bits"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"max-size"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"encoded-pub-key"), OCTET_STRING, 0),
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::describe(Some(c"priv"), OCTET_STRING, 0),
    Param::END,
];

static SETTABLE: [Param; 3] = [
    Param::describe(Some(c"encoded-pub-key"), OCTET_STRING, 0),
    Param::describe(Some(c"properties"), UTF8_STRING, 0),
    Param::END,
];

pub(crate) static KEYMGMT: [Dispatch; 20] = keymgmt::functions!(X25519);

pub(crate) static KEYEXCH: [Dispatch; 9] = [
    entry!(KEYEXCH_NEWCTX, newctx, KeyexchNewctx),
    entry!(KEYEXCH_INIT, init, KeyexchInit),
    entry!(KEYEXCH_SET_PEER, set_peer, KeyexchSetPeer),
    entry!(KEYEXCH_DERIVE, derive, KeyexchDerive),
    entry!(KEYEXCH_FREECTX, freectx, CtxFree),
    entry!(KEYEXCH_DUPCTX, dupctx, CtxDup),
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
    key: Option<Arc<Key<X25519>>>,
    peer: Option<Arc<Key<X25519>>>,
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
    unsafe fn key(&self, keydata: *mut c_void) -> Result<Arc<Key<X25519>>, Failure> {
        // SAFETY: per the caller.
        unsafe { KeyData::<X25519>::from_ptr(keydata) }
            .ok_or_else(|| Failure::invalid("no key is set"))?
            .operand()
    }

    fn derive(&self, secret: *mut u8, secretlen: *mut usize, outlen: usize) -> Result<(), Failure> {
        let (Some(private), Some(peer)) = (
            self.key.as_deref().and_then(Key::private),
            self.peer.as_deref(),
        ) else {
            return Err(Failure::invalid(
                "the key exchange needs a private key and a peer key",
            ));
        };
        if secretlen.is_null() {
            return Err(Failure::invalid("no length to write"));
        }
        if !secret.is_null() {
            if outlen < LEN {
                return Err(Failure::invalid("the output buffer is too small"));
            }
            let shared = private.agree(peer.public())?;
            // SAFETY: OpenSSL passes `outlen` writable bytes at `secret`.
            unsafe { core::ptr::copy_nonoverlapping(shared.as_ref().as_ptr(), secret, LEN) };
        }
        // SAFETY: OpenSSL passes a length to write.
        unsafe { *secretlen = LEN };
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
    }))
    .cast()
}

unsafe extern "C" fn init(ctx: *mut c_void, keydata: *mut c_void, _params: *const Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this exchange and a key object of
    // this provider's X25519 key management.
    let Some(ctx) = (unsafe { Exchange::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = unsafe { ctx.key(keydata) }.map(|key| ctx.key = Some(key));
    ctx.provider.status(result)
}

unsafe extern "C" fn set_peer(ctx: *mut c_void, keydata: *mut c_void) -> c_int {
    // SAFETY: as for `init`.
    let Some(ctx) = (unsafe { Exchange::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as for `init`.
    let result = unsafe { ctx.key(keydata) }.map(|key| ctx.peer = Some(key));
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

// OpenSSL's default provider gets only its FIPS indicator, which this
// provider, outside FIPS, does not have.
static GETTABLE_CTX: [Param; 1] = [Param::END];

unsafe extern "C" fn get_ctx_params(_ctx: *mut c_void, _params: *mut Param) -> c_int {
    1
}

unsafe extern "C" fn gettable_ctx_params(_ctx: *mut c_void, _provctx: *mut c_void) -> *const Param {
    GETTABLE_CTX.as_ptr()
}
