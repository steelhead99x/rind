// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! Ed25519 key management and signatures, as OpenSSL's default provider
//! offers them under `ED25519`.
//!
//! rind signs and verifies pure Ed25519 only, so it refuses the Ed25519ph
//! and Ed25519ctx instances OpenSSL's `ED25519` also takes.

use core::ffi::{c_char, c_int, c_void};
use core::mem::ManuallyDrop;
use core::slice;
use std::sync::Arc;

use rind::ed25519::{KeyPair, PublicKey, Seed};
use zeroize::Zeroizing;

use crate::ffi::{
    CtxDup, CtxFree, CtxGetParams, CtxParamList, CtxSetParams, Dispatch, INTEGER, OCTET_STRING,
    Param, SIGNATURE_DIGEST_SIGN, SIGNATURE_DIGEST_SIGN_INIT, SIGNATURE_DIGEST_VERIFY,
    SIGNATURE_DIGEST_VERIFY_INIT, SIGNATURE_DUPCTX, SIGNATURE_FREECTX, SIGNATURE_GET_CTX_PARAMS,
    SIGNATURE_GETTABLE_CTX_PARAMS, SIGNATURE_NEWCTX, SIGNATURE_QUERY_KEY_TYPES,
    SIGNATURE_SET_CTX_PARAMS, SIGNATURE_SETTABLE_CTX_PARAMS, SIGNATURE_SIGN, SIGNATURE_SIGN_INIT,
    SIGNATURE_SIGN_MESSAGE_INIT, SIGNATURE_VERIFY, SIGNATURE_VERIFY_INIT,
    SIGNATURE_VERIFY_MESSAGE_INIT, SignatureDigestInit, SignatureInit, SignatureNewctx,
    SignatureQueryKeyTypes, SignatureSign, SignatureVerify, UTF8_STRING, entry,
};
use crate::keymgmt::{self, Key, KeyData, Kind, LEN};
use crate::params::{Params, ParamsMut};
use crate::provider::{Failure, Provider};

/// An Ed25519 signature's length.
const SIGNATURE_LEN: usize = 64;

/// The DER `AlgorithmIdentifier` of Ed25519 (RFC 8410): `id-Ed25519`, with
/// no parameters.
const ALGORITHM_ID: [u8; 7] = [0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70];

/// The longest context string RFC 8032 allows.
const MAX_CONTEXT_LEN: usize = 255;

pub(crate) struct Ed25519;

/// A key pair, with its public key's bytes, which `priv` and `pub` read.
/// Both halves wipe themselves, so the whole value is wiped on drop.
pub(crate) struct Pair {
    pair: KeyPair,
    public: Zeroizing<[u8; LEN]>,
}

impl Pair {
    fn new(pair: KeyPair) -> Self {
        let mut public = Zeroizing::new([0; LEN]);
        public.copy_from_slice(pair.public_key().as_ref());
        Self { pair, public }
    }
}

/// A public key alone, which verifies nothing if rind refuses its point, as
/// one of small order or off the curve. It wipes its whole value on drop,
/// parsed verifier included, which rind's `PublicKey` does not wipe itself.
pub(crate) struct Public {
    bytes: [u8; LEN],
    verifier: ManuallyDrop<Option<PublicKey>>,
}

impl Drop for Public {
    fn drop(&mut self) {
        // SAFETY: the verifier is dropped once, here, and no field is read
        // after; the wipe only writes `self`'s own bytes.
        unsafe {
            ManuallyDrop::drop(&mut self.verifier);
            let bytes = (self as *mut Self).cast::<u8>();
            for i in 0..size_of::<Self>() {
                core::ptr::write_volatile(bytes.add(i), 0);
            }
        }
    }
}

impl Kind for Ed25519 {
    type Private = Pair;
    type Public = Public;
    type Secret = Seed;

    const BITS: c_int = 256;
    const SECURITY_BITS: c_int = 128;
    const MAX_SIZE: c_int = SIGNATURE_LEN as c_int;
    const GROUP: Option<&'static [u8]> = None;
    const TAG: u8 = 2;

    fn generate(ikm: Option<&[u8]>) -> Result<Pair, Failure> {
        if ikm.is_some() {
            return Err(Failure::invalid("dhkem-ikm derives only X25519 keys"));
        }
        Ok(Pair::new(KeyPair::generate()?))
    }

    fn load(private: &[u8]) -> Result<Pair, rind::Error> {
        Ok(Pair::new(KeyPair::from_seed(private)?))
    }

    fn public(bytes: [u8; LEN]) -> Public {
        Public {
            verifier: ManuallyDrop::new(PublicKey::new(&bytes).ok()),
            bytes,
        }
    }

    fn public_bytes(public: &Public) -> &[u8] {
        &public.bytes[..]
    }

    fn public_of(private: &Pair) -> &[u8] {
        &private.public[..]
    }

    fn private_bytes(private: &Pair) -> Seed {
        private.pair.to_seed()
    }

    fn get_params(_key: Option<&Key<Self>>, params: &mut ParamsMut<'_>) -> bool {
        // Ed25519 hashes the message itself, so a signature takes no digest.
        params
            .find(c"mandatory-digest")
            .is_none_or(|param| param.set_utf8(c""))
    }

    fn set_params(_data: &mut KeyData<Self>, _params: Params<'_>) -> bool {
        // OpenSSL's default provider sets nothing on an Ed25519 key, and
        // ignores what it is given.
        true
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
    Param::describe(Some(c"mandatory-digest"), UTF8_STRING, 0),
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::describe(Some(c"priv"), OCTET_STRING, 0),
    Param::END,
];

static SETTABLE: [Param; 1] = [Param::END];

pub(crate) static KEYMGMT: [Dispatch; 20] = keymgmt::functions!(Ed25519);

pub(crate) static SIGNATURE: [Dispatch; 19] = [
    entry!(SIGNATURE_NEWCTX, newctx, SignatureNewctx),
    entry!(SIGNATURE_SIGN_INIT, prehashed_init, SignatureInit),
    entry!(SIGNATURE_SIGN, sign, SignatureSign),
    entry!(SIGNATURE_VERIFY_INIT, prehashed_init, SignatureInit),
    entry!(SIGNATURE_VERIFY, verify, SignatureVerify),
    entry!(SIGNATURE_DIGEST_SIGN_INIT, digest_init, SignatureDigestInit),
    entry!(SIGNATURE_DIGEST_SIGN, sign, SignatureSign),
    entry!(
        SIGNATURE_DIGEST_VERIFY_INIT,
        digest_init,
        SignatureDigestInit
    ),
    entry!(SIGNATURE_DIGEST_VERIFY, verify, SignatureVerify),
    entry!(SIGNATURE_SIGN_MESSAGE_INIT, message_init, SignatureInit),
    entry!(SIGNATURE_VERIFY_MESSAGE_INIT, message_init, SignatureInit),
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
    key: Option<Arc<Key<Ed25519>>>,
    /// Whether the operation began as `EVP_PKEY_sign_message_init` does,
    /// naming its instance, which then may not change.
    instance_preset: bool,
    /// Whether the operation began as `EVP_PKEY_sign_init` does, for an
    /// instance whose message the caller hashed: Ed25519ph, which rind
    /// lacks.
    prehashed: bool,
    /// Whether a context string was set, which pure Ed25519 refuses.
    context: bool,
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

    /// Begins an operation with the key of `keydata`, then sets `params`.
    ///
    /// # Safety
    ///
    /// As for [`KeyData::from_ptr`], and `params` as for [`Params::new`].
    unsafe fn init(
        &mut self,
        keydata: *mut c_void,
        params: *const Param,
        instance_preset: bool,
        prehashed: bool,
    ) -> Result<(), Failure> {
        // SAFETY: per the caller.
        let key = unsafe { KeyData::<Ed25519>::from_ptr(keydata) }
            .ok_or_else(|| Failure::invalid("no key is set"))?
            .operand()?;
        self.key = Some(key);
        self.instance_preset = instance_preset;
        self.prehashed = prehashed;
        self.context = false;
        // SAFETY: per the caller.
        self.set_params(unsafe { Params::new(params) })
    }

    fn set_params(&mut self, params: Params<'_>) -> Result<(), Failure> {
        if let Some(instance) = params.find(c"instance") {
            if self.instance_preset {
                return Err(Failure::invalid("the EdDSA instance is preset"));
            }
            match instance.utf8() {
                Some(name) if name.eq_ignore_ascii_case(b"Ed25519") => {}
                Some(name)
                    if name.eq_ignore_ascii_case(b"Ed25519ph")
                        || name.eq_ignore_ascii_case(b"Ed25519ctx") =>
                {
                    return Err(Failure::unsupported(
                        "rind signs only pure Ed25519, not Ed25519ph or Ed25519ctx",
                    ));
                }
                _ => return Err(Failure::invalid("unknown EdDSA instance")),
            }
        }
        if let Some(context) = params.find(c"context-string") {
            match context.octets() {
                Some(context) if context.len() <= MAX_CONTEXT_LEN => {
                    self.context = !context.is_empty()
                }
                _ => {
                    self.context = false;
                    return Err(Failure::invalid(
                        "the context string is longer than 255 bytes",
                    ));
                }
            }
        }
        Ok(())
    }

    /// Checks what pure Ed25519 needs before it signs or verifies.
    fn check(&self) -> Result<&Key<Ed25519>, Failure> {
        let key = self
            .key
            .as_deref()
            .ok_or_else(|| Failure::invalid("no key is set"))?;
        if self.prehashed {
            return Err(Failure::unsupported(
                "rind signs only pure Ed25519, not a prehashed message",
            ));
        }
        if self.context {
            return Err(Failure::invalid("pure Ed25519 takes no context string"));
        }
        Ok(key)
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
        if !signature.is_null() {
            if size < SIGNATURE_LEN {
                return Err(Failure::invalid("the output buffer is too small"));
            }
            let Some(pair) = self.check()?.private() else {
                return Err(Failure::invalid("the key is not a private key"));
            };
            let signed = pair.pair.sign(message);
            // SAFETY: OpenSSL passes `size` writable bytes at `signature`.
            unsafe {
                core::ptr::copy_nonoverlapping(signed.as_ref().as_ptr(), signature, SIGNATURE_LEN)
            };
        }
        // SAFETY: OpenSSL passes a length to write.
        unsafe { *signature_len = SIGNATURE_LEN };
        Ok(())
    }

    fn verify(&self, signature: &[u8], message: &[u8]) -> Result<(), Failure> {
        let verifier = match self.check()? {
            Key::Public(public) => public.verifier.as_ref(),
            Key::Private(pair) => Some(pair.pair.public_key()),
        };
        // OpenSSL's default provider raises no error for a signature that
        // fails, whether its length, its point, or its equation is wrong.
        match verifier.map(|verifier| verifier.verify(message, signature)) {
            Some(Ok(())) => Ok(()),
            _ => Err(Failure::Quiet),
        }
    }
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
        instance_preset: false,
        prehashed: false,
        context: false,
    }))
    .cast()
}

/// `EVP_PKEY_sign_init`, which takes Ed25519ph's prehashed message, so
/// every signature it begins fails.
unsafe extern "C" fn prehashed_init(
    ctx: *mut c_void,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this signature, a key object of
    // this provider's Ed25519 key management, and an array.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = unsafe { ctx.init(keydata, params, false, true) };
    ctx.provider.status(result)
}

unsafe extern "C" fn message_init(
    ctx: *mut c_void,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: as for `prehashed_init`.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as for `prehashed_init`.
    let result = unsafe { ctx.init(keydata, params, true, false) };
    ctx.provider.status(result)
}

unsafe extern "C" fn digest_init(
    ctx: *mut c_void,
    mdname: *const c_char,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: as for `prehashed_init`.
    let Some(ctx) = (unsafe { Signing::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: a digest name is a C string.
    if !mdname.is_null() && !unsafe { core::ffi::CStr::from_ptr(mdname) }.is_empty() {
        return ctx
            .provider
            .status(Err(Failure::invalid("Ed25519 takes no digest")));
    }
    // OpenSSL begins again without a key to change only the parameters.
    let result = if keydata.is_null() && ctx.key.is_some() {
        // SAFETY: OpenSSL passes an array.
        ctx.set_params(unsafe { Params::new(params) })
    } else {
        // SAFETY: as for `prehashed_init`.
        unsafe { ctx.init(keydata, params, false, false) }
    };
    ctx.provider.status(result)
}

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
        Some(message) => ctx.sign(signature, signature_len, size, message),
        None => Err(Failure::invalid("no message")),
    };
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
        (Some(signature), Some(message)) => ctx.verify(signature, message),
        _ => Err(Failure::Quiet),
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

static KEY_TYPES: KeyTypes = KeyTypes([c"ED25519".as_ptr(), core::ptr::null()]);

unsafe extern "C" fn query_key_types() -> *const *const c_char {
    KEY_TYPES.0.as_ptr()
}

static GETTABLE_CTX: [Param; 4] = [
    Param::describe(Some(c"algorithm-id"), OCTET_STRING, 0),
    Param::describe(Some(c"instance"), UTF8_STRING, 0),
    Param::describe(Some(c"context-string"), OCTET_STRING, 0),
    Param::END,
];

static SETTABLE_CTX: [Param; 3] = [
    Param::describe(Some(c"instance"), UTF8_STRING, 0),
    Param::describe(Some(c"context-string"), OCTET_STRING, 0),
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
    match params.find(c"algorithm-id") {
        Some(param) => (ctx.key.is_some() && param.set_octets(&ALGORITHM_ID)).into(),
        None => 1,
    }
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

#[cfg(test)]
mod tests {
    use std::alloc::{Layout, dealloc};

    use super::*;

    /// A private key is zero in every byte once dropped, before it is freed.
    /// Reading it then is a deliberate use after drop, as
    /// `rind/tests/zeroing.rs` does: not sound in theory, but it catches a
    /// part left unwiped in practice.
    /// A public key alone, its parsed verifier included, is zero in every
    /// byte once dropped, as a private key is.
    #[test]
    fn a_public_key_wipes_whole() {
        let key = Box::into_raw(Box::new(Ed25519::public(
            Ed25519::load(&[0x9d; LEN])
                .unwrap()
                .public
                .as_slice()
                .try_into()
                .unwrap(),
        )));
        // SAFETY: `key` is a live allocation of `Public`'s size; it is
        // dropped once, read before it is freed, and freed with its layout.
        unsafe {
            assert!((*key).verifier.is_some());
            core::ptr::drop_in_place(key);
            let bytes = key.cast::<u8>();
            assert!((0..size_of::<Public>()).all(|i| core::ptr::read_volatile(bytes.add(i)) == 0));
            dealloc(bytes, Layout::new::<Public>());
        }
    }

    #[test]
    fn a_private_key_wipes_whole() {
        let key = Box::into_raw(Box::new(Ed25519::load(&[0x9d; LEN]).unwrap()));
        let len = size_of::<Pair>();
        // SAFETY: `key` is a live allocation of `len` bytes; it is dropped
        // once, read before it is freed, and freed with its own layout.
        unsafe {
            core::ptr::drop_in_place(key);
            let bytes = key.cast::<u8>();
            assert!((0..len).all(|i| core::ptr::read_volatile(bytes.add(i)) == 0));
            dealloc(bytes, Layout::new::<Pair>());
        }
    }
}
