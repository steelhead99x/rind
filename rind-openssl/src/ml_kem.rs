// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! ML-KEM key management and key encapsulation, as OpenSSL 3.5's default
//! provider offers them under `ML-KEM-512`, `ML-KEM-768`, and `ML-KEM-1024`.
//!
//! OpenSSL's hybrid TLS groups, such as `X25519MLKEM768`, stay its default
//! provider's, which runs their ML-KEM half through the provider the
//! configuration prefers: rind.

use core::ffi::{c_int, c_void};
use core::marker::PhantomData;
use std::sync::Arc;

use rind::kem::{
    Algorithm, Ciphertext, DecapsulationKey, EncapsulationKey, MlKem512, MlKem768, MlKem1024,
};
use zeroize::Zeroizing;

use crate::ffi::{
    CtxFree, CtxParamList, CtxSetParams, Dispatch, KEM_DECAPSULATE, KEM_DECAPSULATE_INIT,
    KEM_ENCAPSULATE, KEM_ENCAPSULATE_INIT, KEM_FREECTX, KEM_NEWCTX, KEM_SET_CTX_PARAMS,
    KEM_SETTABLE_CTX_PARAMS, KemDecapsulate, KemEncapsulate, KemInit, KeyexchNewctx, OCTET_STRING,
    Param, entry,
};
use crate::params::Params;
use crate::pq_keymgmt::{self, Key, KeyData, Scheme, Secret};
use crate::provider::{Failure, Provider};

/// The length of the shared secret every parameter set agrees on.
const SECRET_LEN: usize = 32;

/// ML-KEM with parameter set `A`.
pub(crate) struct MlKem<A>(PhantomData<A>);

/// What tells the parameter sets apart, beyond rind's own types.
pub(crate) trait Set: Algorithm + Send + Sync + 'static {
    const NAME: &'static str;
    const TAG: u8;
    const PRIVATE_LEN: usize;
    const PUBLIC_LEN: usize;
    const CIPHERTEXT_LEN: usize;
    const SECURITY_BITS: c_int;
    const BITS: c_int;
}

impl Set for MlKem512 {
    const NAME: &'static str = "ML-KEM-512";
    const TAG: u8 = 16;
    const PRIVATE_LEN: usize = 1632;
    const PUBLIC_LEN: usize = 800;
    const CIPHERTEXT_LEN: usize = 768;
    const SECURITY_BITS: c_int = 128;
    const BITS: c_int = 512;
}

impl Set for MlKem768 {
    const NAME: &'static str = "ML-KEM-768";
    const TAG: u8 = 17;
    const PRIVATE_LEN: usize = 2400;
    const PUBLIC_LEN: usize = 1184;
    const CIPHERTEXT_LEN: usize = 1088;
    const SECURITY_BITS: c_int = 192;
    const BITS: c_int = 768;
}

impl Set for MlKem1024 {
    const NAME: &'static str = "ML-KEM-1024";
    const TAG: u8 = 18;
    const PRIVATE_LEN: usize = 3168;
    const PUBLIC_LEN: usize = 1568;
    const CIPHERTEXT_LEN: usize = 1568;
    const SECURITY_BITS: c_int = 256;
    const BITS: c_int = 1024;
}

impl<A: Set> Scheme for MlKem<A> {
    type Private = DecapsulationKey<A>;
    type Public = EncapsulationKey<A>;

    const NAME: &'static str = A::NAME;
    const TAG: u8 = A::TAG;
    const SEED_LEN: usize = 64;
    const PRIVATE_LEN: usize = A::PRIVATE_LEN;
    const PUBLIC_LEN: usize = A::PUBLIC_LEN;
    const BITS: c_int = A::BITS;
    const SECURITY_BITS: c_int = A::SECURITY_BITS;
    const MAX_SIZE: c_int = A::CIPHERTEXT_LEN as c_int;
    const ENCODED_PUBLIC: bool = true;
    const SEED_ONCE: bool = true;

    fn generate() -> Result<Self::Private, rind::Error> {
        DecapsulationKey::generate()
    }

    fn from_seed(seed: &[u8]) -> Result<Self::Private, rind::Error> {
        DecapsulationKey::from_seed(seed)
    }

    fn load(seed: Option<&[u8]>, expanded: Option<&[u8]>) -> Result<Self::Private, Failure> {
        match (seed, expanded) {
            (Some(seed), expanded) => {
                let key = DecapsulationKey::from_seed(seed)?;
                if let Some(expanded) = expanded
                    && rind::constant_time::verify(key.to_bytes().as_ref(), expanded).is_err()
                {
                    return Err(Failure::Raise(
                        crate::provider::Reason::KeyRejected,
                        format!("the {} seed is not the expanded key's", A::NAME),
                    ));
                }
                Ok(key)
            }
            (None, Some(expanded)) => {
                let key = DecapsulationKey::new(expanded)?;
                // FIPS 203's checks pass a secret vector that is not its
                // public key's, which then decapsulates every ciphertext to
                // an implicit rejection, so a pairwise test refuses it, as
                // OpenSSL's default provider tests a key it imports.
                let (ciphertext, secret) = key.public_key().encapsulate()?;
                if rind::constant_time::verify(
                    key.decapsulate(&ciphertext).as_ref(),
                    secret.as_ref(),
                )
                .is_err()
                {
                    return Err(Failure::Raise(
                        crate::provider::Reason::KeyRejected,
                        format!("the {} expanded key's halves are not a pair", A::NAME),
                    ));
                }
                Ok(key)
            }
            (None, None) => Err(Failure::invalid("neither seed nor priv is given")),
        }
    }

    fn parse_public(bytes: &[u8]) -> Result<Self::Public, rind::Error> {
        EncapsulationKey::new(bytes)
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

    fn expanded(private: &Self::Private) -> Option<Secret> {
        Some(Zeroizing::new(private.to_bytes().as_ref().to_vec()))
    }
}

pub(crate) static KEYMGMT_512: [Dispatch; 20] = pq_keymgmt::functions!(MlKem<MlKem512>);
pub(crate) static KEYMGMT_768: [Dispatch; 20] = pq_keymgmt::functions!(MlKem<MlKem768>);
pub(crate) static KEYMGMT_1024: [Dispatch; 20] = pq_keymgmt::functions!(MlKem<MlKem1024>);

/// The KEM functions for parameter set `$set`, as a dispatch table.
macro_rules! kem_functions {
    ($set:ty) => {
        [
            entry!(KEM_NEWCTX, newctx::<$set>, KeyexchNewctx),
            entry!(KEM_ENCAPSULATE_INIT, encapsulate_init::<$set>, KemInit),
            entry!(KEM_ENCAPSULATE, encapsulate::<$set>, KemEncapsulate),
            entry!(KEM_DECAPSULATE_INIT, decapsulate_init::<$set>, KemInit),
            entry!(KEM_DECAPSULATE, decapsulate::<$set>, KemDecapsulate),
            entry!(KEM_FREECTX, freectx::<$set>, CtxFree),
            entry!(KEM_SET_CTX_PARAMS, set_ctx_params::<$set>, CtxSetParams),
            entry!(KEM_SETTABLE_CTX_PARAMS, settable_ctx_params, CtxParamList),
            Dispatch::END,
        ]
    };
}

pub(crate) static KEM_512: [Dispatch; 9] = kem_functions!(MlKem512);
pub(crate) static KEM_768: [Dispatch; 9] = kem_functions!(MlKem768);
pub(crate) static KEM_1024: [Dispatch; 9] = kem_functions!(MlKem1024);

/// An encapsulation or decapsulation under way. It has no `dupctx`, as
/// OpenSSL's default provider's has none.
struct Encapsulation<A: Set> {
    provider: Arc<Provider>,
    key: Option<Arc<Key<MlKem<A>>>>,
    decapsulating: bool,
}

impl<A: Set> Encapsulation<A> {
    /// # Safety
    ///
    /// `ctx` is null or a context `newctx` made, which OpenSSL
    /// has not freed, and no one else uses for `'a`.
    unsafe fn from_ptr<'a>(ctx: *mut c_void) -> Option<&'a mut Self> {
        // SAFETY: per the caller.
        unsafe { ctx.cast::<Self>().as_mut() }
    }

    /// Begins an operation with the key of `keydata`, which decapsulation
    /// needs the private key of, then sets `params`.
    ///
    /// # Safety
    ///
    /// As for [`KeyData::from_ptr`], and `params` as for [`Params::new`].
    unsafe fn init(
        &mut self,
        keydata: *mut c_void,
        params: *const Param,
        private: bool,
    ) -> Result<(), Failure> {
        // SAFETY: per the caller.
        let key = unsafe { KeyData::<MlKem<A>>::from_ptr(keydata) }
            .ok_or_else(|| Failure::invalid("no key is set"))?
            .operand()?;
        if private && key.private().is_none() {
            return Err(Failure::invalid("decapsulation needs a private key"));
        }
        self.key = Some(key);
        self.decapsulating = private;
        // SAFETY: per the caller.
        self.set_params(unsafe { Params::new(params) })
    }

    /// Sets OpenSSL's `ikme`, the randomness of a deterministic
    /// encapsulation that only tests use, which rind lacks. Decapsulation
    /// ignores it, as OpenSSL's does, so one array can serve both.
    fn set_params(&self, params: Params<'_>) -> Result<(), Failure> {
        match params.find(c"ikme") {
            Some(_) if !self.decapsulating => Err(Failure::unsupported(
                "rind encapsulates only with fresh randomness, not ikme",
            )),
            _ => Ok(()),
        }
    }

    fn key(&self) -> Result<&Key<MlKem<A>>, Failure> {
        self.key
            .as_deref()
            .ok_or_else(|| Failure::invalid("no key is set"))
    }

    fn encapsulate(
        &self,
        out: *mut u8,
        out_len: *mut usize,
        secret: *mut u8,
        secret_len: *mut usize,
    ) -> Result<(), Failure> {
        let key = self.key()?;
        // Asked only the lengths, as for buffers to hold them.
        if out.is_null() {
            if out_len.is_null() && secret_len.is_null() {
                return Err(Failure::invalid("no length to write"));
            }
            // SAFETY: OpenSSL passes lengths to write where they are not
            // null.
            unsafe {
                if !out_len.is_null() {
                    *out_len = A::CIPHERTEXT_LEN;
                }
                if !secret_len.is_null() {
                    *secret_len = SECRET_LEN;
                }
            }
            return Ok(());
        }
        if secret.is_null() || out_len.is_null() || secret_len.is_null() {
            return Err(Failure::invalid("no secret buffer or length to write"));
        }
        // SAFETY: OpenSSL passes the sizes of its buffers in the lengths.
        if unsafe { *out_len < A::CIPHERTEXT_LEN || *secret_len < SECRET_LEN } {
            return Err(Failure::invalid("the output buffer is too small"));
        }
        let public = match key {
            Key::Public(public) => public,
            Key::Private(private) => private.public_key(),
        };
        let (ciphertext, shared) = public.encapsulate()?;
        // SAFETY: OpenSSL passes buffers of the sizes checked above, and
        // lengths to write.
        unsafe {
            core::ptr::copy_nonoverlapping(ciphertext.as_ref().as_ptr(), out, A::CIPHERTEXT_LEN);
            core::ptr::copy_nonoverlapping(shared.as_ref().as_ptr(), secret, SECRET_LEN);
            *out_len = A::CIPHERTEXT_LEN;
            *secret_len = SECRET_LEN;
        }
        Ok(())
    }

    fn decapsulate(
        &self,
        secret: *mut u8,
        secret_len: *mut usize,
        ciphertext: &[u8],
    ) -> Result<(), Failure> {
        let Some(private) = self.key()?.private() else {
            return Err(Failure::invalid("decapsulation needs a private key"));
        };
        if secret.is_null() {
            if secret_len.is_null() {
                return Err(Failure::invalid("no length to write"));
            }
            // SAFETY: OpenSSL passes a length to write.
            unsafe { *secret_len = SECRET_LEN };
            return Ok(());
        }
        // OpenSSL 3.5 lets the length be null for a buffer it knows is
        // large enough.
        // SAFETY: OpenSSL passes the size of its buffer in the length.
        if !secret_len.is_null() && unsafe { *secret_len } < SECRET_LEN {
            return Err(Failure::invalid("the output buffer is too small"));
        }
        let ciphertext = Ciphertext::<A>::new(ciphertext)?;
        let shared = private.decapsulate(&ciphertext);
        // SAFETY: OpenSSL passes a buffer of the size checked above, and a
        // length to write where it is not null.
        unsafe {
            core::ptr::copy_nonoverlapping(shared.as_ref().as_ptr(), secret, SECRET_LEN);
            if !secret_len.is_null() {
                *secret_len = SECRET_LEN;
            }
        }
        Ok(())
    }
}

unsafe extern "C" fn newctx<A: Set>(provctx: *mut c_void) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    Box::into_raw(Box::new(Encapsulation::<A> {
        provider,
        key: None,
        decapsulating: false,
    }))
    .cast()
}

unsafe extern "C" fn encapsulate_init<A: Set>(
    ctx: *mut c_void,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this KEM, a key object of this
    // provider's key management for its parameter set, and an array.
    let Some(ctx) = (unsafe { Encapsulation::<A>::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = unsafe { ctx.init(keydata, params, false) };
    ctx.provider.status(result)
}

unsafe extern "C" fn decapsulate_init<A: Set>(
    ctx: *mut c_void,
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: as for `encapsulate_init`.
    let Some(ctx) = (unsafe { Encapsulation::<A>::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as for `encapsulate_init`.
    let result = unsafe { ctx.init(keydata, params, true) };
    ctx.provider.status(result)
}

unsafe extern "C" fn encapsulate<A: Set>(
    ctx: *mut c_void,
    out: *mut u8,
    out_len: *mut usize,
    secret: *mut u8,
    secret_len: *mut usize,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this KEM.
    let Some(ctx) = (unsafe { Encapsulation::<A>::from_ptr(ctx) }) else {
        return 0;
    };
    ctx.provider
        .status(ctx.encapsulate(out, out_len, secret, secret_len))
}

unsafe extern "C" fn decapsulate<A: Set>(
    ctx: *mut c_void,
    secret: *mut u8,
    secret_len: *mut usize,
    ciphertext: *const u8,
    ciphertext_len: usize,
) -> c_int {
    // SAFETY: OpenSSL passes a context of this KEM.
    let Some(ctx) = (unsafe { Encapsulation::<A>::from_ptr(ctx) }) else {
        return 0;
    };
    let result = match (ciphertext.is_null(), ciphertext_len) {
        (true, _) | (_, 0) => Err(Failure::invalid("no ciphertext")),
        // SAFETY: OpenSSL passes `ciphertext_len` bytes at `ciphertext`.
        _ => ctx.decapsulate(secret, secret_len, unsafe {
            core::slice::from_raw_parts(ciphertext, ciphertext_len)
        }),
    };
    ctx.provider.status(result)
}

unsafe extern "C" fn freectx<A: Set>(ctx: *mut c_void) {
    if !ctx.is_null() {
        // SAFETY: OpenSSL frees a context `newctx` made.
        drop(unsafe { Box::from_raw(ctx.cast::<Encapsulation<A>>()) });
    }
}

unsafe extern "C" fn set_ctx_params<A: Set>(ctx: *mut c_void, params: *const Param) -> c_int {
    // SAFETY: OpenSSL passes a context of this KEM, and an array.
    let Some(ctx) = (unsafe { Encapsulation::<A>::from_ptr(ctx) }) else {
        return 0;
    };
    // SAFETY: as above.
    let result = ctx.set_params(unsafe { Params::new(params) });
    ctx.provider.status(result)
}

// Listed so that OpenSSL hands rind a caller's `ikme`, which it refuses,
// rather than dropping it unread.
static SETTABLE_CTX: [Param; 2] = [Param::describe(Some(c"ikme"), OCTET_STRING, 0), Param::END];

unsafe extern "C" fn settable_ctx_params(_ctx: *mut c_void, _provctx: *mut c_void) -> *const Param {
    SETTABLE_CTX.as_ptr()
}
