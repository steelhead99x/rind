// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! Key management for ML-KEM's and ML-DSA's keys, as OpenSSL 3.5's default
//! provider does it in `ml_kem_kmgmt.c` and `ml_dsa_kmgmt.c`.
//!
//! A key's parameters are its seed, `seed`, its expanded private key,
//! `priv`, and its public key, `pub`, each as FIPS 203 and FIPS 204 encode
//! them. That is how OpenSSL moves a key between providers: to use rind with
//! a key its default provider decoded, or to encode a key rind generated.

use core::ffi::{CStr, c_int, c_void};
use std::sync::Arc;

use zeroize::Zeroizing;

use crate::ffi::{
    Callback, INTEGER, OCTET_STRING, Param, SELECT_KEYPAIR, SELECT_PRIVATE_KEY, SELECT_PUBLIC_KEY,
    UNMODIFIED, UTF8_STRING,
};
use crate::params::{Params, ParamsMut};
use crate::provider::{Failure, Provider, Reason};

/// Bytes of a private key, which wipe themselves.
pub(crate) type Secret = Zeroizing<Vec<u8>>;

/// What tells one parameter set's keys from another's.
pub(crate) trait Scheme: Sized + 'static {
    /// The private key rind holds, with its public key, which wipes itself.
    type Private: Send + Sync;
    /// A public key held alone.
    type Public: Send + Sync;

    /// The name OpenSSL knows the parameter set by, for errors.
    const NAME: &'static str;
    /// Tells this set's keys from every other's, X25519's and Ed25519's
    /// included.
    const TAG: u8;
    const SEED_LEN: usize;
    const PRIVATE_LEN: usize;
    const PUBLIC_LEN: usize;
    /// What `bits` reports.
    const BITS: c_int;
    /// What `security-bits` reports.
    const SECURITY_BITS: c_int;
    /// What `max-size` reports: the longest output an operation gives.
    const MAX_SIZE: c_int;
    /// Whether a key takes and gives `encoded-pub-key`, as TLS sets and reads
    /// an ML-KEM key share; otherwise it gives `mandatory-digest`, empty, as
    /// an ML-DSA key does.
    const ENCODED_PUBLIC: bool;
    /// Whether a generation context's seed makes one key, as OpenSSL's
    /// default provider uses an ML-KEM seed, or every key the context
    /// generates, as it uses an ML-DSA one.
    const SEED_ONCE: bool;

    fn generate() -> Result<Self::Private, rind::Error>;
    fn from_seed(seed: &[u8]) -> Result<Self::Private, rind::Error>;
    /// Loads a private key from its seed, its expanded form, or both, which
    /// must agree; at least one is given, each of its length.
    fn load(seed: Option<&[u8]>, expanded: Option<&[u8]>) -> Result<Self::Private, Failure>;
    fn parse_public(bytes: &[u8]) -> Result<Self::Public, rind::Error>;
    fn public_bytes(public: &Self::Public) -> &[u8];
    fn public_of(private: &Self::Private) -> &[u8];
    /// The seed the key was generated or loaded from, if it was.
    fn seed(private: &Self::Private) -> Option<Secret>;
    /// The expanded private key, where rind gives it.
    fn expanded(private: &Self::Private) -> Option<Secret>;
}

/// A key: a public key alone, or a private key with its public key.
pub(crate) enum Key<S: Scheme> {
    Public(S::Public),
    Private(S::Private),
}

impl<S: Scheme> Key<S> {
    pub(crate) fn public(&self) -> &[u8] {
        match self {
            Self::Public(public) => S::public_bytes(public),
            Self::Private(private) => S::public_of(private),
        }
    }

    pub(crate) fn private(&self) -> Option<&S::Private> {
        match self {
            Self::Public(_) => None,
            Self::Private(private) => Some(private),
        }
    }
}

/// What a key object holds.
enum Held<S: Scheme> {
    /// No key, until one is generated or imported.
    Empty,
    Key(Arc<Key<S>>),
    /// An imported key rind refuses, with why: see `import`.
    Refused(String),
}

/// The key object OpenSSL holds: empty until a key is generated or
/// imported into it.
///
/// Operations hold the key itself, so they run on the key they began with
/// even if an import replaces it.
#[repr(C)]
pub(crate) struct KeyData<S: Scheme> {
    // First, so a pointer to any key object of this provider's reads it.
    tag: u8,
    pub(crate) provider: Arc<Provider>,
    held: Held<S>,
}

impl<S: Scheme> KeyData<S> {
    fn boxed(provider: Arc<Provider>, held: Held<S>) -> *mut c_void {
        Box::into_raw(Box::new(Self {
            tag: S::TAG,
            provider,
            held,
        }))
        .cast()
    }

    /// The key a query reads, which finds none in a refused key.
    fn key(&self) -> Option<&Key<S>> {
        match &self.held {
            Held::Key(key) => Some(key),
            Held::Empty | Held::Refused(_) => None,
        }
    }

    /// The key an operation runs on, or why there is none.
    pub(crate) fn operand(&self) -> Result<Arc<Key<S>>, Failure> {
        match &self.held {
            Held::Key(key) => Ok(key.clone()),
            Held::Empty => Err(Failure::invalid("no key is set")),
            Held::Refused(why) => Err(refused(why)),
        }
    }

    /// The key object OpenSSL passes, or `None` if it is null or another
    /// parameter set's.
    ///
    /// # Safety
    ///
    /// `keydata` is null or a key object of this provider's that OpenSSL has
    /// not freed, and no one mutates it for `'a`.
    pub(crate) unsafe fn from_ptr<'a>(keydata: *const c_void) -> Option<&'a Self> {
        // SAFETY: every key object of this provider's starts with its tag,
        // per the caller.
        if keydata.is_null() || unsafe { *keydata.cast::<u8>() } != S::TAG {
            return None;
        }
        // SAFETY: the tag says it is a `KeyData<S>`.
        Some(unsafe { &*keydata.cast::<Self>() })
    }

    /// As [`Self::from_ptr`], to mutate.
    ///
    /// # Safety
    ///
    /// As for [`Self::from_ptr`], and no one else reads it for `'a`.
    unsafe fn from_mut_ptr<'a>(keydata: *mut c_void) -> Option<&'a mut Self> {
        // SAFETY: as for `from_ptr`.
        if keydata.is_null() || unsafe { *keydata.cast::<u8>() } != S::TAG {
            return None;
        }
        // SAFETY: the tag says it is a `KeyData<S>`, which the caller lends.
        Some(unsafe { &mut *keydata.cast::<Self>() })
    }
}

/// Why a refused key fails each use.
fn refused(why: &str) -> Failure {
    Failure::Raise(Reason::KeyRejected, why.into())
}

/// A key generation in progress.
struct Gen<S: Scheme> {
    provider: Arc<Provider>,
    selection: c_int,
    seed: Option<Secret>,
    _scheme: core::marker::PhantomData<S>,
}

/// The key management functions for `$scheme`, as a dispatch table.
macro_rules! functions {
    ($scheme:ty) => {{
        use $crate::ffi::*;
        use $crate::pq_keymgmt as km;
        [
            entry!(KEYMGMT_NEW, km::new::<$scheme>, KeymgmtNew),
            entry!(KEYMGMT_FREE, km::free::<$scheme>, KeymgmtFree),
            entry!(
                KEYMGMT_GET_PARAMS,
                km::get_params::<$scheme>,
                KeymgmtGetParams
            ),
            entry!(
                KEYMGMT_GETTABLE_PARAMS,
                km::gettable_params::<$scheme>,
                KeymgmtGettableParams
            ),
            entry!(
                KEYMGMT_SET_PARAMS,
                km::set_params::<$scheme>,
                KeymgmtSetParams
            ),
            entry!(
                KEYMGMT_SETTABLE_PARAMS,
                km::settable_params::<$scheme>,
                KeymgmtSettableParams
            ),
            entry!(KEYMGMT_HAS, km::has::<$scheme>, KeymgmtHas),
            entry!(KEYMGMT_MATCH, km::matches::<$scheme>, KeymgmtMatch),
            entry!(KEYMGMT_VALIDATE, km::validate::<$scheme>, KeymgmtValidate),
            entry!(KEYMGMT_IMPORT, km::import::<$scheme>, KeymgmtImport),
            entry!(KEYMGMT_IMPORT_TYPES, km::types, KeymgmtTypes),
            entry!(KEYMGMT_EXPORT, km::export::<$scheme>, KeymgmtExport),
            entry!(KEYMGMT_EXPORT_TYPES, km::types, KeymgmtTypes),
            entry!(KEYMGMT_GEN_INIT, km::gen_init::<$scheme>, KeymgmtGenInit),
            entry!(
                KEYMGMT_GEN_SET_PARAMS,
                km::gen_set_params::<$scheme>,
                KeymgmtGenSetParams
            ),
            entry!(
                KEYMGMT_GEN_SETTABLE_PARAMS,
                km::gen_settable_params,
                KeymgmtGenSettableParams
            ),
            entry!(KEYMGMT_GEN, km::generate::<$scheme>, KeymgmtGen),
            entry!(
                KEYMGMT_GEN_CLEANUP,
                km::gen_cleanup::<$scheme>,
                KeymgmtGenCleanup
            ),
            entry!(KEYMGMT_DUP, km::dup::<$scheme>, KeymgmtDup),
            Dispatch::END,
        ]
    }};
}

pub(crate) use functions;

pub(crate) unsafe extern "C" fn new<S: Scheme>(provctx: *mut c_void) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    KeyData::<S>::boxed(provider, Held::Empty)
}

pub(crate) unsafe extern "C" fn free<S: Scheme>(keydata: *mut c_void) {
    // SAFETY: OpenSSL frees a key object it holds, which no one uses after.
    if unsafe { KeyData::<S>::from_ptr(keydata) }.is_some() {
        // SAFETY: as above; `new`, `generate`, or `dup` boxed it.
        drop(unsafe { Box::from_raw(keydata.cast::<KeyData<S>>()) });
    }
}

pub(crate) unsafe extern "C" fn has<S: Scheme>(keydata: *const c_void, selection: c_int) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::<S>::from_ptr(keydata) }) else {
        return 0;
    };
    let key = data.key();
    // Neither scheme has domain parameters, so it always has those it needs.
    let public = selection & SELECT_PUBLIC_KEY == 0 || key.is_some();
    let private = selection & SELECT_PRIVATE_KEY == 0 || key.and_then(Key::private).is_some();
    (public && private).into()
}

/// Two keys match on their public keys, the only material OpenSSL's default
/// provider compares for either scheme; a selection of no key matches.
pub(crate) unsafe extern "C" fn matches<S: Scheme>(
    keydata1: *const c_void,
    keydata2: *const c_void,
    selection: c_int,
) -> c_int {
    // SAFETY: OpenSSL passes key objects it holds.
    let (Some(a), Some(b)) = (unsafe {
        (
            KeyData::<S>::from_ptr(keydata1),
            KeyData::<S>::from_ptr(keydata2),
        )
    }) else {
        return 0;
    };
    if selection & SELECT_KEYPAIR == 0 {
        return 1;
    }
    match (a.key(), b.key()) {
        (Some(a), Some(b)) => (a.public() == b.public()).into(),
        _ => 0,
    }
}

pub(crate) unsafe extern "C" fn validate<S: Scheme>(
    keydata: *const c_void,
    selection: c_int,
    _checktype: c_int,
) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::<S>::from_ptr(keydata) }) else {
        return 0;
    };
    if let Held::Refused(why) = &data.held {
        return data.provider.status(Err(refused(why)));
    }
    // A private key's public key is the one rind computed or checked when it
    // loaded the key, so a key pair is always consistent.
    // SAFETY: as above.
    unsafe { has::<S>(keydata, selection) }
}

static TYPES: [Param; 4] = [
    Param::describe(Some(c"seed"), OCTET_STRING, 0),
    Param::describe(Some(c"priv"), OCTET_STRING, 0),
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::END,
];

pub(crate) unsafe extern "C" fn types(selection: c_int) -> *const Param {
    match selection & SELECT_KEYPAIR {
        0 => core::ptr::null(),
        _ => TYPES.as_ptr(),
    }
}

pub(crate) unsafe extern "C" fn import<S: Scheme>(
    keydata: *mut c_void,
    selection: c_int,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL imports into a key object it holds, and passes an
    // array.
    let (Some(data), params) = (unsafe { KeyData::<S>::from_mut_ptr(keydata) }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    if selection & SELECT_KEYPAIR == 0 {
        return 0;
    }
    // A key rind refuses imports, so that its every use fails with rind's
    // error: OpenSSL moves a key here from another provider, which may hold
    // a key rind refuses, before each use, and runs the use on that provider
    // when the move fails. A parameter of the wrong length or type fails
    // the import, as it does on the default provider, which so holds no such
    // key.
    let result = load::<S>(selection, params).map(|held| data.held = held);
    data.provider.status(result)
}

/// The key `params` hold for `selection`: a private key, from its seed or
/// expanded form, which any public key beside must be the public key of, or
/// a public key alone.
fn load<S: Scheme>(selection: c_int, params: Params<'_>) -> Result<Held<S>, Failure> {
    let bytes = |name: &CStr, len: usize| {
        let Some(param) = params.find(name) else {
            return Ok(None);
        };
        match param.octets() {
            Some([]) => Ok(None),
            Some(bytes) if bytes.len() == len => Ok(Some(bytes)),
            _ => Err(Failure::invalid(&format!(
                "{} must be a {len}-byte octet string for {}",
                name.to_string_lossy(),
                S::NAME
            ))),
        }
    };
    let public = bytes(c"pub", S::PUBLIC_LEN)?;
    let (seed, expanded) = match selection & SELECT_PRIVATE_KEY {
        0 => (None, None),
        _ => (
            bytes(c"seed", S::SEED_LEN)?,
            bytes(c"priv", S::PRIVATE_LEN)?,
        ),
    };
    let key = match (seed, expanded, public) {
        (None, None, None) => {
            return Err(Failure::invalid("none of seed, priv, or pub is given"));
        }
        (None, None, Some(public)) => S::parse_public(public).map(Key::Public),
        (seed, expanded, public) => match S::load(seed, expanded) {
            Ok(private) if public.is_some_and(|public| public != S::public_of(&private)) => {
                return Ok(Held::Refused(
                    "the public key is not the private key's".into(),
                ));
            }
            Ok(private) => Ok(Key::Private(private)),
            Err(Failure::Raise(Reason::KeyRejected, why)) => return Ok(Held::Refused(why)),
            Err(failure) => return Err(failure),
        },
    };
    match key {
        Ok(key) => Ok(Held::Key(Arc::new(key))),
        Err(rind::Error::KeyRejected(why)) => Ok(Held::Refused(why.to_string())),
        Err(error) => Err(error.into()),
    }
}

pub(crate) unsafe extern "C" fn export<S: Scheme>(
    keydata: *mut c_void,
    selection: c_int,
    callback: Option<Callback>,
    arg: *mut c_void,
) -> c_int {
    // SAFETY: OpenSSL exports a key object it holds.
    let (Some(data), Some(callback)) = (unsafe { KeyData::<S>::from_ptr(keydata) }, callback)
    else {
        return 0;
    };
    let key = match &data.held {
        Held::Key(key) => key,
        Held::Empty => return 0,
        Held::Refused(why) => return data.provider.status(Err(refused(why))),
    };
    if selection & SELECT_KEYPAIR == 0 {
        return 0;
    }
    // The secrets wipe themselves once the callback has copied them.
    let (seed, expanded) = match (selection & SELECT_PRIVATE_KEY, key.private()) {
        (0, _) | (_, None) => (None, None),
        (_, Some(private)) => (S::seed(private), S::expanded(private)),
    };
    let octets = |key: &'static CStr, bytes: &[u8]| Param {
        key: key.as_ptr(),
        data_type: OCTET_STRING,
        // The callback only reads it.
        data: bytes.as_ptr().cast_mut().cast(),
        data_size: bytes.len(),
        return_size: UNMODIFIED,
    };
    let mut params = Vec::with_capacity(4);
    params.extend(seed.as_ref().map(|seed| octets(c"seed", seed)));
    params.extend(expanded.as_ref().map(|expanded| octets(c"priv", expanded)));
    if selection & SELECT_PUBLIC_KEY != 0 {
        params.push(octets(c"pub", key.public()));
    }
    if params.is_empty() {
        return 0;
    }
    params.push(Param::END);
    // SAFETY: the callback is OpenSSL's, and takes the terminated array.
    unsafe { callback(params.as_ptr(), arg) }
}

pub(crate) unsafe extern "C" fn get_params<S: Scheme>(
    keydata: *mut c_void,
    params: *mut Param,
) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds and a writable array.
    let (Some(data), mut params) = (unsafe { KeyData::<S>::from_ptr(keydata) }, unsafe {
        ParamsMut::new(params)
    }) else {
        return 0;
    };
    let sizes = [
        (c"bits", S::BITS),
        (c"security-bits", S::SECURITY_BITS),
        (c"max-size", S::MAX_SIZE),
    ];
    for (name, value) in sizes {
        if let Some(param) = params.find(name)
            && !param.set_int(value)
        {
            return 0;
        }
    }
    // ML-DSA hashes the message itself, so a signature takes no digest.
    if !S::ENCODED_PUBLIC
        && let Some(param) = params.find(c"mandatory-digest")
        && !param.set_utf8(c"")
    {
        return 0;
    }
    let Some(key) = data.key() else {
        return 1;
    };
    // A private encoding is a copy of the key, made only when asked for.
    let (want_seed, want_expanded) = (
        params.find(c"seed").is_some(),
        params.find(c"priv").is_some(),
    );
    let mut set = |name: &CStr, bytes: &[u8]| params.find(name).is_none_or(|p| p.set_octets(bytes));
    if !set(c"pub", key.public()) {
        return 0;
    }
    if S::ENCODED_PUBLIC && !set(c"encoded-pub-key", key.public()) {
        return 0;
    }
    if let Some(private) = key.private() {
        if want_seed
            && let Some(seed) = S::seed(private)
            && !set(c"seed", &seed)
        {
            return 0;
        }
        if want_expanded
            && let Some(expanded) = S::expanded(private)
            && !set(c"priv", &expanded)
        {
            return 0;
        }
    }
    1
}

static GETTABLE_ENCODED: [Param; 8] = [
    Param::describe(Some(c"bits"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"security-bits"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"max-size"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"seed"), OCTET_STRING, 0),
    Param::describe(Some(c"priv"), OCTET_STRING, 0),
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::describe(Some(c"encoded-pub-key"), OCTET_STRING, 0),
    Param::END,
];

static GETTABLE_DIGEST: [Param; 8] = [
    Param::describe(Some(c"bits"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"security-bits"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"max-size"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"mandatory-digest"), UTF8_STRING, 0),
    Param::describe(Some(c"seed"), OCTET_STRING, 0),
    Param::describe(Some(c"priv"), OCTET_STRING, 0),
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::END,
];

pub(crate) unsafe extern "C" fn gettable_params<S: Scheme>(_provctx: *mut c_void) -> *const Param {
    match S::ENCODED_PUBLIC {
        true => GETTABLE_ENCODED.as_ptr(),
        false => GETTABLE_DIGEST.as_ptr(),
    }
}

pub(crate) unsafe extern "C" fn set_params<S: Scheme>(
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL sets parameters on a key object it holds, and passes
    // an array.
    let (Some(data), params) = (unsafe { KeyData::<S>::from_mut_ptr(keydata) }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    let result = (|| {
        // TLS gives a peer's key share this way, into an empty key.
        let Some(param) = params
            .find(c"encoded-pub-key")
            .filter(|_| S::ENCODED_PUBLIC)
        else {
            return Ok(());
        };
        let public = match param.octets() {
            Some(bytes) if bytes.len() == S::PUBLIC_LEN => bytes,
            _ => {
                return Err(Failure::invalid(&format!(
                    "encoded-pub-key must be a {}-byte octet string",
                    S::PUBLIC_LEN
                )));
            }
        };
        if !matches!(data.held, Held::Empty) {
            return Err(Failure::invalid(&format!(
                "{} keys cannot be changed",
                S::NAME
            )));
        }
        data.held = Held::Key(Arc::new(Key::Public(S::parse_public(public)?)));
        Ok(())
    })();
    data.provider.status(result)
}

static SETTABLE_ENCODED: [Param; 2] = [
    Param::describe(Some(c"encoded-pub-key"), OCTET_STRING, 0),
    Param::END,
];

static SETTABLE_NONE: [Param; 1] = [Param::END];

pub(crate) unsafe extern "C" fn settable_params<S: Scheme>(_provctx: *mut c_void) -> *const Param {
    match S::ENCODED_PUBLIC {
        true => SETTABLE_ENCODED.as_ptr(),
        false => SETTABLE_NONE.as_ptr(),
    }
}

pub(crate) unsafe extern "C" fn gen_init<S: Scheme>(
    provctx: *mut c_void,
    selection: c_int,
    params: *const Param,
) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    let generation = Box::into_raw(Box::new(Gen::<S> {
        provider,
        selection,
        seed: None,
        _scheme: core::marker::PhantomData,
    }));
    // SAFETY: `generation` is the context just made, and OpenSSL passes an
    // array.
    if unsafe { gen_set_params::<S>(generation.cast(), params) } == 0 {
        // SAFETY: as above; no one else holds it.
        drop(unsafe { Box::from_raw(generation) });
        return core::ptr::null_mut();
    }
    generation.cast()
}

pub(crate) unsafe extern "C" fn gen_set_params<S: Scheme>(
    genctx: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL passes the context `gen_init` made, and an array.
    let (Some(generation), params) = (unsafe { genctx.cast::<Gen<S>>().as_mut() }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    let result = (|| {
        if params
            .find(c"properties")
            .is_some_and(|properties| properties.utf8().is_none())
        {
            return Err(Failure::invalid("properties must be a UTF-8 string"));
        }
        if let Some(seed) = params.find(c"seed") {
            match seed.octets() {
                Some(seed) if seed.len() == S::SEED_LEN => {
                    generation.seed = Some(Zeroizing::new(seed.to_vec()));
                }
                // OpenSSL's default provider drops the seed it had, so
                // the context generates fresh keys.
                _ => {
                    generation.seed = None;
                    return Err(Failure::invalid(&format!(
                        "seed must be a {}-byte octet string",
                        S::SEED_LEN
                    )));
                }
            }
        }
        Ok(())
    })();
    generation.provider.status(result)
}

static GEN_SETTABLE: [Param; 3] = [
    Param::describe(Some(c"properties"), UTF8_STRING, 0),
    Param::describe(Some(c"seed"), OCTET_STRING, 0),
    Param::END,
];

pub(crate) unsafe extern "C" fn gen_settable_params(
    _genctx: *mut c_void,
    _provctx: *mut c_void,
) -> *const Param {
    GEN_SETTABLE.as_ptr()
}

pub(crate) unsafe extern "C" fn generate<S: Scheme>(
    genctx: *mut c_void,
    _callback: Option<Callback>,
    _arg: *mut c_void,
) -> *mut c_void {
    // SAFETY: OpenSSL passes the context `gen_init` made.
    let Some(generation) = (unsafe { genctx.cast::<Gen<S>>().as_mut() }) else {
        return core::ptr::null_mut();
    };
    let provider = generation.provider.clone();
    // Asked for no key, as for parameters alone, it gives an empty key, which
    // TLS then gives a peer's key share.
    if generation.selection & SELECT_KEYPAIR == 0 {
        return KeyData::<S>::boxed(provider, Held::Empty);
    }
    let seed = match S::SEED_ONCE {
        true => generation.seed.take(),
        false => generation.seed.clone(),
    };
    let private = match seed {
        Some(seed) => S::from_seed(&seed),
        None => S::generate(),
    };
    match private {
        Ok(private) => KeyData::<S>::boxed(provider, Held::Key(Arc::new(Key::Private(private)))),
        Err(error) => {
            provider.status(Err(error.into()));
            core::ptr::null_mut()
        }
    }
}

pub(crate) unsafe extern "C" fn gen_cleanup<S: Scheme>(genctx: *mut c_void) {
    if !genctx.is_null() {
        // SAFETY: OpenSSL frees the context `gen_init` made.
        drop(unsafe { Box::from_raw(genctx.cast::<Gen<S>>()) });
    }
}

pub(crate) unsafe extern "C" fn dup<S: Scheme>(
    keydata: *const c_void,
    selection: c_int,
) -> *mut c_void {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::<S>::from_ptr(keydata) }) else {
        return core::ptr::null_mut();
    };
    let held = match &data.held {
        Held::Key(key) => match (&**key, selection & SELECT_KEYPAIR) {
            (Key::Private(_), SELECT_KEYPAIR | SELECT_PRIVATE_KEY)
            | (Key::Public(_), SELECT_KEYPAIR | SELECT_PUBLIC_KEY) => Held::Key(key.clone()),
            (Key::Private(private), SELECT_PUBLIC_KEY) => {
                match S::parse_public(S::public_of(private)) {
                    Ok(public) => Held::Key(Arc::new(Key::Public(public))),
                    Err(error) => {
                        data.provider.status(Err(error.into()));
                        return core::ptr::null_mut();
                    }
                }
            }
            _ => Held::Empty,
        },
        // A copy of either half fails each use as the original does.
        Held::Refused(why) if selection & SELECT_KEYPAIR != 0 => Held::Refused(why.clone()),
        Held::Refused(_) | Held::Empty => Held::Empty,
    };
    KeyData::<S>::boxed(data.provider.clone(), held)
}
