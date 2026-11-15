// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! Key management for the 32-byte keys of X25519 and Ed25519, as OpenSSL's
//! default provider does it in `ecx_kmgmt.c`.
//!
//! A key's parameters are its raw halves, `pub` and `priv`, which is how
//! OpenSSL moves a key between providers: to use rind with a key its default
//! provider decoded, or to encode a key rind generated.

use core::ffi::{CStr, c_int, c_void};
use std::sync::Arc;

use zeroize::Zeroizing;

use crate::ffi::{
    Callback, OCTET_STRING, Param, SELECT_KEYPAIR, SELECT_PRIVATE_KEY, SELECT_PUBLIC_KEY,
    UNMODIFIED, UTF8_STRING,
};
use crate::params::{Params, ParamsMut};
use crate::provider::{Failure, Provider};

/// The length of every key, public or private.
pub(crate) const LEN: usize = 32;

/// What tells X25519's keys from Ed25519's.
pub(crate) trait Kind: Sized + 'static {
    /// The private key rind holds, which wipes itself.
    type Private: Send + Sync;
    /// A public key held alone.
    type Public: Send + Sync;
    /// A private key's bytes, as `priv` gives them, which wipe themselves.
    type Secret: AsRef<[u8]>;

    /// What `bits` reports.
    const BITS: c_int;
    /// What `security-bits` reports.
    const SECURITY_BITS: c_int;
    /// What `max-size` reports: the longest output an operation gives.
    const MAX_SIZE: c_int;
    /// The group name key generation takes, or `None` if it takes none.
    const GROUP: Option<&'static [u8]>;
    /// Tells this kind's keys from the other's.
    const TAG: u8;

    /// Generates a private key, from `ikm` as RFC 9180's `DeriveKeyPair`
    /// does if it is given.
    fn generate(ikm: Option<&[u8]>) -> Result<Self::Private, Failure>;
    /// Loads a private key from its 32 bytes.
    fn load(private: &[u8]) -> Result<Self::Private, rind::Error>;
    /// Holds a public key's 32 bytes.
    fn public(bytes: [u8; LEN]) -> Self::Public;
    fn public_bytes(public: &Self::Public) -> &[u8];
    fn public_of(private: &Self::Private) -> &[u8];
    fn private_bytes(private: &Self::Private) -> Self::Secret;
    /// Fills the parameters only this kind gives.
    fn get_params(key: Option<&Key<Self>>, params: &mut ParamsMut<'_>) -> bool;
    /// Sets the parameters only this kind takes.
    fn set_params(data: &mut KeyData<Self>, params: Params<'_>) -> bool;
    /// The parameters `get_params` gives, ending in `Param::END`.
    fn gettable() -> &'static [Param];
    /// The parameters `set_params` takes, ending in `Param::END`.
    fn settable() -> &'static [Param];
}

/// A key: a public key alone, or a private key with its public key.
pub(crate) enum Key<K: Kind> {
    Public(K::Public),
    Private(K::Private),
}

impl<K: Kind> Key<K> {
    pub(crate) fn public(&self) -> &[u8] {
        match self {
            Self::Public(public) => K::public_bytes(public),
            Self::Private(private) => K::public_of(private),
        }
    }

    pub(crate) fn private(&self) -> Option<&K::Private> {
        match self {
            Self::Public(_) => None,
            Self::Private(private) => Some(private),
        }
    }
}

/// What a key object holds.
enum Held<K: Kind> {
    /// No key, until one is generated or imported.
    Empty,
    Key(Arc<Key<K>>),
    /// An imported private key whose public key is not its own: see
    /// `import`.
    Mismatched,
}

/// The key object OpenSSL holds: empty until a key is generated or
/// imported into it.
///
/// Operations hold the key itself, so they run on the key they began with
/// even if an import replaces it.
#[repr(C)]
pub(crate) struct KeyData<K: Kind> {
    // First, so a pointer to any `KeyData` reads it.
    tag: u8,
    pub(crate) provider: Arc<Provider>,
    held: Held<K>,
}

impl<K: Kind> KeyData<K> {
    fn boxed(provider: Arc<Provider>, held: Held<K>) -> *mut c_void {
        Box::into_raw(Box::new(Self {
            tag: K::TAG,
            provider,
            held,
        }))
        .cast()
    }

    /// The key a query reads, which finds none in a mismatched key.
    pub(crate) fn key(&self) -> Option<&Key<K>> {
        match &self.held {
            Held::Key(key) => Some(key),
            Held::Empty | Held::Mismatched => None,
        }
    }

    /// The key an operation runs on, or why there is none.
    pub(crate) fn operand(&self) -> Result<Arc<Key<K>>, Failure> {
        match &self.held {
            Held::Key(key) => Ok(key.clone()),
            Held::Empty => Err(Failure::invalid("no key is set")),
            Held::Mismatched => Err(mismatched()),
        }
    }

    /// Holds `key` in place of whatever it held.
    pub(crate) fn set(&mut self, key: Key<K>) {
        self.held = Held::Key(Arc::new(key));
    }

    /// The key object OpenSSL passes, or `None` if it is null or of the
    /// other kind.
    ///
    /// # Safety
    ///
    /// `keydata` is null or a key object of this provider's that OpenSSL has
    /// not freed, and no one mutates it for `'a`.
    pub(crate) unsafe fn from_ptr<'a>(keydata: *const c_void) -> Option<&'a Self> {
        // SAFETY: every `KeyData` starts with its tag, per the caller.
        if keydata.is_null() || unsafe { *keydata.cast::<u8>() } != K::TAG {
            return None;
        }
        // SAFETY: the tag says it is a `KeyData<K>`.
        Some(unsafe { &*keydata.cast::<Self>() })
    }

    /// As [`Self::from_ptr`], to mutate.
    ///
    /// # Safety
    ///
    /// As for [`Self::from_ptr`], and no one else reads it for `'a`.
    unsafe fn from_mut_ptr<'a>(keydata: *mut c_void) -> Option<&'a mut Self> {
        // SAFETY: as for `from_ptr`.
        if keydata.is_null() || unsafe { *keydata.cast::<u8>() } != K::TAG {
            return None;
        }
        // SAFETY: the tag says it is a `KeyData<K>`, which the caller lends.
        Some(unsafe { &mut *keydata.cast::<Self>() })
    }
}

/// A key generation in progress.
struct Gen<K: Kind> {
    provider: Arc<Provider>,
    selection: c_int,
    ikm: Option<Zeroizing<Vec<u8>>>,
    _kind: core::marker::PhantomData<K>,
}

/// The key management functions for `$kind`, as a dispatch table.
macro_rules! functions {
    ($kind:ty) => {{
        use $crate::ffi::*;
        use $crate::keymgmt;
        [
            entry!(KEYMGMT_NEW, keymgmt::new::<$kind>, KeymgmtNew),
            entry!(KEYMGMT_FREE, keymgmt::free::<$kind>, KeymgmtFree),
            entry!(
                KEYMGMT_GET_PARAMS,
                keymgmt::get_params::<$kind>,
                KeymgmtGetParams
            ),
            entry!(
                KEYMGMT_GETTABLE_PARAMS,
                keymgmt::gettable_params::<$kind>,
                KeymgmtGettableParams
            ),
            entry!(
                KEYMGMT_SET_PARAMS,
                keymgmt::set_params::<$kind>,
                KeymgmtSetParams
            ),
            entry!(
                KEYMGMT_SETTABLE_PARAMS,
                keymgmt::settable_params::<$kind>,
                KeymgmtSettableParams
            ),
            entry!(KEYMGMT_HAS, keymgmt::has::<$kind>, KeymgmtHas),
            entry!(KEYMGMT_MATCH, keymgmt::matches::<$kind>, KeymgmtMatch),
            entry!(
                KEYMGMT_VALIDATE,
                keymgmt::validate::<$kind>,
                KeymgmtValidate
            ),
            entry!(KEYMGMT_IMPORT, keymgmt::import::<$kind>, KeymgmtImport),
            entry!(KEYMGMT_IMPORT_TYPES, keymgmt::types, KeymgmtTypes),
            entry!(KEYMGMT_EXPORT, keymgmt::export::<$kind>, KeymgmtExport),
            entry!(KEYMGMT_EXPORT_TYPES, keymgmt::types, KeymgmtTypes),
            entry!(KEYMGMT_GEN_INIT, keymgmt::gen_init::<$kind>, KeymgmtGenInit),
            entry!(
                KEYMGMT_GEN_SET_PARAMS,
                keymgmt::gen_set_params::<$kind>,
                KeymgmtGenSetParams
            ),
            entry!(
                KEYMGMT_GEN_SETTABLE_PARAMS,
                keymgmt::gen_settable_params,
                KeymgmtGenSettableParams
            ),
            entry!(KEYMGMT_GEN, keymgmt::generate::<$kind>, KeymgmtGen),
            entry!(
                KEYMGMT_GEN_CLEANUP,
                keymgmt::gen_cleanup::<$kind>,
                KeymgmtGenCleanup
            ),
            entry!(KEYMGMT_DUP, keymgmt::dup::<$kind>, KeymgmtDup),
            Dispatch::END,
        ]
    }};
}

pub(crate) use functions;

pub(crate) unsafe extern "C" fn new<K: Kind>(provctx: *mut c_void) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    KeyData::<K>::boxed(provider, Held::Empty)
}

pub(crate) unsafe extern "C" fn free<K: Kind>(keydata: *mut c_void) {
    // SAFETY: OpenSSL frees a key object it holds, which no one uses after.
    if unsafe { KeyData::<K>::from_ptr(keydata) }.is_some() {
        // SAFETY: as above; `new`, `generate`, or `dup` boxed it.
        drop(unsafe { Box::from_raw(keydata.cast::<KeyData<K>>()) });
    }
}

pub(crate) unsafe extern "C" fn has<K: Kind>(keydata: *const c_void, selection: c_int) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::<K>::from_ptr(keydata) }) else {
        return 0;
    };
    let key = data.key();
    // Neither kind has domain parameters, so it always has those it needs.
    let public = selection & SELECT_PUBLIC_KEY == 0 || key.is_some();
    let private = selection & SELECT_PRIVATE_KEY == 0 || key.and_then(Key::private).is_some();
    (public && private).into()
}

pub(crate) unsafe extern "C" fn matches<K: Kind>(
    keydata1: *const c_void,
    keydata2: *const c_void,
    selection: c_int,
) -> c_int {
    // SAFETY: OpenSSL passes key objects it holds.
    let (Some(a), Some(b)) = (unsafe {
        (
            KeyData::<K>::from_ptr(keydata1),
            KeyData::<K>::from_ptr(keydata2),
        )
    }) else {
        return 0;
    };
    equal(a.key(), b.key(), selection).into()
}

/// Whether two keys match on `selection`: the public keys decide when both
/// are asked for and present, else the private keys, as OpenSSL's do; a
/// selection neither key can answer does not match.
fn equal<K: Kind>(a: Option<&Key<K>>, b: Option<&Key<K>>, selection: c_int) -> bool {
    if selection & SELECT_KEYPAIR == 0 {
        return true;
    }
    let equal = match (a, b) {
        (Some(a), Some(b)) if selection & SELECT_PUBLIC_KEY != 0 => Some(a.public() == b.public()),
        _ if selection & SELECT_PRIVATE_KEY != 0 => {
            match (a.and_then(Key::private), b.and_then(Key::private)) {
                (Some(a), Some(b)) => Some(
                    rind::constant_time::verify(
                        K::private_bytes(a).as_ref(),
                        K::private_bytes(b).as_ref(),
                    )
                    .is_ok(),
                ),
                _ => None,
            }
        }
        _ => None,
    };
    equal == Some(true)
}

pub(crate) unsafe extern "C" fn validate<K: Kind>(
    keydata: *const c_void,
    selection: c_int,
    _checktype: c_int,
) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::<K>::from_ptr(keydata) }) else {
        return 0;
    };
    if let Held::Mismatched = data.held {
        return data.provider.status(Err(mismatched()));
    }
    // A private key's public key is the one rind computed or checked when it
    // loaded the key, so a key pair is always consistent.
    // SAFETY: as above.
    unsafe { has::<K>(keydata, selection) }
}

static TYPES: [Param; 3] = [
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::describe(Some(c"priv"), OCTET_STRING, 0),
    Param::END,
];

pub(crate) unsafe extern "C" fn types(selection: c_int) -> *const Param {
    match selection & SELECT_KEYPAIR {
        0 => core::ptr::null(),
        _ => TYPES.as_ptr(),
    }
}

pub(crate) unsafe extern "C" fn import<K: Kind>(
    keydata: *mut c_void,
    selection: c_int,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL imports into a key object it holds, and passes an
    // array.
    let (Some(data), params) = (unsafe { KeyData::<K>::from_mut_ptr(keydata) }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    if selection & SELECT_KEYPAIR == 0 {
        return 0;
    }
    // A mismatched key imports, so that its every use fails with rind's
    // error: OpenSSL moves a key here from another provider, which may hold
    // it mismatched, before each use, and runs the use on that provider when
    // the move fails.
    let result = load::<K>(selection, params).map(|held| data.held = held);
    data.provider.status(result)
}

/// The key `params` hold for `selection`: a private key, `Mismatched` unless
/// any public key beside it is its own, or a public key alone.
fn load<K: Kind>(selection: c_int, params: Params<'_>) -> Result<Held<K>, Failure> {
    fn bytes<'a>(param: &'a Param, what: &str) -> Result<&'a [u8], Failure> {
        match param.octets() {
            Some(bytes) if bytes.len() == LEN => Ok(bytes),
            _ => Err(Failure::invalid(&format!(
                "{what} must be a {LEN}-byte octet string"
            ))),
        }
    }
    let public = params
        .find(c"pub")
        .map(|param| bytes(param, "pub"))
        .transpose()?;
    let private = match selection & SELECT_PRIVATE_KEY {
        0 => None,
        _ => params
            .find(c"priv")
            .map(|param| bytes(param, "priv"))
            .transpose()?,
    };
    let key = match (private, public) {
        (Some(private), public) => {
            let private = K::load(private)?;
            if public.is_some_and(|public| public != K::public_of(&private)) {
                return Ok(Held::Mismatched);
            }
            Key::Private(private)
        }
        (None, Some(public)) => Key::Public(K::public(
            public.try_into().expect("checked to be LEN bytes"),
        )),
        (None, None) => return Err(Failure::invalid("neither pub nor priv is given")),
    };
    Ok(Held::Key(Arc::new(key)))
}

/// Why a mismatched key fails each use.
fn mismatched() -> Failure {
    Failure::Raise(
        crate::provider::Reason::KeyRejected,
        "the public key is not the private key's".into(),
    )
}

pub(crate) unsafe extern "C" fn export<K: Kind>(
    keydata: *mut c_void,
    selection: c_int,
    callback: Option<Callback>,
    arg: *mut c_void,
) -> c_int {
    // SAFETY: OpenSSL exports a key object it holds.
    let (Some(data), Some(callback)) = (unsafe { KeyData::<K>::from_ptr(keydata) }, callback)
    else {
        return 0;
    };
    let key = match &data.held {
        Held::Key(key) => key,
        Held::Empty => return 0,
        Held::Mismatched => return data.provider.status(Err(mismatched())),
    };
    if selection & SELECT_KEYPAIR == 0 {
        return 0;
    }
    // The secret wipes itself once the callback has copied it.
    let secret = match selection & SELECT_PRIVATE_KEY {
        0 => None,
        _ => key.private().map(K::private_bytes),
    };
    let octets = |key: &'static CStr, bytes: &[u8]| Param {
        key: key.as_ptr(),
        data_type: OCTET_STRING,
        // The callback only reads it.
        data: bytes.as_ptr().cast_mut().cast(),
        data_size: bytes.len(),
        return_size: UNMODIFIED,
    };
    let mut params = vec![octets(c"pub", key.public())];
    params.extend(
        secret
            .as_ref()
            .map(|secret| octets(c"priv", secret.as_ref())),
    );
    params.push(Param::END);
    // SAFETY: the callback is OpenSSL's, and takes the terminated array.
    unsafe { callback(params.as_ptr(), arg) }
}

pub(crate) unsafe extern "C" fn get_params<K: Kind>(
    keydata: *mut c_void,
    params: *mut Param,
) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds and a writable array.
    let (Some(data), mut params) = (unsafe { KeyData::<K>::from_ptr(keydata) }, unsafe {
        ParamsMut::new(params)
    }) else {
        return 0;
    };
    let key = data.key();
    let sizes = [
        (c"bits", K::BITS),
        (c"security-bits", K::SECURITY_BITS),
        (c"max-size", K::MAX_SIZE),
    ];
    for (name, value) in sizes {
        if let Some(param) = params.find(name)
            && !param.set_int(value)
        {
            return 0;
        }
    }
    if !K::get_params(key, &mut params) {
        return 0;
    }
    let Some(key) = key else {
        return 1;
    };
    if let Some(param) = params.find(c"pub")
        && !param.set_octets(key.public())
    {
        return 0;
    }
    if let Some(private) = key.private()
        && let Some(param) = params.find(c"priv")
        && !param.set_octets(K::private_bytes(private).as_ref())
    {
        return 0;
    }
    1
}

pub(crate) unsafe extern "C" fn gettable_params<K: Kind>(_provctx: *mut c_void) -> *const Param {
    K::gettable().as_ptr()
}

pub(crate) unsafe extern "C" fn set_params<K: Kind>(
    keydata: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL sets parameters on a key object it holds, and passes
    // an array.
    let (Some(data), params) = (unsafe { KeyData::<K>::from_mut_ptr(keydata) }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    K::set_params(data, params).into()
}

pub(crate) unsafe extern "C" fn settable_params<K: Kind>(_provctx: *mut c_void) -> *const Param {
    K::settable().as_ptr()
}

pub(crate) unsafe extern "C" fn gen_init<K: Kind>(
    provctx: *mut c_void,
    selection: c_int,
    params: *const Param,
) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    let generation = Box::into_raw(Box::new(Gen::<K> {
        provider,
        selection,
        ikm: None,
        _kind: core::marker::PhantomData,
    }));
    // SAFETY: `generation` is the context just made, and OpenSSL passes an
    // array.
    if unsafe { gen_set_params::<K>(generation.cast(), params) } == 0 {
        // SAFETY: as above; no one else holds it.
        drop(unsafe { Box::from_raw(generation) });
        return core::ptr::null_mut();
    }
    generation.cast()
}

pub(crate) unsafe extern "C" fn gen_set_params<K: Kind>(
    genctx: *mut c_void,
    params: *const Param,
) -> c_int {
    // SAFETY: OpenSSL passes the context `gen_init` made, and an array.
    let (Some(generation), params) = (unsafe { genctx.cast::<Gen<K>>().as_mut() }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    let result = (|| {
        if let Some(group) = params.find(c"group") {
            match (group.utf8(), K::GROUP) {
                (Some(name), Some(group)) if name.eq_ignore_ascii_case(group) => {}
                _ => return Err(Failure::invalid("the key type takes no such group")),
            }
        }
        if params
            .find(c"properties")
            .is_some_and(|properties| properties.utf8().is_none())
        {
            return Err(Failure::invalid("properties must be a UTF-8 string"));
        }
        if let Some(ikm) = params.find(c"dhkem-ikm")
            && !(ikm.data.is_null() || ikm.data_size == 0)
        {
            let ikm = ikm
                .octets()
                .ok_or_else(|| Failure::invalid("dhkem-ikm must be an octet string"))?;
            generation.ikm = Some(Zeroizing::new(ikm.to_vec()));
        }
        Ok(())
    })();
    generation.provider.status(result)
}

static GEN_SETTABLE: [Param; 4] = [
    Param::describe(Some(c"group"), UTF8_STRING, 0),
    Param::describe(Some(c"properties"), UTF8_STRING, 0),
    Param::describe(Some(c"dhkem-ikm"), OCTET_STRING, 0),
    Param::END,
];

pub(crate) unsafe extern "C" fn gen_settable_params(
    _genctx: *mut c_void,
    _provctx: *mut c_void,
) -> *const Param {
    GEN_SETTABLE.as_ptr()
}

pub(crate) unsafe extern "C" fn generate<K: Kind>(
    genctx: *mut c_void,
    _callback: Option<Callback>,
    _arg: *mut c_void,
) -> *mut c_void {
    // SAFETY: OpenSSL passes the context `gen_init` made.
    let Some(generation) = (unsafe { genctx.cast::<Gen<K>>().as_ref() }) else {
        return core::ptr::null_mut();
    };
    let provider = generation.provider.clone();
    // Asked for no key, as for parameters alone, it gives an empty key.
    if generation.selection & SELECT_KEYPAIR == 0 {
        return KeyData::<K>::boxed(provider, Held::Empty);
    }
    match K::generate(generation.ikm.as_deref().map(Vec::as_slice)) {
        Ok(private) => KeyData::<K>::boxed(provider, Held::Key(Arc::new(Key::Private(private)))),
        Err(failure) => {
            provider.status(Err(failure));
            core::ptr::null_mut()
        }
    }
}

pub(crate) unsafe extern "C" fn gen_cleanup<K: Kind>(genctx: *mut c_void) {
    if !genctx.is_null() {
        // SAFETY: OpenSSL frees the context `gen_init` made.
        drop(unsafe { Box::from_raw(genctx.cast::<Gen<K>>()) });
    }
}

pub(crate) unsafe extern "C" fn dup<K: Kind>(
    keydata: *const c_void,
    selection: c_int,
) -> *mut c_void {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::<K>::from_ptr(keydata) }) else {
        return core::ptr::null_mut();
    };
    let held = match &data.held {
        Held::Key(key) => match (&**key, selection & SELECT_KEYPAIR) {
            (Key::Private(_), SELECT_KEYPAIR | SELECT_PRIVATE_KEY)
            | (Key::Public(_), SELECT_KEYPAIR | SELECT_PUBLIC_KEY) => Held::Key(key.clone()),
            (Key::Private(private), SELECT_PUBLIC_KEY) => {
                Held::Key(Arc::new(Key::Public(K::public(
                    K::public_of(private)
                        .try_into()
                        .expect("a public key is LEN bytes"),
                ))))
            }
            _ => Held::Empty,
        },
        // A copy of either half fails each use as the original does.
        Held::Mismatched if selection & SELECT_KEYPAIR != 0 => Held::Mismatched,
        Held::Mismatched | Held::Empty => Held::Empty,
    };
    KeyData::<K>::boxed(data.provider.clone(), held)
}

#[cfg(test)]
mod tests {
    use crabgrind::memcheck::{self, MemState};
    use crabgrind::valgrind::{self, RunningMode};

    use super::*;
    use crate::{ed25519::Ed25519, x25519::X25519};

    /// Under `admin/ctgrind`, memcheck fails this if comparing private keys
    /// alone, which only the dispatch table asks for, branches on them.
    #[test]
    fn private_keys_match_in_constant_time() {
        fn check<K: Kind>() {
            let key = |byte: u8| {
                let bytes = [byte; LEN];
                if let RunningMode::Valgrind = valgrind::running_mode() {
                    memcheck::mark_memory(bytes.as_ptr().cast(), LEN, MemState::Undefined).unwrap();
                }
                Key::<K>::Private(K::load(&bytes).unwrap())
            };
            let (a, again, b) = (key(0x9d), key(0x9d), key(0x5a));
            assert!(equal(Some(&a), Some(&again), SELECT_PRIVATE_KEY));
            assert!(!equal(Some(&a), Some(&b), SELECT_PRIVATE_KEY));
        }
        check::<Ed25519>();
        check::<X25519>();
    }
}
