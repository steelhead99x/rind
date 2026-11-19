//! Drives rind-openssl as OpenSSL does: through `OSSL_provider_init` and
//! the dispatch tables it returns, with `OSSL_PARAM` arrays whose keys,
//! types, sizes, and values the caller picks, and output buffers of any
//! size. Every answer must match rind's own API, which the `sign`, `verify`,
//! and `kx` targets compare with aws-lc-rs, and every error must reach the
//! core as a known reason and a format with no conversions to read.

#![no_main]

use std::ffi::{CStr, CString, c_char, c_int, c_uint, c_void};
use std::ptr::{null, null_mut};
use std::sync::OnceLock;

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::agreement::{PrivateKey, X25519};
use rind::ed25519::{KeyPair, PublicKey};

fuzz_target!(|input: Input| {
    let provider = provider();
    match input {
        Input::Import {
            ed25519,
            selection,
            params,
        } => {
            let keymgmt = provider.keymgmt(ed25519);
            let key = keymgmt.import(selection.into(), &params);
            if !key.is_null() {
                let public = keymgmt.check(key);
                // A key holding nothing fails each use.
                assert_eq!(provider.begins(ed25519, key), public);
                keymgmt.free(key);
            }
        }
        Input::Generate {
            ed25519,
            selection,
            params,
        } => {
            let keymgmt = provider.keymgmt(ed25519);
            let key = keymgmt.generate(selection.into(), &params);
            if !key.is_null() {
                let public = keymgmt.check(key);
                // A key holding nothing, such as a private key imported
                // beside another's public key, fails each use.
                assert_eq!(provider.begins(ed25519, key), public);
                keymgmt.free(key);
            }
        }
        Input::Pair {
            ed25519,
            private,
            mut public,
            matching,
        } => {
            let derived = public_of(ed25519, &private);
            if matching {
                public.copy_from_slice(&derived);
            }
            let keymgmt = provider.keymgmt(ed25519);
            let key = keymgmt.import(
                KEYPAIR,
                &[Arg::octets(c"priv", &private), Arg::octets(c"pub", &public)],
            );
            // A mismatched pair imports too, so that OpenSSL never reruns its
            // use on the provider it came from, and holds nothing, so that
            // each use fails.
            assert!(!key.is_null());
            let held = public[..] == derived[..];
            assert_eq!(keymgmt.check(key), held);
            assert_eq!(provider.begins(ed25519, key), held);
            keymgmt.free(key);
        }
        Input::Sign {
            seed,
            mdname,
            params,
            size,
            message,
        } => sign(provider, &seed, mdname, &params, size, &message),
        Input::Verify {
            mut public,
            signed,
            params,
            mut signature,
            message,
        } => {
            if let Some(seed) = signed {
                let pair = KeyPair::from_seed(&seed).unwrap();
                public.copy_from_slice(pair.public_key().as_ref());
                signature = pair.sign(&message).as_ref().to_vec();
            }
            let keymgmt = provider.keymgmt(true);
            let key = keymgmt.import(PUBLIC_KEY, &[Arg::octets(c"pub", &public)]);
            assert!(!key.is_null());
            let ctx = provider.signature_ctx();
            let init: DigestInit = provider.signature(DIGEST_VERIFY_INIT);
            // SAFETY: the context and key are live, and the parameters end.
            let initialized = unsafe { init(ctx, null(), key, Params::new(&params).as_ptr()) };
            // Without parameters nothing can refuse a key that imported.
            if params.is_empty() {
                assert_eq!(initialized, 1);
            }
            if initialized == 1 {
                let verified = provider.signature::<DigestVerify>(DIGEST_VERIFY);
                // SAFETY: each buffer is valid for its length.
                let ok = unsafe {
                    verified(
                        ctx,
                        signature.as_ptr(),
                        signature.len(),
                        message.as_ptr(),
                        message.len(),
                    )
                };
                let expected = PublicKey::new(&public)
                    .and_then(|key| key.verify(&message, &signature))
                    .is_ok();
                // Parameters may still refuse a valid signature, as a context
                // string does, but never accept an invalid one.
                match params.is_empty() {
                    true => assert_eq!(ok == 1, expected),
                    false => assert!(ok != 1 || expected),
                }
            }
            provider.free_signature_ctx(ctx);
            keymgmt.free(key);
        }
        Input::Derive {
            private,
            peer,
            encoded,
            size,
        } => derive(provider, &private, &peer, encoded, size),
    }
});

#[derive(Arbitrary, Debug)]
enum Input {
    /// Imports a key from any parameters, then reads it back.
    Import {
        ed25519: bool,
        selection: u8,
        params: Vec<Arg>,
    },
    /// Generates a key with any parameters, then reads it back.
    Generate {
        ed25519: bool,
        selection: u8,
        params: Vec<Arg>,
    },
    /// Imports a private key beside a public key, its own when `matching`,
    /// as OpenSSL moves a key another provider holds.
    Pair {
        ed25519: bool,
        private: [u8; 32],
        public: [u8; 32],
        matching: bool,
    },
    /// Signs as `EVP_DigestSign` does, with any digest name and parameters.
    Sign {
        seed: [u8; 32],
        mdname: Option<Vec<u8>>,
        params: Vec<Arg>,
        size: u8,
        message: Vec<u8>,
    },
    /// Verifies as `EVP_DigestVerify` does. With a seed, the key is the
    /// seed's and the signature its own over the message, so verification
    /// passes too, not only random signatures that fail.
    Verify {
        public: [u8; 32],
        signed: Option<[u8; 32]>,
        params: Vec<Arg>,
        signature: Vec<u8>,
        message: Vec<u8>,
    },
    /// Agrees as `EVP_PKEY_derive` does, with the peer's key imported or,
    /// as TLS gives it, set as an encoded key on an empty one.
    Derive {
        private: [u8; 32],
        peer: Vec<u8>,
        encoded: bool,
        size: u8,
    },
}

/// A parameter of a name the provider reads, or any other, holding a value
/// of any type the caller can pass.
#[derive(Arbitrary, Debug)]
struct Arg {
    key: Name,
    value: Value,
}

#[derive(Arbitrary, Debug)]
enum Name {
    Pub,
    Priv,
    EncodedPubKey,
    Group,
    Properties,
    DhkemIkm,
    Instance,
    ContextString,
    Other(Vec<u8>),
}

#[derive(Arbitrary, Debug)]
enum Value {
    Octets(Vec<u8>),
    Utf8(Vec<u8>),
    Int(i32),
    Long(i64),
    Uint(u32),
    /// A parameter with no data, as `OSSL_PARAM_construct_*` makes from a
    /// null pointer.
    Empty(u8),
}

impl Arg {
    fn octets(key: &CStr, value: &[u8]) -> Self {
        Self {
            key: Name::Other(key.to_bytes().to_vec()),
            value: Value::Octets(value.to_vec()),
        }
    }
}

const INTEGER: c_uint = 1;
const UNSIGNED_INTEGER: c_uint = 2;
const UTF8_STRING: c_uint = 4;
const OCTET_STRING: c_uint = 5;

#[repr(C)]
struct Dispatch {
    id: c_int,
    function: Option<unsafe extern "C" fn()>,
}

#[repr(C)]
struct Algorithm {
    names: *const c_char,
    properties: *const c_char,
    implementation: *const Dispatch,
    description: *const c_char,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Param {
    key: *const c_char,
    data_type: c_uint,
    data: *mut c_void,
    data_size: usize,
    return_size: usize,
}

const END: Param = Param {
    key: null(),
    data_type: 0,
    data: null_mut(),
    data_size: 0,
    return_size: 0,
};

/// A parameter array and the keys and data it points into.
struct Params {
    params: Vec<Param>,
    _keys: Vec<CString>,
    _data: Vec<Vec<u64>>,
}

impl Params {
    fn new(args: &[Arg]) -> Self {
        let mut keys = Vec::new();
        let mut data = Vec::new();
        let mut params = Vec::new();
        for arg in args {
            let key = match &arg.key {
                Name::Pub => c"pub".to_owned(),
                Name::Priv => c"priv".to_owned(),
                Name::EncodedPubKey => c"encoded-pub-key".to_owned(),
                Name::Group => c"group".to_owned(),
                Name::Properties => c"properties".to_owned(),
                Name::DhkemIkm => c"dhkem-ikm".to_owned(),
                Name::Instance => c"instance".to_owned(),
                Name::ContextString => c"context-string".to_owned(),
                Name::Other(key) => {
                    CString::new(key.iter().copied().filter(|&b| b != 0).collect::<Vec<_>>())
                        .unwrap()
                }
            };
            // Integer data is aligned for its type, as OpenSSL's is.
            let (data_type, bytes): (c_uint, Vec<u8>) = match &arg.value {
                Value::Octets(bytes) => (OCTET_STRING, bytes.clone()),
                Value::Utf8(bytes) => (UTF8_STRING, bytes.clone()),
                Value::Int(value) => (INTEGER, value.to_ne_bytes().to_vec()),
                Value::Long(value) => (INTEGER, value.to_ne_bytes().to_vec()),
                Value::Uint(value) => (UNSIGNED_INTEGER, value.to_ne_bytes().to_vec()),
                Value::Empty(data_type) => (c_uint::from(*data_type % 8), Vec::new()),
            };
            let mut words = vec![0u64; bytes.len().div_ceil(8)];
            // SAFETY: the words hold at least as many bytes.
            unsafe {
                core::ptr::copy_nonoverlapping(
                    bytes.as_ptr(),
                    words.as_mut_ptr().cast::<u8>(),
                    bytes.len(),
                )
            };
            let empty = matches!(arg.value, Value::Empty(_));
            params.push(Param {
                key: key.as_ptr(),
                data_type,
                data: if empty {
                    null_mut()
                } else {
                    words.as_mut_ptr().cast()
                },
                data_size: bytes.len(),
                return_size: usize::MAX,
            });
            keys.push(key);
            data.push(words);
        }
        params.push(END);
        Self {
            params,
            _keys: keys,
            _data: data,
        }
    }

    fn as_ptr(&self) -> *const Param {
        self.params.as_ptr()
    }
}

// The core's error functions, which check what the provider raises.
unsafe extern "C" fn new_error(_handle: *const c_void) {}

unsafe extern "C" fn vset_error(
    _handle: *const c_void,
    reason: u32,
    format: *const c_char,
    _args: *mut c_void,
) {
    assert!((1..=4).contains(&reason), "unknown reason {reason}");
    // SAFETY: the provider passes a C string.
    let format = unsafe { CStr::from_ptr(format) }.to_bytes();
    let mut at = 0;
    while at < format.len() {
        if format[at] == b'%' {
            assert_eq!(
                format.get(at + 1),
                Some(&b'%'),
                "a conversion in {format:?}"
            );
            at += 1;
        }
        at += 1;
    }
}

const CORE_NEW_ERROR: c_int = 5;
const CORE_VSET_ERROR: c_int = 7;
const QUERY_OPERATION: c_int = 1027;
const OP_KEYMGMT: c_int = 10;
const OP_KEYEXCH: c_int = 11;
const OP_SIGNATURE: c_int = 12;

const PRIVATE_KEY: c_int = 1;
const PUBLIC_KEY: c_int = 2;
const KEYPAIR: c_int = 3;

const KEYMGMT_NEW: c_int = 1;
const KEYMGMT_GEN_INIT: c_int = 2;
const KEYMGMT_GEN: c_int = 6;
const KEYMGMT_GEN_CLEANUP: c_int = 7;
const KEYMGMT_FREE: c_int = 10;
const KEYMGMT_GET_PARAMS: c_int = 11;
const KEYMGMT_SET_PARAMS: c_int = 13;
const KEYMGMT_HAS: c_int = 21;
const KEYMGMT_MATCH: c_int = 23;
const KEYMGMT_IMPORT: c_int = 40;
const KEYMGMT_EXPORT: c_int = 42;
const KEYMGMT_DUP: c_int = 44;

const KEYEXCH_NEWCTX: c_int = 1;
const KEYEXCH_INIT: c_int = 2;
const KEYEXCH_DERIVE: c_int = 3;
const KEYEXCH_SET_PEER: c_int = 4;
const KEYEXCH_FREECTX: c_int = 5;

const SIGNATURE_NEWCTX: c_int = 1;
const DIGEST_SIGN_INIT: c_int = 8;
const DIGEST_SIGN: c_int = 11;
const DIGEST_VERIFY_INIT: c_int = 12;
const DIGEST_VERIFY: c_int = 15;
const SIGNATURE_FREECTX: c_int = 16;

type QueryOperation = unsafe extern "C" fn(*mut c_void, c_int, *mut c_int) -> *const Algorithm;
type New = unsafe extern "C" fn(*mut c_void) -> *mut c_void;
type Free = unsafe extern "C" fn(*mut c_void);
type GenInit = unsafe extern "C" fn(*mut c_void, c_int, *const Param) -> *mut c_void;
type Gen = unsafe extern "C" fn(*mut c_void, *const c_void, *mut c_void) -> *mut c_void;
type GetParams = unsafe extern "C" fn(*mut c_void, *mut Param) -> c_int;
type SetParams = unsafe extern "C" fn(*mut c_void, *const Param) -> c_int;
type Has = unsafe extern "C" fn(*const c_void, c_int) -> c_int;
type Match = unsafe extern "C" fn(*const c_void, *const c_void, c_int) -> c_int;
type Import = unsafe extern "C" fn(*mut c_void, c_int, *const Param) -> c_int;
type Callback = unsafe extern "C" fn(*const Param, *mut c_void) -> c_int;
type Export = unsafe extern "C" fn(*mut c_void, c_int, Callback, *mut c_void) -> c_int;
type Dup = unsafe extern "C" fn(*const c_void, c_int) -> *mut c_void;
type NewCtx = unsafe extern "C" fn(*mut c_void, *const c_char) -> *mut c_void;
/// A key exchange's context takes no property query, unlike a signature's.
type ExchangeNewCtx = unsafe extern "C" fn(*mut c_void) -> *mut c_void;
type ExchangeInit = unsafe extern "C" fn(*mut c_void, *mut c_void, *const Param) -> c_int;
type SetPeer = unsafe extern "C" fn(*mut c_void, *mut c_void) -> c_int;
type Derive = unsafe extern "C" fn(*mut c_void, *mut u8, *mut usize, usize) -> c_int;
type DigestInit =
    unsafe extern "C" fn(*mut c_void, *const c_char, *mut c_void, *const Param) -> c_int;
type DigestSign =
    unsafe extern "C" fn(*mut c_void, *mut u8, *mut usize, usize, *const u8, usize) -> c_int;
type DigestVerify = unsafe extern "C" fn(*mut c_void, *const u8, usize, *const u8, usize) -> c_int;

/// The function `id` names in `table`, as the signature `F` its id gives.
fn lookup<F: Copy>(table: *const Dispatch, id: c_int) -> F {
    assert_eq!(size_of::<F>(), size_of::<unsafe extern "C" fn()>());
    let mut at = table;
    loop {
        // SAFETY: the table runs to an entry with id 0.
        let entry = unsafe { &*at };
        assert_ne!(entry.id, 0, "no function {id}");
        if entry.id == id {
            let function = entry.function.unwrap();
            // SAFETY: OpenSSL's ABI gives each id one signature, which `F` is.
            return unsafe { core::mem::transmute_copy(&function) };
        }
        // SAFETY: the table has not ended.
        at = unsafe { at.add(1) };
    }
}

/// The provider, started once, as OpenSSL starts it for a library context.
struct Provider {
    provctx: *mut c_void,
    x25519: Keymgmt,
    ed25519: Keymgmt,
    keyexch: *const Dispatch,
    signature: *const Dispatch,
}

// SAFETY: the provider serves every thread, and the fuzzer runs one.
unsafe impl Send for Provider {}
// SAFETY: as for `Send`.
unsafe impl Sync for Provider {}

#[derive(Clone, Copy)]
struct Keymgmt {
    provctx: *mut c_void,
    table: *const Dispatch,
    ed25519: bool,
}

fn provider() -> &'static Provider {
    static PROVIDER: OnceLock<Provider> = OnceLock::new();
    PROVIDER.get_or_init(|| {
        let core = [
            Dispatch {
                id: CORE_NEW_ERROR,
                // SAFETY: OpenSSL's ABI passes each function as `void (*)(void)`.
                function: Some(unsafe {
                    core::mem::transmute::<
                        unsafe extern "C" fn(*const c_void),
                        unsafe extern "C" fn(),
                    >(new_error)
                }),
            },
            Dispatch {
                id: CORE_VSET_ERROR,
                // SAFETY: as above.
                function: Some(unsafe {
                    core::mem::transmute::<
                        unsafe extern "C" fn(*const c_void, u32, *const c_char, *mut c_void),
                        unsafe extern "C" fn(),
                    >(vset_error)
                }),
            },
            Dispatch {
                id: 0,
                function: None,
            },
        ];
        let (mut out, mut provctx): (*const Dispatch, _) = (null(), null_mut());
        // SAFETY: the core table ends, and both outputs are writable. The
        // provider reads the core table only as it starts.
        let started = unsafe {
            rind_openssl::OSSL_provider_init(
                null(),
                core.as_ptr().cast(),
                (&raw mut out).cast(),
                &mut provctx,
            )
        };
        assert_eq!(started, 1);
        let query: QueryOperation = lookup(out, QUERY_OPERATION);
        let algorithms = |operation| {
            let mut no_store = 1;
            // SAFETY: the context is live, and the flag writable.
            let list = unsafe { query(provctx, operation, &mut no_store) };
            let mut found = Vec::new();
            for at in 0.. {
                // SAFETY: the list runs to an entry with no names.
                let algorithm = unsafe { &*list.add(at) };
                if algorithm.names.is_null() {
                    break;
                }
                // SAFETY: names are C strings.
                let names = unsafe { CStr::from_ptr(algorithm.names) }.to_str().unwrap();
                found.push((
                    names.split(':').next().unwrap().to_owned(),
                    algorithm.implementation,
                ));
            }
            found
        };
        let find = |operation, name: &str| {
            algorithms(operation)
                .into_iter()
                .find(|(found, _)| found == name)
                .unwrap()
                .1
        };
        Provider {
            provctx,
            x25519: Keymgmt {
                provctx,
                table: find(OP_KEYMGMT, "X25519"),
                ed25519: false,
            },
            ed25519: Keymgmt {
                provctx,
                table: find(OP_KEYMGMT, "ED25519"),
                ed25519: true,
            },
            keyexch: find(OP_KEYEXCH, "X25519"),
            signature: find(OP_SIGNATURE, "ED25519"),
        }
    })
}

impl Provider {
    fn keymgmt(&self, ed25519: bool) -> Keymgmt {
        if ed25519 { self.ed25519 } else { self.x25519 }
    }

    fn signature<F: Copy>(&self, id: c_int) -> F {
        lookup(self.signature, id)
    }

    fn signature_ctx(&self) -> *mut c_void {
        let new: NewCtx = self.signature(SIGNATURE_NEWCTX);
        // SAFETY: the provider's context is live.
        let ctx = unsafe { new(self.provctx, null()) };
        assert!(!ctx.is_null());
        ctx
    }

    fn free_signature_ctx(&self, ctx: *mut c_void) {
        let free: Free = self.signature(SIGNATURE_FREECTX);
        // SAFETY: the context is live, and this is its last use.
        unsafe { free(ctx) };
    }

    /// Whether `key` begins an operation: verification for Ed25519, an
    /// exchange for X25519.
    fn begins(&self, ed25519: bool, key: *mut c_void) -> bool {
        if ed25519 {
            let ctx = self.signature_ctx();
            let init: DigestInit = self.signature(DIGEST_VERIFY_INIT);
            // SAFETY: the context and key are live, and the parameters end.
            let ok = unsafe { init(ctx, null(), key, Params::new(&[]).as_ptr()) } == 1;
            self.free_signature_ctx(ctx);
            ok
        } else {
            let new: ExchangeNewCtx = lookup(self.keyexch, KEYEXCH_NEWCTX);
            let init: ExchangeInit = lookup(self.keyexch, KEYEXCH_INIT);
            let free: Free = lookup(self.keyexch, KEYEXCH_FREECTX);
            // SAFETY: the provider's context and the key are live, and the
            // exchange's context is freed after its last use.
            unsafe {
                let ctx = new(self.provctx);
                let ok = init(ctx, key, null()) == 1;
                free(ctx);
                ok
            }
        }
    }
}

/// The public key of a 32-byte private key, by rind's own API.
fn public_of(ed25519: bool, private: &[u8]) -> Vec<u8> {
    if ed25519 {
        KeyPair::from_seed(private)
            .unwrap()
            .public_key()
            .as_ref()
            .to_vec()
    } else {
        PrivateKey::from_scalar(&X25519, private)
            .unwrap()
            .public_key()
            .as_ref()
            .to_vec()
    }
}

/// A key's halves, as `export` gives them.
#[derive(Default, Debug, PartialEq)]
struct Exported {
    public: Option<Vec<u8>>,
    private: Option<Vec<u8>>,
}

unsafe extern "C" fn collect(params: *const Param, arg: *mut c_void) -> c_int {
    // SAFETY: `export` passes the `Exported` its caller gave.
    let out = unsafe { &mut *arg.cast::<Exported>() };
    let mut at = params;
    loop {
        // SAFETY: the array runs to its terminator.
        let param = unsafe { &*at };
        if param.key.is_null() {
            return 1;
        }
        assert_eq!(param.data_type, OCTET_STRING);
        // SAFETY: the data is valid for its size.
        let bytes =
            unsafe { core::slice::from_raw_parts(param.data.cast::<u8>(), param.data_size) }
                .to_vec();
        // SAFETY: keys are C strings.
        match unsafe { CStr::from_ptr(param.key) }.to_bytes() {
            b"pub" => out.public = Some(bytes),
            b"priv" => out.private = Some(bytes),
            key => panic!("exported {key:?}"),
        }
        // SAFETY: the array has not ended.
        at = unsafe { at.add(1) };
    }
}

impl Keymgmt {
    fn get<F: Copy>(&self, id: c_int) -> F {
        lookup(self.table, id)
    }

    fn import(&self, selection: c_int, args: &[Arg]) -> *mut c_void {
        let new: New = self.get(KEYMGMT_NEW);
        let import: Import = self.get(KEYMGMT_IMPORT);
        // SAFETY: the provider's context is live.
        let key = unsafe { new(self.provctx) };
        assert!(!key.is_null());
        let params = Params::new(args);
        // SAFETY: the key is live, and the parameters end.
        if unsafe { import(key, selection, params.as_ptr()) } == 1 {
            key
        } else {
            self.free(key);
            null_mut()
        }
    }

    fn generate(&self, selection: c_int, args: &[Arg]) -> *mut c_void {
        let init: GenInit = self.get(KEYMGMT_GEN_INIT);
        let generate: Gen = self.get(KEYMGMT_GEN);
        let cleanup: Free = self.get(KEYMGMT_GEN_CLEANUP);
        let params = Params::new(args);
        // SAFETY: the provider's context is live, and the parameters end.
        let ctx = unsafe { init(self.provctx, selection, params.as_ptr()) };
        if ctx.is_null() {
            return null_mut();
        }
        // SAFETY: the context is live; OpenSSL may pass no callback.
        let key = unsafe { generate(ctx, null(), null_mut()) };
        // SAFETY: the context's last use.
        unsafe { cleanup(ctx) };
        key
    }

    fn free(&self, key: *mut c_void) {
        let free: Free = self.get(KEYMGMT_FREE);
        // SAFETY: the key is live, and this is its last use.
        unsafe { free(key) };
    }

    fn export(&self, key: *mut c_void, selection: c_int) -> Option<Exported> {
        let export: Export = self.get(KEYMGMT_EXPORT);
        let mut out = Exported::default();
        // SAFETY: the key is live, and the callback takes the `Exported`.
        let ok = unsafe { export(key, selection, collect, (&raw mut out).cast()) };
        (ok == 1).then_some(out)
    }

    /// What a key holds must agree with itself and with rind, however it is
    /// read. Returns whether it holds a public key.
    fn check(&self, key: *mut c_void) -> bool {
        let has: Has = self.get(KEYMGMT_HAS);
        // SAFETY: the key is live.
        let (public, private) = unsafe { (has(key, PUBLIC_KEY) == 1, has(key, PRIVATE_KEY) == 1) };
        assert!(public || !private, "a private key without its public half");
        // An empty key, which parameter generation gives, exports nothing.
        let exported = self.export(key, KEYPAIR);
        assert_eq!(exported.is_some(), public);
        let exported = exported.unwrap_or_default();
        assert_eq!(
            (exported.public.is_some(), exported.private.is_some()),
            (public, private)
        );
        if let Some(private) = &exported.private {
            let derived = public_of(self.ed25519, private);
            assert_eq!(exported.public.as_deref(), Some(&derived[..]));
        }

        // `get_params` gives the same halves, into a buffer of each size.
        let get: GetParams = self.get(KEYMGMT_GET_PARAMS);
        for (name, half) in [(c"pub", &exported.public), (c"priv", &exported.private)] {
            for size in [0, 31, 32, 64] {
                // Exactly `size`, so a sanitizer catches a write past it.
                let mut buf = vec![0u8; size];
                let mut params = [
                    Param {
                        key: name.as_ptr(),
                        data_type: OCTET_STRING,
                        data: buf.as_mut_ptr().cast(),
                        data_size: size,
                        return_size: usize::MAX,
                    },
                    END,
                ];
                // SAFETY: the key is live, and the buffer valid for its size.
                let ok = unsafe { get(key, params.as_mut_ptr()) } == 1;
                match half {
                    Some(half) if size >= half.len() => {
                        assert!(ok);
                        assert_eq!(&buf[..params[0].return_size], &half[..]);
                    }
                    Some(_) => assert!(!ok),
                    None => assert!(ok && params[0].return_size == usize::MAX),
                }
            }
        }

        // A duplicate of either half matches the original on it.
        let dup: Dup = self.get(KEYMGMT_DUP);
        let matches: Match = self.get(KEYMGMT_MATCH);
        for selection in [PUBLIC_KEY, KEYPAIR] {
            // SAFETY: the key is live.
            let copy = unsafe { dup(key, selection) };
            assert!(!copy.is_null());
            // SAFETY: both keys are live.
            assert_eq!(unsafe { matches(key, copy, selection) } == 1, public);
            if selection == PUBLIC_KEY {
                assert_eq!(
                    self.export(copy, KEYPAIR).and_then(|copy| copy.private),
                    None
                );
            }
            self.free(copy);
        }
        public
    }
}

fn sign(
    provider: &Provider,
    seed: &[u8; 32],
    mdname: Option<Vec<u8>>,
    args: &[Arg],
    size: u8,
    message: &[u8],
) {
    let keymgmt = provider.keymgmt(true);
    let key = keymgmt.import(KEYPAIR, &[Arg::octets(c"priv", seed)]);
    assert!(!key.is_null());
    let ctx = provider.signature_ctx();
    let mdname = mdname.map(|name| {
        CString::new(name.into_iter().filter(|&b| b != 0).collect::<Vec<_>>()).unwrap()
    });
    let plain = mdname.as_ref().is_none_or(|name| name.is_empty()) && args.is_empty();
    let init: DigestInit = provider.signature(DIGEST_SIGN_INIT);
    let params = Params::new(args);
    // SAFETY: the context and key are live, and the parameters end.
    let ok = unsafe {
        init(
            ctx,
            mdname.as_ref().map_or(null(), |name| name.as_ptr()),
            key,
            params.as_ptr(),
        )
    };
    assert!(ok == 1 || !plain);
    if ok == 1 {
        let sign: DigestSign = provider.signature(DIGEST_SIGN);
        let mut signature = vec![0u8; size.into()];
        let mut len = 0;
        // SAFETY: each buffer is valid for its length.
        let ok = unsafe {
            sign(
                ctx,
                signature.as_mut_ptr(),
                &mut len,
                signature.len(),
                message.as_ptr(),
                message.len(),
            )
        };
        if plain && signature.len() >= 64 {
            assert_eq!(ok, 1);
        }
        if ok == 1 {
            let expected = KeyPair::from_seed(seed).unwrap().sign(message);
            assert_eq!(&signature[..len], expected.as_ref());
            // A null buffer asks only the length.
            // SAFETY: the context is live, and the message valid.
            assert_eq!(
                unsafe {
                    sign(
                        ctx,
                        null_mut(),
                        &mut len,
                        0,
                        message.as_ptr(),
                        message.len(),
                    )
                },
                1
            );
            assert_eq!(len, 64);
        }
    }
    provider.free_signature_ctx(ctx);
    keymgmt.free(key);
}

fn derive(provider: &Provider, private: &[u8; 32], peer: &[u8], encoded: bool, size: u8) {
    let keymgmt = provider.keymgmt(false);
    let key = keymgmt.import(KEYPAIR, &[Arg::octets(c"priv", private)]);
    assert!(!key.is_null());
    let peer_key = if encoded {
        let peer_key = keymgmt.generate(0, &[]);
        assert!(!peer_key.is_null());
        let set: SetParams = keymgmt.get(KEYMGMT_SET_PARAMS);
        let params = Params::new(&[Arg::octets(c"encoded-pub-key", peer)]);
        // SAFETY: the key is live, and the parameters end.
        if unsafe { set(peer_key, params.as_ptr()) } != 1 {
            keymgmt.free(peer_key);
            null_mut()
        } else {
            peer_key
        }
    } else {
        keymgmt.import(PUBLIC_KEY, &[Arg::octets(c"pub", peer)])
    };
    if peer_key.is_null() {
        assert_ne!(peer.len(), 32);
        keymgmt.free(key);
        return;
    }
    let new: ExchangeNewCtx = lookup(provider.keyexch, KEYEXCH_NEWCTX);
    let init: ExchangeInit = lookup(provider.keyexch, KEYEXCH_INIT);
    let set_peer: SetPeer = lookup(provider.keyexch, KEYEXCH_SET_PEER);
    let derive: Derive = lookup(provider.keyexch, KEYEXCH_DERIVE);
    let free: Free = lookup(provider.keyexch, KEYEXCH_FREECTX);
    // SAFETY: the provider's context, the keys, and the buffer are live.
    unsafe {
        let ctx = new(provider.provctx);
        assert_eq!(init(ctx, key, null()), 1);
        assert_eq!(set_peer(ctx, peer_key), 1);
        let mut secret = vec![0u8; size.into()];
        let mut len = 0;
        let ok = derive(ctx, secret.as_mut_ptr(), &mut len, secret.len()) == 1;
        let expected = PrivateKey::from_scalar(&X25519, private)
            .unwrap()
            .agree(peer);
        match expected {
            Ok(expected) if secret.len() >= 32 => {
                assert!(ok);
                assert_eq!(&secret[..len], expected.as_ref());
            }
            _ => assert!(!ok),
        }
        free(ctx);
    }
    keymgmt.free(peer_key);
    keymgmt.free(key);
}
