// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! ML-KEM and ML-DSA from the provider this crate builds, loaded into the
//! system's OpenSSL 3 with the configuration the README documents, and
//! checked against OpenSSL's default provider: the same keys in each must
//! give the same outputs.
//!
//! The default provider has ML-KEM and ML-DSA from OpenSSL 3.5, as do its
//! encoders and its TLS groups and signature schemes, so the tests that need
//! them pass vacuously, saying so, where the linked OpenSSL is older, as
//! Ubuntu 24.04's 3.0 is; the macOS runners' Homebrew OpenSSL and the Nix dev
//! shell's run them. The rest run on every OpenSSL 3.
#![cfg(unix)]
#![allow(clippy::undocumented_unsafe_blocks)]

use std::ffi::{CStr, CString, c_char, c_int, c_long, c_ulong, c_void};
use std::ptr::{null, null_mut};

use openssl_sys::*;

mod common;

// What `openssl-sys` does not bind, all in OpenSSL 3.0, so that the binary
// links against any OpenSSL 3.
unsafe extern "C" {
    fn OSSL_LIB_CTX_load_config(ctx: *mut OSSL_LIB_CTX, file: *const c_char) -> c_int;
    fn OSSL_PROVIDER_get0_name(provider: *const OSSL_PROVIDER) -> *const c_char;
    fn OSSL_PROVIDER_get_capabilities(
        provider: *const OSSL_PROVIDER,
        capability: *const c_char,
        callback: unsafe extern "C" fn(*const OSSL_PARAM, *mut c_void) -> c_int,
        arg: *mut c_void,
    ) -> c_int;
    fn OSSL_PARAM_get_uint(param: *const OSSL_PARAM, value: *mut std::ffi::c_uint) -> c_int;
    fn EVP_PKEY_get0_provider(pkey: *const EVP_PKEY) -> *const OSSL_PROVIDER;
    fn EVP_PKEY_CTX_get0_provider(ctx: *const EVP_PKEY_CTX) -> *const OSSL_PROVIDER;
    fn EVP_PKEY_CTX_new_from_pkey(
        ctx: *mut OSSL_LIB_CTX,
        pkey: *mut EVP_PKEY,
        propq: *const c_char,
    ) -> *mut EVP_PKEY_CTX;
    fn EVP_PKEY_get_octet_string_param(
        pkey: *const EVP_PKEY,
        name: *const c_char,
        buf: *mut u8,
        max: usize,
        len: *mut usize,
    ) -> c_int;
    fn EVP_PKEY_encapsulate_init(ctx: *mut EVP_PKEY_CTX, params: *const OSSL_PARAM) -> c_int;
    fn EVP_PKEY_encapsulate(
        ctx: *mut EVP_PKEY_CTX,
        out: *mut u8,
        out_len: *mut usize,
        secret: *mut u8,
        secret_len: *mut usize,
    ) -> c_int;
    fn EVP_PKEY_decapsulate_init(ctx: *mut EVP_PKEY_CTX, params: *const OSSL_PARAM) -> c_int;
    fn EVP_PKEY_CTX_dup(ctx: *const EVP_PKEY_CTX) -> *mut EVP_PKEY_CTX;
    fn EVP_PKEY_decapsulate(
        ctx: *mut EVP_PKEY_CTX,
        secret: *mut u8,
        secret_len: *mut usize,
        input: *const u8,
        input_len: usize,
    ) -> c_int;
    fn EVP_KEM_fetch(
        ctx: *mut OSSL_LIB_CTX,
        algorithm: *const c_char,
        propq: *const c_char,
    ) -> *mut c_void;
    fn EVP_KEM_get0_provider(kem: *const c_void) -> *const OSSL_PROVIDER;
    fn EVP_KEM_free(kem: *mut c_void);
    fn EVP_SIGNATURE_fetch(
        ctx: *mut OSSL_LIB_CTX,
        algorithm: *const c_char,
        propq: *const c_char,
    ) -> *mut c_void;
    fn EVP_SIGNATURE_get0_provider(signature: *const c_void) -> *const OSSL_PROVIDER;
    fn EVP_SIGNATURE_free(signature: *mut c_void);
    fn EVP_DigestSignInit_ex(
        ctx: *mut EVP_MD_CTX,
        pctx: *mut *mut EVP_PKEY_CTX,
        mdname: *const c_char,
        libctx: *mut OSSL_LIB_CTX,
        props: *const c_char,
        pkey: *mut EVP_PKEY,
        params: *const OSSL_PARAM,
    ) -> c_int;
    fn EVP_DigestVerifyInit_ex(
        ctx: *mut EVP_MD_CTX,
        pctx: *mut *mut EVP_PKEY_CTX,
        mdname: *const c_char,
        libctx: *mut OSSL_LIB_CTX,
        props: *const c_char,
        pkey: *mut EVP_PKEY,
        params: *const OSSL_PARAM,
    ) -> c_int;
    fn PEM_read_bio_PrivateKey_ex(
        bio: *mut BIO,
        key: *mut *mut EVP_PKEY,
        callback: *mut c_void,
        arg: *mut c_void,
        libctx: *mut OSSL_LIB_CTX,
        propq: *const c_char,
    ) -> *mut EVP_PKEY;
    fn PEM_read_bio_PUBKEY_ex(
        bio: *mut BIO,
        key: *mut *mut EVP_PKEY,
        callback: *mut c_void,
        arg: *mut c_void,
        libctx: *mut OSSL_LIB_CTX,
        propq: *const c_char,
    ) -> *mut EVP_PKEY;
    fn OSSL_PARAM_construct_int(key: *const c_char, buf: *mut c_int) -> OSSL_PARAM;
    fn OSSL_PARAM_construct_int64(key: *const c_char, buf: *mut i64) -> OSSL_PARAM;
    fn ERR_error_string_n(error: c_ulong, buf: *mut c_char, len: usize);
    fn X509_new_ex(libctx: *mut OSSL_LIB_CTX, propq: *const c_char) -> *mut X509;
    fn SSL_CTX_new_ex(
        libctx: *mut OSSL_LIB_CTX,
        propq: *const c_char,
        method: *const SSL_METHOD,
    ) -> *mut SSL_CTX;
    fn BIO_new_bio_pair(
        bio1: *mut *mut BIO,
        size1: usize,
        bio2: *mut *mut BIO,
        size2: usize,
    ) -> c_int;
}

/// The errors OpenSSL holds for this thread, taken off its queue.
fn errors() -> String {
    let mut out = String::new();
    loop {
        let mut data = null();
        let mut flags = 0;
        let code =
            unsafe { ERR_get_error_all(null_mut(), null_mut(), null_mut(), &mut data, &mut flags) };
        if code == 0 {
            return out;
        }
        let mut buf = [0 as c_char; 256];
        unsafe { ERR_error_string_n(code, buf.as_mut_ptr(), buf.len()) };
        out += &unsafe { CStr::from_ptr(buf.as_ptr()) }.to_string_lossy();
        if !data.is_null() {
            out += ": ";
            out += &unsafe { CStr::from_ptr(data) }.to_string_lossy();
        }
        out += "\n";
    }
}

#[track_caller]
fn check(ok: c_int) {
    assert_eq!(ok, 1, "OpenSSL failed:\n{}", errors());
}

#[track_caller]
fn non_null<T>(ptr: *mut T) -> *mut T {
    assert!(!ptr.is_null(), "OpenSSL failed:\n{}", errors());
    ptr
}

fn name(provider: *const OSSL_PROVIDER) -> String {
    assert!(!provider.is_null());
    unsafe { CStr::from_ptr(OSSL_PROVIDER_get0_name(provider)) }
        .to_string_lossy()
        .into_owned()
}

/// Whether the linked OpenSSL has its own ML-KEM and ML-DSA, from 3.5, to
/// check rind's against; a test that needs them says when it cannot run.
fn has_reference(test: &str) -> bool {
    let has = unsafe { OpenSSL_version_num() } >= 0x3050_0000;
    if !has {
        eprintln!("{test}: skipped, as it needs OpenSSL 3.5's ML-KEM and ML-DSA");
    }
    has
}

/// `SSL_CTRL_GET_NEGOTIATED_GROUP`, behind OpenSSL's
/// `SSL_get_negotiated_group` macro.
const SSL_CTRL_GET_NEGOTIATED_GROUP: c_int = 134;

const RIND: &CStr = c"provider=rind";
const DEFAULT: &CStr = c"provider=default";

const ML_KEM: [&CStr; 3] = [c"ML-KEM-512", c"ML-KEM-768", c"ML-KEM-1024"];
const ML_DSA: [&CStr; 3] = [c"ML-DSA-44", c"ML-DSA-65", c"ML-DSA-87"];

/// A library context configured as the README says, with the provider this
/// test binary links.
struct Context(*mut OSSL_LIB_CTX);

impl Context {
    fn new() -> Self {
        let ctx = non_null(unsafe { OSSL_LIB_CTX_new() });
        common::add_builtin(ctx);
        let config = common::config(None);
        let config = CString::new(config.as_os_str().as_encoded_bytes()).unwrap();
        check(unsafe { OSSL_LIB_CTX_load_config(ctx, config.as_ptr()) });
        Self(ctx)
    }

    /// A fresh key of `algorithm`, in the provider `propq` picks, from
    /// `seed` if one is given.
    fn generate(&self, algorithm: &CStr, propq: Option<&CStr>, seed: Option<&[u8]>) -> Key {
        unsafe {
            let ctx = non_null(EVP_PKEY_CTX_new_from_name(
                self.0,
                algorithm.as_ptr(),
                propq.map_or(null(), CStr::as_ptr),
            ));
            check(EVP_PKEY_keygen_init(ctx));
            if let Some(seed) = seed {
                let mut seed = seed.to_vec();
                let params = [
                    OSSL_PARAM_construct_octet_string(
                        c"seed".as_ptr(),
                        seed.as_mut_ptr().cast(),
                        seed.len(),
                    ),
                    OSSL_PARAM_construct_end(),
                ];
                check(EVP_PKEY_CTX_set_params(ctx, params.as_ptr()));
            }
            let mut key = null_mut();
            check(EVP_PKEY_generate(ctx, &mut key));
            EVP_PKEY_CTX_free(ctx);
            Key(key)
        }
    }

    /// A key of `algorithm` from its parameters, each name and its bytes, in
    /// the provider `propq` picks, or why OpenSSL refused it.
    fn load(
        &self,
        algorithm: &CStr,
        propq: &CStr,
        selection: c_int,
        params: &[(&CStr, &[u8])],
    ) -> Result<Key, String> {
        let mut values: Vec<Vec<u8>> = params.iter().map(|(_, value)| value.to_vec()).collect();
        let mut list: Vec<OSSL_PARAM> = params
            .iter()
            .zip(&mut values)
            .map(|((name, _), value)| unsafe {
                OSSL_PARAM_construct_octet_string(
                    name.as_ptr(),
                    value.as_mut_ptr().cast(),
                    value.len(),
                )
            })
            .collect();
        list.push(unsafe { OSSL_PARAM_construct_end() });
        unsafe {
            let pctx = non_null(EVP_PKEY_CTX_new_from_name(
                self.0,
                algorithm.as_ptr(),
                propq.as_ptr(),
            ));
            check(EVP_PKEY_fromdata_init(pctx));
            let mut key = null_mut();
            let ok = EVP_PKEY_fromdata(pctx, &mut key, selection, list.as_mut_ptr());
            EVP_PKEY_CTX_free(pctx);
            match ok {
                1 => Ok(Key(key)),
                _ => Err(errors()),
            }
        }
    }

    /// Encapsulates to `key` on the provider `propq` picks, returning the
    /// ciphertext, the shared secret, and the provider that made them.
    fn encapsulate(
        &self,
        key: &Key,
        propq: Option<&CStr>,
    ) -> Result<(Vec<u8>, Vec<u8>, String), String> {
        unsafe {
            let ctx = non_null(EVP_PKEY_CTX_new_from_pkey(
                self.0,
                key.0,
                propq.map_or(null(), CStr::as_ptr),
            ));
            let result = (|| {
                let (mut ct_len, mut secret_len) = (0, 0);
                if EVP_PKEY_encapsulate_init(ctx, null()) != 1
                    || EVP_PKEY_encapsulate(
                        ctx,
                        null_mut(),
                        &mut ct_len,
                        null_mut(),
                        &mut secret_len,
                    ) != 1
                {
                    return Err(errors());
                }
                let (mut ct, mut secret) = (vec![0; ct_len], vec![0; secret_len]);
                if EVP_PKEY_encapsulate(
                    ctx,
                    ct.as_mut_ptr(),
                    &mut ct_len,
                    secret.as_mut_ptr(),
                    &mut secret_len,
                ) != 1
                {
                    return Err(errors());
                }
                ct.truncate(ct_len);
                secret.truncate(secret_len);
                Ok((ct, secret, name(EVP_PKEY_CTX_get0_provider(ctx))))
            })();
            EVP_PKEY_CTX_free(ctx);
            result
        }
    }

    /// Decapsulates `ct` with `key` on the provider `propq` picks.
    fn decapsulate(
        &self,
        key: &Key,
        propq: Option<&CStr>,
        ct: &[u8],
    ) -> Result<(Vec<u8>, String), String> {
        unsafe {
            let ctx = non_null(EVP_PKEY_CTX_new_from_pkey(
                self.0,
                key.0,
                propq.map_or(null(), CStr::as_ptr),
            ));
            let result = (|| {
                let mut len = 0;
                if EVP_PKEY_decapsulate_init(ctx, null()) != 1
                    || EVP_PKEY_decapsulate(ctx, null_mut(), &mut len, ct.as_ptr(), ct.len()) != 1
                {
                    return Err(errors());
                }
                let mut secret = vec![0; len];
                if EVP_PKEY_decapsulate(ctx, secret.as_mut_ptr(), &mut len, ct.as_ptr(), ct.len())
                    != 1
                {
                    return Err(errors());
                }
                secret.truncate(len);
                Ok((secret, name(EVP_PKEY_CTX_get0_provider(ctx))))
            })();
            EVP_PKEY_CTX_free(ctx);
            result
        }
    }

    /// Signs `message` with `key` as `EVP_DigestSign` does, on the provider
    /// `propq` picks, with `params`.
    fn sign(
        &self,
        key: &Key,
        message: &[u8],
        propq: Option<&CStr>,
        params: *const OSSL_PARAM,
    ) -> Result<(Vec<u8>, String), String> {
        unsafe {
            let md = non_null(EVP_MD_CTX_new());
            let mut pctx = null_mut();
            let result = (|| {
                if EVP_DigestSignInit_ex(
                    md,
                    &mut pctx,
                    null(),
                    self.0,
                    propq.map_or(null(), CStr::as_ptr),
                    key.0,
                    params,
                ) != 1
                {
                    return Err(errors());
                }
                let mut len = 0;
                if EVP_DigestSign(md, null_mut(), &mut len, message.as_ptr(), message.len()) != 1 {
                    return Err(errors());
                }
                let mut signature = vec![0; len];
                if EVP_DigestSign(
                    md,
                    signature.as_mut_ptr(),
                    &mut len,
                    message.as_ptr(),
                    message.len(),
                ) != 1
                {
                    return Err(errors());
                }
                signature.truncate(len);
                Ok((signature, name(EVP_PKEY_CTX_get0_provider(pctx))))
            })();
            EVP_MD_CTX_free(md);
            result
        }
    }

    /// Verifies as `EVP_DigestVerify` does, on the provider `propq` picks,
    /// returning whether it passed and the provider that checked it.
    fn verify(
        &self,
        key: &Key,
        propq: Option<&CStr>,
        message: &[u8],
        signature: &[u8],
    ) -> (bool, String) {
        unsafe {
            let md = non_null(EVP_MD_CTX_new());
            let mut pctx = null_mut();
            check(EVP_DigestVerifyInit_ex(
                md,
                &mut pctx,
                null(),
                self.0,
                propq.map_or(null(), CStr::as_ptr),
                key.0,
                null(),
            ));
            let ok = EVP_DigestVerify(
                md,
                signature.as_ptr(),
                signature.len(),
                message.as_ptr(),
                message.len(),
            );
            let provider = name(EVP_PKEY_CTX_get0_provider(pctx));
            EVP_MD_CTX_free(md);
            ERR_clear_error();
            (ok == 1, provider)
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { OSSL_LIB_CTX_free(self.0) };
    }
}

struct Key(*mut EVP_PKEY);

impl Key {
    fn provider(&self) -> String {
        name(unsafe { EVP_PKEY_get0_provider(self.0) })
    }

    /// The octet string parameter `param`, if the key has it.
    fn octets(&self, param: &CStr) -> Option<Vec<u8>> {
        let mut out = vec![0; 8192];
        let mut len = 0;
        let ok = unsafe {
            EVP_PKEY_get_octet_string_param(
                self.0,
                param.as_ptr(),
                out.as_mut_ptr(),
                out.len(),
                &mut len,
            )
        };
        unsafe { ERR_clear_error() };
        (ok == 1).then(|| {
            out.truncate(len);
            out
        })
    }

    fn eq(&self, other: &Key) -> bool {
        unsafe { EVP_PKEY_eq(self.0, other.0) == 1 }
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        unsafe { EVP_PKEY_free(self.0) };
    }
}

/// rind backs ML-KEM and ML-DSA keys and operations, including the ML-KEM-768
/// that OpenSSL's hybrid X25519MLKEM768 fetches.
#[test]
fn rind_backs_ml_kem_and_ml_dsa() {
    let ctx = Context::new();
    for algorithm in ML_KEM.iter().chain(&ML_DSA) {
        assert_eq!(ctx.generate(algorithm, None, None).provider(), "rind");
    }
    for algorithm in ML_KEM {
        let kem = non_null(unsafe { EVP_KEM_fetch(ctx.0, algorithm.as_ptr(), null()) });
        assert_eq!(name(unsafe { EVP_KEM_get0_provider(kem) }), "rind");
        unsafe { EVP_KEM_free(kem) };
    }
    for algorithm in ML_DSA {
        let signature = non_null(unsafe { EVP_SIGNATURE_fetch(ctx.0, algorithm.as_ptr(), null()) });
        assert_eq!(
            name(unsafe { EVP_SIGNATURE_get0_provider(signature) }),
            "rind"
        );
        unsafe { EVP_SIGNATURE_free(signature) };
    }
}

/// Collects each TLS signature scheme a provider offers: its name, and its
/// code point, which `ssl/t1_lib.c` takes as `uint`.
unsafe extern "C" fn collect_sigalg(params: *const OSSL_PARAM, sigalgs: *mut c_void) -> c_int {
    let (mut name, mut code_point) = (null(), 0);
    unsafe {
        let found = OSSL_PARAM_locate_const(params, c"tls-sigalg-iana-name".as_ptr());
        assert!(!found.is_null());
        assert_eq!(OSSL_PARAM_get_utf8_string_ptr(found, &mut name), 1);
        let found = OSSL_PARAM_locate_const(params, c"tls-sigalg-code-point".as_ptr());
        assert!(!found.is_null());
        assert_eq!(OSSL_PARAM_get_uint(found, &mut code_point), 1);
        let sigalgs = &mut *sigalgs.cast::<Vec<(String, u32)>>();
        sigalgs.push((CStr::from_ptr(name).to_str().unwrap().into(), code_point));
    }
    1
}

/// TLS offers a provider's signature scheme only when that provider also
/// backs its key type, so with rind preferred the default provider's ML-DSA
/// schemes are dropped and rind lists them. Only the handshake below shows
/// that; this shows what rind lists on every release.
#[test]
fn rind_offers_the_ml_dsa_tls_sigalgs() {
    let ctx = Context::new();
    let provider = non_null(unsafe { OSSL_PROVIDER_try_load(ctx.0, c"rind".as_ptr(), 1) });
    let mut sigalgs: Vec<(String, u32)> = Vec::new();
    check(unsafe {
        OSSL_PROVIDER_get_capabilities(
            provider,
            c"TLS-SIGALG".as_ptr(),
            collect_sigalg,
            (&raw mut sigalgs).cast(),
        )
    });
    // draft-ietf-tls-mldsa's code points.
    assert_eq!(
        sigalgs,
        [
            ("mldsa44".to_string(), 0x0904),
            ("mldsa65".to_string(), 0x0905),
            ("mldsa87".to_string(), 0x0906),
        ]
    );
}

/// A key generated from a seed is the default provider's from that seed,
/// each way: the same seed, expanded private key, and public key.
#[test]
fn keys_from_a_seed_match_the_default_provider() {
    if !has_reference("keys_from_a_seed_match_the_default_provider") {
        return;
    }
    let ctx = Context::new();
    for algorithm in ML_KEM.iter().chain(&ML_DSA) {
        let theirs = ctx.generate(algorithm, Some(DEFAULT), None);
        assert_eq!(theirs.provider(), "default");
        let seed = theirs.octets(c"seed").unwrap();
        let ours = ctx.generate(algorithm, Some(RIND), Some(&seed));
        assert_eq!(ours.provider(), "rind");
        assert_eq!(ours.octets(c"seed").unwrap(), seed);
        assert_eq!(ours.octets(c"pub"), theirs.octets(c"pub"));
        assert!(ours.eq(&theirs));
        if ML_KEM.contains(algorithm) {
            assert_eq!(ours.octets(c"priv"), theirs.octets(c"priv"));
            // What TLS reads to send the key share.
            assert_eq!(ours.octets(c"encoded-pub-key"), theirs.octets(c"pub"));
        } else {
            // rind keeps an ML-DSA key's seed, not its expansion, which
            // OpenSSL's `priv` asks for: the README lists it.
            assert_eq!(ours.octets(c"priv"), None);
        }

        // And rind's fresh key, given to the default provider.
        let ours = ctx.generate(algorithm, Some(RIND), None);
        let seed = ours.octets(c"seed").unwrap();
        let theirs = ctx.generate(algorithm, Some(DEFAULT), Some(&seed));
        assert_eq!(ours.octets(c"pub"), theirs.octets(c"pub"));
    }
}

/// A generation context given a seed reuses it as the default provider
/// does: for every ML-DSA key it generates, and for only the first ML-KEM
/// key, after which it generates fresh ones. Both drop a seed when a
/// replacement for it is refused.
#[test]
fn a_generation_seed_is_reused_as_the_default_provider_reuses_it() {
    if !has_reference("a_generation_seed_is_reused_as_the_default_provider_reuses_it") {
        return;
    }
    let ctx = Context::new();
    for algorithm in ML_KEM.iter().chain(&ML_DSA) {
        let seed = vec![7u8; if ML_KEM.contains(algorithm) { 64 } else { 32 }];
        let mut long = seed.clone();
        long.push(7);
        // Two keys from one context given `seed`, then `refused` if any,
        // which it refuses.
        let generate = |propq: &CStr, refused: Option<&[u8]>| unsafe {
            let gen_ctx = non_null(EVP_PKEY_CTX_new_from_name(
                ctx.0,
                algorithm.as_ptr(),
                propq.as_ptr(),
            ));
            check(EVP_PKEY_keygen_init(gen_ctx));
            for (i, seed) in [Some(&seed[..]), refused].into_iter().flatten().enumerate() {
                let mut seed = seed.to_vec();
                let params = [
                    OSSL_PARAM_construct_octet_string(
                        c"seed".as_ptr(),
                        seed.as_mut_ptr().cast(),
                        seed.len(),
                    ),
                    OSSL_PARAM_construct_end(),
                ];
                let ok = EVP_PKEY_CTX_set_params(gen_ctx, params.as_ptr());
                assert_eq!(ok == 1, i == 0, "{algorithm:?} {propq:?}");
            }
            ERR_clear_error();
            let keys = [(); 2].map(|()| {
                let mut key = null_mut();
                check(EVP_PKEY_generate(gen_ctx, &mut key));
                Key(key)
            });
            EVP_PKEY_CTX_free(gen_ctx);
            keys
        };
        let [first, second] = generate(RIND, None);
        assert_eq!(first.provider(), "rind");
        let [theirs, theirs_again] = generate(DEFAULT, None);
        assert!(first.eq(&theirs), "{algorithm:?}");
        assert_eq!(second.eq(&first), theirs_again.eq(&theirs), "{algorithm:?}");
        assert_eq!(
            second.eq(&first),
            ML_DSA.contains(algorithm),
            "{algorithm:?}"
        );
        for propq in [RIND, DEFAULT] {
            let [fresh, _] = generate(propq, Some(&long));
            assert!(!fresh.eq(&first), "{algorithm:?} {propq:?}");
        }
    }
}

/// Each provider decapsulates what the other encapsulates, to keys either
/// made, and both reject a tampered ciphertext to the same implicit secret.
#[test]
fn ml_kem_agrees_with_the_default_provider() {
    let ctx = Context::new();
    let reference = has_reference("ml_kem_agrees_with_the_default_provider (the cross-checks)");
    for algorithm in ML_KEM {
        let ours = ctx.generate(algorithm, None, None);
        let (ct, secret, provider) = ctx.encapsulate(&ours, None).unwrap();
        assert_eq!((secret.len(), provider.as_str()), (32, "rind"));
        assert_eq!(
            ctx.decapsulate(&ours, None, &ct).unwrap(),
            (secret.clone(), "rind".into())
        );
        let mut tampered = ct.clone();
        tampered[0] ^= 1;
        let (rejected, _) = ctx.decapsulate(&ours, None, &tampered).unwrap();
        assert_ne!(rejected, secret);
        // A ciphertext of another length is refused, not rejected implicitly.
        assert!(ctx.decapsulate(&ours, None, &ct[1..]).is_err());

        if !reference {
            continue;
        }
        // The key moves to the default provider to encapsulate, and back.
        let (ct, secret, provider) = ctx.encapsulate(&ours, Some(DEFAULT)).unwrap();
        assert_eq!(provider, "default");
        assert_eq!(ctx.decapsulate(&ours, None, &ct).unwrap().0, secret);
        assert_eq!(
            ctx.decapsulate(&ours, Some(DEFAULT), &tampered).unwrap().0,
            rejected
        );

        let theirs = ctx.generate(algorithm, Some(DEFAULT), None);
        let (ct, secret, provider) = ctx.encapsulate(&theirs, None).unwrap();
        assert_eq!(provider, "rind");
        assert_eq!(
            ctx.decapsulate(&theirs, Some(DEFAULT), &ct).unwrap(),
            (secret.clone(), "default".into())
        );
        assert_eq!(
            ctx.decapsulate(&theirs, None, &ct).unwrap(),
            (secret, "rind".into())
        );
    }
}

/// A key given only its expanded form, FIPS 203's `dk`, which has no seed,
/// loads into rind and decapsulates as the default provider does; one whose
/// embedded public key hash is wrong is refused at each use.
#[test]
fn ml_kem_loads_an_expanded_key() {
    if !has_reference("ml_kem_loads_an_expanded_key") {
        return;
    }
    let ctx = Context::new();
    for algorithm in ML_KEM {
        let theirs = ctx.generate(algorithm, Some(DEFAULT), None);
        let private = theirs.octets(c"priv").unwrap();
        let public = theirs.octets(c"pub").unwrap();
        let ours = ctx
            .load(algorithm, RIND, EVP_PKEY_KEYPAIR, &[(c"priv", &private)])
            .unwrap();
        assert_eq!(ours.provider(), "rind");
        assert_eq!(ours.octets(c"seed"), None);
        assert_eq!(ours.octets(c"priv").unwrap(), private);
        assert_eq!(ours.octets(c"pub").unwrap(), public);
        let (ct, secret, _) = ctx.encapsulate(&theirs, Some(DEFAULT)).unwrap();
        assert_eq!(
            ctx.decapsulate(&ours, None, &ct).unwrap(),
            (secret, "rind".into())
        );

        // `H(ek)` sits 64 bytes from the end.
        let mut corrupt = private.clone();
        let at = corrupt.len() - 64;
        corrupt[at] ^= 1;
        let refused = ctx
            .load(algorithm, RIND, EVP_PKEY_KEYPAIR, &[(c"priv", &corrupt)])
            .unwrap();
        let error = ctx.decapsulate(&refused, None, &ct).unwrap_err();
        assert!(error.contains("key rejected"), "{error}");

        // Another key's secret vector, `dkPKE`, which FIPS 203's checks
        // pass beside this key's public half: only a pairwise test finds it.
        let other = ctx
            .generate(algorithm, Some(DEFAULT), None)
            .octets(c"priv")
            .unwrap();
        let mut spliced = private.clone();
        let k = (spliced.len() - 96) / 768;
        spliced[..384 * k].copy_from_slice(&other[..384 * k]);
        let refused = ctx
            .load(algorithm, RIND, EVP_PKEY_KEYPAIR, &[(c"priv", &spliced)])
            .unwrap();
        let error = ctx.decapsulate(&refused, None, &ct).unwrap_err();
        assert!(error.contains("not a pair"), "{error}");
    }
}

/// Each provider verifies what the other signs, with keys either made, and
/// neither verifies a tampered signature or message.
#[test]
fn ml_dsa_agrees_with_the_default_provider() {
    let ctx = Context::new();
    let reference = has_reference("ml_dsa_agrees_with_the_default_provider (the cross-checks)");
    let message = b"rind as an OpenSSL provider";
    for algorithm in ML_DSA {
        let ours = ctx.generate(algorithm, None, None);
        let (signature, provider) = ctx.sign(&ours, message, None, null()).unwrap();
        assert_eq!(provider, "rind");
        assert_eq!(
            ctx.verify(&ours, None, message, &signature),
            (true, "rind".into())
        );
        assert!(!ctx.verify(&ours, None, b"another message", &signature).0);
        assert!(!ctx.verify(&ours, None, message, &signature[1..]).0);
        let mut tampered = signature.clone();
        tampered[0] ^= 1;
        assert!(!ctx.verify(&ours, None, message, &tampered).0);

        if !reference {
            continue;
        }
        assert_eq!(
            ctx.verify(&ours, Some(DEFAULT), message, &signature),
            (true, "default".into())
        );
        assert!(!ctx.verify(&ours, Some(DEFAULT), message, &tampered).0);
        let (signature, provider) = ctx.sign(&ours, message, Some(DEFAULT), null()).unwrap();
        assert_eq!(provider, "default");
        assert!(ctx.verify(&ours, None, message, &signature).0);

        let theirs = ctx.generate(algorithm, Some(DEFAULT), None);
        let (signature, provider) = ctx.sign(&theirs, message, None, null()).unwrap();
        assert_eq!(provider, "rind");
        assert!(ctx.verify(&theirs, Some(DEFAULT), message, &signature).0);

        // A key given only its expanded form signs as one from its seed.
        let private = theirs.octets(c"priv").unwrap();
        let expanded = ctx
            .load(algorithm, RIND, EVP_PKEY_KEYPAIR, &[(c"priv", &private)])
            .unwrap();
        assert_eq!(expanded.provider(), "rind");
        assert_eq!(expanded.octets(c"priv").unwrap(), private);
        assert!(expanded.eq(&theirs));
        let (signature, _) = ctx.sign(&expanded, message, None, null()).unwrap();
        assert!(ctx.verify(&theirs, Some(DEFAULT), message, &signature).0);
    }
}

/// What OpenSSL takes but rind does not back fails with rind's error, rather
/// than signing something else.
#[test]
fn ml_dsa_refuses_what_rind_cannot_back() {
    let ctx = Context::new();
    let key = ctx.generate(c"ML-DSA-65", None, None);
    let mut context = *b"context";
    let mut entropy = [0u8; 32];
    let (mut deterministic, mut raw, mut mu) = (1 as c_int, 0 as c_int, 1 as c_int);
    let cases = unsafe {
        [
            OSSL_PARAM_construct_octet_string(
                c"context-string".as_ptr(),
                context.as_mut_ptr().cast(),
                context.len(),
            ),
            OSSL_PARAM_construct_octet_string(
                c"test-entropy".as_ptr(),
                entropy.as_mut_ptr().cast(),
                entropy.len(),
            ),
            OSSL_PARAM_construct_int(c"deterministic".as_ptr(), &mut deterministic),
            OSSL_PARAM_construct_int(c"message-encoding".as_ptr(), &mut raw),
            OSSL_PARAM_construct_int(c"mu".as_ptr(), &mut mu),
        ]
    };
    for case in cases {
        let params = [case, unsafe { OSSL_PARAM_construct_end() }];
        let error = ctx
            .sign(&key, b"message", None, params.as_ptr())
            .unwrap_err();
        assert!(error.contains("unsupported by rind"), "{error}");
    }
    // The empty context string is pure ML-DSA's own.
    let params = unsafe {
        [
            OSSL_PARAM_construct_octet_string(
                c"context-string".as_ptr(),
                context.as_mut_ptr().cast(),
                0,
            ),
            OSSL_PARAM_construct_end(),
        ]
    };
    ctx.sign(&key, b"message", None, params.as_ptr()).unwrap();

    // OpenSSL signs with fresh randomness at `deterministic` 2.
    let mut hedged = 2 as c_int;
    let params = unsafe {
        [
            OSSL_PARAM_construct_int(c"deterministic".as_ptr(), &mut hedged),
            OSSL_PARAM_construct_end(),
        ]
    };
    ctx.sign(&key, b"message", None, params.as_ptr()).unwrap();

    // Test entropy of the wrong size is refused and drops what was set
    // before.
    unsafe {
        let (md, pctx) = sign_init(&ctx, &key);
        let entropy = |len| {
            [
                OSSL_PARAM_construct_octet_string(
                    c"test-entropy".as_ptr(),
                    entropy.as_ptr().cast_mut().cast(),
                    len,
                ),
                OSSL_PARAM_construct_end(),
            ]
        };
        check(EVP_PKEY_CTX_set_params(pctx, entropy(32).as_ptr()));
        assert_ne!(EVP_PKEY_CTX_set_params(pctx, entropy(1).as_ptr()), 1);
        assert!(errors().contains("32 bytes"));
        assert_eq!(digest_sign(md), Ok(()));
        EVP_MD_CTX_free(md);
    }
}

/// OpenSSL's ML-DSA stores `deterministic` as it reads it, ahead of the
/// parameters after it (`ml_dsa_set_ctx_params` in OpenSSL 3.5's
/// `ml_dsa_sig.c` reads the context string, test entropy, `deterministic`,
/// message encoding, then `mu`), so a call it refuses after that leaves the
/// operation deterministic, which rind then refuses to sign. OpenSSL reads
/// `deterministic` as an `int`, refusing a value outside that range without
/// storing it.
#[test]
fn ml_dsa_keeps_what_was_set_before_a_refusal() {
    let ctx = Context::new();
    let key = ctx.generate(c"ML-DSA-65", None, None);
    let (mut deterministic, mut raw) = (1 as c_int, 0 as c_int);
    unsafe {
        let (md, pctx) = sign_init(&ctx, &key);
        let params = [
            OSSL_PARAM_construct_int(c"deterministic".as_ptr(), &mut deterministic),
            OSSL_PARAM_construct_int(c"message-encoding".as_ptr(), &mut raw),
            OSSL_PARAM_construct_end(),
        ];
        assert_ne!(EVP_PKEY_CTX_set_params(pctx, params.as_ptr()), 1);
        ERR_clear_error();
        let error = digest_sign(md).unwrap_err();
        assert!(error.contains("hedged, not deterministically"), "{error}");
        EVP_MD_CTX_free(md);

        // 2^32 + 1 is 1 when truncated to an `int`, so it is refused whole.
        let (md, pctx) = sign_init(&ctx, &key);
        let mut wide = (1_i64 << 32) | 1;
        let params = [
            OSSL_PARAM_construct_int64(c"deterministic".as_ptr(), &mut wide),
            OSSL_PARAM_construct_end(),
        ];
        assert_ne!(EVP_PKEY_CTX_set_params(pctx, params.as_ptr()), 1);
        ERR_clear_error();
        assert_eq!(digest_sign(md), Ok(()));
        EVP_MD_CTX_free(md);
    }
}

/// A signing operation on `key`, under rind.
unsafe fn sign_init(ctx: &Context, key: &Key) -> (*mut EVP_MD_CTX, *mut EVP_PKEY_CTX) {
    unsafe {
        let md = non_null(EVP_MD_CTX_new());
        let mut pctx = null_mut();
        check(EVP_DigestSignInit_ex(
            md,
            &mut pctx,
            null(),
            ctx.0,
            RIND.as_ptr(),
            key.0,
            null(),
        ));
        (md, pctx)
    }
}

/// Signs a message, as the operation's parameters allow.
unsafe fn digest_sign(md: *mut EVP_MD_CTX) -> Result<(), String> {
    unsafe {
        let message = b"message";
        let mut len = 0;
        check(EVP_DigestSign(
            md,
            null_mut(),
            &mut len,
            message.as_ptr(),
            message.len(),
        ));
        let mut signature = vec![0; len];
        if EVP_DigestSign(
            md,
            signature.as_mut_ptr(),
            &mut len,
            message.as_ptr(),
            message.len(),
        ) != 1
        {
            return Err(errors());
        }
        Ok(())
    }
}

/// An ML-KEM operation takes what the default provider's does: `ikme`,
/// which rind refuses to encapsulate with, is ignored by decapsulation,
/// so one array can serve both, and neither duplicates its context.
#[test]
fn ml_kem_operations_take_what_the_default_provider_takes() {
    let ctx = Context::new();
    let reference =
        has_reference("ml_kem_operations_take_what_the_default_provider_takes (the cross-checks)");
    let key = ctx.generate(c"ML-KEM-768", None, None);
    let mut ikme = [0u8; 32];
    let params = unsafe {
        [
            OSSL_PARAM_construct_octet_string(
                c"ikme".as_ptr(),
                ikme.as_mut_ptr().cast(),
                ikme.len(),
            ),
            OSSL_PARAM_construct_end(),
        ]
    };
    unsafe {
        let pctx = non_null(EVP_PKEY_CTX_new_from_pkey(ctx.0, key.0, RIND.as_ptr()));
        assert_ne!(EVP_PKEY_encapsulate_init(pctx, params.as_ptr()), 1);
        assert!(errors().contains("unsupported by rind"));
        EVP_PKEY_CTX_free(pctx);
    }
    for propq in [RIND].into_iter().chain(reference.then_some(DEFAULT)) {
        unsafe {
            let pctx = non_null(EVP_PKEY_CTX_new_from_pkey(ctx.0, key.0, propq.as_ptr()));
            check(EVP_PKEY_decapsulate_init(pctx, params.as_ptr()));
            assert_eq!(
                name(EVP_PKEY_CTX_get0_provider(pctx)),
                &propq.to_str().unwrap()[9..]
            );
            assert!(EVP_PKEY_CTX_dup(pctx).is_null(), "{propq:?}");
            ERR_clear_error();
            EVP_PKEY_CTX_free(pctx);
        }
    }
}

/// A private key beside another's public key, or a seed beside another's
/// expansion, fails each use with rind's error: were rind to refuse the
/// import instead, OpenSSL would run the use on the default provider.
#[test]
fn a_mismatched_key_fails_every_use() {
    let ctx = Context::new();
    for algorithm in ML_KEM.iter().chain(&ML_DSA) {
        let ours = ctx.generate(algorithm, None, None);
        let theirs = ctx.generate(algorithm, None, None);
        let seed = ours.octets(c"seed").unwrap();
        let public = theirs.octets(c"pub").unwrap();
        let mut cases = vec![[(c"seed", &seed[..]), (c"pub", &public[..])]];
        let expanded = theirs.octets(c"priv");
        if let Some(expanded) = &expanded {
            cases.push([(c"seed", &seed[..]), (c"priv", &expanded[..])]);
        }
        for params in cases {
            let key = ctx
                .load(algorithm, RIND, EVP_PKEY_KEYPAIR, &params)
                .unwrap();
            assert_eq!(key.provider(), "rind");
            let error = if ML_KEM.contains(algorithm) {
                let (ct, _, _) = ctx.encapsulate(&ours, None).unwrap();
                ctx.decapsulate(&key, None, &ct).unwrap_err()
            } else {
                ctx.sign(&key, b"message", None, null()).unwrap_err()
            };
            assert!(error.contains("key rejected"), "{algorithm:?}: {error}");
        }
    }
}

/// Keys move through OpenSSL's encoders and decoders, which are the default
/// provider's, and come back usable.
#[test]
fn keys_round_trip_through_pem() {
    if !has_reference("keys_round_trip_through_pem") {
        return;
    }
    let ctx = Context::new();
    for algorithm in ML_KEM.iter().chain(&ML_DSA) {
        let key = ctx.generate(algorithm, None, None);
        unsafe {
            let bio = non_null(BIO_new(BIO_s_mem()));
            check(PEM_write_bio_PrivateKey(
                bio,
                key.0,
                null(),
                null_mut(),
                0,
                None,
                null_mut(),
            ));
            let decoded = Key(non_null(PEM_read_bio_PrivateKey_ex(
                bio,
                null_mut(),
                null_mut(),
                null_mut(),
                ctx.0,
                null(),
            )));
            check(PEM_write_bio_PUBKEY(bio, key.0));
            let public = Key(non_null(PEM_read_bio_PUBKEY_ex(
                bio,
                null_mut(),
                null_mut(),
                null_mut(),
                ctx.0,
                null(),
            )));
            BIO_free_all(bio);
            assert!(decoded.eq(&key) && public.eq(&key));
            assert_eq!(decoded.octets(c"seed"), key.octets(c"seed"));

            if ML_KEM.contains(algorithm) {
                let (ct, secret, _) = ctx.encapsulate(&public, None).unwrap();
                assert_eq!(
                    ctx.decapsulate(&decoded, None, &ct).unwrap(),
                    (secret, "rind".into())
                );
            } else {
                let (signature, provider) = ctx.sign(&decoded, b"message", None, null()).unwrap();
                assert_eq!(provider, "rind");
                assert!(ctx.verify(&public, None, b"message", &signature).0);
            }
        }
    }
}

/// A TLS 1.3 handshake whose only group is the hybrid X25519MLKEM768, which
/// OpenSSL's default provider builds from rind's ML-KEM-768 and X25519, and
/// whose certificate is an ML-DSA-65 key's, which rind signed and signs the
/// handshake with.
#[test]
fn tls13_handshake_over_x25519mlkem768_and_ml_dsa() {
    if !has_reference("tls13_handshake_over_x25519mlkem768_and_ml_dsa") {
        return;
    }
    let ctx = Context::new();
    let key = ctx.generate(c"ML-DSA-65", None, None);
    assert_eq!(key.provider(), "rind");
    unsafe {
        let cert = non_null(X509_new_ex(ctx.0, null()));
        check(X509_set_version(cert, 2));
        check(ASN1_INTEGER_set(X509_get_serialNumber(cert), 1));
        non_null(X509_gmtime_adj(X509_getm_notBefore(cert), -60));
        non_null(X509_gmtime_adj(X509_getm_notAfter(cert), 3600));
        check(X509_set_pubkey(cert, key.0));
        let name = X509_get_subject_name(cert);
        check(X509_NAME_add_entry_by_txt(
            name,
            c"CN".as_ptr(),
            MBSTRING_ASC,
            c"rind".as_ptr().cast(),
            -1,
            -1,
            0,
        ));
        check(X509_set_issuer_name(cert, name));
        assert!(X509_sign(cert, key.0, null()) > 0, "{}", errors());

        let server = non_null(SSL_CTX_new_ex(ctx.0, null(), TLS_server_method()));
        let client = non_null(SSL_CTX_new_ex(ctx.0, null(), TLS_client_method()));
        check(SSL_CTX_use_certificate(server, cert));
        check(SSL_CTX_use_PrivateKey(server, key.0));
        check(X509_STORE_add_cert(SSL_CTX_get_cert_store(client), cert));
        SSL_CTX_set_verify(client, SSL_VERIFY_PEER, None);
        for side in [server, client] {
            check(SSL_CTX_set_min_proto_version(side, TLS1_3_VERSION) as c_int);
            check(SSL_CTX_set1_groups_list(side, c"X25519MLKEM768".as_ptr()) as c_int);
            check(SSL_CTX_set1_sigalgs_list(side, c"mldsa65".as_ptr()) as c_int);
        }

        let (s, c) = (non_null(SSL_new(server)), non_null(SSL_new(client)));
        let (mut a, mut b) = (null_mut(), null_mut());
        check(BIO_new_bio_pair(&mut a, 0, &mut b, 0));
        SSL_set_bio(s, a, a);
        SSL_set_bio(c, b, b);
        SSL_set_accept_state(s);
        SSL_set_connect_state(c);
        let mut done = false;
        for _ in 0..8 {
            let (rc, rs) = (SSL_do_handshake(c), SSL_do_handshake(s));
            if rc == 1 && rs == 1 {
                done = true;
                break;
            }
            for (ssl, ret) in [(c, rc), (s, rs)] {
                let error = SSL_get_error(ssl, ret);
                assert!(
                    ret == 1 || error == SSL_ERROR_WANT_READ || error == SSL_ERROR_WANT_WRITE,
                    "handshake failed: {error}\n{}",
                    errors()
                );
            }
        }
        assert!(done, "the handshake did not finish");
        assert_eq!(SSL_get_verify_result(c), X509_V_OK as c_long);
        // X25519MLKEM768's code point, which OpenSSL tags as a group with no
        // NID of its own (`TLSEXT_nid_unknown`).
        assert_eq!(
            SSL_ctrl(c, SSL_CTRL_GET_NEGOTIATED_GROUP, 0, null_mut()),
            0x0100_0000 | 0x11ec
        );

        SSL_free(s);
        SSL_free(c);
        SSL_CTX_free(server);
        SSL_CTX_free(client);
        X509_free(cert);
    }
}
