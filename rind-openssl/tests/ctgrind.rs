// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! Constant-time checks for each secret path through the provider, run under
//! valgrind by `admin/ctgrind`, with keys handed in through OpenSSL's own API
//! as an application would.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. rind itself marks the private keys it
//! generates or parses.
#![cfg(unix)]
#![allow(clippy::undocumented_unsafe_blocks)]

use std::ffi::{CStr, CString, c_char, c_int};
use std::path::{Path, PathBuf};
use std::ptr::{null, null_mut};
use std::sync::OnceLock;

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use openssl_sys::*;

unsafe extern "C" {
    fn OSSL_LIB_CTX_load_config(ctx: *mut OSSL_LIB_CTX, file: *const c_char) -> c_int;
    fn OSSL_PROVIDER_get0_name(provider: *const OSSL_PROVIDER) -> *const c_char;
    fn EVP_PKEY_get0_provider(pkey: *const EVP_PKEY) -> *const OSSL_PROVIDER;
    fn EVP_PKEY_CTX_get0_provider(ctx: *const EVP_PKEY_CTX) -> *const OSSL_PROVIDER;
    fn EVP_PKEY_todata(
        pkey: *const EVP_PKEY,
        selection: c_int,
        params: *mut *mut OSSL_PARAM,
    ) -> c_int;
    fn OSSL_PARAM_free(params: *mut OSSL_PARAM);
    fn EVP_PKEY_CTX_new_from_pkey(
        ctx: *mut OSSL_LIB_CTX,
        pkey: *mut EVP_PKEY,
        propq: *const c_char,
    ) -> *mut EVP_PKEY_CTX;
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
}

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

/// Asserts rind backs a key or operation: a provider that fails to activate
/// leaves the default provider serving it, which would pass every check here.
fn assert_rind(provider: *const OSSL_PROVIDER) {
    assert!(!provider.is_null());
    assert_eq!(
        unsafe { CStr::from_ptr(OSSL_PROVIDER_get0_name(provider)) },
        c"rind"
    );
}

/// A library context with the README's configuration, loading the library
/// this build made.
fn context() -> *mut OSSL_LIB_CTX {
    static CONFIG: OnceLock<CString> = OnceLock::new();
    let path = CONFIG.get_or_init(write_config);
    unsafe {
        let ctx = OSSL_LIB_CTX_new();
        assert!(!ctx.is_null());
        assert_eq!(OSSL_LIB_CTX_load_config(ctx, path.as_ptr()), 1);
        ctx
    }
}

/// Writes the configuration once, since the tests run in parallel.
fn write_config() -> CString {
    let exe = std::env::current_exe().unwrap();
    let library = exe.with_file_name(format!(
        "{}rind_openssl{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    ));
    let config: String = include_str!("../openssl.cnf")
        .lines()
        .map(|line| match line.starts_with("module = ") {
            true => format!("module = {}\n", conf_value(&library)),
            false => format!("{line}\n"),
        })
        .collect();
    let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("rind-openssl-ctgrind-{}.cnf", std::process::id()));
    std::fs::write(&path, config).unwrap();
    CString::new(path.into_os_string().into_encoded_bytes()).unwrap()
}

/// `path` as an `openssl.cnf` value: each ASCII character but a letter,
/// digit, or `/._-` escaped, as a `#` would start a comment and a `$` a
/// variable.
fn conf_value(path: &Path) -> String {
    let mut out = String::new();
    for c in path.display().to_string().chars() {
        if c.is_ascii() && !(c.is_ascii_alphanumeric() || "/._-".contains(c)) {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

fn private_key(ctx: *mut OSSL_LIB_CTX, algorithm: &CStr, private: &[u8; 32]) -> *mut EVP_PKEY {
    let key = unsafe {
        EVP_PKEY_new_raw_private_key_ex(
            ctx,
            algorithm.as_ptr(),
            null(),
            private.as_ptr(),
            private.len(),
        )
    };
    assert!(!key.is_null());
    assert_rind(unsafe { EVP_PKEY_get0_provider(key) });
    key
}

fn raw_private(key: *mut EVP_PKEY) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut len = out.len();
    assert_eq!(
        unsafe { EVP_PKEY_get_raw_private_key(key, out.as_mut_ptr(), &mut len) },
        1
    );
    out
}

/// Exports the key pair, as encoders and other providers take it.
fn export(key: *mut EVP_PKEY) {
    const KEYPAIR: c_int = 0x03;
    let mut params = null_mut();
    unsafe {
        assert_eq!(EVP_PKEY_todata(key, KEYPAIR, &mut params), 1);
        OSSL_PARAM_free(params);
    }
}

#[test]
fn x25519() {
    let ctx = context();
    let private = [0x77u8; 32];
    secret(&private);
    let key = private_key(ctx, c"X25519", &private);
    let peer = unsafe {
        EVP_PKEY_new_raw_public_key_ex(ctx, c"X25519".as_ptr(), null(), [9u8; 32].as_ptr(), 32)
    };
    assert!(!peer.is_null());
    unsafe {
        assert_rind(EVP_PKEY_get0_provider(peer));
        let pctx = EVP_PKEY_CTX_new_from_pkey(ctx, key, null());
        assert_eq!(EVP_PKEY_derive_init(pctx), 1);
        assert_rind(EVP_PKEY_CTX_get0_provider(pctx));
        assert_eq!(EVP_PKEY_derive_set_peer(pctx, peer), 1);
        let mut shared = [0u8; 32];
        let mut len = shared.len();
        assert_eq!(EVP_PKEY_derive(pctx, shared.as_mut_ptr(), &mut len), 1);
        public(&shared);
        assert_ne!(shared, [0; 32]);
        EVP_PKEY_CTX_free(pctx);
    }

    // Reading the private key back, and generating one, which TLS does.
    export(key);
    let back = raw_private(key);
    public(&back);
    assert_eq!(back, [0x77; 32]);
    unsafe {
        let gen_ctx = EVP_PKEY_CTX_new_from_name(ctx, c"X25519".as_ptr(), null());
        assert_eq!(EVP_PKEY_keygen_init(gen_ctx), 1);
        let mut generated = null_mut();
        assert_eq!(EVP_PKEY_generate(gen_ctx, &mut generated), 1);
        EVP_PKEY_CTX_free(gen_ctx);
        assert_rind(EVP_PKEY_get0_provider(generated));
        let private = raw_private(generated);
        public(&private);
        assert_eq!(private[31] & 0xc0, 0x40);
        EVP_PKEY_free(generated);

        // RFC 9180's DeriveKeyPair, from secret input keying material.
        let mut ikm = [0x5au8; 32];
        secret(&ikm);
        let params = [
            OSSL_PARAM_construct_octet_string(
                c"dhkem-ikm".as_ptr(),
                ikm.as_mut_ptr().cast(),
                ikm.len(),
            ),
            OSSL_PARAM_construct_end(),
        ];
        let gen_ctx = EVP_PKEY_CTX_new_from_name(ctx, c"X25519".as_ptr(), null());
        assert_eq!(EVP_PKEY_keygen_init(gen_ctx), 1);
        assert_eq!(EVP_PKEY_CTX_set_params(gen_ctx, params.as_ptr()), 1);
        let mut derived = null_mut();
        assert_eq!(EVP_PKEY_generate(gen_ctx, &mut derived), 1);
        EVP_PKEY_CTX_free(gen_ctx);
        assert_rind(EVP_PKEY_get0_provider(derived));
        let private = raw_private(derived);
        public(&private);
        assert_eq!(private[31] & 0xc0, 0x40);
        EVP_PKEY_free(derived);
        EVP_PKEY_free(peer);
        EVP_PKEY_free(key);
        OSSL_LIB_CTX_free(ctx);
    }
}

#[test]
fn ed25519() {
    let ctx = context();
    let seed = [0x9du8; 32];
    secret(&seed);
    let key = private_key(ctx, c"ED25519", &seed);
    let message = b"rind as an OpenSSL provider";
    unsafe {
        let md = EVP_MD_CTX_new();
        let mut pctx = null_mut();
        assert_eq!(
            EVP_DigestSignInit_ex(md, &mut pctx, null(), ctx, null(), key, null()),
            1
        );
        assert_rind(EVP_PKEY_CTX_get0_provider(pctx));
        let mut signature = [0u8; 64];
        let mut len = signature.len();
        assert_eq!(
            EVP_DigestSign(
                md,
                signature.as_mut_ptr(),
                &mut len,
                message.as_ptr(),
                message.len()
            ),
            1
        );
        public(&signature);
        EVP_MD_CTX_free(md);

        let md = EVP_MD_CTX_new();
        let mut pctx = null_mut();
        assert_eq!(
            EVP_DigestVerifyInit_ex(md, &mut pctx, null(), ctx, null(), key, null()),
            1
        );
        assert_rind(EVP_PKEY_CTX_get0_provider(pctx));
        assert_eq!(
            EVP_DigestVerify(md, signature.as_ptr(), len, message.as_ptr(), message.len()),
            1
        );
        EVP_MD_CTX_free(md);
    }
    // Two keys from the same secret seed match.
    let again = private_key(ctx, c"ED25519", &seed);
    assert_eq!(unsafe { EVP_PKEY_eq(key, again) }, 1);
    export(key);
    let back = raw_private(key);
    public(&back);
    assert_eq!(back, [0x9d; 32]);
    unsafe {
        EVP_PKEY_free(again);
        EVP_PKEY_free(key);
        OSSL_LIB_CTX_free(ctx);
    }
}
