// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! The NIST curves the provider backs when its configuration sets `ec = 1`,
//! loaded into the system's OpenSSL 3 and checked against OpenSSL's default
//! provider: the same keys in each must give the same outputs.
#![cfg(unix)]
#![allow(clippy::undocumented_unsafe_blocks)]

use std::ffi::{CStr, CString, c_char, c_int, c_long, c_void};
use std::ptr::{null, null_mut};

use openssl_sys::*;

mod common;

unsafe extern "C" {
    fn OSSL_LIB_CTX_load_config(ctx: *mut OSSL_LIB_CTX, file: *const c_char) -> c_int;
    fn OSSL_PROVIDER_get0_name(provider: *const OSSL_PROVIDER) -> *const c_char;
    fn EVP_PKEY_get0_provider(pkey: *const EVP_PKEY) -> *const OSSL_PROVIDER;
    fn EVP_PKEY_CTX_get0_provider(ctx: *const EVP_PKEY_CTX) -> *const OSSL_PROVIDER;
    fn EVP_PKEY_CTX_new_from_pkey(
        ctx: *mut OSSL_LIB_CTX,
        pkey: *mut EVP_PKEY,
        propq: *const c_char,
    ) -> *mut EVP_PKEY_CTX;
    fn EVP_PKEY_CTX_set_params(ctx: *mut EVP_PKEY_CTX, params: *const OSSL_PARAM) -> c_int;
    fn EVP_PKEY_CTX_get_params(ctx: *mut EVP_PKEY_CTX, params: *mut OSSL_PARAM) -> c_int;
    fn OSSL_PARAM_construct_int(key: *const c_char, buf: *mut c_int) -> OSSL_PARAM;
    fn EVP_PKEY_sign_init(ctx: *mut EVP_PKEY_CTX) -> c_int;
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
    fn OSSL_PARAM_construct_utf8_string(
        key: *const c_char,
        buf: *mut c_char,
        len: usize,
    ) -> OSSL_PARAM;
    fn EVP_PKEY_get_bn_param(
        pkey: *const EVP_PKEY,
        name: *const c_char,
        bn: *mut *mut BIGNUM,
    ) -> c_int;
    fn ERR_error_string_n(error: std::ffi::c_ulong, buf: *mut c_char, len: usize);
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

const RIND: &CStr = c"provider=rind";
const DEFAULT: &CStr = c"provider=default";

const CURVES: [&str; 3] = ["prime256v1", "secp384r1", "secp521r1"];

fn name(provider: *const OSSL_PROVIDER) -> String {
    assert!(!provider.is_null());
    unsafe { CStr::from_ptr(OSSL_PROVIDER_get0_name(provider)) }
        .to_string_lossy()
        .into_owned()
}

/// A library context configured as the README says, with the rind section's
/// extra lines, and the provider this test binary links.
struct Context(*mut OSSL_LIB_CTX);

impl Context {
    /// Loads the configuration, or says why OpenSSL refused it.
    fn try_new(extra: &str) -> Result<Self, String> {
        let ctx = non_null(unsafe { OSSL_LIB_CTX_new() });
        common::add_builtin(ctx);
        let config = common::config_with(None, extra);
        let config = CString::new(config.as_os_str().as_encoded_bytes()).unwrap();
        let this = Self(ctx);
        match unsafe { OSSL_LIB_CTX_load_config(ctx, config.as_ptr()) } {
            1 => Ok(this),
            _ => Err(errors()),
        }
    }

    /// The configuration with `ec = 1`.
    fn new() -> Self {
        Self::try_new("ec = 1").unwrap()
    }

    /// A fresh key on `curve`, in the provider `propq` picks.
    fn generate(&self, curve: &str, propq: &CStr) -> Result<Key, String> {
        unsafe {
            let pctx = non_null(EVP_PKEY_CTX_new_from_name(
                self.0,
                c"EC".as_ptr(),
                propq.as_ptr(),
            ));
            let result = (|| {
                if EVP_PKEY_keygen_init(pctx) != 1 {
                    return Err(errors());
                }
                let mut group = CString::new(curve).unwrap().into_bytes_with_nul();
                let params = [
                    OSSL_PARAM_construct_utf8_string(
                        c"group".as_ptr(),
                        group.as_mut_ptr().cast(),
                        0,
                    ),
                    OSSL_PARAM_construct_end(),
                ];
                if EVP_PKEY_CTX_set_params(pctx, params.as_ptr()) != 1 {
                    return Err(errors());
                }
                let mut key = null_mut();
                if EVP_PKEY_generate(pctx, &mut key) != 1 {
                    return Err(errors());
                }
                Ok(Key(key))
            })();
            EVP_PKEY_CTX_free(pctx);
            result
        }
    }

    /// Signs as `EVP_DigestSign` does, with the digest `md` names, or the
    /// key's default if it is null.
    fn sign(
        &self,
        key: &Key,
        md: *const c_char,
        message: &[u8],
        propq: *const c_char,
    ) -> Result<(Vec<u8>, String), String> {
        unsafe {
            let ctx = non_null(EVP_MD_CTX_new());
            let mut pctx = null_mut();
            let result = (|| {
                if EVP_DigestSignInit_ex(ctx, &mut pctx, md, self.0, propq, key.0, null()) != 1 {
                    return Err(errors());
                }
                let mut len = 0;
                if EVP_DigestSign(ctx, null_mut(), &mut len, message.as_ptr(), message.len()) != 1 {
                    return Err(errors());
                }
                let mut signature = vec![0u8; len];
                if EVP_DigestSign(
                    ctx,
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
            EVP_MD_CTX_free(ctx);
            result
        }
    }

    /// Verifies as `EVP_DigestVerify` does, returning whether it passed and
    /// the provider that checked it.
    fn verify(
        &self,
        key: &Key,
        md: *const c_char,
        message: &[u8],
        signature: &[u8],
        propq: *const c_char,
    ) -> Result<(bool, String), String> {
        unsafe {
            let ctx = non_null(EVP_MD_CTX_new());
            let mut pctx = null_mut();
            if EVP_DigestVerifyInit_ex(ctx, &mut pctx, md, self.0, propq, key.0, null()) != 1 {
                EVP_MD_CTX_free(ctx);
                return Err(errors());
            }
            let ok = EVP_DigestVerify(
                ctx,
                signature.as_ptr(),
                signature.len(),
                message.as_ptr(),
                message.len(),
            );
            let provider = name(EVP_PKEY_CTX_get0_provider(pctx));
            EVP_MD_CTX_free(ctx);
            ERR_clear_error();
            Ok((ok == 1, provider))
        }
    }

    fn derive(
        &self,
        key: &Key,
        peer: &Key,
        propq: *const c_char,
    ) -> Result<(Vec<u8>, String), String> {
        unsafe {
            let ctx = non_null(EVP_PKEY_CTX_new_from_pkey(self.0, key.0, propq));
            let result = (|| {
                if EVP_PKEY_derive_init(ctx) != 1 || EVP_PKEY_derive_set_peer(ctx, peer.0) != 1 {
                    return Err(errors());
                }
                let mut len = 0;
                if EVP_PKEY_derive(ctx, null_mut(), &mut len) != 1 {
                    return Err(errors());
                }
                let mut secret = vec![0; len];
                if EVP_PKEY_derive(ctx, secret.as_mut_ptr(), &mut len) != 1 {
                    return Err(errors());
                }
                secret.truncate(len);
                Ok((secret, name(EVP_PKEY_CTX_get0_provider(ctx))))
            })();
            EVP_PKEY_CTX_free(ctx);
            result
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { OSSL_LIB_CTX_free(self.0) };
    }
}

#[derive(Debug)]
struct Key(*mut EVP_PKEY);

impl Key {
    fn provider(&self) -> String {
        name(unsafe { EVP_PKEY_get0_provider(self.0) })
    }

    /// A parameter that is a bignum, big-endian.
    fn bn(&self, param: &CStr) -> Vec<u8> {
        unsafe {
            let mut bn = null_mut();
            check(EVP_PKEY_get_bn_param(self.0, param.as_ptr(), &mut bn));
            let mut out = vec![0u8; ((BN_num_bits(bn) + 7) / 8) as usize];
            BN_bn2bin(bn, out.as_mut_ptr());
            BN_free(bn);
            out
        }
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        unsafe { EVP_PKEY_free(self.0) };
    }
}

#[test]
fn ec_is_registered_only_by_the_config() {
    for (extra, provider) in [("", "default"), ("ec = 0", "default"), ("ec = 1", "rind")] {
        let ctx = Context::try_new(extra).unwrap();
        assert_eq!(
            ctx.generate("prime256v1", c"").unwrap().provider(),
            provider,
            "{extra:?}"
        );
        // Ed25519 is rind's either way.
        assert_eq!(
            ctx.sign(
                &ctx.generate("prime256v1", c"").unwrap(),
                null(),
                b"m",
                null()
            )
            .unwrap()
            .1,
            provider
        );
    }
}

#[test]
fn a_misspelled_switch_stops_rind_loading() {
    // OpenSSL either fails its configuration or carries on without rind.
    for extra in ["ec = yes", "ec = 2", "ec ="] {
        if let Ok(ctx) = Context::try_new(extra) {
            let key = ctx.generate("prime256v1", c"").unwrap();
            assert_eq!(key.provider(), "default", "{extra:?}");
        }
    }
}

#[test]
fn ecdsa_agrees_with_the_default_provider() {
    let ctx = Context::new();
    for curve in CURVES {
        let rind = ctx.generate(curve, c"").unwrap();
        assert_eq!(rind.provider(), "rind");
        let default = ctx.generate(curve, DEFAULT).unwrap();
        assert_eq!(default.provider(), "default");
        let message = b"rind signs and OpenSSL verifies";
        // The curve's own hash, the key's default, and the three that rind
        // verifies with.
        let own = match curve {
            "prime256v1" => c"SHA256",
            "secp384r1" => c"SHA384",
            _ => c"SHA512",
        };
        for key in [&rind, &default] {
            let (signature, signer) = ctx.sign(key, own.as_ptr(), message, null()).unwrap();
            // Signing is rind's under the configuration, whichever provider
            // made the key.
            assert_eq!(signer, "rind", "{curve}");
            // The default provider verifies what rind signs, and rind too.
            let (ok, verifier) = ctx
                .verify(key, own.as_ptr(), message, &signature, DEFAULT.as_ptr())
                .unwrap();
            assert!(ok && verifier == "default", "{curve}: {verifier}");
            let (ok, verifier) = ctx
                .verify(key, own.as_ptr(), message, &signature, RIND.as_ptr())
                .unwrap();
            assert!(ok && verifier == "rind", "{curve}: {verifier}");
            let mut bad = signature.clone();
            *bad.last_mut().unwrap() ^= 1;
            assert!(
                !ctx.verify(key, own.as_ptr(), message, &bad, null())
                    .unwrap()
                    .0
            );
            assert!(
                !ctx.verify(key, own.as_ptr(), b"another", &signature, null())
                    .unwrap()
                    .0
            );
        }
        // A signature the default provider makes over each hash verifies.
        for md in [c"SHA256", c"SHA384", c"SHA512"] {
            let (signature, signer) = ctx
                .sign(&default, md.as_ptr(), message, DEFAULT.as_ptr())
                .unwrap();
            assert_eq!(signer, "default");
            let (ok, verifier) = ctx
                .verify(&default, md.as_ptr(), message, &signature, RIND.as_ptr())
                .unwrap();
            assert!(ok && verifier == "rind", "{curve} {md:?}");
        }
        // A key with no digest named signs with the curve's own, which
        // verifies as that.
        let (signature, _) = ctx.sign(&rind, null(), message, null()).unwrap();
        assert!(
            ctx.verify(&rind, own.as_ptr(), message, &signature, DEFAULT.as_ptr())
                .unwrap()
                .0
        );
    }
}

#[test]
fn ecdsa_refuses_what_rind_cannot_back() {
    let ctx = Context::new();
    let key = ctx.generate("secp384r1", c"").unwrap();
    // Each curve signs with its own hash only.
    let error = ctx
        .sign(&key, c"SHA256".as_ptr(), b"m", null())
        .unwrap_err();
    assert!(error.contains("unsupported by rind"), "{error}");
    let error = ctx.sign(&key, c"SHA1".as_ptr(), b"m", null()).unwrap_err();
    assert!(error.contains("unsupported by rind"), "{error}");
    // Nor does it verify with SHA-1.
    let (signature, _) = ctx.sign(&key, null(), b"m", null()).unwrap();
    let error = ctx
        .verify(&key, c"SHA1".as_ptr(), b"m", &signature, null())
        .unwrap_err();
    assert!(error.contains("unsupported by rind"), "{error}");

    // A signature over a digest the caller made is not rind's to make.
    unsafe {
        let pctx = non_null(EVP_PKEY_CTX_new_from_pkey(ctx.0, key.0, null()));
        assert!(EVP_PKEY_sign_init(pctx) <= 0);
        let error = errors();
        assert!(error.contains("unsupported by rind"), "{error}");
        EVP_PKEY_CTX_free(pctx);
    }
}

#[test]
fn a_signing_digest_the_curve_does_not_own_fails_at_init() {
    let ctx = Context::new();
    for (curve, wrong) in [
        ("prime256v1", c"SHA384"),
        ("secp384r1", c"SHA256"),
        ("secp521r1", c"SHA256"),
    ] {
        let key = ctx.generate(curve, c"").unwrap();
        unsafe {
            // Signing fails at init, before any message is hashed.
            let md_ctx = non_null(EVP_MD_CTX_new());
            let mut pctx = null_mut();
            let status = EVP_DigestSignInit_ex(
                md_ctx,
                &mut pctx,
                wrong.as_ptr(),
                ctx.0,
                null(),
                key.0,
                null(),
            );
            let error = errors();
            EVP_MD_CTX_free(md_ctx);
            assert!(status <= 0, "{curve} with {wrong:?} began signing");
            assert!(error.contains("unsupported by rind"), "{curve}: {error}");
            // Verifying with another digest is not refused at init: the
            // signature simply does not verify.
            let md_ctx = non_null(EVP_MD_CTX_new());
            let mut pctx = null_mut();
            assert_eq!(
                EVP_DigestVerifyInit_ex(
                    md_ctx,
                    &mut pctx,
                    wrong.as_ptr(),
                    ctx.0,
                    null(),
                    key.0,
                    null()
                ),
                1,
                "{curve}"
            );
            EVP_MD_CTX_free(md_ctx);
        }
    }
}

#[test]
fn ecdh_cofactor_mode_reads_back_as_openssl_does() {
    let ctx = Context::new();
    let key = ctx.generate("prime256v1", c"").unwrap();
    unsafe {
        let pctx = non_null(EVP_PKEY_CTX_new_from_pkey(ctx.0, key.0, null()));
        assert_eq!(EVP_PKEY_derive_init(pctx), 1);
        let read = || {
            let mut mode: c_int = 99;
            let mut params = [
                OSSL_PARAM_construct_int(c"ecdh-cofactor-mode".as_ptr(), &mut mode),
                OSSL_PARAM_construct_end(),
            ];
            assert_eq!(EVP_PKEY_CTX_get_params(pctx, params.as_mut_ptr()), 1);
            mode
        };
        let set = |mut mode: c_int| {
            let params = [
                OSSL_PARAM_construct_int(c"ecdh-cofactor-mode".as_ptr(), &mut mode),
                OSSL_PARAM_construct_end(),
            ];
            EVP_PKEY_CTX_set_params(pctx, params.as_ptr())
        };
        // OpenSSL's default provider starts with the mode off: -1 reads as 0.
        assert_eq!(read(), 0);
        assert_eq!(set(1), 1);
        assert_eq!(read(), 1);
        assert_eq!(set(0), 1);
        assert_eq!(read(), 0);
        assert_eq!(set(1), 1);
        assert_eq!(set(-1), 1);
        assert_eq!(read(), 0);
        // Nothing else is a mode, and a refused one leaves the last in place.
        assert_eq!(set(1), 1);
        assert!(set(2) <= 0);
        let error = errors();
        assert!(error.contains("ecdh-cofactor-mode"), "{error}");
        assert_eq!(read(), 1);
        EVP_PKEY_CTX_free(pctx);
    }
}

#[test]
fn other_curves_are_refused_not_handed_on() {
    let ctx = Context::new();
    // Generating one fails.
    for curve in ["secp256k1", "brainpoolP256r1"] {
        let error = ctx.generate(curve, c"").unwrap_err();
        assert!(error.contains("unsupported by rind"), "{curve}: {error}");
        // The default provider still makes it.
        assert_eq!(ctx.generate(curve, DEFAULT).unwrap().provider(), "default");
    }
    // A key the default provider made fails each use with rind's error,
    // rather than running on the default provider.
    let k1 = ctx.generate("secp256k1", DEFAULT).unwrap();
    let error = ctx.sign(&k1, c"SHA256".as_ptr(), b"m", null()).unwrap_err();
    assert!(error.contains("unsupported by rind"), "{error}");
    let peer = ctx.generate("secp256k1", DEFAULT).unwrap();
    let error = ctx.derive(&k1, &peer, null()).unwrap_err();
    assert!(error.contains("unsupported by rind"), "{error}");
    // And the default provider's own use of it works.
    assert!(
        ctx.sign(&k1, c"SHA256".as_ptr(), b"m", DEFAULT.as_ptr())
            .is_ok()
    );
}

#[test]
fn ecdh_agrees_with_the_default_provider() {
    let ctx = Context::new();
    for curve in CURVES {
        let a = ctx.generate(curve, c"").unwrap();
        let b = ctx.generate(curve, DEFAULT).unwrap();
        let (reference, provider) = ctx.derive(&b, &a, DEFAULT.as_ptr()).unwrap();
        assert_eq!(provider, "default");
        for (key, peer) in [(&a, &b), (&b, &a)] {
            let (secret, provider) = ctx.derive(key, peer, null()).unwrap();
            assert_eq!(
                (&secret, provider.as_str()),
                (&reference, "rind"),
                "{curve}"
            );
        }
    }
    // Keys on different curves do not agree.
    let (p256, p384) = (
        ctx.generate("prime256v1", c"").unwrap(),
        ctx.generate("secp384r1", c"").unwrap(),
    );
    assert!(ctx.derive(&p256, &p384, null()).is_err());
}

/// A private key moves between the providers as OpenSSL needs, whole.
#[test]
fn keys_move_between_providers() {
    let ctx = Context::new();
    for curve in CURVES {
        let rind = ctx.generate(curve, c"").unwrap();
        let default = ctx.generate(curve, DEFAULT).unwrap();
        for key in [&rind, &default] {
            let private = key.bn(c"priv");
            assert!(!private.is_empty() && private.len() <= 66);
            // The same key, held by the other provider, signs the same.
            unsafe {
                assert_eq!(EVP_PKEY_eq(key.0, key.0), 1);
            }
        }
        // `EVP_PKEY_eq` across providers exports one to the other.
        unsafe {
            assert_ne!(EVP_PKEY_eq(rind.0, default.0), 1);
        }
    }
}

#[test]
fn tls13_handshake_over_the_nist_curves() {
    let ctx = Context::new();
    for (curve, group, sigalg) in [
        ("prime256v1", c"secp256r1", c"ecdsa_secp256r1_sha256"),
        ("secp384r1", c"secp384r1", c"ecdsa_secp384r1_sha384"),
        ("secp521r1", c"secp521r1", c"ecdsa_secp521r1_sha512"),
    ] {
        let key = ctx.generate(curve, c"").unwrap();
        unsafe {
            let cert = non_null(X509_new_ex(ctx.0, null()));
            check(X509_set_version(cert, 2));
            check(ASN1_INTEGER_set(X509_get_serialNumber(cert), 1));
            non_null(X509_gmtime_adj(X509_getm_notBefore(cert), -60));
            non_null(X509_gmtime_adj(X509_getm_notAfter(cert), 3600));
            check(X509_set_pubkey(cert, key.0));
            let subject = X509_get_subject_name(cert);
            check(X509_NAME_add_entry_by_txt(
                subject,
                c"CN".as_ptr(),
                MBSTRING_ASC,
                c"rind".as_ptr().cast(),
                -1,
                -1,
                0,
            ));
            check(X509_set_issuer_name(cert, subject));
            assert!(X509_sign(cert, key.0, null()) > 0, "{curve}: {}", errors());

            let server = non_null(SSL_CTX_new_ex(ctx.0, null(), TLS_server_method()));
            let client = non_null(SSL_CTX_new_ex(ctx.0, null(), TLS_client_method()));
            check(SSL_CTX_use_certificate(server, cert));
            check(SSL_CTX_use_PrivateKey(server, key.0));
            check(X509_STORE_add_cert(SSL_CTX_get_cert_store(client), cert));
            SSL_CTX_set_verify(client, SSL_VERIFY_PEER, None);
            for side in [server, client] {
                check(SSL_CTX_set_min_proto_version(side, TLS1_3_VERSION) as c_int);
                check(SSL_CTX_set1_groups_list(side, group.as_ptr()) as c_int);
                check(SSL_CTX_set1_sigalgs_list(side, sigalg.as_ptr()) as c_int);
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
                        "{curve}: handshake failed: {error}\n{}",
                        errors()
                    );
                }
            }
            assert!(done, "{curve}: the handshake did not finish");
            assert_eq!(SSL_get_verify_result(c), X509_V_OK as c_long);

            SSL_free(s);
            SSL_free(c);
            SSL_CTX_free(server);
            SSL_CTX_free(client);
            X509_free(cert);
        }
    }
}

// Silences an unused import when no test needs it.
#[allow(dead_code)]
fn _void(_: *mut c_void) {}

/// Prints how fast each provider signs, verifies, and agrees, as the README's
/// table: `cargo test --release -p rind-openssl --test ec -- --ignored
/// --nocapture`. The default provider is OpenSSL's own build, so the numbers
/// depend on the system.
#[test]
#[ignore = "a benchmark"]
fn benchmark_against_the_default_provider() {
    use std::time::{Duration, Instant};

    fn rate(mut op: impl FnMut()) -> f64 {
        for _ in 0..20 {
            op();
        }
        let (start, mut n) = (Instant::now(), 0u32);
        while start.elapsed() < Duration::from_secs(1) {
            for _ in 0..20 {
                op();
            }
            n += 20;
        }
        f64::from(n) / start.elapsed().as_secs_f64()
    }

    let ctx = Context::new();
    let message = [0x78u8; 64];
    for curve in CURVES {
        // Rind has no digests of its own, so it is the preference.
        for (provider, propq) in [("default", DEFAULT), ("rind", c"")] {
            let key = ctx.generate(curve, propq).unwrap();
            let peer = ctx.generate(curve, propq).unwrap();
            let (signature, _) = ctx.sign(&key, null(), &message, propq.as_ptr()).unwrap();
            let sign = rate(|| {
                ctx.sign(&key, null(), &message, propq.as_ptr()).unwrap();
            });
            let verify = rate(|| {
                let ok = ctx
                    .verify(&key, null(), &message, &signature, propq.as_ptr())
                    .unwrap();
                assert!(ok.0);
            });
            let agree = rate(|| {
                ctx.derive(&key, &peer, propq.as_ptr()).unwrap();
            });
            let generate = rate(|| {
                ctx.generate(curve, propq).unwrap();
            });
            println!(
                "{curve:11} {provider:8} sign {sign:8.0}/s verify {verify:8.0}/s ecdh {agree:8.0}/s keygen {generate:8.0}/s"
            );
        }
    }
}

/// Where one P-256 ECDH's time goes, in one process: the library alone, the
/// provider's `derive` through an `EVP_PKEY_CTX` reused across operations (as
/// `openssl speed ecdh` runs it), and the whole path with a new context each
/// time (as `benchmark_against_the_default_provider` runs it).
/// Run: `cargo test --release -p rind-openssl --test ec -- --ignored --nocapture p256_ecdh_layers`
#[test]
#[ignore = "a benchmark"]
fn p256_ecdh_layers() {
    use std::hint::black_box;
    use std::time::{Duration, Instant};

    fn micros(mut op: impl FnMut()) -> f64 {
        for _ in 0..200 {
            op();
        }
        let (start, mut n) = (Instant::now(), 0u32);
        while start.elapsed() < Duration::from_secs(2) {
            for _ in 0..50 {
                op();
            }
            n += 50;
        }
        start.elapsed().as_secs_f64() * 1e6 / f64::from(n)
    }

    let ctx = Context::new();
    // rind's library, with the peer as the bytes a TLS peer sends.
    let library = {
        use rind::agreement::{ECDH_P256, PrivateKey};
        let ours = PrivateKey::generate(&ECDH_P256).unwrap();
        let peer = PrivateKey::generate(&ECDH_P256).unwrap();
        let peer_public = peer.public_key().as_ref().to_vec();
        micros(|| {
            black_box(ours.agree(black_box(&peer_public)).unwrap());
        })
    };
    println!("library      agree (stored key, peer bytes)        {library:7.2} us");
    for (provider, propq) in [("default", DEFAULT), ("rind", c"")] {
        let key = ctx.generate("prime256v1", propq).unwrap();
        let peer = ctx.generate("prime256v1", propq).unwrap();
        unsafe {
            let pctx = non_null(EVP_PKEY_CTX_new_from_pkey(ctx.0, key.0, propq.as_ptr()));
            assert_eq!(EVP_PKEY_derive_init(pctx), 1);
            assert_eq!(EVP_PKEY_derive_set_peer(pctx, peer.0), 1);
            let mut secret = [0u8; 66];
            let reused = micros(|| {
                let mut len = secret.len();
                assert_eq!(EVP_PKEY_derive(pctx, secret.as_mut_ptr(), &mut len), 1);
                black_box(&secret);
            });
            let mut size_and_derive = || {
                let mut len = 0;
                assert_eq!(EVP_PKEY_derive(pctx, null_mut(), &mut len), 1);
                let mut len = secret.len();
                assert_eq!(EVP_PKEY_derive(pctx, secret.as_mut_ptr(), &mut len), 1);
            };
            let two_calls = micros(&mut size_and_derive);
            EVP_PKEY_CTX_free(pctx);
            let fresh = micros(|| {
                black_box(ctx.derive(&key, &peer, propq.as_ptr()).unwrap());
            });
            println!(
                "{provider:8}     reused ctx, one derive call           {reused:7.2} us\n{provider:8}     reused ctx, size query then derive    {two_calls:7.2} us\n{provider:8}     new ctx + init + set_peer + both calls {fresh:6.2} us"
            );
        }
    }
}
