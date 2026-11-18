// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! The provider this crate builds, loaded into the system's OpenSSL 3 with
//! the configuration the README documents, checked against OpenSSL's default
//! provider: the same keys in each must give the same outputs.
#![cfg(unix)]
#![allow(clippy::undocumented_unsafe_blocks)]

use std::ffi::{CStr, CString, c_char, c_int, c_long, c_uint, c_void};
use std::process::Command;
use std::ptr::{null, null_mut};

use openssl_sys::*;

mod common;

// What `openssl-sys` does not bind, all in OpenSSL 3.0.
unsafe extern "C" {
    fn OSSL_LIB_CTX_load_config(ctx: *mut OSSL_LIB_CTX, file: *const c_char) -> c_int;
    fn OSSL_PROVIDER_get0_name(provider: *const OSSL_PROVIDER) -> *const c_char;
    fn OSSL_PARAM_get_uint(param: *const OSSL_PARAM, value: *mut c_uint) -> c_int;
    fn OSSL_PROVIDER_get_capabilities(
        provider: *const OSSL_PROVIDER,
        capability: *const c_char,
        callback: unsafe extern "C" fn(*const OSSL_PARAM, *mut c_void) -> c_int,
        arg: *mut c_void,
    ) -> c_int;
    fn EVP_PKEY_get0_provider(pkey: *const EVP_PKEY) -> *const OSSL_PROVIDER;
    fn EVP_PKEY_CTX_get0_provider(ctx: *const EVP_PKEY_CTX) -> *const OSSL_PROVIDER;
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
    fn EVP_PKEY_set1_encoded_public_key(
        pkey: *mut EVP_PKEY,
        public: *const u8,
        len: usize,
    ) -> c_int;
    fn EVP_PKEY_get1_encoded_public_key(pkey: *mut EVP_PKEY, public: *mut *mut u8) -> usize;
    fn OSSL_PARAM_construct_utf8_string(
        key: *const c_char,
        buf: *mut c_char,
        len: usize,
    ) -> OSSL_PARAM;
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
    fn OPENSSL_init_crypto(opts: u64, settings: *const c_void) -> c_int;
}

const OPENSSL_INIT_LOAD_CONFIG: u64 = 0x40;

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

    /// A key of `algorithm` from its raw private bytes, in the provider
    /// `propq` picks.
    fn private(&self, algorithm: &CStr, propq: &CStr, private: &[u8]) -> Key {
        Key(non_null(unsafe {
            EVP_PKEY_new_raw_private_key_ex(
                self.0,
                algorithm.as_ptr(),
                propq.as_ptr(),
                private.as_ptr(),
                private.len(),
            )
        }))
    }

    fn public(&self, algorithm: &CStr, propq: &CStr, public: &[u8]) -> Key {
        Key(non_null(unsafe {
            EVP_PKEY_new_raw_public_key_ex(
                self.0,
                algorithm.as_ptr(),
                propq.as_ptr(),
                public.as_ptr(),
                public.len(),
            )
        }))
    }

    /// A fresh key of `algorithm`, in the provider the configuration prefers.
    fn generate(&self, algorithm: &CStr) -> Key {
        unsafe {
            let ctx = non_null(EVP_PKEY_CTX_new_from_name(
                self.0,
                algorithm.as_ptr(),
                null(),
            ));
            check(EVP_PKEY_keygen_init(ctx));
            let mut key = null_mut();
            check(EVP_PKEY_generate(ctx, &mut key));
            EVP_PKEY_CTX_free(ctx);
            Key(key)
        }
    }

    fn derive(&self, key: &Key, peer: &Key) -> (Vec<u8>, String) {
        self.derive_on(key, peer, null())
    }

    /// Derives on the provider `propq` picks, such as `DEFAULT`.
    fn derive_on(&self, key: &Key, peer: &Key, propq: *const c_char) -> (Vec<u8>, String) {
        unsafe {
            let ctx = non_null(EVP_PKEY_CTX_new_from_pkey(self.0, key.0, propq));
            check(EVP_PKEY_derive_init(ctx));
            check(EVP_PKEY_derive_set_peer(ctx, peer.0));
            let mut len = 0;
            check(EVP_PKEY_derive(ctx, null_mut(), &mut len));
            let mut secret = vec![0; len];
            let ok = EVP_PKEY_derive(ctx, secret.as_mut_ptr(), &mut len);
            let provider = name(EVP_PKEY_CTX_get0_provider(ctx));
            EVP_PKEY_CTX_free(ctx);
            check(ok);
            secret.truncate(len);
            (secret, provider)
        }
    }

    /// Signs `message` with `key` as `EVP_DigestSign` does, returning the
    /// signature and the provider that made it.
    fn sign(&self, key: &Key, message: &[u8]) -> Result<(Vec<u8>, String), String> {
        self.sign_with(key, message, null(), null())
    }

    /// Signs on the provider `propq` picks, such as `DEFAULT`, with `params`.
    fn sign_with(
        &self,
        key: &Key,
        message: &[u8],
        propq: *const c_char,
        params: *const OSSL_PARAM,
    ) -> Result<(Vec<u8>, String), String> {
        unsafe {
            let md = non_null(EVP_MD_CTX_new());
            let mut pctx = null_mut();
            let result = (|| {
                if EVP_DigestSignInit_ex(md, &mut pctx, null(), self.0, propq, key.0, params) != 1 {
                    return Err(errors());
                }
                let mut signature = [0u8; 64];
                let mut len = signature.len();
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
                Ok((
                    signature[..len].to_vec(),
                    name(EVP_PKEY_CTX_get0_provider(pctx)),
                ))
            })();
            EVP_MD_CTX_free(md);
            result
        }
    }

    /// Verifies as `EVP_DigestVerify` does, returning whether it passed and
    /// the provider that checked it.
    fn verify(&self, key: &Key, message: &[u8], signature: &[u8]) -> (bool, String) {
        unsafe {
            let md = non_null(EVP_MD_CTX_new());
            let mut pctx = null_mut();
            check(EVP_DigestVerifyInit_ex(
                md,
                &mut pctx,
                null(),
                self.0,
                null(),
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

    fn raw_public(&self) -> Vec<u8> {
        let mut out = [0u8; 64];
        let mut len = out.len();
        check(unsafe { EVP_PKEY_get_raw_public_key(self.0, out.as_mut_ptr(), &mut len) });
        out[..len].to_vec()
    }

    fn raw_private(&self) -> Vec<u8> {
        let mut out = [0u8; 64];
        let mut len = out.len();
        check(unsafe { EVP_PKEY_get_raw_private_key(self.0, out.as_mut_ptr(), &mut len) });
        out[..len].to_vec()
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

fn name(provider: *const OSSL_PROVIDER) -> String {
    assert!(!provider.is_null());
    unsafe { CStr::from_ptr(OSSL_PROVIDER_get0_name(provider)) }
        .to_string_lossy()
        .into_owned()
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

const RIND: &CStr = c"provider=rind";
const DEFAULT: &CStr = c"provider=default";

#[test]
fn rind_backs_only_x25519_and_ed25519() {
    let ctx = Context::new();
    assert_eq!(ctx.generate(c"X25519").provider(), "rind");
    assert_eq!(ctx.generate(c"ED25519").provider(), "rind");
    // The default provider keeps what rind does not register.
    assert_eq!(ctx.generate(c"X448").provider(), "default");
    assert_eq!(ctx.generate(c"ED448").provider(), "default");
    assert_eq!(ctx.generate(c"RSA").provider(), "default");
}

/// Collects each TLS group a provider offers, as OpenSSL's TLS stack reads
/// them: its name, and its id, which `ssl/t1_lib.c` takes as `uint`.
unsafe extern "C" fn collect_group(params: *const OSSL_PARAM, groups: *mut c_void) -> c_int {
    let (mut name, mut id) = (null(), 0);
    unsafe {
        let found = OSSL_PARAM_locate_const(params, c"tls-group-name".as_ptr());
        assert!(!found.is_null());
        assert_eq!(OSSL_PARAM_get_utf8_string_ptr(found, &mut name), 1);
        let found = OSSL_PARAM_locate_const(params, c"tls-group-id".as_ptr());
        assert!(!found.is_null());
        assert_eq!(OSSL_PARAM_get_uint(found, &mut id), 1);
        let groups = &mut *groups.cast::<Vec<(String, u32)>>();
        groups.push((CStr::from_ptr(name).to_str().unwrap().into(), id));
    }
    1
}

/// Through OpenSSL 3.4 a TLS group is offered only when the provider that
/// lists it also backs its algorithm, and the README's configuration makes
/// that rind for X25519. Only the TLS handshake test below shows that on
/// those releases; this one shows it on every release.
#[test]
fn rind_offers_the_x25519_tls_group() {
    let ctx = Context::new();
    let provider = non_null(unsafe { OSSL_PROVIDER_try_load(ctx.0, c"rind".as_ptr(), 1) });
    let mut groups: Vec<(String, u32)> = Vec::new();
    check(unsafe {
        OSSL_PROVIDER_get_capabilities(
            provider,
            c"TLS-GROUP".as_ptr(),
            collect_group,
            (&raw mut groups).cast(),
        )
    });
    // IANA's id for x25519, RFC 8446 section 4.2.7.
    assert_eq!(groups, [("x25519".to_string(), 29)]);
    // Any other capability is one rind has nothing for, not a failure.
    let mut none: Vec<(String, u32)> = Vec::new();
    check(unsafe {
        OSSL_PROVIDER_get_capabilities(
            provider,
            c"TLS-SIGALG".as_ptr(),
            collect_group,
            (&raw mut none).cast(),
        )
    });
    assert!(none.is_empty());
}

#[test]
fn x25519_agrees_with_the_default_provider() {
    let ctx = Context::new();
    // RFC 7748 section 6.1.
    let alice = hex("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
    let bob = hex("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb");
    let shared = hex("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742");

    let alice_rind = ctx.private(c"X25519", RIND, &alice);
    let bob_default = ctx.private(c"X25519", DEFAULT, &bob);
    assert_eq!(
        alice_rind.raw_public(),
        hex("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
    );
    assert_eq!(alice_rind.raw_private(), alice);

    // Each side's key is the other provider's, which OpenSSL moves into the
    // preferred one: rind, both times.
    assert_eq!(
        ctx.derive(&alice_rind, &bob_default),
        (shared.clone(), "rind".into())
    );
    assert_eq!(
        ctx.derive(&bob_default, &alice_rind),
        (shared, "rind".into())
    );

    // Fresh keys from each provider agree too, and with the default
    // provider's own exchange.
    let a = ctx.generate(c"X25519");
    let b = ctx.private(c"X25519", DEFAULT, &ctx.generate(c"X25519").raw_private());
    let reference = ctx.derive_on(&b, &a, DEFAULT.as_ptr());
    assert_eq!(reference.1, "default");
    assert_eq!(ctx.derive(&a, &b).0, reference.0);
    assert_eq!(ctx.derive(&b, &a).0, reference.0);
    // And a generated key is clamped, as the default provider stores one.
    let private = a.raw_private();
    assert_eq!((private[0] & 7, private[31] & 0xc0), (0, 0x40));
}

/// RFC 9180's `DeriveKeyPair`, which OpenSSL runs as key generation from
/// `dhkem-ikm`, gives the RFC's keys. Its vectors, rather than the default
/// provider, decide, since OpenSSL before 3.2 ignores `dhkem-ikm`.
#[test]
fn x25519_derives_the_rfc_9180_key_pair() {
    let ctx = Context::new();
    // RFC 9180 appendix A.1.1: ikmE to skEm and pkEm, and ikmR to skRm and
    // pkRm.
    let vectors = [
        (
            "7268600d403fce431561aef583ee1613527cff655c1343f29812e66706df3234",
            "52c4a758a802cd8b936eceea314432798d5baf2d7e9235dc084ab1b9cfa2f736",
            "37fda3567bdbd628e88668c3c8d7e97d1d1253b6d4ea6d44c150f741f1bf4431",
        ),
        (
            "6db9df30aa07dd42ee5e8181afdb977e538f5e1fec8a06223f33f7013e525037",
            "4612c550263fc8ad58375df3f557aac531d26850903e55a9f23f21d8534e8ac8",
            "3948cfe0ad1ddb695d780e59077195da6c56506b027329794ab02bca80815c4d",
        ),
    ];
    for (ikm, private, public) in vectors {
        let mut ikm = hex(ikm);
        let key = unsafe {
            let params = [
                OSSL_PARAM_construct_octet_string(
                    c"dhkem-ikm".as_ptr(),
                    ikm.as_mut_ptr().cast(),
                    ikm.len(),
                ),
                OSSL_PARAM_construct_end(),
            ];
            let gen_ctx = non_null(EVP_PKEY_CTX_new_from_name(
                ctx.0,
                c"X25519".as_ptr(),
                null(),
            ));
            check(EVP_PKEY_keygen_init(gen_ctx));
            check(EVP_PKEY_CTX_set_params(gen_ctx, params.as_ptr()));
            let mut key = null_mut();
            check(EVP_PKEY_generate(gen_ctx, &mut key));
            EVP_PKEY_CTX_free(gen_ctx);
            Key(key)
        };
        assert_eq!(key.provider(), "rind");
        // Clamped, as OpenSSL stores a key it makes.
        let mut private = hex(private);
        private[0] &= 248;
        private[31] = private[31] & 127 | 64;
        assert_eq!(key.raw_private(), private);
        assert_eq!(key.raw_public(), hex(public));
    }
}

#[test]
fn x25519_refuses_a_small_order_peer() {
    let ctx = Context::new();
    let key = ctx.generate(c"X25519");
    let peer = ctx.public(c"X25519", RIND, &[0; 32]);
    unsafe {
        let pctx = non_null(EVP_PKEY_CTX_new_from_pkey(ctx.0, key.0, null()));
        check(EVP_PKEY_derive_init(pctx));
        check(EVP_PKEY_derive_set_peer(pctx, peer.0));
        let mut secret = [0u8; 32];
        let mut len = secret.len();
        assert_ne!(EVP_PKEY_derive(pctx, secret.as_mut_ptr(), &mut len), 1);
        EVP_PKEY_CTX_free(pctx);
    }
    assert!(errors().contains("rind"));
}

/// The path TLS takes: an empty key from parameter generation, given the
/// peer's encoded key.
#[test]
fn x25519_takes_an_encoded_peer_key() {
    let ctx = Context::new();
    let key = ctx.generate(c"X25519");
    let peer = ctx.generate(c"X25519");
    unsafe {
        let mut encoded = null_mut();
        let len = EVP_PKEY_get1_encoded_public_key(peer.0, &mut encoded);
        assert_eq!(len, 32);
        let paramgen = non_null(EVP_PKEY_CTX_new_from_name(
            ctx.0,
            c"X25519".as_ptr(),
            null(),
        ));
        check(EVP_PKEY_paramgen_init(paramgen));
        let mut blank = null_mut();
        check(EVP_PKEY_paramgen(paramgen, &mut blank));
        EVP_PKEY_CTX_free(paramgen);
        let blank = Key(blank);
        assert_eq!(blank.provider(), "rind");
        check(EVP_PKEY_set1_encoded_public_key(blank.0, encoded, len));
        CRYPTO_free(encoded.cast(), c"".as_ptr(), 0);
        assert_eq!(ctx.derive(&key, &blank), ctx.derive(&key, &peer));
    }
}

#[test]
fn ed25519_signs_as_the_default_provider_does() {
    let ctx = Context::new();
    // RFC 8032 section 7.1, test 1.
    let seed = hex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
    let expected = hex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065\
         224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b");
    let rind = ctx.private(c"ED25519", RIND, &seed);
    let default = ctx.private(c"ED25519", DEFAULT, &seed);
    assert_eq!(
        rind.raw_public(),
        hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
    );
    assert_eq!(rind.raw_private(), seed);
    assert!(rind.eq(&default));

    assert_eq!(
        ctx.sign(&rind, b"").unwrap(),
        (expected.clone(), "rind".into())
    );
    // The default provider's key moves into rind to sign.
    assert_eq!(
        ctx.sign(&default, b"").unwrap(),
        (expected.clone(), "rind".into())
    );

    // A fresh key signs as the default provider's own signature does.
    let message = b"rind as an OpenSSL provider";
    let fresh = ctx.generate(c"ED25519");
    let (signature, _) = ctx.sign(&fresh, message).unwrap();
    let reference = ctx
        .sign_with(&fresh, message, DEFAULT.as_ptr(), null())
        .unwrap();
    assert_eq!(reference.1, "default");
    assert_eq!(signature, reference.0);
    let (signature, _) = ctx.sign(&rind, message).unwrap();
    assert_eq!(
        ctx.verify(&rind, message, &signature),
        (true, "rind".into())
    );
    assert_eq!(
        ctx.verify(&default, message, &signature),
        (true, "rind".into())
    );
    assert!(!ctx.verify(&rind, b"another message", &signature).0);
    assert!(!ctx.verify(&rind, message, &signature[..63]).0);
    let mut tampered = signature.clone();
    tampered[0] ^= 1;
    assert!(!ctx.verify(&rind, message, &tampered).0);
}

#[test]
fn ed25519_refuses_what_rind_cannot_back() {
    let ctx = Context::new();
    let key = ctx.generate(c"ED25519");
    let mut instance = *b"Ed25519ph\0";
    let params = unsafe {
        [
            OSSL_PARAM_construct_utf8_string(c"instance".as_ptr(), instance.as_mut_ptr().cast(), 0),
            OSSL_PARAM_construct_end(),
        ]
    };
    let error = ctx
        .sign_with(&key, b"message", null(), params.as_ptr())
        .unwrap_err();
    assert!(error.contains("unsupported by rind"), "{error}");

    // Pure Ed25519 takes no context string, as the default provider says.
    let mut context = *b"context";
    let params = unsafe {
        [
            OSSL_PARAM_construct_octet_string(
                c"context-string".as_ptr(),
                context.as_mut_ptr().cast(),
                context.len(),
            ),
            OSSL_PARAM_construct_end(),
        ]
    };
    assert!(
        ctx.sign_with(&key, b"message", null(), params.as_ptr())
            .is_err()
    );
}

/// A private key beside another's public key fails each use with rind's
/// error, whichever provider made it: one the default provider holds moves to
/// rind before each use, and were that move refused, OpenSSL would run the
/// use there instead.
#[test]
fn a_mismatched_key_fails_every_use() {
    let ctx = Context::new();
    for algorithm in [c"X25519", c"ED25519"] {
        let ours = ctx.generate(algorithm);
        let theirs = ctx.generate(algorithm);
        let mut private = ours.raw_private();
        let mut public = theirs.raw_public();
        // Through the configuration's preference, rind's, and the default
        // provider's.
        for (propq, provider) in [(None, "rind"), (Some(DEFAULT), "default")] {
            let key = unsafe {
                let mut params = [
                    OSSL_PARAM_construct_octet_string(
                        c"priv".as_ptr(),
                        private.as_mut_ptr().cast(),
                        private.len(),
                    ),
                    OSSL_PARAM_construct_octet_string(
                        c"pub".as_ptr(),
                        public.as_mut_ptr().cast(),
                        public.len(),
                    ),
                    OSSL_PARAM_construct_end(),
                ];
                let pctx = non_null(EVP_PKEY_CTX_new_from_name(
                    ctx.0,
                    algorithm.as_ptr(),
                    propq.map_or(null(), CStr::as_ptr),
                ));
                check(EVP_PKEY_fromdata_init(pctx));
                let mut key = null_mut();
                check(EVP_PKEY_fromdata(
                    pctx,
                    &mut key,
                    EVP_PKEY_KEYPAIR,
                    params.as_mut_ptr(),
                ));
                EVP_PKEY_CTX_free(pctx);
                Key(key)
            };
            assert_eq!(key.provider(), provider);
            unsafe { ERR_clear_error() };
            let failed = if algorithm == c"ED25519" {
                ctx.sign(&key, b"message").err()
            } else {
                unsafe {
                    let pctx = non_null(EVP_PKEY_CTX_new_from_pkey(ctx.0, key.0, null()));
                    let ok = EVP_PKEY_derive_init(pctx) == 1
                        && EVP_PKEY_derive_set_peer(pctx, theirs.0) == 1;
                    EVP_PKEY_CTX_free(pctx);
                    (!ok).then(errors)
                }
            };
            let error = failed.unwrap_or_else(|| panic!("{algorithm:?} from {provider} was used"));
            assert!(
                error.contains("not the private key's"),
                "{algorithm:?} from {provider}: {error:?}"
            );
        }
    }
}

/// Keys move through OpenSSL's encoders and decoders, which are the default
/// provider's, and come back usable.
#[test]
fn keys_round_trip_through_pem() {
    let ctx = Context::new();
    for algorithm in [c"X25519", c"ED25519"] {
        let key = ctx.generate(algorithm);
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
            assert_eq!(decoded.raw_private(), key.raw_private());

            if algorithm == c"ED25519" {
                let (signature, provider) = ctx.sign(&decoded, b"message").unwrap();
                assert_eq!(provider, "rind");
                assert!(ctx.verify(&public, b"message", &signature).0);
            } else {
                let peer = ctx.generate(algorithm);
                assert_eq!(ctx.derive(&decoded, &peer), ctx.derive(&peer, &public));
            }
        }
    }
}

/// A TLS 1.3 handshake whose only group is X25519 and whose certificate is
/// an Ed25519 key's, which rind signed: what nginx would do with rind.
#[test]
fn tls13_handshake_over_x25519_and_ed25519() {
    let ctx = Context::new();
    let key = ctx.generate(c"ED25519");
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
            check(SSL_CTX_set1_groups_list(side, c"X25519".as_ptr()) as c_int);
            check(SSL_CTX_set1_sigalgs_list(side, c"ed25519".as_ptr()) as c_int);
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

        SSL_free(s);
        SSL_free(c);
        SSL_CTX_free(server);
        SSL_CTX_free(client);
        X509_free(cert);
    }
}

/// The documented configuration, read from `OPENSSL_CONF` as OpenSSL
/// initializes, loads rind into the default library context.
#[test]
fn documented_config_loads_rind() {
    if std::env::var_os("RIND_OPENSSL_CHILD").is_some() {
        // SAFETY: OpenSSL reads `OPENSSL_CONF` as it initializes.
        check(unsafe { OPENSSL_init_crypto(OPENSSL_INIT_LOAD_CONFIG, null()) });
        // The null context is OpenSSL's default one.
        let ctx = Context(null_mut());
        assert_eq!(ctx.generate(c"ED25519").provider(), "rind");
        return;
    }
    let mut child = Command::new(std::env::current_exe().unwrap());
    child
        .args(["--exact", "documented_config_loads_rind", "--nocapture"])
        .env("OPENSSL_CONF", common::config(Some(&common::library())))
        .env("RIND_OPENSSL_CHILD", "1");
    let output = child.output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    // The child ran the test, rather than filtering it out.
    assert!(stdout.contains("1 passed"), "{stdout}");
}
