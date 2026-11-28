//! A 32-byte key for one label, from a PRK extracted once: what a QUIC token
//! or an e2ee track key derives from a long-lived secret.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

#[cfg(not(target_arch = "xtensa"))]
const SECRET: [u8; 32] = [0x5a; 32];
#[cfg(not(target_arch = "xtensa"))]
const INFO: [&[u8]; 1] = [b"label"];

#[cfg(not(target_arch = "xtensa"))]
struct Len(usize);

#[cfg(not(target_arch = "xtensa"))]
impl aws_lc_rs::hkdf::KeyType for Len {
    fn len(&self) -> usize {
        self.0
    }
}

#[cfg(not(target_arch = "xtensa"))]
impl ring::hkdf::KeyType for Len {
    fn len(&self) -> usize {
        self.0
    }
}

// verified-garbage has no HKDF, so this is RFC 5869 over its HMAC, as rind's
// glue would run it.
#[cfg(not(target_arch = "xtensa"))]
fn vg_expand<V: verified_garbage::hmac::HmacHash>(prk: &[u8], info: &[u8], out: &mut [u8]) {
    let mut previous: Option<V::Output> = None;
    for (counter, chunk) in (1u8..).zip(out.chunks_mut(V::OUTPUT_SIZE)) {
        let mut ctx = verified_garbage::hmac::Hmac::<V>::new(prk);
        if let Some(previous) = &previous {
            ctx.update(previous.as_ref());
        }
        ctx.update(info);
        ctx.update(&[counter]);
        let block = ctx.finalize();
        chunk.copy_from_slice(&block.as_ref()[..chunk.len()]);
        previous = Some(block);
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn vg_extract_expand<V: verified_garbage::hmac::HmacHash>(out: &mut [u8]) {
    let prk = verified_garbage::hmac::Hmac::<V>::mac(b"salt", &SECRET);
    vg_expand::<V>(prk.as_ref(), INFO[0], out);
}

/// OpenSSL's HKDF over `md`: it expands `key` as a PRK, or extracts from it
/// with the salt first.
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
fn openssl_derive(md: &openssl::md::MdRef, expand_only: bool, key: &[u8]) -> [u8; 32] {
    use openssl::pkey::Id;
    use openssl::pkey_ctx::{HkdfMode, PkeyCtx};
    let mut out = [0u8; 32];
    let mut ctx = PkeyCtx::new_id(Id::HKDF).unwrap();
    ctx.derive_init().unwrap();
    ctx.set_hkdf_md(md).unwrap();
    if expand_only {
        ctx.set_hkdf_mode(HkdfMode::EXPAND_ONLY).unwrap();
    } else {
        ctx.set_hkdf_salt(b"salt").unwrap();
    }
    ctx.set_hkdf_key(key).unwrap();
    ctx.add_hkdf_info(INFO[0]).unwrap();
    ctx.derive(Some(&mut out)).unwrap();
    out
}

/// One hash's rows. `$hkdf` names the ring and aws-lc-rs algorithm, `$hmac`
/// aws-lc-rs's HMAC over the same hash, and `$md` OpenSSL's digest;
/// libcrux's rows, where it has the hash, take its algorithm and PRK length.
macro_rules! rows {
    (
        $hkdf:ident, $hmac:ident, $rind:path, $rustcrypto:ty, $vg:ty, $md:ident
        $(, libcrux($libcrux:ident, $prk_len:literal))?
    ) => {
        // aws-lc-rs extracts lazily, inside each expansion, so extraction is
        // timed with one expansion after it.
        mod extract_expand {
            use super::*;
            use swole::bench;

            #[bench]
            fn ring() -> [u8; 32] {
                let mut out = [0u8; 32];
                ring::hkdf::Salt::new(ring::hkdf::$hkdf, b"salt")
                    .extract(&SECRET)
                    .expand(&INFO, Len(32))
                    .unwrap()
                    .fill(&mut out)
                    .unwrap();
                out
            }

            #[bench]
            fn aws_lc_rs() -> [u8; 32] {
                let mut out = [0u8; 32];
                aws_lc_rs::hkdf::Salt::new(aws_lc_rs::hkdf::$hkdf, b"salt")
                    .extract(&SECRET)
                    .expand(&INFO, Len(32))
                    .unwrap()
                    .fill(&mut out)
                    .unwrap();
                out
            }


            #[bench(setup = dit)]
            fn rind(_: &Dit<()>) -> [u8; 32] {
                let mut out = [0u8; 32];
                rind::hkdf::Salt::new(&$rind, b"salt")
                    .extract(&SECRET)
                    .unwrap()
                    .fill(&INFO, &mut out)
                    .unwrap();
                out
            }

            #[bench]
            fn rustcrypto() -> [u8; 32] {
                let mut out = [0u8; 32];
                hkdf::GenericHkdf::<$rustcrypto>::new(Some(b"salt"), &SECRET)
                    .expand(INFO[0], &mut out)
                    .unwrap();
                out
            }

            $(
                #[bench]
                fn libcrux() -> [u8; 32] {
                    let mut out = [0u8; 32];
                    libcrux_hkdf::hkdf(
                        libcrux_hkdf::Algorithm::$libcrux,
                        &mut out,
                        b"salt",
                        &SECRET,
                        INFO[0],
                    )
                    .unwrap();
                    out
                }
            )?

            /// Checks verified-garbage derives the key rind does.
            fn vg_checked() {
                let mut expected = [0u8; 32];
                rind::hkdf::Salt::new(&$rind, b"salt")
                    .extract(&SECRET)
                    .unwrap()
                    .fill(&INFO, &mut expected)
                    .unwrap();
                let mut out = [0u8; 32];
                vg_extract_expand::<$vg>(&mut out);
                assert_eq!(out, expected);
            }

            #[bench(setup = vg_checked)]
            fn verified_garbage(_: &()) -> [u8; 32] {
                let mut out = [0u8; 32];
                vg_extract_expand::<$vg>(&mut out);
                out
            }

            #[cfg(target_arch = "aarch64")]
            #[bench(setup = vg_checked)]
            fn verified_garbage_dit_held(input: &(), iterations: swole::Iterations) -> std::time::Duration {
                common::vg_dit_held(iterations, || verified_garbage(input))
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            #[bench]
            fn openssl() -> [u8; 32] {
                openssl_derive(openssl::md::Md::$md(), false, &SECRET)
            }
        }

        mod expand {
            use super::*;
            use swole::bench;

            pub(super) fn ring_prk() -> ring::hkdf::Prk {
                ring::hkdf::Salt::new(ring::hkdf::$hkdf, b"salt").extract(&SECRET)
            }

            #[bench(setup = ring_prk)]
            fn ring(prk: &ring::hkdf::Prk) -> [u8; 32] {
                let mut out = [0u8; 32];
                prk.expand(&INFO, Len(32)).unwrap().fill(&mut out).unwrap();
                out
            }

            // aws-lc-rs's `extract` defers extraction to each expansion, so
            // its PRK is computed here instead.
            pub(super) fn aws_prk() -> aws_lc_rs::hkdf::Prk {
                let prk = aws_lc_rs::hmac::sign(
                    &aws_lc_rs::hmac::Key::new(aws_lc_rs::hmac::$hmac, b"salt"),
                    &SECRET,
                );
                aws_lc_rs::hkdf::Prk::new_less_safe(aws_lc_rs::hkdf::$hkdf, prk.as_ref())
            }

            #[bench(setup = aws_prk)]
            fn aws_lc_rs(prk: &aws_lc_rs::hkdf::Prk) -> [u8; 32] {
                let mut out = [0u8; 32];
                prk.expand(&INFO, Len(32)).unwrap().fill(&mut out).unwrap();
                out
            }

            pub(super) fn rind_prk() -> Dit<rind::hkdf::Prk> {
                Dit::hold(rind::hkdf::Salt::new(&$rind, b"salt").extract(&SECRET).unwrap())
            }

            #[bench(setup = rind_prk)]
            fn rind(prk: &Dit<rind::hkdf::Prk>) -> [u8; 32] {
                let mut out = [0u8; 32];
                prk.fill(&INFO, &mut out).unwrap();
                out
            }

            fn rustcrypto_prk() -> hkdf::GenericHkdf<$rustcrypto> {
                hkdf::GenericHkdf::<$rustcrypto>::new(Some(b"salt"), &SECRET)
            }

            #[bench(setup = rustcrypto_prk)]
            fn rustcrypto(prk: &hkdf::GenericHkdf<$rustcrypto>) -> [u8; 32] {
                let mut out = [0u8; 32];
                prk.expand(INFO[0], &mut out).unwrap();
                out
            }

            $(
                fn libcrux_prk() -> [u8; $prk_len] {
                    let mut prk = [0u8; $prk_len];
                    libcrux_hkdf::extract(
                        libcrux_hkdf::Algorithm::$libcrux,
                        &mut prk,
                        b"salt",
                        &SECRET,
                    )
                    .unwrap();
                    prk
                }

                #[bench(setup = libcrux_prk)]
                fn libcrux(prk: &[u8; $prk_len]) -> [u8; 32] {
                    let mut out = [0u8; 32];
                    libcrux_hkdf::expand(libcrux_hkdf::Algorithm::$libcrux, &mut out, prk, INFO[0])
                        .unwrap();
                    out
                }
            )?

            fn vg_prk() -> <$vg as verified_garbage::hashes::HashFunction>::Output {
                verified_garbage::hmac::Hmac::<$vg>::mac(b"salt", &SECRET)
            }

            #[bench(setup = vg_prk)]
            fn verified_garbage(prk: &<$vg as verified_garbage::hashes::HashFunction>::Output) -> [u8; 32] {
                let mut out = [0u8; 32];
                vg_expand::<$vg>(prk.as_ref(), INFO[0], &mut out);
                out
            }

            #[cfg(target_arch = "aarch64")]
            #[bench(setup = vg_prk)]
            fn verified_garbage_dit_held(prk: &<$vg as verified_garbage::hashes::HashFunction>::Output, iterations: swole::Iterations) -> std::time::Duration {
                common::vg_dit_held(iterations, || verified_garbage(prk))
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            fn openssl_prk() -> aws_lc_rs::hmac::Tag {
                aws_lc_rs::hmac::sign(
                    &aws_lc_rs::hmac::Key::new(aws_lc_rs::hmac::$hmac, b"salt"),
                    &SECRET,
                )
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            #[bench(setup = openssl_prk)]
            fn openssl(prk: &aws_lc_rs::hmac::Tag) -> [u8; 32] {
                openssl_derive(openssl::md::Md::$md(), true, prk.as_ref())
            }
        }

        mod expand_aes_256_gcm_key {
            use std::hint::black_box;

            use super::expand::{aws_prk, ring_prk, rind_prk};
            use super::*;
            use swole::bench;

            // Each key drops inside the call, so its wiping is timed too.
            #[bench(setup = ring_prk)]
            fn ring(prk: &ring::hkdf::Prk) {
                black_box(ring::aead::UnboundKey::from(
                    prk.expand(&INFO, &ring::aead::AES_256_GCM).unwrap(),
                ));
            }

            #[bench(setup = aws_prk)]
            fn aws_lc_rs(prk: &aws_lc_rs::hkdf::Prk) {
                black_box(aws_lc_rs::aead::UnboundKey::from(
                    prk.expand(&INFO, &aws_lc_rs::aead::AES_256_GCM).unwrap(),
                ));
            }

            #[bench(setup = rind_prk)]
            fn rind(prk: &Dit<rind::hkdf::Prk>) {
                black_box(rind::aead::Key::from(
                    prk.expand(&INFO, &rind::aead::AES_256_GCM).unwrap(),
                ));
            }
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod hkdf_sha1 {
    use super::*;

    rows!(
        HKDF_SHA1_FOR_LEGACY_USE_ONLY,
        HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        rind::hkdf::legacy::HKDF_SHA1,
        hkdf::hmac::Hmac<sha1::Sha1>,
        verified_garbage::hashes::sha1::Sha1,
        sha1
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod hkdf_sha256 {
    use super::*;

    rows!(
        HKDF_SHA256,
        HMAC_SHA256,
        rind::hkdf::HKDF_SHA256,
        hkdf::hmac::Hmac<sha2::Sha256>,
        verified_garbage::hashes::sha256::Sha256,
        sha256,
        libcrux(Sha256, 32)
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod hkdf_sha384 {
    use super::*;

    rows!(
        HKDF_SHA384,
        HMAC_SHA384,
        rind::hkdf::HKDF_SHA384,
        hkdf::hmac::Hmac<sha2::Sha384>,
        verified_garbage::hashes::sha384::Sha384,
        sha384,
        libcrux(Sha384, 48)
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod hkdf_sha512 {
    use super::*;

    rows!(
        HKDF_SHA512,
        HMAC_SHA512,
        rind::hkdf::HKDF_SHA512,
        hkdf::hmac::Hmac<sha2::Sha512>,
        verified_garbage::hashes::sha512::Sha512,
        sha512,
        libcrux(Sha512, 64)
    );
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
