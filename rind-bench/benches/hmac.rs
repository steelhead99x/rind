//! Each row keys HMAC per message, as a one-off MAC does; the `reused_key`
//! rows sign with a long-lived key, such as a STUN or SRTP session's.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, HASH_SIZES, Size};

#[cfg(not(target_arch = "xtensa"))]
fn input(size: Size) -> Vec<u8> {
    size.zeros()
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_input(size: Size) -> Dit<Vec<u8>> {
    Dit::hold(size.zeros())
}

/// The rows every HMAC hash has, keyed with `[0xff; $len]`. Its modules are
/// named after crates, so paths here start with `::`.
macro_rules! rows {
    ($ring:ident, $rind:path, $rustcrypto:ty, $vg:ty, $len:literal) => {
        const KEY: [u8; $len] = [0xff; $len];

        #[bench(args = HASH_SIZES, setup = input)]
        fn ring(input: &[u8]) -> ::ring::hmac::Tag {
            let mut ctx =
                ::ring::hmac::Context::with_key(&::ring::hmac::Key::new(::ring::hmac::$ring, &KEY));
            ctx.update(input);
            ctx.sign()
        }

        #[bench(args = HASH_SIZES, setup = input)]
        fn aws_lc_rs(input: &[u8]) -> ::aws_lc_rs::hmac::Tag {
            let mut ctx = ::aws_lc_rs::hmac::Context::with_key(&::aws_lc_rs::hmac::Key::new(
                ::aws_lc_rs::hmac::$ring,
                &KEY,
            ));
            ctx.update(input);
            ctx.sign()
        }

        #[bench(args = HASH_SIZES, setup = input)]
        fn rustcrypto(input: &[u8]) -> impl Sized + use<> {
            use ::hmac::{KeyInit, Mac};
            let mut ctx = <$rustcrypto as KeyInit>::new_from_slice(&KEY).unwrap();
            ctx.update(input);
            ctx.finalize()
        }

        #[bench(args = HASH_SIZES, setup = rind_input)]
        fn rind(input: &Dit<Vec<u8>>) -> ::rind::hmac::Tag {
            ::rind::hmac::sign(&::rind::hmac::Key::new(&$rind, &KEY), input)
        }

        /// The message, after checking verified-garbage's MAC of it matches
        /// rind's.
        fn vg_input(size: Size) -> Vec<u8> {
            let input = size.zeros();
            assert_eq!(
                ::verified_garbage::hmac::Hmac::<$vg>::mac(&KEY, &input).as_ref(),
                ::rind::hmac::sign(&::rind::hmac::Key::new(&$rind, &KEY), &input).as_ref()
            );
            input
        }

        #[bench(args = HASH_SIZES, setup = vg_input)]
        fn verified_garbage(input: &[u8]) -> impl AsRef<[u8]> + use<> {
            let mut ctx = ::verified_garbage::hmac::Hmac::<$vg>::new(&KEY);
            ctx.update(input);
            ctx.finalize()
        }

        #[cfg(target_arch = "aarch64")]
        #[bench(args = HASH_SIZES, setup = vg_input)]
        fn verified_garbage_dit_held(
            input: &[u8],
            iterations: swole::Iterations,
        ) -> std::time::Duration {
            common::vg_dit_held(iterations, || verified_garbage(input))
        }

        mod ring {
            use swole::bench;

            use super::*;

            fn keyed(size: Size) -> (::ring::hmac::Key, Vec<u8>) {
                (
                    ::ring::hmac::Key::new(::ring::hmac::$ring, &KEY),
                    size.zeros(),
                )
            }

            #[bench(args = HASH_SIZES, setup = keyed)]
            fn reused_key((key, input): &(::ring::hmac::Key, Vec<u8>)) -> ::ring::hmac::Tag {
                ::ring::hmac::sign(key, input)
            }
        }

        mod aws_lc_rs {
            use swole::bench;

            use super::*;

            fn keyed(size: Size) -> (::aws_lc_rs::hmac::Key, Vec<u8>) {
                (
                    ::aws_lc_rs::hmac::Key::new(::aws_lc_rs::hmac::$ring, &KEY),
                    size.zeros(),
                )
            }

            #[bench(args = HASH_SIZES, setup = keyed)]
            fn reused_key(
                (key, input): &(::aws_lc_rs::hmac::Key, Vec<u8>),
            ) -> ::aws_lc_rs::hmac::Tag {
                ::aws_lc_rs::hmac::sign(key, input)
            }
        }

        mod rind {
            use swole::bench;

            use super::*;

            fn keyed(size: Size) -> Dit<(::rind::hmac::Key, Vec<u8>)> {
                Dit::hold((::rind::hmac::Key::new(&$rind, &KEY), size.zeros()))
            }

            #[bench(args = HASH_SIZES, setup = keyed)]
            fn reused_key(keyed: &Dit<(::rind::hmac::Key, Vec<u8>)>) -> ::rind::hmac::Tag {
                let (key, input) = &**keyed;
                ::rind::hmac::sign(key, input)
            }
        }

        // Its keyed state, cloned per message, is the key schedule reused.
        mod verified_garbage {
            use swole::bench;

            use super::*;

            fn keyed(size: Size) -> (::verified_garbage::hmac::Hmac<$vg>, Vec<u8>) {
                (
                    ::verified_garbage::hmac::Hmac::<$vg>::new(&KEY),
                    size.zeros(),
                )
            }

            #[bench(args = HASH_SIZES, setup = keyed)]
            fn reused_key(
                (key, input): &(::verified_garbage::hmac::Hmac<$vg>, Vec<u8>),
            ) -> impl AsRef<[u8]> + use<> {
                let mut ctx = key.clone();
                ctx.update(input);
                ctx.finalize()
            }
        }
    };
}

/// OpenSSL's row, keying an EVP signer per message.
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
macro_rules! openssl {
    ($md:ident) => {
        #[bench(args = HASH_SIZES, setup = input)]
        fn openssl(input: &[u8]) {
            let key = ::openssl::pkey::PKey::hmac(&KEY).unwrap();
            let mut signer =
                ::openssl::sign::Signer::new(::openssl::hash::MessageDigest::$md(), &key).unwrap();
            signer.update(input).unwrap();
            ::std::hint::black_box(signer.sign_to_vec().unwrap());
        }
    };
}

/// Graviola's row.
#[cfg(graviola)]
macro_rules! graviola {
    ($hash:ident) => {
        #[bench(args = HASH_SIZES, setup = input)]
        fn graviola(input: &[u8]) -> impl Sized + use<> {
            let mut ctx = ::graviola::hashing::hmac::Hmac::<::graviola::hashing::$hash>::new(&KEY);
            ctx.update(input);
            ctx.finish()
        }
    };
}

/// libcrux's row.
macro_rules! libcrux {
    ($mac:ident, $len:literal) => {
        #[bench(args = HASH_SIZES, setup = input)]
        fn libcrux(input: &[u8]) -> [u8; $len] {
            let mut tag = [0u8; $len];
            ::libcrux_hmac::$mac(&mut tag, &KEY, input);
            tag
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod hmac_sha1 {
    use swole::bench;

    use super::*;

    rows!(
        HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        ::rind::hmac::legacy::HMAC_SHA1,
        ::hmac::Hmac<::sha1::Sha1>,
        ::verified_garbage::hashes::sha1::Sha1,
        20
    );
    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    openssl!(sha1);
}

#[cfg(not(target_arch = "xtensa"))]
mod hmac_sha256 {
    use swole::bench;

    use super::*;

    rows!(
        HMAC_SHA256,
        ::rind::hmac::HMAC_SHA256,
        ::hmac::Hmac<::sha2::Sha256>,
        ::verified_garbage::hashes::sha256::Sha256,
        32
    );
    libcrux!(hmac_sha2_256, 32);
    #[cfg(graviola)]
    graviola!(Sha256);
    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    openssl!(sha256);
}

#[cfg(not(target_arch = "xtensa"))]
mod hmac_sha384 {
    use swole::bench;

    use super::*;

    rows!(
        HMAC_SHA384,
        ::rind::hmac::HMAC_SHA384,
        ::hmac::Hmac<::sha2::Sha384>,
        ::verified_garbage::hashes::sha384::Sha384,
        48
    );
    libcrux!(hmac_sha2_384, 48);
    #[cfg(graviola)]
    graviola!(Sha384);
    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    openssl!(sha384);
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
