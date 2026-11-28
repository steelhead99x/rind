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

/// Each SHA-3 hash's rows.
macro_rules! rows {
    ($alg:ident, $rustcrypto:ty, $libcrux:path, $openssl:ident, $vg:ty) => {
        #[bench(args = HASH_SIZES, setup = input)]
        fn aws_lc_rs(input: &[u8]) -> aws_lc_rs::digest::Digest {
            let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::$alg);
            ctx.update(input);
            ctx.finish()
        }

        #[bench(args = HASH_SIZES, setup = input)]
        fn rustcrypto(input: &[u8]) -> impl Sized + use<> {
            use sha3::Digest;
            let mut ctx = <$rustcrypto>::new();
            ctx.update(input);
            ctx.finalize()
        }

        #[bench(args = HASH_SIZES, setup = input)]
        fn libcrux(input: &[u8]) -> impl Sized + use<> {
            $libcrux(input)
        }

        #[bench(args = HASH_SIZES, setup = rind_input)]
        fn rind(input: &Dit<Vec<u8>>) -> rind::digest::Digest {
            let mut ctx = rind::digest::Context::new(&rind::digest::$alg);
            ctx.update(input);
            ctx.finish()
        }

        /// The message, after checking OpenSSL's digest of it matches rind's.
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        fn openssl_input(size: Size) -> Vec<u8> {
            let input = size.zeros();
            assert_eq!(
                openssl(&input).as_ref(),
                rind::digest::digest(&rind::digest::$alg, &input).as_ref()
            );
            input
        }

        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        #[bench(args = HASH_SIZES, setup = openssl_input)]
        fn openssl(input: &[u8]) -> openssl::hash::DigestBytes {
            openssl::hash::hash(openssl::hash::MessageDigest::$openssl(), input).unwrap()
        }

        /// The message, after checking verified-garbage's digest of it
        /// matches rind's.
        fn vg_input(size: Size) -> Vec<u8> {
            let input = size.zeros();
            assert_eq!(
                verified_garbage(&input).as_ref(),
                rind::digest::digest(&rind::digest::$alg, &input).as_ref()
            );
            input
        }

        #[bench(args = HASH_SIZES, setup = vg_input)]
        fn verified_garbage(input: &[u8]) -> impl AsRef<[u8]> + use<> {
            let mut ctx = <$vg>::new();
            ctx.update(input);
            ctx.finalize()
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod sha3_256 {
    use swole::bench;

    use super::*;

    rows!(
        SHA3_256,
        sha3::Sha3_256,
        libcrux_sha3::sha256,
        sha3_256,
        verified_garbage::hashes::sha3::Sha3_256
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod sha3_384 {
    use swole::bench;

    use super::*;

    rows!(
        SHA3_384,
        sha3::Sha3_384,
        libcrux_sha3::sha384,
        sha3_384,
        verified_garbage::hashes::sha3::Sha3_384
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod sha3_512 {
    use swole::bench;

    use super::*;

    rows!(
        SHA3_512,
        sha3::Sha3_512,
        libcrux_sha3::sha512,
        sha3_512,
        verified_garbage::hashes::sha3::Sha3_512
    );
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
