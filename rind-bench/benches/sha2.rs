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

/// The rows every SHA-2 hash has: each library's streaming context, fed the
/// whole message in one update.
macro_rules! rows {
    ($ring:ident, $rustcrypto:ty, $rind:ident, $vg:ty) => {
        #[bench(args = HASH_SIZES, setup = input)]
        fn ring(input: &[u8]) -> ring::digest::Digest {
            let mut ctx = ring::digest::Context::new(&ring::digest::$ring);
            ctx.update(input);
            ctx.finish()
        }

        #[bench(args = HASH_SIZES, setup = input)]
        fn aws_lc_rs(input: &[u8]) -> aws_lc_rs::digest::Digest {
            let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::$ring);
            ctx.update(input);
            ctx.finish()
        }

        #[bench(args = HASH_SIZES, setup = input)]
        fn rustcrypto(input: &[u8]) -> impl Sized + use<> {
            use sha2::Digest;
            let mut ctx = <$rustcrypto>::new();
            ctx.update(input);
            ctx.finalize()
        }

        #[bench(args = HASH_SIZES, setup = rind_input)]
        fn rind(input: &Dit<Vec<u8>>) -> rind::digest::Digest {
            let mut ctx = rind::digest::Context::new(&rind::digest::$rind);
            ctx.update(input);
            ctx.finish()
        }

        /// The message, after checking verified-garbage's digest of it
        /// matches rind's.
        fn vg_input(size: Size) -> Vec<u8> {
            let input = size.zeros();
            assert_eq!(
                verified_garbage(&input).as_ref(),
                rind::digest::digest(&rind::digest::$rind, &input).as_ref()
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
mod sha256 {
    use swole::bench;

    use super::*;

    rows!(
        SHA256,
        sha2::Sha256,
        SHA256,
        verified_garbage::hashes::sha256::Sha256
    );

    #[cfg(graviola)]
    #[bench(args = HASH_SIZES, setup = input)]
    fn graviola(input: &[u8]) -> impl Sized + use<> {
        let mut ctx = graviola::hashing::sha2::Sha256Context::new();
        ctx.update(input);
        ctx.finish()
    }

    #[bench(args = HASH_SIZES, setup = input)]
    fn libcrux(input: &[u8]) -> [u8; 32] {
        libcrux_sha2::sha256(input)
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(args = HASH_SIZES, setup = input)]
    fn openssl(input: &[u8]) -> [u8; 32] {
        openssl::sha::sha256(input)
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod sha512 {
    use swole::bench;

    use super::*;

    rows!(
        SHA512,
        sha2::Sha512,
        SHA512,
        verified_garbage::hashes::sha512::Sha512
    );

    #[cfg(graviola)]
    #[bench(args = HASH_SIZES, setup = input)]
    fn graviola(input: &[u8]) -> impl Sized + use<> {
        let mut ctx = graviola::hashing::sha2::Sha512Context::new();
        ctx.update(input);
        ctx.finish()
    }

    #[bench(args = HASH_SIZES, setup = input)]
    fn libcrux(input: &[u8]) -> [u8; 64] {
        libcrux_sha2::sha512(input)
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(args = HASH_SIZES, setup = input)]
    fn openssl(input: &[u8]) -> [u8; 64] {
        openssl::sha::sha512(input)
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod sha512_256 {
    use swole::bench;

    use super::*;

    rows!(
        SHA512_256,
        sha2::Sha512_256,
        SHA512_256,
        verified_garbage::hashes::sha512_256::Sha512_256
    );
}

/// Many small updates show the cost of dispatching each one on the algorithm.
#[cfg(not(target_arch = "xtensa"))]
mod sha256_updates {
    use swole::bench;

    use super::*;

    const CHUNKS: [Size; 2] = [Size::new(1, "1B"), Size::new(16, "16B")];

    /// A 4 KB message, fed in `chunk`-byte updates.
    fn message(chunk: Size) -> (Vec<u8>, usize) {
        (vec![0; 4096], chunk.len)
    }

    fn rind_message(chunk: Size) -> Dit<(Vec<u8>, usize)> {
        Dit::hold(message(chunk))
    }

    #[bench(args = CHUNKS, setup = message)]
    fn aws_lc_rs((input, chunk): &(Vec<u8>, usize)) -> aws_lc_rs::digest::Digest {
        let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA256);
        for part in input.chunks(*chunk) {
            ctx.update(part);
        }
        ctx.finish()
    }

    #[bench(args = CHUNKS, setup = rind_message)]
    fn rind(message: &Dit<(Vec<u8>, usize)>) -> rind::digest::Digest {
        let (input, chunk) = &**message;
        let mut ctx = rind::digest::Context::new(&rind::digest::SHA256);
        for part in input.chunks(*chunk) {
            ctx.update(part);
        }
        ctx.finish()
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
