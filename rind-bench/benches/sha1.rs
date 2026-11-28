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

// A module named after the crate, so the crate is `::sha1` inside it.
#[cfg(not(target_arch = "xtensa"))]
mod sha1 {
    use swole::bench;

    use super::*;

    #[bench(args = HASH_SIZES, setup = input)]
    fn ring(input: &[u8]) -> ring::digest::Digest {
        let mut ctx = ring::digest::Context::new(&ring::digest::SHA1_FOR_LEGACY_USE_ONLY);
        ctx.update(input);
        ctx.finish()
    }

    #[bench(args = HASH_SIZES, setup = input)]
    fn aws_lc_rs(input: &[u8]) -> aws_lc_rs::digest::Digest {
        let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA1_FOR_LEGACY_USE_ONLY);
        ctx.update(input);
        ctx.finish()
    }

    #[bench(args = HASH_SIZES, setup = input)]
    fn rustcrypto(input: &[u8]) -> impl Sized + use<> {
        use ::sha1::Digest;
        let mut ctx = ::sha1::Sha1::new();
        ctx.update(input);
        ctx.finalize()
    }

    #[bench(args = HASH_SIZES, setup = rind_input)]
    fn rind(input: &Dit<Vec<u8>>) -> rind::digest::Digest {
        let mut ctx = rind::digest::Context::new(&rind::digest::legacy::SHA1);
        ctx.update(input);
        ctx.finish()
    }

    /// The message, after checking verified-garbage's digest of it matches
    /// rind's.
    fn vg_input(size: Size) -> Vec<u8> {
        let input = size.zeros();
        assert_eq!(
            verified_garbage(&input).as_ref(),
            rind::digest::digest(&rind::digest::legacy::SHA1, &input).as_ref()
        );
        input
    }

    #[bench(args = HASH_SIZES, setup = vg_input)]
    fn verified_garbage(input: &[u8]) -> impl AsRef<[u8]> + use<> {
        let mut ctx = verified_garbage::hashes::sha1::Sha1::new();
        ctx.update(input);
        ctx.finalize()
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
