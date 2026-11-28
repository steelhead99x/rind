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

// A module named after the crate, so the crate is `::md5` inside it.
#[cfg(not(target_arch = "xtensa"))]
mod md5 {
    use swole::bench;

    use super::*;

    // aws-lc's MD5, which aws-lc-rs does not export, through aws-lc-sys.
    #[bench(args = HASH_SIZES, setup = input)]
    fn aws_lc_rs(input: &[u8]) -> [u8; 16] {
        let mut out = [0u8; 16];
        // SAFETY: `input` is readable for its length, and `out` is writable
        // for MD5's 16-byte digest.
        let ok = unsafe {
            aws_lc_sys::EVP_Digest(
                input.as_ptr().cast(),
                input.len(),
                out.as_mut_ptr(),
                core::ptr::null_mut(),
                aws_lc_sys::EVP_md5(),
                core::ptr::null_mut(),
            )
        };
        assert_eq!(ok, 1);
        out
    }

    #[bench(args = HASH_SIZES, setup = input)]
    fn rustcrypto(input: &[u8]) -> impl Sized + use<> {
        use ::md5::Digest;
        let mut ctx = ::md5::Md5::new();
        ctx.update(input);
        ctx.finalize()
    }

    #[bench(args = HASH_SIZES, setup = rind_input)]
    fn rind(input: &Dit<Vec<u8>>) -> rind::digest::Digest {
        let mut ctx = rind::digest::Context::new(&rind::digest::legacy::MD5);
        ctx.update(input);
        ctx.finish()
    }

    /// The message, after checking verified-garbage's digest of it matches
    /// rind's.
    fn vg_input(size: Size) -> Vec<u8> {
        let input = size.zeros();
        assert_eq!(
            verified_garbage(&input).as_ref(),
            rind::digest::digest(&rind::digest::legacy::MD5, &input).as_ref()
        );
        input
    }

    #[bench(args = HASH_SIZES, setup = vg_input)]
    fn verified_garbage(input: &[u8]) -> impl AsRef<[u8]> + use<> {
        let mut ctx = verified_garbage::hashes::md5::Md5::new();
        ctx.update(input);
        ctx.finalize()
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
