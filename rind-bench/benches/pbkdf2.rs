#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::num::NonZeroU32;

#[cfg(not(target_arch = "xtensa"))]
use common::Dit;

// One key the length of the hash, as password storage derives. The cost is
// all in the iterations.
#[cfg(not(target_arch = "xtensa"))]
const ITERATIONS: NonZeroU32 = NonZeroU32::new(1000).unwrap();

/// Each PBKDF2 hash's rows, deriving a `$len`-byte key.
macro_rules! rows {
    ($ring:ident, $rind:path, $vg:ty, $len:literal) => {
        fn out() -> [u8; $len] {
            [0; $len]
        }

        fn rind_out() -> Dit<[u8; $len]> {
            Dit::hold(out())
        }

        #[bench(setup = out)]
        fn ring(out: &mut [u8; $len]) {
            ring::pbkdf2::derive(ring::pbkdf2::$ring, ITERATIONS, b"salt", b"password", out);
        }

        #[bench(setup = out)]
        fn aws_lc_rs(out: &mut [u8; $len]) {
            aws_lc_rs::pbkdf2::derive(
                aws_lc_rs::pbkdf2::$ring,
                ITERATIONS,
                b"salt",
                b"password",
                out,
            );
        }

        #[bench(setup = rind_out)]
        fn rind(out: &mut Dit<[u8; $len]>) {
            rind::pbkdf2::Secret::new(&$rind, b"password")
                .derive(ITERATIONS, b"salt", &mut **out)
                .unwrap();
        }

        /// The output buffer, after checking verified-garbage derives the
        /// key rind does.
        fn vg_out() -> [u8; $len] {
            let mut expected = out();
            rind::pbkdf2::Secret::new(&$rind, b"password")
                .derive(ITERATIONS, b"salt", &mut expected)
                .unwrap();
            let mut got = out();
            verified_garbage(&mut got);
            assert_eq!(got, expected);
            got
        }

        #[bench(setup = vg_out)]
        fn verified_garbage(out: &mut [u8; $len]) {
            verified_garbage::kdf::pbkdf2_hmac::derive::<$vg>(
                b"password",
                b"salt",
                ITERATIONS,
                out,
            );
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod pbkdf2_sha1 {
    use swole::bench;

    use super::*;

    rows!(
        PBKDF2_HMAC_SHA1,
        rind::pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        verified_garbage::hashes::sha1::Sha1,
        20
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod pbkdf2_sha256 {
    use swole::bench;

    use super::*;

    rows!(
        PBKDF2_HMAC_SHA256,
        rind::pbkdf2::PBKDF2_HMAC_SHA256,
        verified_garbage::hashes::sha256::Sha256,
        32
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod pbkdf2_sha384 {
    use swole::bench;

    use super::*;

    rows!(
        PBKDF2_HMAC_SHA384,
        rind::pbkdf2::PBKDF2_HMAC_SHA384,
        verified_garbage::hashes::sha384::Sha384,
        48
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod pbkdf2_sha512 {
    use swole::bench;

    use super::*;

    rows!(
        PBKDF2_HMAC_SHA512,
        rind::pbkdf2::PBKDF2_HMAC_SHA512,
        verified_garbage::hashes::sha512::Sha512,
        64
    );
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
