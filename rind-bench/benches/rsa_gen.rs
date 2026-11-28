//! RSA key generation. Each key takes tens to hundreds of milliseconds, and
//! varies with the primes it draws; under swole's count, which fixes the
//! randomness, it counts the same every run.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

macro_rules! generation {
    ($name:ident, $bits:literal, $aws:ident, $rind:ident $(, $rustcrypto:ident)?) => {
        mod $name {
            use super::*;
            use swole::bench;

            #[bench]
            fn aws_lc_rs() {
                black_box(aws_lc_rs::rsa::KeyPair::generate(aws_lc_rs::rsa::KeySize::$aws).unwrap());
            }

            #[bench(setup = dit)]
            fn rind(_: &Dit<()>) {
                black_box(rind::rsa::KeyPair::generate(rind::rsa::KeySize::$rind).unwrap());
            }

            fn vg_generate() -> verified_garbage::rsa::PrivateKey {
                use verified_garbage::rsa::{BigUint, keygen};
                keygen::generate($bits, BigUint::from_be_bytes(&[1, 0, 1])).unwrap()
            }

            /// Checks verified-garbage's key is of the size asked for.
            fn vg_check() {
                assert_eq!(vg_generate().modulus_len(), $bits / 8);
            }

            #[bench(setup = vg_check)]
            fn verified_garbage(_: &()) {
                black_box(vg_generate());
            }

            // RustCrypto takes seconds per 4096-bit key.
            $(
                #[bench]
                fn $rustcrypto() {
                    use getrandom::{SysRng, rand_core::UnwrapErr};
                    black_box(rsa::PrivateKey::new(&mut UnwrapErr(SysRng), $bits).unwrap());
                }
            )?
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
generation!(rsa2048_key_generation, 2048, Rsa2048, Rsa2048, rustcrypto);
#[cfg(not(target_arch = "xtensa"))]
generation!(rsa3072_key_generation, 3072, Rsa3072, Rsa3072);
#[cfg(not(target_arch = "xtensa"))]
generation!(rsa4096_key_generation, 4096, Rsa4096, Rsa4096);

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
