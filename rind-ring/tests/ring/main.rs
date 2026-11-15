//! ring 0.17.14's own tests, run against rind-ring renamed to `ring`; see
//! `README.md` for what changed.

#![allow(deprecated)]
// Lints on ring's code, kept as ring wrote it.
#![allow(
    clippy::manual_clear,
    clippy::manual_is_multiple_of,
    clippy::useless_borrows_in_formatting
)]

extern crate rind_ring as ring;

mod test;

mod aead_tests;
mod agreement_tests;
mod constant_time_tests;
mod digest_tests;
mod ecdsa_tests;
mod ed25519_tests;
mod error_tests;
mod hkdf_tests;
mod hmac_tests;
mod pbkdf2_tests;
mod quic_tests;
mod rand_tests;
#[cfg(feature = "alloc")]
mod rsa_tests;
mod signature_tests;

// After the modules, so they reach it through `use crate::test_file`, as
// they reached ring's.
/// References a test input file beside the test that names it.
macro_rules! test_file {
    ($file_name:expr) => {
        crate::test::File {
            file_name: $file_name,
            contents: include_str!($file_name),
        }
    };
}

use test_file;
