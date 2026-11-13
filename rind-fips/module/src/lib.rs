// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! rind's FIPS 140-3 cryptographic module: a shared library whose loaded
//! code and constants are the module's boundary, exporting a C ABI over
//! opaque heap handles that `rind-fips` wraps in rind's API.
//!
//! `rind-fips`'s build script builds it from rind's source with `--cfg
//! rind_fips`, which draws every random value from the module's DRBG, and
//! with pinned flags; a plain workspace build compiles it empty.
//!
//! - At load, a constructor runs the HMAC-SHA-256 and SHA-256 self-tests,
//!   then the integrity test ([`integrity`]).
//! - Each algorithm's self-test runs before its first use ([`selftest`]),
//!   and a pairwise consistency test follows each key pair generation.
//! - A failure prints which test failed and aborts: the error state.
//! - Every service that handles an SSP zeroes the stack it used
//!   ([`scrub`]), and the allocator zeroes every block it frees
//!   ([`alloc`]), so no SSP outlives the call or handle holding it.
//! - Every service is approved, with approved parameters, so a successful
//!   call is the service indicator.
#![cfg(rind_fips)]

mod abi;
mod aes;
mod agreement;
mod alloc;
mod digest;
mod ids;
mod image;
mod integrity;
mod kem;
mod mac;
mod scrub;
mod selftest;
mod signature;

#[global_allocator]
static ALLOCATOR: alloc::Zeroing = alloc::Zeroing;

/// The module's name and version, as its security policy would name it.
pub(crate) const VERSION: &str = concat!("rind-fips ", env!("CARGO_PKG_VERSION"));

/// Runs at load, before any service: the pre-operational self-tests.
#[used]
#[unsafe(link_section = ".init_array")]
static INIT: extern "C" fn() = init;

extern "C" fn init() {
    // The integrity test runs on HMAC-SHA-256, so those go first. Their
    // first call detects the CPU's features, so the `RIND_CPU_DISABLE_*`
    // mask, by which each CPU path is reached for its ACVP run, is read at
    // load, and a CPU missing a feature the module requires aborts here,
    // naming it.
    selftest::ensure(&[selftest::SelfTest::Sha256, selftest::SelfTest::Hmac]);
    if !integrity::check() {
        rind::fips::fail("integrity");
    }
}

/// Runs as the process exits, after the exiting thread's destructors: wipes
/// the DRBG of every thread still running, whose own never run.
#[used]
#[unsafe(link_section = ".fini_array")]
static FINI: extern "C" fn() = fini;

extern "C" fn fini() {
    let wiped = rind::fips::zeroise_drbgs();
    // The break build shows the lab that it ran.
    #[cfg(rind_fips_break)]
    std::eprintln!("rind-fips: zeroised {wiped} DRBG instances at exit");
    #[cfg(not(rind_fips_break))]
    let _ = wiped;
}
