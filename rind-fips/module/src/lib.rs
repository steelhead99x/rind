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
    // SAFETY: the handlers are `extern "C"` and never unwind.
    if unsafe { pthread_atfork(Some(fork_prepare), Some(fork_parent), Some(fork_child)) } != 0 {
        // Only out of memory, at load.
        std::eprintln!("rind-fips: cannot register its fork handlers");
        std::process::abort();
    }
}

unsafe extern "C" {
    fn pthread_atfork(
        prepare: Option<extern "C" fn()>,
        parent: Option<extern "C" fn()>,
        child: Option<extern "C" fn()>,
    ) -> core::ffi::c_int;
}

/// What a `fork` holds, from this thread's prepare handler to its parent's
/// or child's handler.
struct ForkHold {
    // A self-test may draw, so the self-tests are held first.
    #[allow(dead_code)]
    self_tests: selftest::Hold,
    drbgs: rind::fips::DrbgHold,
}

/// The hold of the `fork` in progress. Only a thread holding both of its
/// locks touches it, from its prepare handler to its parent or child
/// handler, and those locks admit one such thread at a time. A static,
/// unlike a thread local, still holds for a thread whose locals are torn
/// down, as when a destructor forks.
struct ForkSlot(core::cell::UnsafeCell<Option<ForkHold>>);

// SAFETY: the locks it holds serialize every access, as above; the guards
// it holds are released by the thread that took them, or by the child's
// copy of it.
unsafe impl Sync for ForkSlot {}

static FORK: ForkSlot = ForkSlot(core::cell::UnsafeCell::new(None));

impl ForkSlot {
    /// Swaps the hold in the slot for `hold`.
    ///
    /// # Safety
    /// This thread must hold the locks of the hold it takes or puts.
    unsafe fn replace(&self, hold: Option<ForkHold>) -> Option<ForkHold> {
        // SAFETY: the caller's contract, so no other thread accesses it.
        unsafe { core::mem::replace(&mut *self.0.get(), hold) }
    }
}

/// Holds the self-tests and the DRBGs across `fork`, so a child of a process
/// whose other threads were testing or drawing inherits neither half done,
/// and can still test, draw, and wipe its DRBGs at exit.
extern "C" fn fork_prepare() {
    let self_tests = selftest::hold();
    let drbgs = rind::fips::hold_drbgs();
    // SAFETY: this thread now holds both locks.
    unsafe { FORK.replace(Some(ForkHold { self_tests, drbgs })) };
}

extern "C" fn fork_parent() {
    // SAFETY: this thread's prepare handler took both locks.
    drop(unsafe { FORK.replace(None) });
}

/// Also wipes and forgets the DRBGs of the parent's other threads, which the
/// child copied but does not run.
extern "C" fn fork_child() {
    // SAFETY: the parent's forking thread, which this one copies, took both
    // locks in its prepare handler.
    if let Some(hold) = unsafe { FORK.replace(None) } {
        hold.drbgs.release_in_child();
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
