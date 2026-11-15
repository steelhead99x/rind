// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The FIPS module's random generator: SP 800-90A HMAC_DRBG with SHA-512,
//! at its 256-bit security strength, one instance per thread.
//!
//! Entropy comes from the OS, outside the module's boundary (IG 9.3.A
//! scenario 2(b)). Every request reseeds first, which is SP 800-90A's
//! prediction resistance: a forked child, which inherits its parent's
//! instance, still never repeats its parent's output. The OS read this costs
//! is the one a `rind` draw already makes.
//!
//! It lives at the crate root, not in `mid` beside [`crate::mid::rng`], which
//! draws from it in the module's build, because HMAC lives in `high`.
//!
//! Each thread's instance wipes itself as its thread exits. A process's
//! `exit` runs only the exiting thread's destructors, so the module's own
//! destructor wipes the rest with [`zeroise_all`], as aws-lc's
//! `rand_thread_state_clear_all` does.

use core::cell::RefCell;
use core::sync::atomic::{AtomicBool, Ordering};
use std::sync::{PoisonError, RwLock, RwLockWriteGuard};

use crate::Error;
use crate::high::hash::Sha512;
use crate::high::hmac_drbg::HmacDrbg;
use crate::low::Entry;

/// Bytes of entropy per instantiation and reseed: the security strength.
const ENTROPY_LEN: usize = 32;

/// Bytes of the instantiation's nonce: half the security strength, drawn from
/// the same source (SP 800-90A section 8.6.7).
const NONCE_LEN: usize = 16;

/// SP 800-90A's `max_number_of_bits_per_request` for HMAC_DRBG, in bytes.
const MAX_REQUEST_LEN: usize = 1 << 16;

std::thread_local! {
    static DRBG: RefCell<Option<ThreadDrbg>> = const { RefCell::new(None) };
}

/// A thread's DRBG, whose state is wiped as the thread exits: unlike ECDSA's,
/// it outlives the call that seeded it.
///
/// The state has its own allocation, which every access reaches through
/// this pointer or the registry's copy of it, under [`LIVE`]: so the exit
/// wipe, writing it while the thread waits in this drop, aliases no
/// reference the thread holds.
struct ThreadDrbg(*mut HmacDrbg<Sha512>);

impl ThreadDrbg {
    fn new(drbg: HmacDrbg<Sha512>) -> Self {
        Self(Box::into_raw(Box::new(drbg)))
    }
}

impl Drop for ThreadDrbg {
    fn drop(&mut self) {
        let mut live = LIVE.write().unwrap_or_else(PoisonError::into_inner);
        live.instances.retain(|&a| a != self.0 as usize);
        // SAFETY: `new` allocated it, only this drop frees it, and the write
        // excludes every other access.
        let mut drbg = unsafe { Box::from_raw(self.0) };
        drbg.zeroise();
    }
}

/// Every thread's instance, by the address of its state, once instantiated:
/// a draw holds it for reading, and instantiation, [`zeroise_all`], and
/// [`hold`] for writing.
pub(crate) struct Live {
    instances: Vec<usize>,
    /// Whether [`zeroise_all`] has run, after which every draw fails.
    zeroised: bool,
}

static LIVE: RwLock<Live> = RwLock::new(Live {
    instances: Vec::new(),
    zeroised: false,
});

/// Wipes every thread's instance, returning how many, and fails every draw
/// after: the module's destructor runs it as the process exits.
pub(crate) fn zeroise_all() -> usize {
    let mut live = LIVE.write().unwrap_or_else(PoisonError::into_inner);
    for &address in &live.instances {
        // SAFETY: each address is a live thread's instance, which its thread
        // registers under a write of `LIVE`, frees only after removing it
        // here, and otherwise touches only under a read, which this write
        // excludes.
        unsafe { (*(address as *mut HmacDrbg<Sha512>)).zeroise() };
    }
    live.zeroised = true;
    live.instances.len()
}

/// The registry held for writing, so no draw, instantiation, or wipe runs
/// until it drops.
pub(crate) struct Hold(RwLockWriteGuard<'static, Live>);

/// Waits for every draw in progress, then holds the registry, as the module
/// does across `fork`: the child then inherits no instance mid-draw and no
/// lock held by a thread it lacks.
pub(crate) fn hold() -> Hold {
    Hold(LIVE.write().unwrap_or_else(PoisonError::into_inner))
}

/// In a forked child, under the hold its parent's `fork` took: wipes, frees,
/// and forgets the instance of every thread but this one, the child's only
/// thread. The child holds a copy of each, but no thread that would
/// unregister or free it, so a process that forks and forks again would
/// otherwise accumulate them.
pub(crate) fn forked(hold: Hold) {
    let Hold(mut live) = hold;
    // This thread called `fork`, so it is inside no draw, and its instance
    // is not borrowed.
    let own = DRBG
        .try_with(|drbg| Some(drbg.try_borrow().ok()?.as_ref()?.0 as usize))
        .ok()
        .flatten();
    for &address in &live.instances {
        if Some(address) != own {
            // SAFETY: the parent registered `address` as a live thread's
            // instance, allocated by `ThreadDrbg::new`, under a write of
            // `LIVE`, and its `fork` held that lock, so the child's copy is
            // whole. No thread of the child holds its `ThreadDrbg`, so
            // nothing else frees or uses it.
            let mut drbg = unsafe { Box::from_raw(address as *mut HmacDrbg<Sha512>) };
            drbg.zeroise();
        }
    }
    live.instances.retain(|&address| Some(address) == own);
}

/// Fills `out` from this thread's DRBG, instantiating it on first use.
///
/// Fails if the OS supplies no entropy, or if called while this thread is
/// being torn down.
pub(crate) fn fill(out: &mut [u8]) -> Result<(), Error> {
    // `rand::fill` reaches here with no other entry held.
    let _entry = Entry::new_secret();
    DRBG.try_with(|drbg| {
        let mut drbg = drbg.try_borrow_mut().map_err(|_| Error::RngFailed)?;
        if drbg.is_none() {
            // Instantiated and registered under one write, so the exit wipe
            // either finds the instance or has already run and refuses it.
            let mut live = LIVE.write().map_err(|_| Error::RngFailed)?;
            if live.zeroised {
                return Err(Error::RngFailed);
            }
            let instance = drbg.insert(ThreadDrbg::new(instantiate()?));
            live.instances.push(instance.0 as usize);
        }
        let live = LIVE.read().map_err(|_| Error::RngFailed)?;
        if live.zeroised {
            return Err(Error::RngFailed);
        }
        let &mut ThreadDrbg(drbg) = drbg.as_mut().ok_or(Error::RngFailed)?;
        // SAFETY: this thread's instance, which only the holder of a write
        // of `LIVE` touches otherwise, and this read excludes that.
        let drbg = unsafe { &mut *drbg };
        for request in out.chunks_mut(MAX_REQUEST_LEN) {
            generate(drbg, request)?;
        }
        Ok(())
    })
    .map_err(|_| Error::RngFailed)?
}

/// Whether the self-test has passed in this process.
static CAST_PASSED: AtomicBool = AtomicBool::new(false);

fn instantiate() -> Result<HmacDrbg<Sha512>, Error> {
    // The self-test passes once per process, before the first instantiation.
    // A plain flag, not a `Once`: `fork` copies a `Once` that another thread
    // is inside, and the child, which lacks that thread, then waits forever
    // on its first draw. Threads that race here each run the test, which is
    // pure, so the race only repeats it.
    if !CAST_PASSED.load(Ordering::Acquire) {
        if !cast() {
            crate::fips::fail("drbg");
        }
        CAST_PASSED.store(true, Ordering::Release);
    }

    let mut entropy = [0u8; ENTROPY_LEN];
    let mut nonce = [0u8; NONCE_LEN];
    getrandom::fill(&mut entropy).map_err(|_| Error::RngFailed)?;
    getrandom::fill(&mut nonce).map_err(|_| Error::RngFailed)?;
    Ok(HmacDrbg::new(&entropy, &nonce, b""))
}

/// Section 9.3.1's generate with prediction resistance: reseed from the OS,
/// then generate with no additional input.
fn generate(drbg: &mut HmacDrbg<Sha512>, out: &mut [u8]) -> Result<(), Error> {
    let mut entropy = [0u8; ENTROPY_LEN];
    getrandom::fill(&mut entropy).map_err(|_| Error::RngFailed)?;
    drbg.reseed(&entropy, b"");
    drbg.generate(out, b"");
    Ok(())
}

/// Section 11.3's known-answer health test of instantiate, reseed, and
/// generate, with every input present: the first SHA-512 vector of CAVP's
/// `HMAC_DRBG.rsp` with personalization and additional input. Its second
/// generate is shortened to one block, since a shorter request returns a
/// prefix of a longer one.
pub(crate) fn cast() -> bool {
    const ENTROPY: [u8; 32] = *b"\xda\x74\x0c\xbc\x36\x05\x7a\x8e\x28\x2a\xe7\x17\xfe\x7d\xfb\xb2\x45\xe9\xe5\xd4\x99\x08\xa0\x11\x9c\x5d\xbc\xf0\xa1\xf2\xd5\xab";
    const NONCE: [u8; 16] = *b"\x46\x56\x1f\xf6\x12\x21\x7b\xa3\xff\x91\xba\xa0\x6d\x4b\x54\x40";
    const PERSONALIZATION: [u8; 32] = *b"\xfc\x22\x72\x93\x52\x3e\xcb\x5b\x1e\x28\xc8\x78\x63\x62\x66\x27\xd9\x58\xac\xc5\x58\xa6\x72\xb1\x48\xce\x19\xe2\xab\xd2\xdd\xe4";
    const ENTROPY_RESEED: [u8; 32] = *b"\x1d\x61\xd4\xd8\xa4\x1c\x32\x54\xb9\x21\x04\xfd\x55\x5a\xda\xe0\x56\x9d\x18\x35\xbb\x52\x65\x7e\xc7\xfb\xba\x0f\xe0\x35\x79\xc5";
    const ADDITIONAL_RESEED: [u8; 32] = *b"\xb9\xed\x8e\x35\xad\x01\x8a\x37\x5b\x61\x18\x9c\x8d\x36\x5b\x00\x50\x7c\xb1\xb4\x51\x0d\x21\xca\xc2\x12\x35\x6b\x5b\xba\xa8\xb2";
    const ADDITIONAL_1: [u8; 32] = *b"\xb7\x99\x89\x98\xea\xf9\xe5\xd3\x4e\x64\xff\x7f\x03\xde\x76\x5b\x31\xf4\x07\x89\x9d\x20\x53\x55\x73\xe6\x70\xc1\xb4\x02\xc2\x6a";
    const ADDITIONAL_2: [u8; 32] = *b"\x20\x89\xd4\x9d\x63\xe0\xc4\xdf\x58\x87\x9d\x0c\xb1\xba\x99\x8e\x5b\x3d\x1a\x77\x86\xb7\x85\xe7\xcf\x13\xca\x5e\xa5\xe3\x3c\xfd";
    #[cfg(all(test, unix, not(miri)))]
    tests::stall();

    const EXPECTED: [u8; 64] = *b"\x5b\x70\xf3\xe4\xda\x95\x26\x42\x33\xef\xba\xb1\x55\xb8\x28\xd4\xe2\x31\xb6\x7c\xc9\x27\x57\xfe\xca\x40\x7c\xc9\x61\x5a\x66\x08\x71\xcb\x07\xad\x1a\x2e\x9a\x99\x41\x2f\xed\xa8\xee\x34\xdc\x9c\x57\xfa\x08\xd3\xf8\x22\x5b\x30\xd2\x98\x87\xd2\x09\x07\xd1\x23";

    let mut entropy = ENTROPY;
    if crate::fips::broken("drbg") {
        entropy[0] ^= 1;
    }
    let mut drbg = HmacDrbg::<Sha512>::new(&entropy, &NONCE, &PERSONALIZATION);
    drbg.reseed(&ENTROPY_RESEED, &ADDITIONAL_RESEED);
    let mut out = [0u8; 256];
    drbg.generate(&mut out, &ADDITIONAL_1);
    drbg.generate(&mut out[..64], &ADDITIONAL_2);
    out[..64] == EXPECTED
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn cast_passes() {
        assert!(cast());
    }

    #[test]
    fn fills_across_requests() {
        // Two requests' worth, each from a fresh reseed, so the halves differ.
        let mut out = vec![0u8; 2 * MAX_REQUEST_LEN];
        fill(&mut out).unwrap();
        let (a, b) = out.split_at(MAX_REQUEST_LEN);
        assert_ne!(a[..64], b[..64]);
        assert!(out[out.len() - 64..].iter().any(|&b| b != 0));
    }

    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn threads_draw_independently() {
        let mut ours = [0u8; 32];
        fill(&mut ours).unwrap();
        let theirs = std::thread::spawn(|| {
            let mut out = [0u8; 32];
            fill(&mut out).unwrap();
            out
        })
        .join()
        .unwrap();
        assert_ne!(ours, theirs);
    }

    /// Set by the fork test, so a thread inside the self-test waits there
    /// until `RELEASE` is set.
    #[cfg(all(unix, not(miri)))]
    static STALL: AtomicBool = AtomicBool::new(false);
    #[cfg(all(unix, not(miri)))]
    static STALLED: AtomicBool = AtomicBool::new(false);
    #[cfg(all(unix, not(miri)))]
    static RELEASE: AtomicBool = AtomicBool::new(false);

    #[cfg(all(unix, not(miri)))]
    pub(super) fn stall() {
        if STALL.load(Ordering::Acquire) {
            STALLED.store(true, Ordering::Release);
            while !RELEASE.load(Ordering::Acquire) {
                std::thread::yield_now();
            }
        }
    }

    /// A process forked while another thread is inside the self-test still
    /// instantiates. Clearing the passed flag first makes the next
    /// instantiation run the self-test again, whatever other tests did, so
    /// this needs no fresh process.
    #[cfg(all(unix, not(miri)))]
    #[test]
    fn fork_during_self_test() {
        // Finishes every lazy initialization the child reaches, such as
        // SHA-512's routine choice, so no other thread is inside one at fork.
        assert!(cast());
        STALL.store(true, Ordering::Release);
        // A test thread already past `stall` can set the flag again after
        // the reset, letting the drawer skip the self-test; draw again then.
        let drawer = loop {
            CAST_PASSED.store(false, Ordering::Release);
            // A fresh thread has no DRBG yet, so its draw instantiates.
            let drawer = std::thread::spawn(|| fill(&mut [0u8; 32]).unwrap());
            while !STALLED.load(Ordering::Acquire) && !drawer.is_finished() {
                std::thread::yield_now();
            }
            if STALLED.load(Ordering::Acquire) {
                break drawer;
            }
            drawer.join().unwrap();
        };

        // The test build checks each assembly call under one lock, which a
        // child forked while another test thread held it could never take.
        #[cfg(any(
            rind_backend = "x86_64",
            rind_backend = "aarch64",
            rind_backend = "arm"
        ))]
        let abi = crate::low::abi::hold();
        // SAFETY: the child calls only `instantiate`, which allocates
        // nothing, and leaves through `_exit`.
        let pid = unsafe { libc::fork() };
        #[cfg(any(
            rind_backend = "x86_64",
            rind_backend = "aarch64",
            rind_backend = "arm"
        ))]
        drop(abi);
        if pid < 0 {
            RELEASE.store(true, Ordering::Release);
            panic!("fork failed");
        }
        if pid == 0 {
            RELEASE.store(true, Ordering::Release);
            // Whatever another thread published, the child runs the self-test.
            CAST_PASSED.store(false, Ordering::Release);
            let ok = instantiate().is_ok();
            // SAFETY: ends the child without running the parent's destructors.
            unsafe { libc::_exit(if ok { 0 } else { 1 }) };
        }

        RELEASE.store(true, Ordering::Release);
        drawer.join().unwrap();
        let mut status = 0;
        for _ in 0..1000 {
            // SAFETY: `pid` is our child and `status` a valid out pointer.
            let done = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
            if done == pid {
                assert!(libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0);
                return;
            }
            std::thread::sleep(core::time::Duration::from_millis(10));
        }
        // SAFETY: `pid` is our child, still running.
        unsafe { libc::kill(pid, libc::SIGKILL) };
        panic!("the forked child hung instantiating");
    }
}
