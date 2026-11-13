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
use std::sync::{Once, PoisonError, RwLock};

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
struct ThreadDrbg(HmacDrbg<Sha512>);

impl Drop for ThreadDrbg {
    fn drop(&mut self) {
        let mut live = LIVE.write().unwrap_or_else(PoisonError::into_inner);
        let address = core::ptr::from_mut(self) as usize;
        live.instances.retain(|&a| a != address);
        self.0.zeroise();
    }
}

/// Every thread's instance, by address, once instantiated: a draw holds it
/// for reading, and [`zeroise_all`] for writing.
struct Live {
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
        // drops only after removing it here, and uses only under a read of
        // `LIVE`, which this write excludes.
        unsafe { (*(address as *mut ThreadDrbg)).0.zeroise() };
    }
    live.zeroised = true;
    live.instances.len()
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
        let ThreadDrbg(drbg) = match &mut *drbg {
            Some(drbg) => drbg,
            None => {
                let instance = drbg.insert(ThreadDrbg(instantiate()?));
                let mut live = LIVE.write().map_err(|_| Error::RngFailed)?;
                live.instances.push(core::ptr::from_mut(instance) as usize);
                instance
            }
        };
        let live = LIVE.read().map_err(|_| Error::RngFailed)?;
        if live.zeroised {
            return Err(Error::RngFailed);
        }
        for request in out.chunks_mut(MAX_REQUEST_LEN) {
            generate(drbg, request)?;
        }
        Ok(())
    })
    .map_err(|_| Error::RngFailed)?
}

fn instantiate() -> Result<HmacDrbg<Sha512>, Error> {
    static CAST: Once = Once::new();
    CAST.call_once(|| {
        if !cast() {
            crate::fips::fail("drbg");
        }
    });

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
}
