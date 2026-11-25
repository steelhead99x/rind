// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-DSA signing on pyca/verified-garbage's proven routines (`super::vg`),
//! for x86_64 CPUs without AVX2.
//!
//! Each routine is FIPS 204's `ML-DSA.Sign_internal` from the expanded
//! private key, its hashing and key expansion included: rind's glue keeps
//! computing `mu` and the hedged `rnd`. Only tests call it until a bench run
//! shows it at least as fast as rind's at every size on the tiers without
//! AVX2 (quest/m2/verified-garbage/mldsa-sign.md).

use core::mem::MaybeUninit;

use super::vg;
use crate::low::ct;

/// The working space each routine takes, the largest of the three (ML-DSA-87's
/// 18048 words), aligned to a cache line as VG's own API aligns it. VG proves
/// no variant that leaves it unwiped, so rind keeps the wipe, as AGENTS.md's
/// exception for imported routines allows.
#[repr(C, align(64))]
struct Scratch(MaybeUninit<[u64; 18048]>);

/// `ML-DSA.Sign_internal(sk, mu, rnd)` (FIPS 204 Algorithm 7) into `sig`, at
/// the parameter set `sk`'s length names. `None` if VG's loop reached its
/// bound (probability about 2^-256), or `sk` or `sig` is no set's length.
///
/// `sk` must be the expanded key of a key pair generated from its seed, as
/// VG's contract asks (`sk` written by its key generation).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn sign(sk: &[u8], mu: &[u8; 64], rnd: &[u8; 32], sig: &mut [u8]) -> Option<()> {
    let mut scratch = Scratch(MaybeUninit::uninit());
    let s = scratch.0.as_mut_ptr();
    // SAFETY: each pointer is to a distinct Rust object valid for its
    // routine's size (the scratch for the largest), so none overlaps
    // another, the stack, or the end of the address space; the routines
    // need no CPU feature. The caller vouches for `sk`'s origin.
    let ok = unsafe {
        match (sk.len(), sig.len()) {
            (2560, 2420) => vg::vg_mldsa44_sign::vg_mldsa44_sign(
                sk.as_ptr().cast(),
                mu,
                rnd,
                sig.as_mut_ptr().cast(),
                s.cast(),
            ),
            (4032, 3309) => vg::vg_mldsa65_sign::vg_mldsa65_sign(
                sk.as_ptr().cast(),
                mu,
                rnd,
                sig.as_mut_ptr().cast(),
                s.cast(),
            ),
            (4896, 4627) => vg::vg_mldsa87_sign::vg_mldsa87_sign(
                sk.as_ptr().cast(),
                mu,
                rnd,
                sig.as_mut_ptr().cast(),
                s.cast(),
            ),
            _ => return None,
        }
    };
    // Whether signing finished, and the signature it wrote, are public, as
    // rind's own signing declassifies them. What VG's routine branches on
    // or indexes by inside (FIPS 204's rejections, each attempt's `c_tilde`,
    // the hint: VG's `signLeak`) is suppressed in `admin/ctgrind.supp`.
    if ct::into_public(ok) != 1 {
        return None;
    }
    ct::public_slice(sig);
    Some(())
}
