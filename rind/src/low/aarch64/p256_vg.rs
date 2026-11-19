// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-256 on pyca/verified-garbage's proven routines (`super::vg`).
//!
//! Each routine is a whole operation on encoded keys: a public key's
//! derivation, ECDH with the peer's key validated, and ECDSA verification of
//! a hash. They measured faster than rind's on every aarch64 CPU for
//! verification, and on every one but the narrow-multiplier cores
//! (Cortex-A72, A76, Neoverse N1) for the other two, which keep rind's own.
//! VG signs only deterministically, so signing takes its public key
//! derivation for the nonce's point and keeps rind's hedged nonce and
//! arithmetic.
//!
//! Each routine's return code says only whether its inputs were valid: the
//! private key's range, which rind's `Scalar` already holds it to, and the
//! peer's point, which is public. So it is declassified for `admin/ctgrind`.

use core::mem::MaybeUninit;

use super::vg;
use crate::low::ct;

/// The 8 KiB of working space each routine takes, aligned to a cache line
/// as VG's own API aligns it. The routines accept any initial contents.
/// Those that take the private key leave secrets in it, which rind does not
/// wipe: it is a stack temporary, as AGENTS.md's wipe rule describes.
#[repr(C, align(64))]
struct Scratch(MaybeUninit<[u64; 1024]>);

impl Scratch {
    fn new() -> Self {
        Self(MaybeUninit::uninit())
    }

    fn as_mut_ptr(&mut self) -> *mut [u64; 1024] {
        self.0.as_mut_ptr()
    }
}

/// Proof that VG's P-256 runs here, as it does on every aarch64 CPU.
#[derive(Clone, Copy, Debug)]
pub(crate) struct P256(());

impl P256 {
    pub(crate) fn check() -> Option<Self> {
        Some(Self(()))
    }

    /// [`Self::check`], for the public key's derivation. A core on the narrow
    /// schedules (Cortex-A72, A76, Neoverse N1) is faster on rind's own
    /// s2n-bignum `p256_scalarmulbase`: on a Pi 5, 36.5 against 45.2 us.
    pub(crate) fn check_public_key() -> Option<Self> {
        super::cpu::wide_multiplier().then_some(Self(()))
    }

    /// [`Self::check`], for ECDH, with the same exception: rind's narrow
    /// `p256_scalarmul` takes 200 us to VG's 282 on a Pi 5. VG's
    /// verification stays faster there, so [`Self::check`] keeps it.
    pub(crate) fn check_ecdh() -> Option<Self> {
        super::cpu::wide_multiplier().then_some(Self(()))
    }

    /// The public key `dG` of the private key `d`, big-endian, as an X9.62
    /// uncompressed point, or `None` if `d` is not in [1, n).
    pub(crate) fn public_key(self, d: &[u8; 32]) -> Option<[u8; 65]> {
        let mut out = [0u8; 65];
        let mut scratch = Scratch::new();
        // SAFETY: every pointer is to a distinct Rust object valid for its
        // size, so none overlaps another, the stack, or the end of the
        // address space.
        let ok = unsafe {
            vg::vg_ec_p256_public_key::vg_ec_p256_public_key(&mut out, d, scratch.as_mut_ptr())
        };
        (ct::into_public(ok) == 1).then_some(out)
    }

    /// The x-coordinate of `dQ`, big-endian, for the private key `d` and the
    /// peer's public key `peer`, an X9.62 uncompressed point, or `None` if
    /// `peer` is not a point on the curve or `d` is not in [1, n).
    pub(crate) fn ecdh(self, d: &[u8; 32], peer: &[u8; 65]) -> Option<[u8; 32]> {
        let mut out = [0u8; 32];
        let mut scratch = Scratch::new();
        // SAFETY: as for `public_key`.
        let ok = unsafe { vg::vg_ecdh_p256::vg_ecdh_p256(&mut out, d, peer, scratch.as_mut_ptr()) };
        (ct::into_public(ok) == 1).then_some(out)
    }

    /// Whether `sig`, `r` then `s`, is a valid ECDSA signature of the
    /// message representative `e` by `public`, an X9.62 uncompressed
    /// point, all big-endian. A `public` not on the curve verifies nothing.
    pub(crate) fn verify(self, public: &[u8; 65], e: &[u8; 32], sig: &[u8; 64]) -> bool {
        let mut scratch = Scratch::new();
        // SAFETY: as for `public_key`, and `e` is valid for reads of its 32
        // bytes.
        let ok = unsafe {
            vg::vg_ecdsa_p256_verify::vg_ecdsa_p256_verify(
                public,
                e.as_ptr(),
                e.len(),
                sig,
                scratch.as_mut_ptr(),
            )
        };
        ok == 1
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::p256_vg::{check_ecdh, check_verify};

    #[test]
    fn matches_wycheproof() {
        let vg = P256::check().unwrap();
        check_ecdh(|d, peer| ct::into_public(vg.ecdh(d, peer)));
        check_verify(|public, e, sig| vg.verify(public, e, sig));
    }
}
