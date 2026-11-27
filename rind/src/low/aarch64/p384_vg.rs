// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-384 on pyca/verified-garbage's proven routines (`super::vg`): `d·G`,
//! which key generation and ECDSA signing take, and ECDSA verification.
//! Each measured faster than rind's; verification only until a key's
//! multiples are ready, as rind's over them measured faster for a reused key.

use core::mem::MaybeUninit;

use super::vg;

/// The 8 KiB of working space each routine takes, aligned to a cache line as
/// VG's own API aligns it. The routines accept any initial contents. Key
/// derivation leaves secrets in it, which AGENTS.md's wipe rule leaves
/// unwiped, as it is stack scratch.
#[repr(C, align(64))]
struct Scratch(MaybeUninit<[u64; 1024]>);

/// Proof that VG's `d·G` runs here, as it does on every aarch64 CPU.
#[derive(Clone, Copy, Debug)]
pub(crate) struct MulBase(());

impl MulBase {
    pub(crate) fn check() -> Option<Self> {
        Some(Self(()))
    }

    /// `d·G` in X9.62's uncompressed encoding, in constant time, for `d`
    /// (big endian) in [1, n); `None` for any other `d`.
    pub(crate) fn public_key(self, d: &[u8; 48]) -> Option<[u8; 97]> {
        let mut out = [0u8; 97];
        let mut scratch = Scratch(MaybeUninit::uninit());
        // SAFETY: every pointer is to a distinct Rust object valid for its
        // size, so none overlaps another, the stack, or the end of the
        // address space.
        let ok = unsafe {
            vg::vg_ec_p384_public_key::vg_ec_p384_public_key(&mut out, d, scratch.0.as_mut_ptr())
        };
        // Whether `d` is in range is public: rind's keys and nonces always
        // are.
        (crate::low::ct::into_public(ok) == 1).then_some(out)
    }
}

/// Proof that VG's ECDSA verification runs here, as it does on every aarch64
/// CPU.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Verify(());

impl Verify {
    pub(crate) fn check() -> Option<Self> {
        Some(Self(()))
    }

    /// FIPS 186-5's ECDSA verification (section 6.4.2) of the signature
    /// `sig`, `r` then `s` big endian, of the message representative `e`, big
    /// endian, under the X9.62 uncompressed key `public`. False for a key off
    /// the curve or a coordinate not below p, and for `r` or `s` outside
    /// [1, n).
    pub(crate) fn ecdsa_verify(self, public: &[u8; 97], e: &[u8; 48], sig: &[u8; 96]) -> bool {
        let mut scratch = Scratch(MaybeUninit::uninit());
        // SAFETY: every pointer is to a distinct Rust object valid for its
        // size, `e` for its length, so none overlaps another, the stack, or
        // the end of the address space.
        let ok = unsafe {
            vg::vg_ecdsa_p384_verify::vg_ecdsa_p384_verify(
                public,
                e.as_ptr(),
                e.len(),
                sig,
                scratch.0.as_mut_ptr(),
            )
        };
        ok == 1
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // On a secret scalar, which `admin/ctgrind` checks it handles in
    // constant time.
    #[test]
    fn derives() {
        let d = crate::low::ct::into_secret([0x5a; 48]);
        let base = MulBase::check().unwrap();
        let public = crate::low::ct::into_public(base.public_key(&d).unwrap());
        assert_eq!(public[0], 4);
        assert_eq!(base.public_key(&[0; 48]), None);
        assert_eq!(base.public_key(&[0xff; 48]), None);
    }

    // rind's other tests reach VG's verification only until a key's multiples
    // are ready.
    #[test]
    fn verify_matches_wycheproof() {
        let vg = Verify::check().unwrap();
        crate::test::vg_ec::check_verify_p384(|public, e, sig| vg.ecdsa_verify(public, e, sig));
    }
}
