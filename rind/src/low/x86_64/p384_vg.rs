// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-384 on pyca/verified-garbage's proven routines (`super::vg`): `d·G`,
//! which key generation and ECDSA signing take, and ECDSA verification.
//! `d·G` measured faster than rind's on every x86_64 CPU, and takes VG's BMI2
//! and ADX variant where the CPU has its features, as VG's own dispatcher
//! does; verification only with BMI2 and ADX.

use core::mem::MaybeUninit;

use super::cpu::{HaveAdxForVg, HaveBmi2Adx};
use super::vg;

/// The 8 KiB of working space each routine takes, aligned to a cache line as
/// VG's own API aligns it. The routines accept any initial contents. Key
/// derivation leaves secrets in it, which AGENTS.md's wipe rule leaves
/// unwiped, as it is stack scratch.
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

/// Proof that VG's `d·G` runs here, as it does on every x86_64 CPU, and
/// whether the CPU has its BMI2 and ADX variant's features.
#[derive(Clone, Copy, Debug)]
pub(crate) struct MulBase(Option<HaveAdxForVg>);

impl MulBase {
    pub(crate) fn check() -> Option<Self> {
        Some(Self(HaveAdxForVg::check()))
    }

    /// `d·G` in X9.62's uncompressed encoding, in constant time, for `d`
    /// (big endian) in [1, n); `None` for any other `d`.
    pub(crate) fn public_key(self, d: &[u8; 48]) -> Option<[u8; 97]> {
        use vg::{vg_ec_p384_public_key::*, vg_ec_p384_public_key_adx::*};
        let mut out = [0u8; 97];
        let mut scratch = Scratch::new();
        let (o, s) = (&mut out, scratch.as_mut_ptr());
        // SAFETY: every pointer is to a distinct Rust object valid for its
        // size, so none overlaps another, the stack, or the end of the
        // address space. `self.0` proves the CPU has the ADX variant's
        // features.
        let ok = unsafe {
            match self.0 {
                Some(_) => vg_ec_p384_public_key_adx(o, d, s),
                None => vg_ec_p384_public_key(o, d, s),
            }
        };
        // Whether `d` is in range is public: rind's keys and nonces always
        // are.
        (crate::low::ct::into_public(ok) == 1).then_some(out)
    }
}

/// Proof that VG's ECDSA verification runs here: the CPU has BMI2 and ADX.
/// Without them, VG's baseline routine measured slower than rind's on AMD's
/// cores, so rind's runs instead.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Verify(HaveBmi2Adx);

impl Verify {
    pub(crate) fn check() -> Option<Self> {
        HaveBmi2Adx::check().map(Self)
    }

    /// FIPS 186-5's ECDSA verification (section 6.4.2) of the signature
    /// `sig`, `r` then `s` big endian, of the message representative `e`, big
    /// endian, under the X9.62 uncompressed key `public`. False for a key off
    /// the curve or a coordinate not below p, and for `r` or `s` outside
    /// [1, n).
    pub(crate) fn ecdsa_verify(self, public: &[u8; 97], e: &[u8; 48], sig: &[u8; 96]) -> bool {
        let mut scratch = Scratch::new();
        let (e, len, s) = (e.as_ptr(), e.len(), scratch.as_mut_ptr());
        // SAFETY: every pointer is to a distinct Rust object valid for its
        // size, `e` for `len` bytes, so none overlaps another, the stack, or
        // the end of the address space. `self` proves the CPU has BMI2 and
        // ADX.
        let ok = unsafe {
            vg::vg_ecdsa_p384_verify_adx::vg_ecdsa_p384_verify_adx(public, e, len, sig, s)
        };
        ok == 1
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // The CPU picks one variant, so each runs here: the baseline one always,
    // and the ADX one where the CPU has it, on a secret scalar each, which
    // `admin/ctgrind` checks they handle in constant time.
    #[test]
    fn variants_agree() {
        let d = crate::low::ct::into_secret([0x5a; 48]);
        let base = crate::low::ct::into_public(MulBase(None).public_key(&d).unwrap());
        if let Some(adx) = HaveAdxForVg::check() {
            let adx = MulBase(Some(adx))
                .public_key(&d)
                .map(crate::low::ct::into_public);
            assert_eq!(adx, Some(base));
        }
        assert_eq!(MulBase(None).public_key(&[0; 48]), None);
        assert_eq!(MulBase::check().unwrap().public_key(&[0xff; 48]), None);
    }

    #[test]
    fn verify_matches_wycheproof() {
        if let Some(vg) = Verify::check() {
            crate::test::vg_ec::check_verify_p384(|public, e, sig| vg.ecdsa_verify(public, e, sig));
        }
    }
}
