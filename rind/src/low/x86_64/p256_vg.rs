// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-256 on pyca/verified-garbage's proven routines (`super::vg`).
//!
//! Each routine is a whole operation on encoded keys: a public key's
//! derivation, ECDH with the peer's key validated, and ECDSA verification of
//! a hash. ECDH and verification measured faster than rind's on CPUs with
//! BMI2 and ADX, and faster still with AVX-512 IFMA, so those are what rind
//! takes; without ADX, rind's own measured faster. The public key's
//! derivation, which has no IFMA variant, measured faster on Intel and on
//! CPUs with IFMA, but 6% slower on AMD's Zen 3, so
//! [`P256::check_public_key`] leaves AMD without AVX-512 on rind's. VG signs
//! only deterministically, so signing takes its public key derivation for
//! the nonce's point and keeps rind's hedged nonce and arithmetic.
//!
//! Each routine's return code says only whether its inputs were valid: the
//! private key's range, which rind's `Scalar` already holds it to, and the
//! peer's point, which is public. So it is declassified for `admin/ctgrind`.

use core::mem::MaybeUninit;

use super::cpu::{HaveAdxForVg, HaveIfmaForVgP256, is_intel};
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

/// Proof that VG's P-256 runs here: the CPU has BMI2, ADX, AVX, and AVX2,
/// and whether it has AVX-512 IFMA too.
#[derive(Clone, Copy, Debug)]
pub(crate) struct P256 {
    adx: HaveAdxForVg,
    ifma: Option<HaveIfmaForVgP256>,
}

impl P256 {
    pub(crate) fn check() -> Option<Self> {
        Some(Self {
            adx: HaveAdxForVg::check()?,
            ifma: HaveIfmaForVgP256::check(),
        })
    }

    /// [`Self::check`], where VG's public key derivation measured faster
    /// than rind's too: on Intel, and with AVX-512 IFMA (AMD's Zen 4 and 5).
    pub(crate) fn check_public_key() -> Option<Self> {
        Self::check().filter(|vg| vg.ifma.is_some() || is_intel())
    }

    /// The public key `dG` of the private key `d`, big-endian, as an X9.62
    /// uncompressed point, or `None` if `d` is not in [1, n).
    pub(crate) fn public_key(self, d: &[u8; 32]) -> Option<[u8; 65]> {
        let mut out = [0u8; 65];
        let mut scratch = Scratch::new();
        // SAFETY: every pointer is to a distinct Rust object valid for its
        // size, so none overlaps another, the stack, or the end of the
        // address space; `self.adx` proves the CPU has the routine's
        // features.
        let ok = unsafe {
            vg::vg_ec_p256_public_key_adx::vg_ec_p256_public_key_adx(
                &mut out,
                d,
                scratch.as_mut_ptr(),
            )
        };
        (ct::into_public(ok) == 1).then_some(out)
    }

    /// The x-coordinate of `dQ`, big-endian, for the private key `d` and the
    /// peer's public key `peer`, an X9.62 uncompressed point, or `None` if
    /// `peer` is not a point on the curve or `d` is not in [1, n).
    pub(crate) fn ecdh(self, d: &[u8; 32], peer: &[u8; 65]) -> Option<[u8; 32]> {
        ecdh(self.width(), d, peer)
    }

    /// Whether `sig`, `r` then `s`, is a valid ECDSA signature of the
    /// message representative `e` by `public`, an X9.62 uncompressed
    /// point, all big-endian. A `public` not on the curve verifies nothing.
    pub(crate) fn verify(self, public: &[u8; 65], e: &[u8; 32], sig: &[u8; 64]) -> bool {
        verify(self.width(), public, e, sig)
    }

    /// The widest variant the CPU runs, as VG's dispatcher picks.
    fn width(self) -> Width {
        match self.ifma {
            Some(ifma) => Width::Ifma(ifma),
            None => Width::Adx(self.adx),
        }
    }
}

/// The variants of VG's ECDH and verification, each with proof that the
/// CPU has its features.
#[derive(Clone, Copy, Debug)]
enum Width {
    Adx(HaveAdxForVg),
    Ifma(HaveIfmaForVgP256),
}

/// [`P256::ecdh`], on the variant `width`.
// Never inlined, holding its `Mcdt` throughout, as `low::mcdt` requires.
#[inline(never)]
fn ecdh(width: Width, d: &[u8; 32], peer: &[u8; 65]) -> Option<[u8; 32]> {
    use vg::*;
    let mut out = [0u8; 32];
    let mut scratch = Scratch::new();
    let (o, s) = (&mut out, scratch.as_mut_ptr());
    // SAFETY: every pointer is to a distinct Rust object valid for its size,
    // so none overlaps another, the stack, or the end of the address space.
    // `width` proves the CPU has its variant's features.
    let ok = unsafe {
        match width {
            Width::Adx(_) => vg_ecdh_p256_adx::vg_ecdh_p256_adx(o, d, peer, s),
            Width::Ifma(_) => {
                // `vpmadd52luq` and `vpmadd52huq` multiply the secret `d`.
                let _mcdt = crate::low::Mcdt::enter();
                vg_ecdh_p256_ifma::vg_ecdh_p256_ifma(o, d, peer, s)
            }
        }
    };
    (ct::into_public(ok) == 1).then_some(out)
}

/// [`P256::verify`], on the variant `width`.
// Never inlined, holding its `Mcdt` throughout, as `low::mcdt` requires.
#[inline(never)]
fn verify(width: Width, public: &[u8; 65], e: &[u8; 32], sig: &[u8; 64]) -> bool {
    use vg::*;
    let mut scratch = Scratch::new();
    let (p, s) = (e.as_ptr(), scratch.as_mut_ptr());
    // SAFETY: as for `ecdh`, and `e` is valid for reads of its 32 bytes.
    let ok = unsafe {
        match width {
            Width::Adx(_) => {
                vg_ecdsa_p256_verify_adx::vg_ecdsa_p256_verify_adx(public, p, e.len(), sig, s)
            }
            Width::Ifma(_) => {
                // Its inputs are public, but `admin/ct-vartime` holds every
                // `vpmadd52luq` to the mitigation, as for RSA's public IFMA.
                let _mcdt = crate::low::Mcdt::enter();
                vg_ecdsa_p256_verify_ifma::vg_ecdsa_p256_verify_ifma(public, p, e.len(), sig, s)
            }
        }
    };
    ok == 1
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::vg_ec::{check_ecdh, check_verify};

    /// The generator G, as an X9.62 uncompressed point.
    const G: [u8; 65] = *b"\x04\
\x6b\x17\xd1\xf2\xe1\x2c\x42\x47\xf8\xbc\xe6\xe5\x63\xa4\x40\xf2\x77\x03\x7d\x81\x2d\xeb\x33\xa0\xf4\xa1\x39\x45\xd8\x98\xc2\x96\
\x4f\xe3\x42\xe2\xfe\x1a\x7f\x9b\x8e\xe7\xeb\x4a\x7c\x0f\x9e\x16\x2b\xce\x33\x57\x6b\x31\x5e\xce\xcb\xb6\x40\x68\x37\xbf\x51\xf5";

    // `vg_p256_mul_base_adx` reads `mid`'s generator table in place of
    // VG's own (admin/import-vg, `SHARED`), so VG's proof is about rind's
    // code only while the two hold the same bytes, and runs as fast only
    // on the same alignment.
    #[test]
    fn generator_table_is_vgs() {
        let rind = &crate::mid::p256::precomp::CURVE_GENERATOR_PRECOMP;
        let words = rind.0.iter().flatten().flat_map(|word| word.to_le_bytes());
        let vg = &vg::vg_p256_comb::VG_P256_COMB;
        assert!(words.eq(vg.0));
        assert_eq!(align_of_val(rind), align_of_val(vg));
        assert_eq!(size_of_val(rind), size_of_val(vg));
    }

    // The CPU's widest variant hides the narrower from every other test, so
    // each variant the CPU runs is checked against Wycheproof here.
    #[test]
    fn widths_match_wycheproof() {
        let Some(vg) = P256::check() else {
            return;
        };
        let widths = [Some(Width::Adx(vg.adx)), vg.ifma.map(Width::Ifma)];
        for width in widths.into_iter().flatten() {
            check_ecdh(|d, peer| ct::into_public(ecdh(width, d, peer)));
            check_verify(|public, e, sig| verify(width, public, e, sig));
        }
    }

    // `check_public_key` keeps rind's own on AMD without IFMA, as on the
    // ctgrind runners, so the public key's derivation is checked here, on
    // secret private keys: 1 gives G, others agree with ECDH against G, and
    // 0 and n are refused.
    #[test]
    fn public_key_matches_ecdh() {
        let Some(vg) = P256::check() else {
            return;
        };
        let mut one = [0u8; 32];
        one[31] = 1;
        let g = vg.public_key(&ct::into_secret(one)).map(ct::into_public);
        assert_eq!(g, Some(G));
        for byte in [0x01, 0x5a, 0xa5, 0xfe] {
            let d = ct::into_secret([byte; 32]);
            let public = vg.public_key(&d).map(ct::into_public).unwrap();
            let shared = ecdh(vg.width(), &d, &G).map(ct::into_public).unwrap();
            assert_eq!(public[0], 4);
            assert_eq!(public[1..33], shared);
        }
        let n = *b"\xff\xff\xff\xff\x00\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\
\xbc\xe6\xfa\xad\xa7\x17\x9e\x84\xf3\xb9\xca\xc2\xfc\x63\x25\x51";
        assert_eq!(vg.public_key(&[0; 32]), None);
        assert_eq!(vg.public_key(&n), None);
    }

    // VG's AVX-512 IFMA ECDH runs no instruction valgrind can, so
    // `admin/ct-sde` checks it: a private key from the seed, with G as the
    // peer. Verification takes no secret.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_p256_ifma_ecdh() {
        use crate::low::ct_sde;

        let ifma = HaveIfmaForVgP256::check().expect("AVX-512 IFMA");
        let mut d = [0x5a; 32];
        d[24..].copy_from_slice(&ct_sde::seed().to_be_bytes());
        assert!(ct_sde::traced(|| ecdh(Width::Ifma(ifma), &d, &G)).is_some());
    }
}
