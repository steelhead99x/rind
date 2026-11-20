// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! X25519 and Ed25519 verification on CPUs with AVX-IFMA and no AVX-512,
//! through [`super::avx_ifma`]'s re-encoding of pyca/verified-garbage's
//! AVX-512 IFMA routines. On Arrow Lake they take 0.66 of the mulx routines'
//! time for X25519 (see `BENCHMARKS.md`).

use core::mem::MaybeUninit;

use super::avx_ifma;
use super::cpu::HaveAvxIfmaForCurve25519;
use crate::low;

/// The working space the routines take, aligned to a cache line as VG's own
/// API aligns it. They accept any initial contents and may leave secrets in
/// it, which rind leaves on the stack, as AGENTS.md's wipe rule says.
#[repr(C, align(64))]
struct Scratch<const N: usize>(MaybeUninit<[u64; N]>);

impl<const N: usize> Scratch<N> {
    fn new() -> Self {
        Self(MaybeUninit::uninit())
    }

    fn as_mut_ptr(&mut self) -> *mut [u64; N] {
        self.0.as_mut_ptr()
    }
}

/// Proof that the CPU runs the AVX-IFMA X25519 and Ed25519 verification.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Curve25519AvxIfma(HaveAvxIfmaForCurve25519);

impl Curve25519AvxIfma {
    pub(crate) fn check() -> Option<Self> {
        HaveAvxIfmaForCurve25519::check().map(Self)
    }

    /// `X25519(scalar, point)` (RFC 7748 section 5) into `res`, each
    /// little-endian words, as [`super::curve25519_ifma::Curve25519Ifma`]'s.
    // Never inlined, holding its `Mcdt` throughout, as `low::mcdt` requires:
    // `vpmadd52luq` and `vpmadd52huq` multiply the secret scalar's ladder.
    #[inline(never)]
    pub(crate) fn x25519(self, res: &mut [u64; 4], scalar: &[u64; 4], point: &[u64; 4]) {
        let _mcdt = low::Mcdt::enter();
        let (scalar, point) = (bytes(scalar), bytes(point));
        let mut out = [0u8; 32];
        let mut scratch = Scratch::<512>::new();
        // SAFETY: `out`, `scalar`, and `point` are 32 bytes and `scratch`
        // 4096, distinct objects, so none overlaps another, the return
        // address, or the stack below it, or wraps the address space. The
        // token proves the CPU features.
        unsafe {
            asm_call!(unsafe extern "sysv64" (avx_ifma::vg_x25519_exchange_ifma::vg_x25519_exchange_ifma)(
                &mut out,
                &scalar,
                &point,
                scratch.as_mut_ptr()
            ))
        };
        // Its return value says whether `out` is zero, which the caller
        // checks itself, as on every other CPU.
        *res = words(&out);
    }

    /// Whether `sig` is an Ed25519 signature of `msg` by `public` (RFC 8032
    /// section 5.1.7), as [`super::curve25519_ifma::Curve25519Ifma`]'s.
    // Never inlined, holding its `Mcdt`, as `Self::x25519`, though every
    // input is public: `admin/ct-vartime` finds every IFMA multiply.
    #[inline(never)]
    pub(crate) fn ed25519_verify(self, public: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
        let _mcdt = low::Mcdt::enter();
        let mut scratch = Scratch::<1024>::new();
        // SAFETY: `public` is 32 bytes, `msg` `msg.len()`, `sig` 64, and
        // `scratch` 8192, distinct objects, so none overlaps another, the
        // return address, or the stack below it, or wraps the address space.
        // The token proves the CPU features.
        let ok = unsafe {
            asm_call!(unsafe extern "sysv64" (avx_ifma::vg_ed25519_verify_avx2_ifma::vg_ed25519_verify_avx2_ifma)(
                public,
                msg.as_ptr(),
                msg.len(),
                sig,
                scratch.as_mut_ptr()
            ))
        };
        ok == 1
    }
}

/// Little-endian words as bytes.
fn bytes(words: &[u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (b, w) in out.as_chunks_mut::<8>().0.iter_mut().zip(words) {
        *b = w.to_le_bytes();
    }
    out
}

/// Bytes as little-endian words.
fn words(bytes: &[u8; 32]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (w, b) in out.iter_mut().zip(bytes.as_chunks::<8>().0) {
        *w = u64::from_le_bytes(*b);
    }
    out
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::super::adx_mux::tests::Rng;
    use super::super::ct_sde;
    use super::*;

    /// `2^255 - 19 + d`, the non-canonical encodings of `d`, and with the
    /// top bit, which X25519 masks, set too.
    fn p_plus(d: u64, top: bool) -> [u64; 4] {
        [
            0xffff_ffff_ffff_ffed + d,
            !0,
            !0,
            (!0 >> 1) | (u64::from(top) << 63),
        ]
    }

    // X25519 on the AVX-IFMA ladder against s2n-bignum's, on random points
    // and edge cases: `u` of `p` and above, with the top bit set, and 0 and
    // 1, of small order, whose result is zero.
    #[test]
    fn x25519_matches_s2n_bignum() {
        let Some(avx_ifma) = Curve25519AvxIfma::check() else {
            return;
        };
        let mut rng = Rng(0x2551_9000_0000_0002);
        let mut points = vec![[0; 4], [1, 0, 0, 0], [!0; 4]];
        for d in 0..19 {
            points.push(p_plus(d, false));
            points.push(p_plus(d, true));
        }
        for _ in 0..2048 {
            points.push(rng.words(256));
        }
        for point in points {
            let scalar = rng.words(256);
            let (mut want, mut got) = ([0; 4], [0; 4]);
            super::super::curve25519_x25519::curve25519_x25519(&mut want, &scalar, &point);
            avx_ifma.x25519(&mut got, &scalar, &point);
            assert_eq!(got, want, "{point:x?}");
        }
    }

    // A secret scalar against a public point, for `admin/ct-sde`.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_x25519_avx_ifma() {
        let mut rng = Rng(ct_sde::seed());
        let avx_ifma = Curve25519AvxIfma::check().expect("AVX-IFMA");
        let scalar = rng.words(256);
        let mut res = [0; 4];
        ct_sde::traced(|| avx_ifma.x25519(&mut res, &scalar, &[9, 0, 0, 0]));
    }
}
