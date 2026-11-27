// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! X25519 and Ed25519 on CPUs with AVX-512 IFMA, by pyca/verified-garbage's
//! routines, which `admin/import-vg` imports.
//!
//! They took 0.52 to 0.68 of rind's time on Zen 4, and lost on every CPU
//! without IFMA, so only these CPUs run them. Each is a whole RFC 7748 or RFC
//! 8032 operation, Ed25519's SHA-512 included: VG's lower routines are
//! internal ones, with no contract of their own. Of VG's IFMA variants, these
//! are the ones it picks on CPUs without the SHA-512 instructions, as every
//! CPU with IFMA measured so far lacks them.
//!
//! VG proves each correct in Lean, over its own models of the instructions,
//! which `admin/prove vg` cosimulates, against the contracts in its
//! `Spec/X25519` and `Spec/Ed25519`; the `# Safety` items below restate their
//! preconditions. It proves X25519, key generation, and signing constant time
//! too; verification's contract lets its timing depend on its inputs, which
//! are all public.

use core::mem::MaybeUninit;

use super::cpu::HaveIfmaForCurve25519;
use super::vg;
use crate::low;

/// The working space VG's routines take, aligned to a cache line as VG's own
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

/// Proof that the CPU runs VG's X25519 and Ed25519 for AVX-512 IFMA.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Curve25519Ifma(HaveIfmaForCurve25519);

impl Curve25519Ifma {
    pub(crate) fn check() -> Option<Self> {
        HaveIfmaForCurve25519::check().map(Self)
    }

    /// `X25519(scalar, point)` (RFC 7748 section 5) into `res`, each
    /// little-endian words, as s2n-bignum's `curve25519_x25519` takes them:
    /// the scalar clamped, the point's top bit masked, and `res` zero for a
    /// point of small order.
    // Never inlined, holding its `Mcdt` throughout, as `low::mcdt` requires:
    // `vpmadd52luq` and `vpmadd52huq` multiply the secret scalar's ladder.
    #[inline(never)]
    pub(crate) fn x25519(self, res: &mut [u64; 4], scalar: &[u64; 4], point: &[u64; 4]) {
        let _mcdt = low::Mcdt::enter();
        let mut scratch = Scratch::<512>::new();
        // SAFETY: `res`, `scalar`, and `point` are 32 bytes and `scratch`
        // 4096, distinct objects, so none overlaps another, the return
        // address, or the stack below it, or wraps the address space. The
        // token proves the CPU features.
        unsafe {
            asm_call!(unsafe extern "sysv64" (vg::vg_x25519_exchange_ifma::vg_x25519_exchange_ifma)(
                as_bytes_mut(res),
                as_bytes(scalar),
                as_bytes(point),
                scratch.as_mut_ptr()
            ))
        };
        // Its return value says whether `res` is zero, which the caller
        // checks itself, as on every other CPU.
    }

    /// `X25519(scalar, 9)`, the public key of `scalar` (RFC 7748 section
    /// 6.1), into `res`, each little-endian words, as s2n-bignum's
    /// `curve25519_x25519base` takes them.
    // Never inlined, holding its `Mcdt`, as `Self::x25519`.
    #[inline(never)]
    pub(crate) fn x25519_base(self, res: &mut [u64; 4], scalar: &[u64; 4]) {
        let _mcdt = low::Mcdt::enter();
        let mut scratch = Scratch::<1024>::new();
        // SAFETY: `res` and `scalar` are 32 bytes and `scratch` 8192,
        // distinct objects, so none overlaps another, the return address, or
        // the stack below it, or wraps the address space. The token proves
        // the CPU features.
        unsafe {
            asm_call!(unsafe extern "sysv64" (vg::vg_x25519_base_ifma::vg_x25519_base_ifma)(
                as_bytes_mut(res),
                as_bytes(scalar),
                scratch.as_mut_ptr()
            ))
        };
    }

    /// Ed25519's key pair for `seed` (RFC 8032 section 5.1.5): the seed's
    /// SHA-512 digest, which [`Self::ed25519_sign`] takes, and the public
    /// key.
    // Never inlined, holding its `Mcdt`, as `Self::x25519`.
    #[inline(never)]
    pub(crate) fn ed25519_key_pair(self, seed: &[u8; 32]) -> ([u8; 64], [u8; 32]) {
        let _mcdt = low::Mcdt::enter();
        let (mut expanded, mut public) = ([0u8; 64], [0u8; 32]);
        let mut scratch = Scratch::<1024>::new();
        // SAFETY: `public` and `seed` are 32 bytes, `expanded` 64, and
        // `scratch` 8192, distinct objects, so none overlaps another, the
        // return address, or the stack below it, or wraps the address space.
        // The token proves the CPU features. Its contract holds for any seed:
        // VG's note that the seed be random is about the key's security.
        unsafe {
            asm_call!(unsafe extern "sysv64" (vg::vg_ed25519_key_pair_avx2_ifma::vg_ed25519_key_pair_avx2_ifma)(
                &mut public,
                &mut expanded,
                seed,
                scratch.as_mut_ptr()
            ))
        };
        (expanded, public)
    }

    /// The Ed25519 signature of `msg` (RFC 8032 section 5.1.6) by the seed
    /// whose SHA-512 digest is `expanded` and whose public key is `public`.
    ///
    /// `expanded` and `public` must be what [`Self::ed25519_key_pair`]
    /// returned for one seed.
    // Never inlined, holding its `Mcdt`, as `Self::x25519`.
    #[inline(never)]
    pub(crate) fn ed25519_sign(
        self,
        expanded: &[u8; 64],
        public: &[u8; 32],
        msg: &[u8],
    ) -> [u8; 64] {
        let _mcdt = low::Mcdt::enter();
        let mut out = [0u8; 64];
        let mut scratch = Scratch::<1024>::new();
        // SAFETY: `out` and `expanded` are 64 bytes, `public` 32, `msg`
        // `msg.len()`, and `scratch` 8192, distinct objects, so none overlaps
        // another, the return address, or the stack below it, or wraps the
        // address space. The caller passes `expanded` and `public` from one
        // seed's key pair, as the contract requires, and the token proves the
        // CPU features.
        unsafe {
            asm_call!(unsafe extern "sysv64" (vg::vg_ed25519_sign_expanded_avx2_ifma::vg_ed25519_sign_expanded_avx2_ifma)(
                &mut out,
                expanded,
                public,
                msg.as_ptr(),
                msg.len(),
                scratch.as_mut_ptr()
            ))
        };
        out
    }

    /// Whether `sig` is an Ed25519 signature of `msg` by `public` (RFC 8032
    /// section 5.1.7): both points canonically encoded, `S < L`, and `[S]B =
    /// R + [k]A` without the cofactor, `k` reduced modulo `L`, as rind checks
    /// on every other CPU.
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
            asm_call!(unsafe extern "sysv64" (vg::vg_ed25519_verify_avx2_ifma::vg_ed25519_verify_avx2_ifma)(
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

/// Little-endian words' memory as the 32 bytes they encode: x86_64 stores
/// each word little-endian, so VG reads and writes the encoding RFC 7748
/// takes without a copy.
fn as_bytes(words: &[u64; 4]) -> *const [u8; 32] {
    core::ptr::from_ref(words).cast()
}

/// [`as_bytes`] for an output.
fn as_bytes_mut(words: &mut [u64; 4]) -> *mut [u8; 32] {
    core::ptr::from_mut(words).cast()
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::super::adx_mux::tests::Rng;
    use super::super::ct_sde;
    use super::*;

    fn random(rng: &mut Rng) -> [u8; 32] {
        let mut out = [0; 32];
        for (b, w) in out
            .as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(rng.words::<4>(256))
        {
            *b = w.to_le_bytes();
        }
        out
    }

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

    // X25519 on VG's routines against s2n-bignum's, on random points and
    // edge cases: `u` of `p` and above, with the top bit set, and 0 and 1,
    // of small order, whose result is zero. Wycheproof's vectors hold the
    // rest of the small-order points.
    #[test]
    fn x25519_matches_s2n_bignum() {
        let Some(ifma) = Curve25519Ifma::check() else {
            return;
        };
        let mut rng = Rng(0x2551_9000_0000_0001);
        let mut points = vec![[0; 4], [1, 0, 0, 0], [!0; 4]];
        for d in 0..19 {
            points.push(p_plus(d, false));
            points.push(p_plus(d, true));
        }
        for _ in 0..256 {
            points.push(rng.words(256));
        }
        for point in points {
            let scalar = rng.words(256);
            let (mut want, mut got) = ([0; 4], [0; 4]);
            super::super::curve25519_x25519::curve25519_x25519(&mut want, &scalar, &point);
            ifma.x25519(&mut got, &scalar, &point);
            assert_eq!(got, want, "{point:x?}");

            super::super::curve25519_x25519base::curve25519_x25519base(&mut want, &scalar);
            ifma.x25519_base(&mut got, &scalar);
            assert_eq!(got, want, "{scalar:x?}");
        }
    }

    // A secret scalar against a public point, and a secret scalar alone, for
    // `admin/ct-sde`.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_x25519() {
        let mut rng = Rng(ct_sde::seed());
        let ifma = Curve25519Ifma::check().expect("AVX-512 IFMA");
        let scalar = rng.words(256);
        let mut res = [0; 4];
        ct_sde::traced(|| ifma.x25519(&mut res, &scalar, &[9, 0, 0, 0]));
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_x25519_base() {
        let mut rng = Rng(ct_sde::seed());
        let ifma = Curve25519Ifma::check().expect("AVX-512 IFMA");
        let scalar = rng.words(256);
        let mut res = [0; 4];
        ct_sde::traced(|| ifma.x25519_base(&mut res, &scalar));
    }

    // A secret seed, then its signature of a public message, for
    // `admin/ct-sde`.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_ed25519_key_pair() {
        let mut rng = Rng(ct_sde::seed());
        let ifma = Curve25519Ifma::check().expect("AVX-512 IFMA");
        let seed = random(&mut rng);
        ct_sde::traced(|| ifma.ed25519_key_pair(&seed));
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_ed25519_sign() {
        let mut rng = Rng(ct_sde::seed());
        let ifma = Curve25519Ifma::check().expect("AVX-512 IFMA");
        let (expanded, public) = ifma.ed25519_key_pair(&random(&mut rng));
        let msg = [0x5a; 200];
        ct_sde::traced(|| ifma.ed25519_sign(&expanded, &public, &msg));
    }
}
