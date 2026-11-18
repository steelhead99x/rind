// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RSA's public operation and its CRT on CPUs with AVX-512 IFMA, by
//! pyca/verified-garbage's routines, which `admin/import-vg` imports.
//!
//! The public operation runs radix-2^52 almost-Montgomery products on
//! AVX-512 IFMA for 2048-, 3072-, and 4096-bit moduli with `e = 65537`, and
//! 64-bit Montgomery products on BMI2 and ADX for the rest, which rind
//! leaves to its own code: VG's measured slower at 2056 bits. The CRT runs the
//! exponentiations modulo `p` and `q` at once on IFMA for 2048- and 4096-bit
//! keys of balanced primes, by a fixed window of 4 or 5 bits whose table entry
//! is gathered by masking every entry, and for 3072-bit keys on CPUs with
//! AVX512_FP16, where it runs its form for two 512-bit multipliers. Its other
//! form measured slower than aws-lc's dual RSAZ at 3072 bits on Zen 5, so
//! other CPUs keep that there.
//!
//! VG proves each correct and constant time in Lean, over its own models of
//! the instructions, which `admin/prove vg` cosimulates: the public operation by
//! `checked_correct` in `Proof/Variants/RsaPublicPrecomputed/X86_64/Ifma.lean`
//! against `pdChkContract`, the CRT by `codeP_inlined` in
//! `Proof/Variants/RsaPrivateCrt/X86_64/Ifma.lean` against `crtContractP`.
//! These are VG's internal functions, which its own padding schemes call, so
//! their contracts are in VG's proofs rather than its trusted `Spec`; the
//! `# Safety` items below restate them.

use super::cpu::HaveAvx512ForRsa;
use super::vg;
use crate::low;

/// Proof that the CPU runs VG's AVX-512 IFMA public operation for a key.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RsaIfma(HaveAvx512ForRsa);

/// A private key's values for VG's CRT, which its contract requires be
/// exactly what `vg_rsa_private_precompute` writes for `n`, `p`, and `q`,
/// so only this computes them, from `n`, `p`, and `q`, which it keeps.
///
/// It holds no `Option` or CPU token, so that all-zero bytes, which its drop
/// leaves, are a valid value: one for no key, which [`IfmaCrt::runs`]
/// refuses.
pub(crate) struct IfmaCrt {
    /// The words of each prime, 16, 24, or 32: half of `n`'s. Zero where
    /// VG's CRT does not run.
    w: usize,
    /// `n` and `2^(128 * 2w) mod n`, at `2w` words each, then `2^(128w)`
    /// modulo `p` and modulo `q`, at `w` words each.
    pre: [u64; 6 * MAX_PRIME_WORDS],
    p: [u64; MAX_PRIME_WORDS],
    q: [u64; MAX_PRIME_WORDS],
}

// Every field is words or a length, valid at zero.
impl low::Zeroable for IfmaCrt {}

impl Drop for IfmaCrt {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

/// `vg_rsa_public_precomputed_checked`'s arguments: `out`, `n_len`, `pre`,
/// `pre_len`, `e`, `e_len`, `input`, `input_len`, `scratch`, `scratch_len`.
type PublicFn = unsafe extern "sysv64" fn(
    *mut u8,
    usize,
    *const u64,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *mut u64,
    usize,
) -> u32;

/// `vg_rsa_private_crt_precomputed`'s arguments: `out`, `out_len`, `n`,
/// `n_len`, `input`, `input_len`, `p`, `p_len`, `q`, `q_len`, `dp`,
/// `dp_len`, `dq`, `dq_len`, `qinv`, `qinv_len`, `scratch`, `scratch_len`,
/// `pre`, `pre_len`.
type CrtFn = unsafe extern "sysv64" fn(
    *mut u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *mut u64,
    usize,
    *const u64,
    usize,
) -> u32;

/// The widest modulus, in 64-bit words.
const MAX_WORDS: usize = 128;

/// The widest prime VG's IFMA CRT takes, in 64-bit words.
const MAX_PRIME_WORDS: usize = 32;

impl RsaIfma {
    /// For a key of modulus `n` and exponent `e`, where VG's routine takes
    /// its IFMA path: a 2048-, 3072-, or 4096-bit `n` and `e = 65537`.
    pub(crate) fn check<const N: usize>(n: &low::PosInt<N>, e: u64) -> Option<Self> {
        if e != 65537 || !matches!(n.len_bytes(), 256 | 384 | 512) {
            return None;
        }
        // Not `map(Self)`, whose translation Lean cannot check.
        let token = HaveAvx512ForRsa::check()?;
        Some(Self(token))
    }

    /// Writes `x^e mod n` to `out`, as long as `n`, for `pre` holding `n`
    /// and then `R^2 mod n`, `R = 2^(64w)`, in `w = ⌈out.len() / 8⌉`
    /// little-endian words each, and big-endian `e` and `x`.
    ///
    /// Returns whether it did: it refuses, writing zeros, an `n` that is
    /// even, outside 512 to 8192 bits, or longer than `out`, an `e` that is
    /// even, below 3, or of more than 33 bits, and an `x` not below `n`.
    /// Constant time in `x`.
    // Never inlined, holding its `Mcdt` throughout, as `low::mcdt` requires.
    #[inline(never)]
    pub(crate) fn public(self, out: &mut [u8], pre: &[u64], e: &[u8], x: &[u8]) -> bool {
        // `vpmadd52luq` and `vpmadd52huq` multiply `x`, which may be secret.
        let _mcdt = low::Mcdt::enter();
        let k = out.len();
        let w = k.div_ceil(8);
        assert!((64..=MAX_WORDS * 8).contains(&k));
        assert!(pre.len() == 2 * w && x.len() == k && (1..=k).contains(&e.len()));
        let mut scratch = [Line([0; 8]); (8 * MAX_WORDS + 48) / 8];
        let scratch = &mut Line::words(&mut scratch)[..8 * w + 48];
        // SAFETY: VG declares its internal functions without parameters, as
        // only its own code calls them, and `PublicFn` is the signature its
        // contract gives this one.
        let f: PublicFn = unsafe {
            core::mem::transmute::<unsafe extern "sysv64" fn(), PublicFn>(
                vg::vg_rsa_public_precomputed_checked_ifma::vg_rsa_public_precomputed_checked_ifma,
            )
        };
        // SAFETY: `out` is `k` writable bytes, `pre` `2w` readable words,
        // `e` and `x` `e.len()` and `k` readable bytes, and `scratch`
        // `8w + 48` writable words, with `64 <= k <= 1024` and
        // `1 <= e.len() <= k`. They are distinct objects, so none overlaps
        // another, the return address, or the stack below it, or wraps the
        // address space. Its contract asks nothing of `pre`'s values, of
        // which only the result depends. The token proves the CPU features.
        let r = unsafe {
            asm_call!(unsafe extern "sysv64" (f)(
                out.as_mut_ptr(),
                k,
                pre.as_ptr(),
                pre.len(),
                e.as_ptr(),
                e.len(),
                x.as_ptr(),
                k,
                scratch.as_mut_ptr(),
                scratch.len(),
            ))
        };
        r == 1
    }
}

impl IfmaCrt {
    /// The values VG's CRT takes for the key of `n`, `p`, and `q`, little-endian
    /// words: if the CPU runs it, and it is the fastest there, for 2048- and
    /// 4096-bit moduli of primes as wide as each other, as aws-lc's dual RSAZ
    /// requires, and 3072-bit ones on CPUs with AVX512_FP16. Otherwise, or if
    /// `n` is even or not `p q`, a value
    /// that [`IfmaCrt::runs`] refuses.
    pub(crate) fn new(n: &[u64], p: &[u64], q: &[u64]) -> Self {
        Self::try_new(n, p, q).unwrap_or(Self {
            w: 0,
            pre: [0; 6 * MAX_PRIME_WORDS],
            p: [0; MAX_PRIME_WORDS],
            q: [0; MAX_PRIME_WORDS],
        })
    }

    fn try_new(n: &[u64], p: &[u64], q: &[u64]) -> Option<Self> {
        let token = HaveAvx512ForRsa::check()?;
        let w = p.len();
        let sized = matches!(w, 16 | 32) || (w == 24 && token.fp16());
        if !sized || q.len() != w || n.len() != 2 * w {
            return None;
        }
        Self::precompute(n, p, q)
    }

    /// [`IfmaCrt::try_new`] past its CPU and size checks, for `p` and `q` of
    /// `w` words and `n` of `2 w`. It runs on any CPU, so `admin/ctgrind`
    /// checks it, as Valgrind hides AVX-512 IFMA from `try_new`.
    fn precompute(n: &[u64], p: &[u64], q: &[u64]) -> Option<Self> {
        let w = p.len();
        let n = low::PosInt::<{ 2 * MAX_PRIME_WORDS }>::from_words(n).ok()?;
        let p = low::PosInt::<MAX_PRIME_WORDS>::from_words(p).ok()?;
        let q = low::PosInt::<MAX_PRIME_WORDS>::from_words(q).ok()?;
        // The modulus `vg_rsa_private_precompute` takes: odd, and as many
        // words as `n_len` bytes make. It is public.
        if n.is_even() || n.as_words()[2 * w - 1] == 0 {
            return None;
        }
        // Its other requirement, revealing only the verdict, as the caller
        // has already checked it.
        let pq: low::PosInt<{ 2 * MAX_PRIME_WORDS }> = low::PosInt::mul(&p, &q);
        if !low::ct::into_public(pq.equals(&n)) {
            return None;
        }

        let mut ifma = Self {
            w,
            pre: [0; 6 * MAX_PRIME_WORDS],
            p: [0; MAX_PRIME_WORDS],
            q: [0; MAX_PRIME_WORDS],
        };
        ifma.p[..w].copy_from_slice(p.as_words());
        ifma.q[..w].copy_from_slice(q.as_words());
        let (pre_n, pre_p) = ifma.pre[..6 * w].split_at_mut(4 * w);
        pre_n[..2 * w].copy_from_slice(n.as_words());
        pre_n[2 * w..].copy_from_slice(n.pub_montifier().as_words());
        pre_p[..w].copy_from_slice(p.montifier().as_words());
        pre_p[w..].copy_from_slice(q.montifier().as_words());
        Some(ifma)
    }

    /// Whether VG's CRT runs for this key on this CPU.
    pub(crate) fn runs(&self) -> bool {
        self.w != 0
    }

    /// Writes `x^d mod n` to `out` by the CRT, for big-endian `x`, `dp`,
    /// `dq`, and `qinv`, `x` and `out` as long as `n` and the others as `p`'s
    /// words make.
    ///
    /// Returns whether it did: it refuses, writing zeros, an `x` not below
    /// `n` and a `qinv` not below `p`, revealing only that, and does nothing
    /// unless [`IfmaCrt::runs`]. Constant time in all but `n`.
    // Never inlined, holding its `Mcdt` throughout, as `low::mcdt` requires.
    #[inline(never)]
    pub(crate) fn crt(&self, out: &mut [u8], x: &[u8], dp: &[u8], dq: &[u8], qinv: &[u8]) -> bool {
        // `vpmadd52luq` and `vpmadd52huq` multiply the secrets.
        let _mcdt = low::Mcdt::enter();
        let w = self.w;
        // `new` checked the CPU wherever `w` is nonzero.
        let Some(token) = HaveAvx512ForRsa::check().filter(|_| w != 0) else {
            return false;
        };
        let (n, pre) = (&self.pre[..2 * w], &self.pre[..6 * w]);
        let k = low::bignum_bitsize(n).div_ceil(8);
        let p_len = 8 * w;
        assert!(out.len() == k && x.len() == k);
        assert!([dp.len(), dq.len(), qinv.len()] == [p_len; 3]);
        let mut n_bytes = [0u8; 16 * MAX_PRIME_WORDS];
        let mut p = [0u8; 8 * MAX_PRIME_WORDS];
        let mut q = [0u8; 8 * MAX_PRIME_WORDS];
        let (n_bytes, p, q) = (&mut n_bytes[..k], &mut p[..p_len], &mut q[..p_len]);
        be_bytes(n, n_bytes);
        be_bytes(&self.p[..w], p);
        be_bytes(&self.q[..w], q);
        // On the heap, at up to 64 KiB, and wiped, as it holds values of the
        // private key.
        let mut lines = alloc::vec![Line([0; 8]); (16 * k + 32).div_ceil(8)];
        let scratch = &mut Line::words(&mut lines)[..16 * k + 32];
        let f: CrtFn = match token.fp16() {
            // SAFETY: VG declares its internal functions without parameters,
            // as only its own code calls them, and `CrtFn` is the signature
            // its contract gives this one.
            true => unsafe {
                core::mem::transmute::<unsafe extern "sysv64" fn(), CrtFn>(
                    vg::vg_rsa_private_crt_precomputed_ifma512::vg_rsa_private_crt_precomputed_ifma512,
                )
            },
            // SAFETY: as above.
            false => unsafe {
                core::mem::transmute::<unsafe extern "sysv64" fn(), CrtFn>(
                    vg::vg_rsa_private_crt_precomputed_ifma::vg_rsa_private_crt_precomputed_ifma,
                )
            },
        };
        // SAFETY: `out` is `k` writable bytes, `n_bytes` and `x` `k` readable
        // bytes, `p`, `dp`, `qinv`, `q`, and `dq` `p_len`, `scratch` `16k + 32`
        // writable words, and `pre` `2 * ⌈k / 8⌉ + 2 * max(2, ⌈p_len / 8⌉)`
        // readable words, with `64 <= k <= 1024` and `p_len < k`. They are
        // distinct objects, so none overlaps another, the return address, or
        // the stack below it, or wraps the address space. `new` computed
        // `pre` as `vg_rsa_private_precompute` does for these `n`, `p`, and
        // `q`, having checked `n` valid and `p q = n`. The token proves the
        // CPU features.
        let r = unsafe {
            asm_call!(unsafe extern "sysv64" (f)(
                out.as_mut_ptr(),
                k,
                n_bytes.as_ptr(),
                k,
                x.as_ptr(),
                k,
                p.as_ptr(),
                p_len,
                q.as_ptr(),
                p_len,
                dp.as_ptr(),
                p_len,
                dq.as_ptr(),
                p_len,
                qinv.as_ptr(),
                p_len,
                scratch.as_mut_ptr(),
                scratch.len(),
                pre.as_ptr(),
                pre.len(),
            ))
        };
        low::zeroise(scratch);
        low::ct::into_public(r) == 1
    }
}

/// A cache line of VG's scratch, which starts on one: VG measured its IFMA
/// CRT a sixth slower at 3072 and 4096 bits on scratch aligned to 8 bytes.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
struct Line([u64; 8]);

impl Line {
    fn words(lines: &mut [Self]) -> &mut [u64] {
        // SAFETY: `Line` is `repr(C)` of 8 `u64`s with no padding, so `lines`
        // is `8 * lines.len()` contiguous initialized words, which this
        // borrows exclusively for as long as `lines`.
        unsafe { core::slice::from_raw_parts_mut(lines.as_mut_ptr().cast(), 8 * lines.len()) }
    }
}

/// Writes little-endian `words` to `out`, big-endian, as long as `out`.
fn be_bytes(words: &[u64], out: &mut [u8]) {
    for (i, byte) in out.iter_mut().rev().enumerate() {
        *byte = (words.get(i / 8).copied().unwrap_or(0) >> (8 * (i % 8))) as u8;
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::super::adx_mux::tests::Rng;
    use super::super::ct_sde;
    use super::*;

    /// Under `admin/ctgrind`, VG's CRT values are computed from the primes
    /// without branching on them or indexing by them; only the public `n`
    /// may be, and whether `p q = n`.
    #[test]
    fn precompute_on_secret_primes() {
        for w in [16, 24, 32] {
            let mut rng = Rng(w as u64);
            let mut prime = || {
                let mut p: [u64; MAX_PRIME_WORDS] = rng.words(64 * w as u32);
                p[0] |= 1;
                p[w - 1] |= 1 << 63;
                p
            };
            let (p, q) = (prime(), prime());
            let pi = low::PosInt::<MAX_PRIME_WORDS>::from_words(&p[..w]).unwrap();
            let qi = low::PosInt::<MAX_PRIME_WORDS>::from_words(&q[..w]).unwrap();
            let n: low::PosInt<{ 2 * MAX_PRIME_WORDS }> = low::PosInt::mul(&pi, &qi);
            low::ct::secret_slice(&p);
            low::ct::secret_slice(&q);
            let ifma = IfmaCrt::precompute(n.as_words(), &p[..w], &q[..w]).unwrap();
            assert_eq!(ifma.w, w);
            let pre = low::ct::into_public(ifma.pre);
            assert_eq!(&pre[..2 * w], n.as_words());
            assert_eq!(
                &pre[4 * w..5 * w],
                low::ct::into_public(pi.montifier()).as_words()
            );
        }
    }

    /// `words` as `bytes` big-endian bytes.
    fn be(words: &[u64], bytes: usize) -> Vec<u8> {
        let mut out = vec![0; bytes];
        be_bytes(words, &mut out);
        out
    }

    // `admin/ct-sde` runs the `_ifma_` tests on Ice Lake, which lacks
    // AVX512_FP16, and the others on Sapphire Rapids, which has it.

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_crt_ifma_2048() {
        trace_crt(16, false);
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_crt_ifma_4096() {
        trace_crt(32, false);
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_crt_ifma512_2048() {
        trace_crt(16, true);
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_crt_ifma512_3072() {
        trace_crt(24, true);
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_crt_ifma512_4096() {
        trace_crt(32, true);
    }

    /// The CRT of a key of odd `w`-word `p` and `q` with their top bits set,
    /// and `dp`, `dq`, `qinv`, and `x` below `p`, `q`, `p`, and `n`, all
    /// from the seed. The exponentiations need no primes to take their
    /// path.
    fn trace_crt(w: usize, fp16: bool) {
        let mut rng = Rng(ct_sde::seed());
        let bits = 64 * w as u32;
        let mut prime = || {
            let mut p: [u64; MAX_PRIME_WORDS] = rng.words(bits);
            p[0] |= 1;
            p[w - 1] |= 1 << 63;
            p
        };
        let (p, q) = (prime(), prime());
        let pi = low::PosInt::<MAX_PRIME_WORDS>::from_words(&p[..w]).unwrap();
        let qi = low::PosInt::<MAX_PRIME_WORDS>::from_words(&q[..w]).unwrap();
        let n: low::PosInt<{ 2 * MAX_PRIME_WORDS }> = low::PosInt::mul(&pi, &qi);
        let ifma = IfmaCrt::new(n.as_words(), &p[..w], &q[..w]);
        assert!(ifma.runs(), "AVX-512 IFMA");
        let token = HaveAvx512ForRsa::check().unwrap();
        assert_eq!(token.fp16(), fp16, "the SDE model takes the other routine");
        let mut below_top = |bits| {
            let mut v: [u64; 2 * MAX_PRIME_WORDS] = rng.words(bits);
            // Two top bits clear, so `x < 2^(2 bits - 2) <= n`, as VG's CRT
            // refuses a larger one, and each CRT value is below its prime.
            v[bits as usize / 64 - 1] >>= 2;
            v
        };
        let (dp, dq, qinv, x) = (
            below_top(bits),
            below_top(bits),
            below_top(bits),
            below_top(2 * bits),
        );
        let (dp, dq, qinv) = (be(&dp, 8 * w), be(&dq, 8 * w), be(&qinv, 8 * w));
        let x = be(&x, 16 * w);
        let mut out = vec![0; 16 * w];
        assert!(ct_sde::traced(|| ifma.crt(&mut out, &x, &dp, &dq, &qinv)));
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_public_ifma_2048() {
        trace_public(32);
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_public_ifma_3072() {
        trace_public(48);
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_public_ifma_4096() {
        trace_public(64);
    }

    /// The public operation with `e = 65537` on an `x` from the seed, below a
    /// `k`-word `n` the same for every seed: it is constant time only in `x`.
    fn trace_public(k: usize) {
        let mut n: [u64; MAX_WORDS] = Rng(1).words(64 * k as u32);
        n[0] |= 1;
        n[k - 1] |= 1 << 63;
        let ni = low::PosInt::<MAX_WORDS>::from_words(&n[..k]).unwrap();
        let mut pre = n[..k].to_vec();
        pre.extend_from_slice(ni.pub_montifier().as_words());
        let mut x: [u64; MAX_WORDS] = Rng(ct_sde::seed()).words(64 * k as u32);
        x[k - 1] >>= 1;
        let x = be(&x, 8 * k);
        let mut out = vec![0; 8 * k];
        let ifma = RsaIfma::check(&ni, 65537).expect("AVX-512 IFMA");
        let e = [1, 0, 1];
        assert!(ct_sde::traced(|| ifma.public(&mut out, &pre, &e, &x)));
    }
}
