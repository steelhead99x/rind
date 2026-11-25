// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RSA's `R² mod n` for a public modulus by pyca/verified-garbage's
//! `vg_rsa_public_precompute_adx`, which `admin/import-vg` imports.
//!
//! VG's routine takes `w` steps of long division by `n`, each a pass of
//! `mulx`, `adcx`, and `adox`, for a modulus of `w` words whose top bit is
//! set and `w` a multiple of four: every 1024-, 2048-, 3072-, 4096-, 6144-,
//! and 8192-bit modulus. There it measured 2.5 to 3.2 times as fast as
//! `PosInt::pub_montifier` on Zen 5. Other moduli take VG's doublings and
//! squarings, 6.7 times as slow at 2056 bits, and its routine without ADX
//! was slower at every size, so both keep rind's.
//!
//! VG proves it correct in Lean, over its own model of the instructions,
//! which `admin/prove vg` cosimulates, against its `Spec`'s
//! `publicPrecomputeContract`.

use core::mem::MaybeUninit;

use super::cpu::HaveBmi2Adx;
use super::vg;

/// The widest modulus, in 64-bit words.
const MAX_WORDS: usize = 128;

/// Proof that VG's routine takes its word steps for a modulus on this CPU.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Precompute(HaveBmi2Adx);

impl Precompute {
    /// For the modulus of little-endian words `n`, where it has a multiple
    /// of four words and its top bit is set.
    pub(crate) fn check(n: &[u64]) -> Option<Self> {
        let w = n.len();
        if w == 0 || !w.is_multiple_of(4) || n[w - 1] >> 63 == 0 {
            return None;
        }
        // Not `map(Self)`, whose translation Lean cannot check.
        let token = HaveBmi2Adx::check()?;
        Some(Self(token))
    }

    /// Writes `n` and then `R² mod n`, `R = 2^(64w)`, in
    /// `w = ⌈n.len() / 8⌉` little-endian words each, to `pre`, for
    /// big-endian `n`.
    ///
    /// Returns whether it did: it refuses, writing zeros, an `n` that is
    /// even, outside 512 to 8192 bits, or with a leading zero byte, or a
    /// `pre` that is not `2w` words.
    pub(crate) fn precompute(self, pre: &mut [u64], n: &[u8]) -> bool {
        let k = n.len();
        let w = k.div_ceil(8);
        if !(64..=MAX_WORDS * 8).contains(&k) || pre.len() != 2 * w {
            pre.fill(0);
            return false;
        }
        // The routine accepts any initial contents. It leaves `n`'s values
        // and the caller's saved registers there, stack temporaries, which
        // AGENTS.md leaves unwiped.
        let mut scratch = MaybeUninit::<[u64; 8 * MAX_WORDS + 48]>::uninit();
        // SAFETY: `pre` is `2w` writable words, `n` `k` readable bytes, and
        // `scratch` `8w + 48` writable words, with `64 <= k <= 1024`. They
        // are distinct objects, so none overlaps another, the return
        // address, or the stack below it, or wraps the address space. The
        // token proves the CPU has BMI2 and ADX.
        let r = unsafe {
            asm_call!(unsafe extern "sysv64" (vg::vg_rsa_public_precompute_adx::vg_rsa_public_precompute_adx)(
                pre.as_mut_ptr(),
                pre.len(),
                n.as_ptr(),
                k,
                scratch.as_mut_ptr().cast::<u64>(),
                8 * w + 48,
            ))
        };
        r == 1
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low;

    #[test]
    fn check_takes_word_step_moduli() {
        let top = 1 << 63;
        let Some(_) = HaveBmi2Adx::check() else {
            assert!(Precompute::check(&[1, 0, 0, top]).is_none());
            return;
        };
        assert!(Precompute::check(&[1, 0, 0, top]).is_some());
        assert!(
            Precompute::check(&[1, 0, 0, top - 1]).is_none(),
            "top bit clear"
        );
        assert!(
            Precompute::check(&[1, 0, 0, 0, 0, top]).is_none(),
            "six words"
        );
        assert!(Precompute::check(&[]).is_none());
    }

    // Against `pub_montifier` at every width `check` takes, from a moduli
    // of random words, and refusing what the routine refuses.
    #[test]
    fn matches_pub_montifier() {
        let Some(token) = HaveBmi2Adx::check() else {
            return;
        };
        let vg = Precompute(token);
        let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for w in (8..=MAX_WORDS).step_by(4) {
            let mut words = [0u64; MAX_WORDS];
            for word in &mut words[..w] {
                *word = next();
            }
            words[0] |= 1;
            words[w - 1] |= 1 << 63;
            let n = low::PosInt::<MAX_WORDS>::from_words(&words[..w]).unwrap();
            let mut bytes = [0u8; 8 * MAX_WORDS];
            n.to_bytes_fixed(&mut bytes[..8 * w]);
            let mut pre = [0u64; 2 * MAX_WORDS];
            assert!(
                vg.precompute(&mut pre[..2 * w], &bytes[..8 * w]),
                "{w} words"
            );
            assert_eq!(&pre[..w], n.as_words(), "{w} words");
            assert_eq!(&pre[w..2 * w], n.pub_montifier().as_words(), "{w} words");

            // An even modulus is refused, with zeros written.
            bytes[8 * w - 1] &= !1;
            assert!(!vg.precompute(&mut pre[..2 * w], &bytes[..8 * w]));
            assert_eq!(pre[..2 * w], [0; 2 * MAX_WORDS][..2 * w]);
        }
        // So are a modulus under 512 bits and a `pre` of the wrong length.
        let mut pre = [1u64; 2 * MAX_WORDS];
        assert!(!vg.precompute(&mut pre[..8], &[0xff; 32]));
        assert_eq!(pre[..8], [0; 8]);
        assert!(!vg.precompute(&mut pre[..63], &[0xff; 256]));
        assert_eq!(pre[..63], [0; 63]);
    }
}
