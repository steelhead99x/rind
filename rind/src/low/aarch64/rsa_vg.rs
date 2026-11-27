// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RSA's `R² mod n` for a public modulus by pyca/verified-garbage's
//! `vg_rsa_public_precompute`, which `admin/import-vg` imports.
//!
//! VG's routine takes `w` steps of long division by `n`, each a pass over
//! its words, for a modulus of `w >= 3` words, as `PosInt::pub_montifier`
//! does in Rust.
//!
//! VG proves it correct in Lean, over its own model of the instructions,
//! which `admin/prove vg` cosimulates, against its `Spec`'s
//! `publicPrecomputeContract`.

use core::mem::MaybeUninit;

use super::vg;

/// The widest modulus, in 64-bit words.
const MAX_WORDS: usize = 128;

/// Proof that VG's routine runs for a modulus, as it does for every one on
/// every aarch64 CPU.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Precompute(());

impl Precompute {
    /// For the modulus of little-endian words `n`.
    pub(crate) fn check(_n: &[u64]) -> Option<Self> {
        Some(Self(()))
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
        // and the pointers and lengths it was passed, which are public.
        let mut scratch = MaybeUninit::<[u64; 8 * MAX_WORDS + 48]>::uninit();
        // SAFETY: `pre` is `2w` writable words, `n` `k` readable bytes, and
        // `scratch` `8w + 48` writable words, with `64 <= k <= 1024`. They
        // are distinct objects, so none overlaps another or wraps the
        // address space.
        let r = unsafe {
            asm_call!(unsafe extern "C" (vg::vg_rsa_public_precompute::vg_rsa_public_precompute)(
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

    // Against `pub_montifier` at every width from 576 to 8192 bits, of
    // random words with the top bit set and clear, and refusing what the
    // routine refuses.
    #[test]
    fn matches_pub_montifier() {
        let vg = Precompute::check(&[]).unwrap();
        let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for w in 9..=MAX_WORDS {
            for top in [1 << 63, 1 << 7] {
                let mut words = [0u64; MAX_WORDS];
                for word in &mut words[..w] {
                    *word = next();
                }
                words[0] |= 1;
                words[w - 1] = (words[w - 1] % top) | top;
                let n = low::PosInt::<MAX_WORDS>::from_words(&words[..w]).unwrap();
                let k = n.len_bytes();
                let mut bytes = [0u8; 8 * MAX_WORDS];
                n.to_bytes_fixed(&mut bytes[..k]);
                let mut pre = [0u64; 2 * MAX_WORDS];
                assert!(vg.precompute(&mut pre[..2 * w], &bytes[..k]), "{w} words");
                assert_eq!(&pre[..w], n.as_words(), "{w} words");
                assert_eq!(&pre[w..2 * w], n.pub_montifier().as_words(), "{w} words");

                // An even modulus is refused, with zeros written.
                bytes[k - 1] &= !1;
                assert!(!vg.precompute(&mut pre[..2 * w], &bytes[..k]));
                assert_eq!(pre[..2 * w], [0; 2 * MAX_WORDS][..2 * w]);
            }
        }
        // So are a modulus under 512 bits and a `pre` of the wrong length.
        let mut pre = [1u64; 2 * MAX_WORDS];
        assert!(!vg.precompute(&mut pre[..8], &[0xff; 32]));
        assert_eq!(pre[..8], [0; 8]);
        assert!(!vg.precompute(&mut pre[..63], &[0xff; 256]));
        assert_eq!(pre[..63], [0; 63]);
    }
}
