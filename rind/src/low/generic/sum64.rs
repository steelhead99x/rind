// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Sums of `u64` words mod 2^64 with no branch on a carry, for SHA-512 on
//! 32-bit microcontrollers.
//!
//! LLVM's Xtensa backend adds two `u64`s as two `add`s and a conditional
//! `bltu` on the low word's carry, since the core has no carry flag and no
//! set-on-less-than instruction. SHA-512's sums are of message, key, and state words,
//! so that branch makes the compression's time depend on them, and with it
//! HMAC-SHA-384/512, HKDF, PBKDF2, and Ed25519's hashing. Poly1305 met the
//! same lowering and sums in `u32` halves there (`poly1305_32`,
//! `add_s_split`); this is the same idea for many-operand `u64` sums.
//!
//! [`Split`] keeps three `u32` lanes: bits 0..16, bits 16..32, and bits
//! 32..64 of each operand, each summed on its own. A lane holds at most
//! `N` times `0xffff` (or the high lane wraps mod 2^32, which is what the
//! result's top word wants), so for the at most seven operands SHA-512
//! adds into one result no lane overflows. [`Split::value`] folds the low
//! lane's carry into the middle one and the middle one's into the high
//! one, with shifts and masks: a carry is the top bits of a `u32`, not a
//! comparison. Sharing a partial sum, as T1 is shared between `e` and
//! `a`, costs no fold.
//!
//! Xtensa takes [`Split`] and every other target the plain [`Wide`] sum,
//! which has no carry branch on any target rind's other backends run.
//! Tests take [`Split`] on every host, so the rolled and unrolled SHA-512
//! bodies' known-answer, cross-body, and ctgrind tests run it, and check it
//! against [`Wide`] here. The board check that no `bltu` on a carry is left
//! is the disassembly count in `quest/m2/speed/xtensa-carry-branches.md`.

/// The sum SHA-512 runs on this target: [`Split`] on Xtensa and in tests,
/// [`Wide`] elsewhere.
#[cfg(any(target_arch = "xtensa", test))]
pub(crate) type Sum64 = Split;
/// The sum SHA-512 runs on this target: [`Split`] on Xtensa and in tests,
/// [`Wide`] elsewhere.
#[cfg(not(any(target_arch = "xtensa", test)))]
pub(crate) type Sum64 = Wide;

/// A sum of `u64`s in three `u32` lanes, unfolded.
#[cfg(any(target_arch = "xtensa", test))]
#[derive(Clone, Copy)]
pub(crate) struct Split {
    /// Bits 0..16 of each operand, summed.
    lo: u32,
    /// Bits 16..32 of each operand, summed.
    mid: u32,
    /// Bits 32..64 of each operand, summed mod 2^32.
    hi: u32,
}

#[cfg(any(target_arch = "xtensa", test))]
impl Split {
    /// The sum of `x` alone.
    #[inline(always)]
    pub(crate) fn of(x: u64) -> Self {
        Self {
            lo: x as u32 & 0xffff,
            mid: x as u32 >> 16,
            hi: (x >> 32) as u32,
        }
    }

    /// This sum plus `x`. One operand at a time, with no array or loop, so
    /// the unrolled IRAM body has no iterator or copy that could outline
    /// into flash. The lanes take `wrapping_add`, so a debug build's
    /// overflow check adds no branch on them either.
    #[inline(always)]
    #[must_use]
    pub(crate) fn add(self, x: u64) -> Self {
        Self {
            lo: self.lo.wrapping_add(x as u32 & 0xffff),
            mid: self.mid.wrapping_add(x as u32 >> 16),
            hi: self.hi.wrapping_add((x >> 32) as u32),
        }
    }

    /// The sum mod 2^64. Exact while the low and middle lanes stay under
    /// 2^32, which fewer than 65,537 operands guarantee.
    #[inline(always)]
    pub(crate) fn value(self) -> u64 {
        let mid = self.mid.wrapping_add(self.lo >> 16);
        let low = (self.lo & 0xffff) | (mid << 16);
        let high = self.hi.wrapping_add(mid >> 16);
        (u64::from(high) << 32) | u64::from(low)
    }
}

/// A sum of `u64`s with `wrapping_add`.
#[cfg(any(not(target_arch = "xtensa"), test))]
#[derive(Clone, Copy)]
pub(crate) struct Wide(u64);

#[cfg(any(not(target_arch = "xtensa"), test))]
impl Wide {
    /// The sum of `x` alone.
    #[inline(always)]
    pub(crate) fn of(x: u64) -> Self {
        Self(x)
    }

    /// This sum plus `x`.
    #[inline(always)]
    #[must_use]
    pub(crate) fn add(self, x: u64) -> Self {
        Self(self.0.wrapping_add(x))
    }

    /// The sum mod 2^64.
    #[inline(always)]
    pub(crate) fn value(self) -> u64 {
        self.0
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn both<const N: usize>(xs: [u64; N]) {
        let wide = xs[1..].iter().fold(xs[0], |s, &x| s.wrapping_add(x));
        let split = xs[1..].iter().fold(Split::of(xs[0]), |s, &x| s.add(x));
        let plain = xs[1..].iter().fold(Wide::of(xs[0]), |s, &x| s.add(x));
        assert_eq!(split.value(), wide, "{xs:x?}");
        assert_eq!(plain.value(), wide, "{xs:x?}");
    }

    /// Edge values: a carry out of each lane, and out of the whole word.
    #[test]
    fn split_matches_wide_at_the_edges() {
        let edges = [
            0,
            1,
            0xffff,
            0x1_0000,
            0xffff_ffff,
            0x1_0000_0000,
            0x0000_0000_ffff_ffff,
            0x0000_ffff_ffff_ffff,
            0x7fff_ffff_ffff_ffff,
            0x8000_0000_0000_0000,
            0xffff_ffff_0000_0000,
            0xffff_ffff_ffff_fffe,
            u64::MAX,
        ];
        for &a in &edges {
            for &b in &edges {
                both([a, b]);
                for &c in &edges {
                    both([a, b, c]);
                }
            }
        }
        for &a in &edges {
            both([a]);
        }
        both([u64::MAX; 7]);
        both([0xffff_ffff; 7]);
        both([0x0000_ffff_0000_ffff; 7]);
    }

    /// Random operands, two to seven at a time, and a partial sum shared as
    /// SHA-512's T1 is.
    #[test]
    fn split_matches_wide_on_random_words() {
        let mut x = 0x0123_4567_89ab_cdefu64;
        let mut next = || {
            // xorshift64*: a fixed sequence, not a secret.
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            x.wrapping_mul(0x2545_f491_4f6c_dd1d)
        };
        for _ in 0..20_000 {
            let w = [next(), next(), next(), next(), next(), next(), next()];
            both([w[0], w[1]]);
            both([w[0], w[1], w[2], w[3]]);
            both([w[0], w[1], w[2], w[3], w[4]]);
            both(w);
            let t1 = Split::of(w[0]).add(w[1]).add(w[2]).add(w[3]).add(w[4]);
            let wide_t1 = Wide::of(w[0]).add(w[1]).add(w[2]).add(w[3]).add(w[4]);
            assert_eq!(t1.add(w[5]).value(), wide_t1.add(w[5]).value());
            assert_eq!(
                t1.add(w[5]).add(w[6]).value(),
                wide_t1.add(w[5]).add(w[6]).value()
            );
        }
    }
}
