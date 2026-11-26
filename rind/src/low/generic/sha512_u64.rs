// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! `u64` addition for SHA-512 on Xtensa.
//!
//! LLVM's Xtensa backend lowers `u64::wrapping_add` to an `add` of the low
//! halves plus a conditional branch on the carry (`bltu` / `bgeu`). The
//! carry is a function of the chaining value and the block, so HMAC-SHA-512,
//! HKDF, and Ed25519's hash would take a secret-dependent branch on every
//! round. Two wrapping `u32` adds do not: each is one `add`, and the carry
//! into the high half is bits of the operands and the low sum.

/// `a + b` mod 2^64, with no branch on `a` or `b`.
///
/// The carry out of the low half is
/// `((a & b) | ((a | b) & !sum)) >> 31`, which is 0 or 1.
#[inline(always)]
pub(super) fn split(a: u64, b: u64) -> u64 {
    let a0 = a as u32;
    let b0 = b as u32;
    let a1 = (a >> 32) as u32;
    let b1 = (b >> 32) as u32;
    let lo = a0.wrapping_add(b0);
    let carry = ((a0 & b0) | ((a0 | b0) & !lo)) >> 31;
    let hi = a1.wrapping_add(b1).wrapping_add(carry);
    ((hi as u64) << 32) | (lo as u64)
}

/// The add the SHA-512 bodies use: [`split`] on Xtensa, `wrapping_add`
/// everywhere else. `SPLIT` lets a host test run both.
#[inline(always)]
pub(super) fn add<const SPLIT: bool>(a: u64, b: u64) -> u64 {
    if SPLIT {
        split(a, b)
    } else {
        a.wrapping_add(b)
    }
}

#[cfg(test)]
mod tests {
    use super::split;

    #[test]
    fn split_matches_wrapping_add() {
        let lows = [0u64, 1, 0x7fff_ffff, 0x8000_0000, 0xffff_fffe, 0xffff_ffff];
        let highs = [0u64, 1, 0x7fff_ffff, 0x8000_0000, 0xffff_fffe, 0xffff_ffff];
        for &low_a in &lows {
            for &high_a in &highs {
                for &low_b in &lows {
                    for &high_b in &highs {
                        let a = (high_a << 32) | low_a;
                        let b = (high_b << 32) | low_b;
                        assert_eq!(split(a, b), a.wrapping_add(b), "{a:#x} + {b:#x}");
                    }
                }
            }
        }
        // A short deterministic walk, including sums of three adds.
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        for _ in 0..256 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let y = x.rotate_left(17) ^ 0x1234_5678_9abc_def0;
            let z = x.wrapping_mul(0x6c62_272e_07bb_0142);
            let once = split(x, y);
            assert_eq!(once, x.wrapping_add(y));
            assert_eq!(split(once, z), x.wrapping_add(y).wrapping_add(z));
        }
    }
}
