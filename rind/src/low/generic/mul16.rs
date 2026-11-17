// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The 64-bit product of two 32-bit values from four 16-bit halves, for the
//! cores `rind_mul16` names (see build.rs). Only Poly1305's limb products
//! call it. X25519, the NIST curves, and RSA on those cores still use a
//! multiply whose time depends on its operands, or a library routine that
//! does.
//!
//! A Cortex-M3's `umull` and `smull` take 3 to 5 cycles and its `umlal` and
//! `smlal` 4 to 7, ending early "depending on the size of the source
//! values", while its 32x32->32-bit `mul` takes one cycle and `mla` two,
//! whatever their operands (Arm DDI 0337, "Cortex-M3 instructions"). BearSSL
//! measured the M3's `umull` finishing early when an operand fits in 16 bits,
//! is zero, or is a power of two ([BearSSL ctmul]). ARMv6-M's and ARMv8-M
//! Baseline's cores (Cortex-M0, M0+, M1, and M23) have no 32x32->64-bit
//! multiply, so the compiler would call compiler-builtins' `__aeabi_lmul`,
//! whose timing nothing documents; their `muls` takes the same time for every
//! operand. On those cores each half is one 32-bit `mul`.
//!
//! ARMv4T's ARM7TDMI and ARM9TDMI end a `mul` early by the top bytes of the
//! multiplier, so a 16-bit half under 2^8 takes fewer iterations than a
//! larger half ([BearSSL ctmul]). XScale, which shares the ARMv5TE triples
//! with the ARM926EJ-S, ends `mul` and `umull` early when `Rs[31:15]` or
//! `Rs[31:27]` is all zeros or all ones ([XScale] Table 10-6): a 16-bit half
//! under 2^15 takes the short path and a larger half does not. Setting bit 31
//! of both halves misses every one of those rows, so the long path is taken
//! whatever the secret is and whichever operand the compiler picks as `Rs`.
//! The low 32 bits of that product are the 16-bit product plus bit 31 when
//! the sum of the halves is odd.
//!
//! RISC-V without the M extension has no multiply instruction. The compiler
//! lowers `wrapping_mul` to `__mulsi3`, whose iterations follow the bits of
//! an operand. Each half is then sixteen masked shifts and adds. The mask and
//! the running sum both pass through an empty `asm!` block: the mask so the
//! and is not a select on the secret bit, which RV32I can lower to a branch,
//! and the sum so the compiler cannot turn the shifts back into that call.
//!
//! The same empty block hides every half that does use `mul`, so the compiler
//! cannot see that the four products make one and fuse them back into a
//! `umull`. `admin/ct-vartime` checks that Poly1305's `blocks` and `finish`,
//! built on this, hold no 32x32->64-bit multiply and call no multiply routine.
//! On ARMv5TE every `mul` and `mla` operand must be an `orr` of `#0x80000000`,
//! and on RV32I a conditional branch there must not test a secret bit.
//!
//! [BearSSL ctmul]: https://www.bearssl.org/ctmul.html
//! [XScale]: https://download.intel.com/design/intelxscale/27347302.pdf

use super::hide::hide;

/// `a * b` from four 16-bit halves. Every step is a multiply, add, shift, or
/// mask, and the wrapping adds never wrap, since the sum is the product,
/// which is under 2^64; they only keep a debug build's overflow checks from
/// branching on a secret.
#[inline(always)]
pub(crate) fn mul16(a: u32, b: u32) -> u64 {
    let (a0, a1) = (a & 0xffff, a >> 16);
    let (b0, b1) = (b & 0xffff, b >> 16);
    // Each product of two halves is under 2^32, and the middle sum under
    // 2^33.
    let low = u64::from(mul_half(a0, b0));
    let middle = u64::from(mul_half(a0, b1)).wrapping_add(u64::from(mul_half(a1, b0)));
    let high = u64::from(mul_half(a1, b1));
    low.wrapping_add(middle << 16).wrapping_add(high << 32)
}

#[inline(always)]
fn mul_half(a: u32, b: u32) -> u32 {
    #[cfg(rind_mul16_soft)]
    {
        mul_half_soft(a, b)
    }
    #[cfg(all(rind_mul16_top, not(rind_mul16_soft)))]
    {
        mul_half_top(a, b)
    }
    #[cfg(not(any(rind_mul16_soft, rind_mul16_top)))]
    {
        mul_half_plain(a, b)
    }
}

/// One 32-bit `mul` of a 16-bit half. Constant time where that instruction is.
#[cfg(any(test, not(any(rind_mul16_soft, rind_mul16_top))))]
#[inline(always)]
fn mul_half_plain(a: u32, b: u32) -> u32 {
    hide(a).wrapping_mul(hide(b))
}

/// A 16-bit product whose multiplier always takes the long early-out path.
#[cfg(any(test, all(rind_mul16_top, not(rind_mul16_soft))))]
#[inline(always)]
fn mul_half_top(a: u32, b: u32) -> u32 {
    // `hide` hides the range. Without it, LLVM simplifies this back to
    // `a * b` and the early-out sees the secret half again.
    let a = hide(a & 0xffff);
    let b = hide(b & 0xffff);
    let prod = (a | 0x8000_0000).wrapping_mul(b | 0x8000_0000);
    let cross = (a.wrapping_add(b) & 1) << 31;
    prod.wrapping_sub(cross)
}

/// A 16-bit product from shifts and adds. No multiply instruction. Inlined,
/// so a block does not pay a hundred calls. `hide` on the mask hides that
/// it is 0 or all-ones: without that, `a & mask` is a select on the secret
/// bit, and RV32I can lower the select to a branch. `opaque` on the sum
/// keeps the compiler from turning the recurrence into `__mulsi3`. It may
/// still unroll the shifts.
#[cfg(any(test, rind_mul16_soft))]
#[inline(always)]
fn mul_half_soft(a: u32, mut b: u32) -> u32 {
    let mut a = a & 0xffff;
    b &= 0xffff;
    let mut acc = 0u32;
    for _ in 0..16 {
        let mask = hide(0u32.wrapping_sub(b & 1));
        acc = hide(acc.wrapping_add(a & mask));
        a <<= 1;
        b >>= 1;
    }
    acc
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn from_halves(half: fn(u32, u32) -> u32, a: u32, b: u32) -> u64 {
        let (a0, a1) = (a & 0xffff, a >> 16);
        let (b0, b1) = (b & 0xffff, b >> 16);
        let low = u64::from(half(a0, b0));
        let middle = u64::from(half(a0, b1)).wrapping_add(u64::from(half(a1, b0)));
        let high = u64::from(half(a1, b1));
        low.wrapping_add(middle << 16).wrapping_add(high << 32)
    }

    // Each pair of edge values, where a half is zero, one, all ones, or a
    // power of two, then pairs from SplitMix64, against the 64-bit multiply.
    // The plain, top-bit, and shift-and-add halves are all checked here, not
    // only the one this target selects.
    #[test]
    fn matches_the_wide_product() {
        let edges = [
            0,
            1,
            2,
            0xffff,
            0x1_0000,
            0x1_0001,
            0x3ff_ffff,
            0x4_0000,
            5 << 26,
            0x7fff_ffff,
            0x8000_0000,
            0xffff_0000,
            0xffff_fffe,
            u32::MAX,
        ];
        type HalfFn = fn(u32, u32) -> u32;
        let halves: [(&str, HalfFn); 3] = [
            ("plain", mul_half_plain),
            ("top", mul_half_top),
            ("soft", mul_half_soft),
        ];
        for a in edges {
            for b in edges {
                assert_eq!(mul16(a, b), u64::from(a) * u64::from(b), "{a:#x} * {b:#x}");
                for (name, half) in halves {
                    assert_eq!(
                        from_halves(half, a, b),
                        u64::from(a) * u64::from(b),
                        "{name} {a:#x} * {b:#x}"
                    );
                }
            }
        }
        let mut state = 0x6d75_6c31_365f_7465u64;
        for _ in 0..100_000 {
            let z = super::super::splitmix::next(&mut state);
            let (a, b) = (z as u32, (z >> 32) as u32);
            assert_eq!(mul16(a, b), u64::from(a) * u64::from(b), "{a:#x} * {b:#x}");
            for (name, half) in halves {
                assert_eq!(
                    from_halves(half, a, b),
                    u64::from(a) * u64::from(b),
                    "{name} {a:#x} * {b:#x}"
                );
            }
        }
    }
}
