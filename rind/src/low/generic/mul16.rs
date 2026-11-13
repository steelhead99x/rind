// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The 64-bit product of two 32-bit values from four 16x16->32-bit
//! multiplies, for the cores `rind_mul16` names (see build.rs), whose
//! 32x32->64-bit multiply takes a time that depends on its operands, or that
//! have none.
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
//! operand.
//!
//! Each 16-bit half passes through an empty `asm!` block, so the compiler
//! cannot see that the four products make one and fuse them back into a
//! `umull`. `admin/ct-vartime` checks that Poly1305's block function, built
//! on this, holds no 32x32->64-bit multiply and calls no multiply routine.
//!
//! [BearSSL ctmul]: https://www.bearssl.org/ctmul.html

/// `a * b`, from 32x32->32-bit multiplies of 16-bit halves. Every operation
/// is a multiply, add, shift, or mask, and the wrapping adds never wrap,
/// since the sum is the product, which is under 2^64; they only keep a debug
/// build's overflow checks from branching on a secret.
#[inline(always)]
pub(crate) fn mul16(a: u32, b: u32) -> u64 {
    let (a0, a1) = (opaque(a & 0xffff), opaque(a >> 16));
    let (b0, b1) = (opaque(b & 0xffff), opaque(b >> 16));
    // Each product of two halves is under 2^32, and the middle sum under
    // 2^33.
    let low = u64::from(a0.wrapping_mul(b0));
    let middle = u64::from(a0.wrapping_mul(b1)).wrapping_add(u64::from(a1.wrapping_mul(b0)));
    let high = u64::from(a1.wrapping_mul(b1));
    low.wrapping_add(middle << 16).wrapping_add(high << 32)
}

/// `v`, which the compiler cannot see through, as `generic::md5` hides its
/// values, without a trip through memory.
#[inline(always)]
#[cfg(all(rind_reg_asm, not(miri)))]
// The operand appears only in a comment, so no register width is printed.
#[allow(asm_sub_register)]
fn opaque(mut v: u32) -> u32 {
    // SAFETY: the assembly is empty, so it reads, writes, and clobbers
    // nothing but returns `v` in the register it took it in.
    unsafe {
        core::arch::asm!("/* {0} */", inout(reg) v, options(pure, nomem, nostack, preserves_flags));
    }
    v
}

// build.rs sets `rind_reg_asm` only where a `reg` operand is stable.
// Elsewhere, and under Miri, `black_box` keeps the halves opaque. None of
// those targets builds with `rind_mul16` except tests, which only check
// the arithmetic.
#[inline(always)]
#[cfg(not(all(rind_reg_asm, not(miri))))]
fn opaque(v: u32) -> u32 {
    core::hint::black_box(v)
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // Each pair of edge values, where a half is zero, one, all ones, or a
    // power of two, then pairs from SplitMix64, against the 64-bit multiply.
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
        for a in edges {
            for b in edges {
                assert_eq!(mul16(a, b), u64::from(a) * u64::from(b), "{a:#x} * {b:#x}");
            }
        }
        let mut state = 0x6d75_6c31_365f_7465u64;
        for _ in 0..100_000 {
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^= z >> 31;
            let (a, b) = (z as u32, (z >> 32) as u32);
            assert_eq!(mul16(a, b), u64::from(a) * u64::from(b), "{a:#x} * {b:#x}");
        }
    }
}
