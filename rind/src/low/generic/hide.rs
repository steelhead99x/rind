// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! An optimisation barrier for 32-bit values. Its own module, apart from the
//! arithmetic it guards, keeps that arithmetic's debug assertions out of a
//! file with `unsafe` (`low::tests::no_debug_assert_beside_unsafe`).

/// `v`, which the compiler cannot see through, as `generic::md5` hides its
/// values, without a trip through memory. `finish`'s mask and every mul16
/// half pass through it, so the compiler cannot turn a select on a secret
/// into a branch, nor fuse the halves back into one long multiply.
#[inline(always)]
#[cfg(all(rind_reg_asm, not(miri)))]
// The operand appears only in a comment, so no register width is printed.
#[allow(asm_sub_register)]
pub(crate) fn hide(mut v: u32) -> u32 {
    // SAFETY: the assembly is empty, so it reads, writes, and clobbers
    // nothing but returns `v` in the register it took it in.
    unsafe {
        core::arch::asm!("/* {0} */", inout(reg) v, options(pure, nomem, nostack, preserves_flags));
    }
    v
}

// build.rs sets `rind_reg_asm` only where a `reg` operand is stable.
// Elsewhere, such as WebAssembly, Xtensa, or MIPS, and under Miri,
// `black_box` hides the value through memory: once per tag in `finish`, and
// on no core that builds with `rind_mul16`.
#[inline(always)]
#[cfg(not(all(rind_reg_asm, not(miri))))]
pub(crate) fn hide(v: u32) -> u32 {
    core::hint::black_box(v)
}
