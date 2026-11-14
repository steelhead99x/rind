// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square, z := x^2
// Input x[16]; output z[32]; temporary buffer t[>=24]
//
//    extern void bignum_ksqr_16_32(uint64_t z[static 32],
//                                  const uint64_t x[static 16],
//                                  uint64_t t[static 24]);
//
// This is a Karatsuba-style function squaring half-sized results
// and using temporary buffer t for intermediate results.
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = t
// ----------------------------------------------------------------------------

// Subroutine-safe copies of the output, inputs and temporary buffer pointers

macro_rules! z {
    () => {
        "x23"
    };
}
macro_rules! x {
    () => {
        "x24"
    };
}
macro_rules! t {
    () => {
        "x25"
    };
}

// More variables for sign masks, with s also necessarily subroutine-safe

macro_rules! s {
    () => {
        "x19"
    };
}

// Transliterated from s2n-bignum's arm/fastmul/bignum_ksqr_16_32.S.
/// Square, z := x^2
///
/// Input x[16]; output z[32]; temporary buffer t[>=24]
///
/// This is a Karatsuba-style function squaring half-sized results
/// and using temporary buffer t for intermediate results.
#[inline(never)]
pub(crate) fn bignum_ksqr_16_32(z: &mut [u64], x: &[u64], t: &mut [u64; 24]) {
    assert!(z.len() == 32);
    assert!(x.len() == 16);
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Save registers, including return address

        Q!("    stp             " "x19, x20, [sp, #-16] !"),
        Q!("    stp             " "x21, x22, [sp, #-16] !"),
        Q!("    stp             " "x23, x24, [sp, #-16] !"),
        Q!("    stp             " "x25, x30, [sp, #-16] !"),

        // Move parameters into subroutine-safe places

        Q!("    mov             " z!() ", x0"),
        Q!("    mov             " x!() ", x1"),
        Q!("    mov             " t!() ", x2"),

        // Compute L = x_lo * y_lo in bottom half of buffer (size 8 x 8 -> 16)

        Q!("    bl              " Label!("Lbignum_ksqr_16_32_local_sqr_8_16", 2, After)),

        // Compute absolute difference [t..] = |x_lo - x_hi|

        Q!("    ldp             " "x10, x11, [" x!() "]"),
        Q!("    ldp             " "x8, x9, [" x!() ", #64]"),
        Q!("    subs            " "x10, x10, x8"),
        Q!("    sbcs            " "x11, x11, x9"),
        Q!("    ldp             " "x12, x13, [" x!() ", #16]"),
        Q!("    ldp             " "x8, x9, [" x!() ", #80]"),
        Q!("    sbcs            " "x12, x12, x8"),
        Q!("    sbcs            " "x13, x13, x9"),
        Q!("    ldp             " "x14, x15, [" x!() ", #32]"),
        Q!("    ldp             " "x8, x9, [" x!() ", #96]"),
        Q!("    sbcs            " "x14, x14, x8"),
        Q!("    sbcs            " "x15, x15, x9"),
        Q!("    ldp             " "x16, x17, [" x!() ", #48]"),
        Q!("    ldp             " "x8, x9, [" x!() ", #112]"),
        Q!("    sbcs            " "x16, x16, x8"),
        Q!("    sbcs            " "x17, x17, x9"),
        Q!("    csetm           " s!() ", cc"),
        Q!("    adds            " "xzr, " s!() ", " s!()),
        Q!("    eor             " "x10, x10, " s!()),
        Q!("    adcs            " "x10, x10, xzr"),
        Q!("    eor             " "x11, x11, " s!()),
        Q!("    adcs            " "x11, x11, xzr"),
        Q!("    stp             " "x10, x11, [" t!() "]"),
        Q!("    eor             " "x12, x12, " s!()),
        Q!("    adcs            " "x12, x12, xzr"),
        Q!("    eor             " "x13, x13, " s!()),
        Q!("    adcs            " "x13, x13, xzr"),
        Q!("    stp             " "x12, x13, [" t!() ", #16]"),
        Q!("    eor             " "x14, x14, " s!()),
        Q!("    adcs            " "x14, x14, xzr"),
        Q!("    eor             " "x15, x15, " s!()),
        Q!("    adcs            " "x15, x15, xzr"),
        Q!("    stp             " "x14, x15, [" t!() ", #32]"),
        Q!("    eor             " "x16, x16, " s!()),
        Q!("    adcs            " "x16, x16, xzr"),
        Q!("    eor             " "x17, x17, " s!()),
        Q!("    adcs            " "x17, x17, xzr"),
        Q!("    stp             " "x16, x17, [" t!() ", #48]"),

        // Compute H = x_hi * y_hi in top half of buffer (size 8 x 8 -> 16)

        Q!("    add             " "x0, " z!() ", #128"),
        Q!("    add             " "x1, " x!() ", #64"),
        Q!("    bl              " Label!("Lbignum_ksqr_16_32_local_sqr_8_16", 2, After)),

        // Compute H' = H + L_top in place of H (it cannot overflow)
        // First add 8-sized block then propagate carry through next 8

        Q!("    ldp             " "x10, x11, [" z!() ", #128]"),
        Q!("    ldp             " "x12, x13, [" z!() ", #64]"),
        Q!("    adds            " "x10, x10, x12"),
        Q!("    adcs            " "x11, x11, x13"),
        Q!("    stp             " "x10, x11, [" z!() ", #128]"),

        Q!("    ldp             " "x10, x11, [" z!() ", #128 + 16]"),
        Q!("    ldp             " "x12, x13, [" z!() ", #64 + 16]"),
        Q!("    adcs            " "x10, x10, x12"),
        Q!("    adcs            " "x11, x11, x13"),
        Q!("    stp             " "x10, x11, [" z!() ", #128 + 16]"),

        Q!("    ldp             " "x10, x11, [" z!() ", #128 + 32]"),
        Q!("    ldp             " "x12, x13, [" z!() ", #64 + 32]"),
        Q!("    adcs            " "x10, x10, x12"),
        Q!("    adcs            " "x11, x11, x13"),
        Q!("    stp             " "x10, x11, [" z!() ", #128 + 32]"),

        Q!("    ldp             " "x10, x11, [" z!() ", #128 + 48]"),
        Q!("    ldp             " "x12, x13, [" z!() ", #64 + 48]"),
        Q!("    adcs            " "x10, x10, x12"),
        Q!("    adcs            " "x11, x11, x13"),
        Q!("    stp             " "x10, x11, [" z!() ", #128 + 48]"),

        Q!("    ldp             " "x10, x11, [" z!() ", #128 + 64]"),
        Q!("    adcs            " "x10, x10, xzr"),
        Q!("    adcs            " "x11, x11, xzr"),
        Q!("    stp             " "x10, x11, [" z!() ", #128 + 64]"),

        Q!("    ldp             " "x10, x11, [" z!() ", #128 + 80]"),
        Q!("    adcs            " "x10, x10, xzr"),
        Q!("    adcs            " "x11, x11, xzr"),
        Q!("    stp             " "x10, x11, [" z!() ", #128 + 80]"),

        Q!("    ldp             " "x10, x11, [" z!() ", #128 + 96]"),
        Q!("    adcs            " "x10, x10, xzr"),
        Q!("    adcs            " "x11, x11, xzr"),
        Q!("    stp             " "x10, x11, [" z!() ", #128 + 96]"),

        Q!("    ldp             " "x10, x11, [" z!() ", #128 + 112]"),
        Q!("    adcs            " "x10, x10, xzr"),
        Q!("    adcs            " "x11, x11, xzr"),
        Q!("    stp             " "x10, x11, [" z!() ", #128 + 112]"),

        // Compute M = |x_lo - x_hi| * |y_hi - y_lo| in [t+8...], size 16

        Q!("    add             " "x0, " t!() ", #64"),
        Q!("    mov             " "x1, " t!()),
        Q!("    bl              " Label!("Lbignum_ksqr_16_32_local_sqr_8_16", 2, After)),

        // Add the interlocking H' and L_bot terms, storing in registers x15..x0
        // Intercept the carry at the 8 + 16 = 24 position and store it in x.
        // (Note that we no longer need the input x was pointing at.)

        Q!("    ldp             " "x0, x1, [" z!() "]"),
        Q!("    ldp             " "x16, x17, [" z!() ", #128]"),
        Q!("    adds            " "x0, x0, x16"),
        Q!("    adcs            " "x1, x1, x17"),
        Q!("    ldp             " "x2, x3, [" z!() ", #16]"),
        Q!("    ldp             " "x16, x17, [" z!() ", #144]"),
        Q!("    adcs            " "x2, x2, x16"),
        Q!("    adcs            " "x3, x3, x17"),
        Q!("    ldp             " "x4, x5, [" z!() ", #32]"),
        Q!("    ldp             " "x16, x17, [" z!() ", #160]"),
        Q!("    adcs            " "x4, x4, x16"),
        Q!("    adcs            " "x5, x5, x17"),
        Q!("    ldp             " "x6, x7, [" z!() ", #48]"),
        Q!("    ldp             " "x16, x17, [" z!() ", #176]"),
        Q!("    adcs            " "x6, x6, x16"),
        Q!("    adcs            " "x7, x7, x17"),
        Q!("    ldp             " "x8, x9, [" z!() ", #128]"),
        Q!("    ldp             " "x16, x17, [" z!() ", #192]"),
        Q!("    adcs            " "x8, x8, x16"),
        Q!("    adcs            " "x9, x9, x17"),
        Q!("    ldp             " "x10, x11, [" z!() ", #144]"),
        Q!("    ldp             " "x16, x17, [" z!() ", #208]"),
        Q!("    adcs            " "x10, x10, x16"),
        Q!("    adcs            " "x11, x11, x17"),
        Q!("    ldp             " "x12, x13, [" z!() ", #160]"),
        Q!("    ldp             " "x16, x17, [" z!() ", #224]"),
        Q!("    adcs            " "x12, x12, x16"),
        Q!("    adcs            " "x13, x13, x17"),
        Q!("    ldp             " "x14, x15, [" z!() ", #176]"),
        Q!("    ldp             " "x16, x17, [" z!() ", #240]"),
        Q!("    adcs            " "x14, x14, x16"),
        Q!("    adcs            " "x15, x15, x17"),
        Q!("    cset            " x!() ", cs"),

        // Subtract the mid-term cross product M

        Q!("    ldp             " "x16, x17, [" t!() ", #64]"),
        Q!("    subs            " "x0, x0, x16"),
        Q!("    sbcs            " "x1, x1, x17"),
        Q!("    stp             " "x0, x1, [" z!() ", #64]"),
        Q!("    ldp             " "x16, x17, [" t!() ", #80]"),
        Q!("    sbcs            " "x2, x2, x16"),
        Q!("    sbcs            " "x3, x3, x17"),
        Q!("    stp             " "x2, x3, [" z!() ", #80]"),
        Q!("    ldp             " "x16, x17, [" t!() ", #96]"),
        Q!("    sbcs            " "x4, x4, x16"),
        Q!("    sbcs            " "x5, x5, x17"),
        Q!("    stp             " "x4, x5, [" z!() ", #96]"),
        Q!("    ldp             " "x16, x17, [" t!() ", #112]"),
        Q!("    sbcs            " "x6, x6, x16"),
        Q!("    sbcs            " "x7, x7, x17"),
        Q!("    stp             " "x6, x7, [" z!() ", #112]"),
        Q!("    ldp             " "x16, x17, [" t!() ", #128]"),
        Q!("    sbcs            " "x8, x8, x16"),
        Q!("    sbcs            " "x9, x9, x17"),
        Q!("    stp             " "x8, x9, [" z!() ", #128]"),
        Q!("    ldp             " "x16, x17, [" t!() ", #144]"),
        Q!("    sbcs            " "x10, x10, x16"),
        Q!("    sbcs            " "x11, x11, x17"),
        Q!("    stp             " "x10, x11, [" z!() ", #144]"),
        Q!("    ldp             " "x16, x17, [" t!() ", #160]"),
        Q!("    sbcs            " "x12, x12, x16"),
        Q!("    sbcs            " "x13, x13, x17"),
        Q!("    stp             " "x12, x13, [" z!() ", #160]"),
        Q!("    ldp             " "x16, x17, [" t!() ", #176]"),
        Q!("    sbcs            " "x14, x14, x16"),
        Q!("    sbcs            " "x15, x15, x17"),
        Q!("    stp             " "x14, x15, [" z!() ", #176]"),

        // Get the next digits effectively resulting so far starting at 24

        Q!("    sbcs            " x!() ", " x!() ", xzr"),
        Q!("    csetm           " t!() ", cc"),

        // Now the final 8 digits of padding; the first one is special in using x
        // and also in getting the carry chain started

        Q!("    ldp             " "x10, x11, [" z!() ", #192]"),
        Q!("    adds            " "x10, x10, " x!()),
        Q!("    adcs            " "x11, x11, " t!()),
        Q!("    stp             " "x10, x11, [" z!() ", #192]"),
        Q!("    ldp             " "x10, x11, [" z!() ", #208]"),
        Q!("    adcs            " "x10, x10, " t!()),
        Q!("    adcs            " "x11, x11, " t!()),
        Q!("    stp             " "x10, x11, [" z!() ", #208]"),
        Q!("    ldp             " "x10, x11, [" z!() ", #224]"),
        Q!("    adcs            " "x10, x10, " t!()),
        Q!("    adcs            " "x11, x11, " t!()),
        Q!("    stp             " "x10, x11, [" z!() ", #224]"),
        Q!("    ldp             " "x10, x11, [" z!() ", #240]"),
        Q!("    adcs            " "x10, x10, " t!()),
        Q!("    adcs            " "x11, x11, " t!()),
        Q!("    stp             " "x10, x11, [" z!() ", #240]"),

        // Restore registers and return

        Q!("    ldp             " "x25, x30, [sp], #16"),
        Q!("    ldp             " "x23, x24, [sp], #16"),
        Q!("    ldp             " "x21, x22, [sp], #16"),
        Q!("    ldp             " "x19, x20, [sp], #16"),

        // proc hoisting in -> ret after Lbignum_ksqr_16_32_local_sqr_8_16
        Q!("    b               " Label!("hoist_finish", 3, After)),

        // -----------------------------------------------------------------------------
        // Local 8x8->16 squaring routine, shared to reduce code size. Effectively
        // the same as bignum_sqr_8_16 without the scratch register preservation.
        // -----------------------------------------------------------------------------

        Q!(Label!("Lbignum_ksqr_16_32_local_sqr_8_16", 2) ":"),

        // Load registers.
        Q!("    ldp             " "x2, x3, [x1]"),
        Q!("    ldr             " "q20, [x1]"),
        Q!("    ldp             " "x4, x5, [x1, #16]"),
        Q!("    ldr             " "q21, [x1, #16]"),
        Q!("    ldp             " "x6, x7, [x1, #32]"),
        Q!("    ldr             " "q22, [x1, #32]"),
        Q!("    ldp             " "x8, x9, [x1, #48]"),
        Q!("    ldr             " "q23, [x1, #48]"),
        Q!("    movi            " "v30.2d, #0xffffffff"),

        Q!("    mul             " "x17, x2, x4"),
        Q!("    mul             " "x14, x3, x5"),

        // Scalar+NEON: square the lower half with a near-clone of bignum_sqr_4_8
        // NEON: prepare 64x64->128 squaring of two 64-bit ints (x2, x3)
        Q!("    ext             " "v1.16b, v20.16b, v20.16b, #8"),
        Q!("    umulh           " "x20, x2, x4"),
        Q!("    shrn            " "v2.2s, v20.2d, #32"),
        Q!("    subs            " "x21, x2, x3"),
        Q!("    zip1            " "v0.2s, v20.2s, v1.2s"),
        Q!("    cneg            " "x21, x21, cc"),
        Q!("    umull           " "v5.2d, v2.2s, v2.2s"),
        Q!("    csetm           " "x11, cc"),
        Q!("    umull           " "v6.2d, v2.2s, v0.2s"),
        Q!("    subs            " "x12, x5, x4"),
        Q!("    umull           " "v3.2d, v0.2s, v0.2s"),
        Q!("    cneg            " "x12, x12, cc"),
        Q!("    mov             " "v1.16b, v6.16b"),
        Q!("    mul             " "x13, x21, x12"),
        Q!("    usra            " "v1.2d, v3.2d, #32"),
        Q!("    umulh           " "x12, x21, x12"),
        Q!("    and             " "v4.16b, v1.16b, v30.16b"),
        Q!("    cinv            " "x11, x11, cc"),
        Q!("    add             " "v4.2d, v4.2d, v6.2d"),
        Q!("    eor             " "x13, x13, x11"),
        Q!("    usra            " "v5.2d, v4.2d, #32"),
        Q!("    eor             " "x12, x12, x11"),
        Q!("    sli             " "v3.2d, v4.2d, #32"),
        Q!("    adds            " "x19, x17, x20"),
        Q!("    usra            " "v5.2d, v1.2d, #32"),
        Q!("    adc             " "x20, x20, xzr"),
        // NEON: prepare 64x64->128 squaring of two 64-bit ints (x4, x5)
        Q!("    ext             " "v1.16b, v21.16b, v21.16b, #8"),
        Q!("    umulh           " "x21, x3, x5"),
        Q!("    shrn            " "v2.2s, v21.2d, #32"),
        Q!("    adds            " "x19, x19, x14"),
        Q!("    zip1            " "v0.2s, v21.2s, v1.2s"),
        Q!("    adcs            " "x20, x20, x21"),
        Q!("    adc             " "x21, x21, xzr"),
        Q!("    adds            " "x20, x20, x14"),
        Q!("    adc             " "x21, x21, xzr"),
        Q!("    cmn             " "x11, #0x1"),
        Q!("    adcs            " "x19, x19, x13"),
        Q!("    mov             " "x13, v3.d[1]"),
        Q!("    adcs            " "x20, x20, x12"),
        Q!("    mov             " "x14, v5.d[1]"),
        Q!("    adc             " "x21, x21, x11"),
        Q!("    mov             " "x12, v3.d[0]"),
        Q!("    adds            " "x17, x17, x17"),
        Q!("    mov             " "x11, v5.d[0]"),
        Q!("    adcs            " "x19, x19, x19"),
        Q!("    umull           " "v5.2d, v2.2s, v2.2s"),
        Q!("    adcs            " "x20, x20, x20"),
        Q!("    umull           " "v6.2d, v2.2s, v0.2s"),
        Q!("    adcs            " "x21, x21, x21"),
        Q!("    umull           " "v3.2d, v0.2s, v0.2s"),
        Q!("    adc             " "x10, xzr, xzr"),
        Q!("    mov             " "v1.16b, v6.16b"),

        Q!("    mul             " "x15, x2, x3"),
        Q!("    usra            " "v1.2d, v3.2d, #32"),
        Q!("    umulh           " "x16, x2, x3"),
        Q!("    and             " "v4.16b, v1.16b, v30.16b"),
        Q!("    adds            " "x11, x11, x15"),
        Q!("    add             " "v4.2d, v4.2d, v6.2d"),
        Q!("    adcs            " "x13, x13, x16"),
        Q!("    usra            " "v5.2d, v4.2d, #32"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    sli             " "v3.2d, v4.2d, #32"),
        Q!("    adds            " "x11, x11, x15"),
        Q!("    usra            " "v5.2d, v1.2d, #32"),
        Q!("    adcs            " "x13, x13, x16"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    stp             " "x12, x11, [x0]"),
        Q!("    mov             " "x11, v5.d[0]"),
        Q!("    adds            " "x17, x17, x13"),
        Q!("    mov             " "x13, v3.d[1]"),
        Q!("    adcs            " "x19, x19, x14"),
        Q!("    mov             " "x14, v5.d[1]"),
        Q!("    adcs            " "x20, x20, xzr"),
        Q!("    mov             " "x12, v3.d[0]"),
        Q!("    adcs            " "x21, x21, xzr"),
        // NEON: prepare muls in the upper half
        Q!("    ext             " "v1.16b, v22.16b, v22.16b, #8"),
        Q!("    adc             " "x10, x10, xzr"),
        Q!("    shrn            " "v2.2s, v22.2d, #32"),
        Q!("    stp             " "x17, x19, [x0, #16]"),
        Q!("    zip1            " "v0.2s, v22.2s, v1.2s"),
        Q!("    mul             " "x15, x4, x5"),
        Q!("    umull           " "v5.2d, v2.2s, v2.2s"),
        Q!("    umulh           " "x16, x4, x5"),
        Q!("    umull           " "v6.2d, v2.2s, v0.2s"),
        Q!("    adds            " "x11, x11, x15"),
        Q!("    umull           " "v3.2d, v0.2s, v0.2s"),
        Q!("    adcs            " "x13, x13, x16"),
        Q!("    mov             " "v1.16b, v6.16b"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    usra            " "v1.2d, v3.2d, #32"),
        Q!("    adds            " "x11, x11, x15"),
        Q!("    and             " "v4.16b, v1.16b, v30.16b"),
        Q!("    adcs            " "x13, x13, x16"),
        Q!("    add             " "v4.2d, v4.2d, v6.2d"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    usra            " "v5.2d, v4.2d, #32"),
        Q!("    adds            " "x12, x12, x20"),
        Q!("    sli             " "v3.2d, v4.2d, #32"),
        Q!("    adcs            " "x11, x11, x21"),
        Q!("    usra            " "v5.2d, v1.2d, #32"),
        Q!("    stp             " "x12, x11, [x0, #32]"),
        // NEON: prepare muls in the upper half
        Q!("    ext             " "v1.16b, v23.16b, v23.16b, #8"),
        Q!("    adcs            " "x13, x13, x10"),
        Q!("    shrn            " "v2.2s, v23.2d, #32"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    zip1            " "v0.2s, v23.2s, v1.2s"),
        Q!("    stp             " "x13, x14, [x0, #48]"),

        // Scalar: square the upper half with a slight variant of the previous block
        Q!("    mul             " "x17, x6, x8"),
        Q!("    umull           " "v16.2d, v2.2s, v2.2s"),
        Q!("    mul             " "x14, x7, x9"),
        Q!("    umull           " "v6.2d, v2.2s, v0.2s"),
        Q!("    umulh           " "x20, x6, x8"),
        Q!("    umull           " "v18.2d, v0.2s, v0.2s"),
        Q!("    subs            " "x21, x6, x7"),
        Q!("    cneg            " "x21, x21, cc"),
        Q!("    mov             " "v1.16b, v6.16b"),
        Q!("    csetm           " "x11, cc"),
        Q!("    subs            " "x12, x9, x8"),
        Q!("    cneg            " "x12, x12, cc"),
        Q!("    usra            " "v1.2d, v18.2d, #32"),
        Q!("    mul             " "x13, x21, x12"),
        Q!("    and             " "v4.16b, v1.16b, v30.16b"),
        Q!("    umulh           " "x12, x21, x12"),
        Q!("    add             " "v4.2d, v4.2d, v6.2d"),
        Q!("    cinv            " "x11, x11, cc"),
        Q!("    eor             " "x13, x13, x11"),
        Q!("    eor             " "x12, x12, x11"),
        Q!("    usra            " "v16.2d, v4.2d, #32"),
        Q!("    adds            " "x19, x17, x20"),
        Q!("    adc             " "x20, x20, xzr"),
        Q!("    sli             " "v18.2d, v4.2d, #32"),
        Q!("    umulh           " "x21, x7, x9"),
        Q!("    adds            " "x19, x19, x14"),
        Q!("    adcs            " "x20, x20, x21"),
        Q!("    adc             " "x21, x21, xzr"),
        Q!("    adds            " "x20, x20, x14"),
        Q!("    mov             " "x14, v5.d[1]"),
        Q!("    adc             " "x21, x21, xzr"),
        Q!("    cmn             " "x11, #0x1"),
        Q!("    adcs            " "x19, x19, x13"),
        Q!("    mov             " "x13, v3.d[1]"),
        Q!("    adcs            " "x20, x20, x12"),
        Q!("    mov             " "x12, v3.d[0]"),
        Q!("    adc             " "x21, x21, x11"),
        Q!("    mov             " "x11, v5.d[0]"),
        Q!("    adds            " "x17, x17, x17"),
        Q!("    adcs            " "x19, x19, x19"),
        Q!("    usra            " "v16.2d, v1.2d, #32"),
        Q!("    adcs            " "x20, x20, x20"),
        Q!("    adcs            " "x21, x21, x21"),
        Q!("    adc             " "x10, xzr, xzr"),
        // NEON: two mul+umulhs for the next stage
        Q!("    uzp2            " "v17.4s, v21.4s, v23.4s"),
        Q!("    mul             " "x15, x6, x7"),
        Q!("    xtn             " "v4.2s, v23.2d"),
        Q!("    umulh           " "x16, x6, x7"),
        Q!("    mov             " "x22, v16.d[0]"),
        Q!("    adds            " "x11, x11, x15"),
        Q!("    adcs            " "x13, x13, x16"),
        Q!("    xtn             " "v5.2s, v21.2d"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    adds            " "x11, x11, x15"),
        Q!("    rev64           " "v1.4s, v21.4s"),
        Q!("    adcs            " "x13, x13, x16"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    stp             " "x12, x11, [x0, #64]"),
        Q!("    adds            " "x17, x17, x13"),
        Q!("    mov             " "x13, v18.d[1]"),
        Q!("    adcs            " "x19, x19, x14"),
        Q!("    mov             " "x14, v16.d[1]"),
        Q!("    adcs            " "x20, x20, xzr"),
        Q!("    mov             " "x12, v18.d[0]"),
        Q!("    adcs            " "x21, x21, xzr"),
        Q!("    adc             " "x10, x10, xzr"),
        Q!("    umull           " "v6.2d, v4.2s, v5.2s"),
        Q!("    stp             " "x17, x19, [x0, #80]"),
        Q!("    umull           " "v7.2d, v4.2s, v17.2s"),
        Q!("    mul             " "x15, x8, x9"),
        Q!("    uzp2            " "v16.4s, v23.4s, v23.4s"),
        Q!("    umulh           " "x16, x8, x9"),
        Q!("    mul             " "v0.4s, v1.4s, v23.4s"),
        Q!("    adds            " "x11, x22, x15"),
        Q!("    adcs            " "x13, x13, x16"),
        Q!("    usra            " "v7.2d, v6.2d, #32"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    adds            " "x11, x11, x15"),
        Q!("    umull           " "v1.2d, v16.2s, v17.2s"),
        Q!("    adcs            " "x13, x13, x16"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    uaddlp          " "v0.2d, v0.4s"),
        Q!("    adds            " "x12, x12, x20"),
        Q!("    adcs            " "x11, x11, x21"),
        Q!("    and             " "v2.16b, v7.16b, v30.16b"),
        Q!("    umlal           " "v2.2d, v16.2s, v5.2s"),
        Q!("    shl             " "v0.2d, v0.2d, #32"),
        Q!("    usra            " "v1.2d, v7.2d, #32"),
        Q!("    umlal           " "v0.2d, v4.2s, v5.2s"),
        Q!("    mov             " "x16, v0.d[1]"),
        Q!("    mov             " "x15, v0.d[0]"),
        Q!("    usra            " "v1.2d, v2.2d, #32"),
        Q!("    mov             " "x20, v1.d[0]"),
        Q!("    mov             " "x21, v1.d[1]"),
        Q!("    stp             " "x12, x11, [x0, #96]"),
        Q!("    adcs            " "x13, x13, x10"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    stp             " "x13, x14, [x0, #112]"),

        // Now get the cross-product in [s7,...,s0] and double it as [c,s7,...,s0]

        Q!("    mul             " "x10, x2, x6"),
        Q!("    mul             " "x14, x3, x7"),
        Q!("    umulh           " "x17, x2, x6"),
        Q!("    adds            " "x14, x14, x17"),
        Q!("    umulh           " "x17, x3, x7"),
        Q!("    adcs            " "x15, x15, x17"),
        Q!("    adcs            " "x16, x16, x20"),
        Q!("    adc             " "x17, x21, xzr"),
        Q!("    adds            " "x11, x14, x10"),
        Q!("    adcs            " "x14, x15, x14"),
        Q!("    adcs            " "x15, x16, x15"),
        Q!("    adcs            " "x16, x17, x16"),
        Q!("    adc             " "x17, xzr, x17"),
        Q!("    adds            " "x12, x14, x10"),
        Q!("    adcs            " "x13, x15, x11"),
        Q!("    adcs            " "x14, x16, x14"),
        Q!("    adcs            " "x15, x17, x15"),
        Q!("    adcs            " "x16, xzr, x16"),
        Q!("    adc             " "x17, xzr, x17"),
        Q!("    subs            " "x22, x4, x5"),
        Q!("    cneg            " "x22, x22, cc"),
        Q!("    csetm           " "x19, cc"),
        Q!("    subs            " "x20, x9, x8"),
        Q!("    cneg            " "x20, x20, cc"),
        Q!("    mul             " "x21, x22, x20"),
        Q!("    umulh           " "x20, x22, x20"),
        Q!("    cinv            " "x19, x19, cc"),
        Q!("    cmn             " "x19, #0x1"),
        Q!("    eor             " "x21, x21, x19"),
        Q!("    adcs            " "x15, x15, x21"),
        Q!("    eor             " "x20, x20, x19"),
        Q!("    adcs            " "x16, x16, x20"),
        Q!("    adc             " "x17, x17, x19"),
        Q!("    subs            " "x22, x2, x3"),
        Q!("    cneg            " "x22, x22, cc"),
        Q!("    csetm           " "x19, cc"),
        Q!("    subs            " "x20, x7, x6"),
        Q!("    cneg            " "x20, x20, cc"),
        Q!("    mul             " "x21, x22, x20"),
        Q!("    umulh           " "x20, x22, x20"),
        Q!("    cinv            " "x19, x19, cc"),
        Q!("    cmn             " "x19, #0x1"),
        Q!("    eor             " "x21, x21, x19"),
        Q!("    adcs            " "x11, x11, x21"),
        Q!("    eor             " "x20, x20, x19"),
        Q!("    adcs            " "x12, x12, x20"),
        Q!("    adcs            " "x13, x13, x19"),
        Q!("    adcs            " "x14, x14, x19"),
        Q!("    adcs            " "x15, x15, x19"),
        Q!("    adcs            " "x16, x16, x19"),
        Q!("    adc             " "x17, x17, x19"),
        Q!("    subs            " "x22, x3, x5"),
        Q!("    cneg            " "x22, x22, cc"),
        Q!("    csetm           " "x19, cc"),
        Q!("    subs            " "x20, x9, x7"),
        Q!("    cneg            " "x20, x20, cc"),
        Q!("    mul             " "x21, x22, x20"),
        Q!("    umulh           " "x20, x22, x20"),
        Q!("    cinv            " "x19, x19, cc"),
        Q!("    cmn             " "x19, #0x1"),
        Q!("    eor             " "x21, x21, x19"),
        Q!("    adcs            " "x14, x14, x21"),
        Q!("    eor             " "x20, x20, x19"),
        Q!("    adcs            " "x15, x15, x20"),
        Q!("    adcs            " "x16, x16, x19"),
        Q!("    adc             " "x17, x17, x19"),
        Q!("    subs            " "x22, x2, x4"),
        Q!("    cneg            " "x22, x22, cc"),
        Q!("    csetm           " "x19, cc"),
        Q!("    subs            " "x20, x8, x6"),
        Q!("    cneg            " "x20, x20, cc"),
        Q!("    mul             " "x21, x22, x20"),
        Q!("    umulh           " "x20, x22, x20"),
        Q!("    cinv            " "x19, x19, cc"),
        Q!("    cmn             " "x19, #0x1"),
        Q!("    eor             " "x21, x21, x19"),
        Q!("    adcs            " "x12, x12, x21"),
        Q!("    eor             " "x20, x20, x19"),
        Q!("    adcs            " "x13, x13, x20"),
        Q!("    adcs            " "x14, x14, x19"),
        Q!("    adcs            " "x15, x15, x19"),
        Q!("    adcs            " "x16, x16, x19"),
        Q!("    adc             " "x17, x17, x19"),
        Q!("    subs            " "x22, x2, x5"),
        Q!("    cneg            " "x22, x22, cc"),
        Q!("    csetm           " "x19, cc"),
        Q!("    subs            " "x20, x9, x6"),
        Q!("    cneg            " "x20, x20, cc"),
        Q!("    mul             " "x21, x22, x20"),
        Q!("    umulh           " "x20, x22, x20"),
        Q!("    cinv            " "x19, x19, cc"),
        Q!("    cmn             " "x19, #0x1"),
        Q!("    eor             " "x21, x21, x19"),
        Q!("    adcs            " "x13, x13, x21"),
        Q!("    eor             " "x20, x20, x19"),
        Q!("    adcs            " "x14, x14, x20"),
        Q!("    adcs            " "x15, x15, x19"),
        Q!("    adcs            " "x16, x16, x19"),
        Q!("    adc             " "x17, x17, x19"),
        Q!("    subs            " "x22, x3, x4"),
        Q!("    cneg            " "x22, x22, cc"),
        Q!("    csetm           " "x19, cc"),
        Q!("    subs            " "x20, x8, x7"),
        Q!("    cneg            " "x20, x20, cc"),
        Q!("    mul             " "x21, x22, x20"),
        Q!("    umulh           " "x20, x22, x20"),
        Q!("    cinv            " "x19, x19, cc"),
        Q!("    cmn             " "x19, #0x1"),
        Q!("    eor             " "x21, x21, x19"),
        Q!("    adcs            " "x13, x13, x21"),
        Q!("    eor             " "x20, x20, x19"),
        Q!("    adcs            " "x14, x14, x20"),
        Q!("    adcs            " "x15, x15, x19"),
        Q!("    adcs            " "x16, x16, x19"),
        Q!("    adc             " "x17, x17, x19"),
        Q!("    adds            " "x10, x10, x10"),
        Q!("    adcs            " "x11, x11, x11"),
        Q!("    adcs            " "x12, x12, x12"),
        Q!("    adcs            " "x13, x13, x13"),
        Q!("    adcs            " "x14, x14, x14"),
        Q!("    adcs            " "x15, x15, x15"),
        Q!("    adcs            " "x16, x16, x16"),
        Q!("    adcs            " "x17, x17, x17"),
        Q!("    adc             " "x19, xzr, xzr"),

        // Add it back to the buffer

        Q!("    ldp             " "x2, x3, [x0, #32]"),
        Q!("    adds            " "x10, x10, x2"),
        Q!("    adcs            " "x11, x11, x3"),
        Q!("    stp             " "x10, x11, [x0, #32]"),

        Q!("    ldp             " "x2, x3, [x0, #48]"),
        Q!("    adcs            " "x12, x12, x2"),
        Q!("    adcs            " "x13, x13, x3"),
        Q!("    stp             " "x12, x13, [x0, #48]"),

        Q!("    ldp             " "x2, x3, [x0, #64]"),
        Q!("    adcs            " "x14, x14, x2"),
        Q!("    adcs            " "x15, x15, x3"),
        Q!("    stp             " "x14, x15, [x0, #64]"),

        Q!("    ldp             " "x2, x3, [x0, #80]"),
        Q!("    adcs            " "x16, x16, x2"),
        Q!("    adcs            " "x17, x17, x3"),
        Q!("    stp             " "x16, x17, [x0, #80]"),

        Q!("    ldp             " "x2, x3, [x0, #96]"),
        Q!("    adcs            " "x2, x2, x19"),
        Q!("    adcs            " "x3, x3, xzr"),
        Q!("    stp             " "x2, x3, [x0, #96]"),

        Q!("    ldp             " "x2, x3, [x0, #112]"),
        Q!("    adcs            " "x2, x2, xzr"),
        Q!("    adc             " "x3, x3, xzr"),
        Q!("    stp             " "x2, x3, [x0, #112]"),

        Q!("    ret             " ),
        Q!(Label!("hoist_finish", 3) ":"),
        inout("x0") z.as_mut_ptr() => _,
        inout("x1") x.as_ptr() => _,
        inout("x2") t.as_mut_ptr() => _,
        // clobbers
        out("v0") _,
        out("v1") _,
        out("v16") _,
        out("v17") _,
        out("v18") _,
        out("v2") _,
        out("v20") _,
        out("v21") _,
        out("v22") _,
        out("v23") _,
        out("v3") _,
        out("v30") _,
        out("v4") _,
        out("v5") _,
        out("v6") _,
        out("v7") _,
        out("x10") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x14") _,
        out("x15") _,
        out("x16") _,
        out("x17") _,
        out("x20") _,
        out("x21") _,
        out("x22") _,
        out("x23") _,
        out("x24") _,
        out("x25") _,
        out("x3") _,
        out("x30") _,
        out("x4") _,
        out("x5") _,
        out("x6") _,
        out("x7") _,
        out("x8") _,
        out("x9") _,
            )
    };
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        bignum_ksqr_16_32,
        &mut [0; 32],
        &[1; 16],
        &mut crate::low::abi::Aligned([0; 24]).0
    );
}
