// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply modulo p_25519, z := (x * y) mod p_25519
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_mul_p25519(uint64_t z[static 4], const uint64_t x[static 4],
//                                  const uint64_t y[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------

macro_rules! z {
    () => {
        "x0"
    };
}
macro_rules! x {
    () => {
        "x1"
    };
}
macro_rules! y {
    () => {
        "x2"
    };
}

macro_rules! a0 {
    () => {
        "x3"
    };
}
macro_rules! a0short {
    () => {
        "w3"
    };
}
macro_rules! a1 {
    () => {
        "x4"
    };
}
macro_rules! b0 {
    () => {
        "x5"
    };
}
macro_rules! b0short {
    () => {
        "w5"
    };
}
macro_rules! b1 {
    () => {
        "x6"
    };
}

macro_rules! u0 {
    () => {
        "x7"
    };
}
macro_rules! u1 {
    () => {
        "x8"
    };
}
macro_rules! u2 {
    () => {
        "x9"
    };
}
macro_rules! u3 {
    () => {
        "x10"
    };
}
macro_rules! u4 {
    () => {
        "x11"
    };
}
macro_rules! u5 {
    () => {
        "x12"
    };
}
macro_rules! u6 {
    () => {
        "x13"
    };
}
macro_rules! u7 {
    () => {
        "x14"
    };
}

macro_rules! u0short {
    () => {
        "w7"
    };
}
macro_rules! u1short {
    () => {
        "w8"
    };
}
macro_rules! u2short {
    () => {
        "w9"
    };
}
macro_rules! u3short {
    () => {
        "w10"
    };
}
macro_rules! u4short {
    () => {
        "w11"
    };
}
macro_rules! u5short {
    () => {
        "w12"
    };
}
macro_rules! u6short {
    () => {
        "w13"
    };
}
macro_rules! u7short {
    () => {
        "w14"
    };
}

macro_rules! t {
    () => {
        "x15"
    };
}

macro_rules! sgn {
    () => {
        "x16"
    };
}
macro_rules! ysgn {
    () => {
        "x17"
    };
}

// These are aliases to registers used elsewhere including input pointers.
// By the time they are used this does not conflict with other uses.

macro_rules! m0 {
    () => {
        Q!(y!())
    };
}
macro_rules! m1 {
    () => {
        Q!(ysgn!())
    };
}
macro_rules! m2 {
    () => {
        Q!(t!())
    };
}
macro_rules! m3 {
    () => {
        Q!(x!())
    };
}
macro_rules! u {
    () => {
        Q!(u2!())
    };
}

// For the reduction stages, again aliasing other things but not the u's

macro_rules! c {
    () => {
        "x3"
    };
}
macro_rules! cshort {
    () => {
        "w3"
    };
}
macro_rules! h {
    () => {
        "x4"
    };
}
macro_rules! l {
    () => {
        "x5"
    };
}
macro_rules! lshort {
    () => {
        "w5"
    };
}
macro_rules! d {
    () => {
        "x6"
    };
}
macro_rules! q {
    () => {
        "x17"
    };
}
macro_rules! qshort {
    () => {
        "w17"
    };
}

// Transliterated from s2n-bignum's arm/curve25519/bignum_mul_p25519.S.
/// Multiply modulo p_25519, z := (x * y) mod p_25519
///
/// Inputs x[4], y[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_mul_p25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Multiply the low halves using Karatsuba 2x2->4 to get [u3,u2,u1,u0]

        Q!("    ldp             " a0!() ", " a1!() ", [" x!() "]"),
        Q!("    ldp             " b0!() ", " b1!() ", [" y!() "]"),

        Q!("    umull           " u0!() ", " a0short!() ", " b0short!()),
        Q!("    lsr             " "x17, " a0!() ", #32"),
        Q!("    umull           " "x15, w17, " b0short!()),
        Q!("    lsr             " "x16, " b0!() ", #32"),
        Q!("    umull           " u1!() ", w16, w17"),
        Q!("    umull           " "x16, " a0short!() ", w16"),
        Q!("    adds            " u0!() ", " u0!() ", x15, lsl #32"),
        Q!("    lsr             " "x15, x15, #32"),
        Q!("    adc             " u1!() ", " u1!() ", x15"),
        Q!("    adds            " u0!() ", " u0!() ", x16, lsl #32"),
        Q!("    lsr             " "x16, x16, #32"),
        Q!("    adc             " u1!() ", " u1!() ", x16"),

        Q!("    mul             " u2!() ", " a1!() ", " b1!()),
        Q!("    umulh           " u3!() ", " a1!() ", " b1!()),

        Q!("    subs            " a1!() ", " a1!() ", " a0!()),
        Q!("    cneg            " a1!() ", " a1!() ", cc"),
        Q!("    csetm           " sgn!() ", cc"),

        Q!("    adds            " u2!() ", " u2!() ", " u1!()),
        Q!("    adc             " u3!() ", " u3!() ", xzr"),

        Q!("    subs            " a0!() ", " b0!() ", " b1!()),
        Q!("    cneg            " a0!() ", " a0!() ", cc"),
        Q!("    cinv            " sgn!() ", " sgn!() ", cc"),

        Q!("    mul             " t!() ", " a1!() ", " a0!()),
        Q!("    umulh           " a0!() ", " a1!() ", " a0!()),

        Q!("    adds            " u1!() ", " u0!() ", " u2!()),
        Q!("    adcs            " u2!() ", " u2!() ", " u3!()),
        Q!("    adc             " u3!() ", " u3!() ", xzr"),

        Q!("    adds            " "xzr, " sgn!() ", #1"),
        Q!("    eor             " t!() ", " t!() ", " sgn!()),
        Q!("    adcs            " u1!() ", " t!() ", " u1!()),
        Q!("    eor             " a0!() ", " a0!() ", " sgn!()),
        Q!("    adcs            " u2!() ", " a0!() ", " u2!()),
        Q!("    adc             " u3!() ", " u3!() ", " sgn!()),

        // Multiply the high halves using Karatsuba 2x2->4 to get [u7,u6,u5,u4]

        Q!("    ldp             " a0!() ", " a1!() ", [" x!() ", #16]"),
        Q!("    ldp             " b0!() ", " b1!() ", [" y!() ", #16]"),

        Q!("    umull           " u4!() ", " a0short!() ", " b0short!()),
        Q!("    lsr             " "x17, " a0!() ", #32"),
        Q!("    umull           " "x15, w17, " b0short!()),
        Q!("    lsr             " "x16, " b0!() ", #32"),
        Q!("    umull           " u5!() ", w16, w17"),
        Q!("    umull           " "x16, " a0short!() ", w16"),
        Q!("    adds            " u4!() ", " u4!() ", x15, lsl #32"),
        Q!("    lsr             " "x15, x15, #32"),
        Q!("    adc             " u5!() ", " u5!() ", x15"),
        Q!("    adds            " u4!() ", " u4!() ", x16, lsl #32"),
        Q!("    lsr             " "x16, x16, #32"),
        Q!("    adc             " u5!() ", " u5!() ", x16"),

        Q!("    mul             " u6!() ", " a1!() ", " b1!()),
        Q!("    umulh           " u7!() ", " a1!() ", " b1!()),

        Q!("    subs            " a1!() ", " a1!() ", " a0!()),
        Q!("    cneg            " a1!() ", " a1!() ", cc"),
        Q!("    csetm           " sgn!() ", cc"),

        Q!("    adds            " u6!() ", " u6!() ", " u5!()),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),

        Q!("    subs            " a0!() ", " b0!() ", " b1!()),
        Q!("    cneg            " a0!() ", " a0!() ", cc"),
        Q!("    cinv            " sgn!() ", " sgn!() ", cc"),

        Q!("    mul             " t!() ", " a1!() ", " a0!()),
        Q!("    umulh           " a0!() ", " a1!() ", " a0!()),

        Q!("    adds            " u5!() ", " u4!() ", " u6!()),
        Q!("    adcs            " u6!() ", " u6!() ", " u7!()),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),

        Q!("    adds            " "xzr, " sgn!() ", #1"),
        Q!("    eor             " t!() ", " t!() ", " sgn!()),
        Q!("    adcs            " u5!() ", " t!() ", " u5!()),
        Q!("    eor             " a0!() ", " a0!() ", " sgn!()),
        Q!("    adcs            " u6!() ", " a0!() ", " u6!()),
        Q!("    adc             " u7!() ", " u7!() ", " sgn!()),

        // Compute  sgn,[a1,a0] = x_hi - x_lo
        // and     ysgn,[b1,b0] = y_lo - y_hi
        // sign-magnitude differences

        Q!("    ldp             " a0!() ", " a1!() ", [" x!() ", #16]"),
        Q!("    ldp             " t!() ", " sgn!() ", [" x!() "]"),
        Q!("    subs            " a0!() ", " a0!() ", " t!()),
        Q!("    sbcs            " a1!() ", " a1!() ", " sgn!()),
        Q!("    csetm           " sgn!() ", cc"),

        Q!("    ldp             " t!() ", " ysgn!() ", [" y!() "]"),
        Q!("    subs            " b0!() ", " t!() ", " b0!()),
        Q!("    sbcs            " b1!() ", " ysgn!() ", " b1!()),
        Q!("    csetm           " ysgn!() ", cc"),

        Q!("    eor             " a0!() ", " a0!() ", " sgn!()),
        Q!("    subs            " a0!() ", " a0!() ", " sgn!()),
        Q!("    eor             " a1!() ", " a1!() ", " sgn!()),
        Q!("    sbc             " a1!() ", " a1!() ", " sgn!()),

        Q!("    eor             " b0!() ", " b0!() ", " ysgn!()),
        Q!("    subs            " b0!() ", " b0!() ", " ysgn!()),
        Q!("    eor             " b1!() ", " b1!() ", " ysgn!()),
        Q!("    sbc             " b1!() ", " b1!() ", " ysgn!()),

        // Save the correct sign for the sub-product

        Q!("    eor             " sgn!() ", " ysgn!() ", " sgn!()),

        // Add H' = H + L_top, still in [u7,u6,u5,u4]

        Q!("    adds            " u4!() ", " u4!() ", " u2!()),
        Q!("    adcs            " u5!() ", " u5!() ", " u3!()),
        Q!("    adcs            " u6!() ", " u6!() ", xzr"),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),

        // Now compute the mid-product as [m3,m2,m1,m0]

        Q!("    mul             " m0!() ", " a0!() ", " b0!()),
        Q!("    umulh           " m1!() ", " a0!() ", " b0!()),
        Q!("    mul             " m2!() ", " a1!() ", " b1!()),
        Q!("    umulh           " m3!() ", " a1!() ", " b1!()),

        Q!("    subs            " a1!() ", " a1!() ", " a0!()),
        Q!("    cneg            " a1!() ", " a1!() ", cc"),
        Q!("    csetm           " u!() ", cc"),

        Q!("    adds            " m2!() ", " m2!() ", " m1!()),
        Q!("    adc             " m3!() ", " m3!() ", xzr"),

        Q!("    subs            " b1!() ", " b0!() ", " b1!()),
        Q!("    cneg            " b1!() ", " b1!() ", cc"),
        Q!("    cinv            " u!() ", " u!() ", cc"),

        Q!("    mul             " b0!() ", " a1!() ", " b1!()),
        Q!("    umulh           " b1!() ", " a1!() ", " b1!()),

        Q!("    adds            " m1!() ", " m0!() ", " m2!()),
        Q!("    adcs            " m2!() ", " m2!() ", " m3!()),
        Q!("    adc             " m3!() ", " m3!() ", xzr"),

        Q!("    adds            " "xzr, " u!() ", #1"),
        Q!("    eor             " b0!() ", " b0!() ", " u!()),
        Q!("    adcs            " m1!() ", " b0!() ", " m1!()),
        Q!("    eor             " b1!() ", " b1!() ", " u!()),
        Q!("    adcs            " m2!() ", " b1!() ", " m2!()),
        Q!("    adc             " m3!() ", " m3!() ", " u!()),

        // Accumulate the positive mid-terms as [u7,u6,u5,u4,u3,u2]

        Q!("    adds            " u2!() ", " u4!() ", " u0!()),
        Q!("    adcs            " u3!() ", " u5!() ", " u1!()),
        Q!("    adcs            " u4!() ", " u6!() ", " u4!()),
        Q!("    adcs            " u5!() ", " u7!() ", " u5!()),
        Q!("    adcs            " u6!() ", " u6!() ", xzr"),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),

        // Add in the sign-adjusted complex term

        Q!("    adds            " "xzr, " sgn!() ", #1"),
        Q!("    eor             " m0!() ", " m0!() ", " sgn!()),
        Q!("    adcs            " u2!() ", " m0!() ", " u2!()),
        Q!("    eor             " m1!() ", " m1!() ", " sgn!()),
        Q!("    adcs            " u3!() ", " m1!() ", " u3!()),
        Q!("    eor             " m2!() ", " m2!() ", " sgn!()),
        Q!("    adcs            " u4!() ", " m2!() ", " u4!()),
        Q!("    eor             " m3!() ", " m3!() ", " sgn!()),
        Q!("    adcs            " u5!() ", " m3!() ", " u5!()),
        Q!("    adcs            " u6!() ", " u6!() ", " sgn!()),
        Q!("    adc             " u7!() ", " u7!() ", " sgn!()),

        // Now we have the full 8-digit product 2^256 * h + l where
        // h = [u7,u6,u5,u4] and l = [u3,u2,u1,u0]
        // and this is == 38 * h + l (mod p_25519).
        // We do the 38 * h + l using 32-bit multiplies avoiding umulh,
        // and pre-estimate and feed in the next-level quotient
        // q = h + 1 where h = an early version of the high 255 bits.
        // We add 2^255 * h - 19 * (h + 1), so end up offset by 2^255.

        Q!("    mov             " c!() ", #38"),

        Q!("    umull           " h!() ", " u4short!() ", " cshort!()),
        Q!("    add             " h!() ", " h!() ", " u0short!() ", uxtw"),
        Q!("    lsr             " u0!() ", " u0!() ", #32"),
        Q!("    lsr             " u4!() ", " u4!() ", #32"),
        Q!("    umaddl          " u4!() ", " u4short!() ", " cshort!() ", " u0!()),
        Q!("    mov             " u0!() ", " h!()),

        Q!("    umull           " h!() ", " u5short!() ", " cshort!()),
        Q!("    add             " h!() ", " h!() ", " u1short!() ", uxtw"),
        Q!("    lsr             " u1!() ", " u1!() ", #32"),
        Q!("    lsr             " u5!() ", " u5!() ", #32"),
        Q!("    umaddl          " u5!() ", " u5short!() ", " cshort!() ", " u1!()),
        Q!("    mov             " u1!() ", " h!()),

        Q!("    umull           " h!() ", " u6short!() ", " cshort!()),
        Q!("    add             " h!() ", " h!() ", " u2short!() ", uxtw"),
        Q!("    lsr             " u2!() ", " u2!() ", #32"),
        Q!("    lsr             " u6!() ", " u6!() ", #32"),
        Q!("    umaddl          " u6!() ", " u6short!() ", " cshort!() ", " u2!()),
        Q!("    mov             " u2!() ", " h!()),

        Q!("    umull           " h!() ", " u7short!() ", " cshort!()),
        Q!("    add             " h!() ", " h!() ", " u3short!() ", uxtw"),
        Q!("    lsr             " u3!() ", " u3!() ", #32"),
        Q!("    lsr             " u7!() ", " u7!() ", #32"),
        Q!("    umaddl          " u7!() ", " u7short!() ", " cshort!() ", " u3!()),
        Q!("    mov             " u3!() ", " h!()),

        Q!("    lsr             " q!() ", " u7!() ", #31"),

        Q!("    mov             " l!() ", #19"),
        Q!("    umaddl          " l!() ", " lshort!() ", " qshort!() ", " l!()),
        Q!("    add             " u0!() ", " u0!() ", " l!()),

        Q!("    adds            " u0!() ", " u0!() ", " u4!() ", lsl #32"),
        Q!("    extr            " c!() ", " u5!() ", " u4!() ", #32"),
        Q!("    adcs            " u1!() ", " u1!() ", " c!()),
        Q!("    extr            " c!() ", " u6!() ", " u5!() ", #32"),
        Q!("    adcs            " u2!() ", " u2!() ", " c!()),
        Q!("    extr            " c!() ", " u7!() ", " u6!() ", #32"),
        Q!("    lsl             " l!() ", " q!() ", #63"),
        Q!("    eor             " u3!() ", " u3!() ", " l!()),
        Q!("    adc             " u3!() ", " u3!() ", " c!()),

        // Now we correct by a final 2^255-19 if the top bit is clear
        // meaning that the "real" pre-reduced result is negative.

        Q!("    mov             " c!() ", #19"),
        Q!("    tst             " u3!() ", #0x8000000000000000"),
        Q!("    csel            " c!() ", " c!() ", xzr, pl"),
        Q!("    subs            " u0!() ", " u0!() ", " c!()),
        Q!("    sbcs            " u1!() ", " u1!() ", xzr"),
        Q!("    sbcs            " u2!() ", " u2!() ", xzr"),
        Q!("    sbc             " u3!() ", " u3!() ", xzr"),
        Q!("    and             " u3!() ", " u3!() ", # ~ 0x8000000000000000"),

        // Write back result

        Q!("    stp             " u0!() ", " u1!() ", [x0]"),
        Q!("    stp             " u2!() ", " u3!() ", [x0, #16]"),

        inout("x0") z.as_mut_ptr() => _,
        inout("x1") x.as_ptr() => _,
        inout("x2") y.as_ptr() => _,
        // clobbers
        out("x10") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x14") _,
        out("x15") _,
        out("x16") _,
        out("x17") _,
        out("x3") _,
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
        bignum_mul_p25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
