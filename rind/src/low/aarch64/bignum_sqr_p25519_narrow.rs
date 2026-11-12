// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square modulo p_25519, z := (x^2) mod p_25519
// Input x[4]; output z[4]
//
//    extern void bignum_sqr_p25519(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x
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

// Variables

macro_rules! u0 {
    () => {
        "x2"
    };
}
macro_rules! u1 {
    () => {
        "x3"
    };
}
macro_rules! u2 {
    () => {
        "x4"
    };
}
macro_rules! u3 {
    () => {
        "x5"
    };
}
macro_rules! u4 {
    () => {
        "x6"
    };
}
macro_rules! u5 {
    () => {
        "x7"
    };
}
macro_rules! u6 {
    () => {
        "x8"
    };
}
macro_rules! u7 {
    () => {
        "x9"
    };
}

macro_rules! u0short {
    () => {
        "w2"
    };
}
macro_rules! u1short {
    () => {
        "w3"
    };
}
macro_rules! u2short {
    () => {
        "w4"
    };
}
macro_rules! u3short {
    () => {
        "w5"
    };
}
macro_rules! u4short {
    () => {
        "w6"
    };
}
macro_rules! u5short {
    () => {
        "w7"
    };
}
macro_rules! u6short {
    () => {
        "w8"
    };
}
macro_rules! u7short {
    () => {
        "w9"
    };
}

macro_rules! c {
    () => {
        "x10"
    };
}
macro_rules! cshort {
    () => {
        "w10"
    };
}
macro_rules! l {
    () => {
        "x11"
    };
}
macro_rules! lshort {
    () => {
        "w11"
    };
}
macro_rules! h {
    () => {
        "x12"
    };
}
macro_rules! hshort {
    () => {
        "w12"
    };
}
macro_rules! q {
    () => {
        "x13"
    };
}
macro_rules! qshort {
    () => {
        "w13"
    };
}

macro_rules! t1 {
    () => {
        "x14"
    };
}
macro_rules! t1short {
    () => {
        "w14"
    };
}
macro_rules! t2 {
    () => {
        "x15"
    };
}
macro_rules! t2short {
    () => {
        "w15"
    };
}
macro_rules! t3 {
    () => {
        "x16"
    };
}
macro_rules! t3short {
    () => {
        "w16"
    };
}

// Transliterated from s2n-bignum's arm/curve25519/bignum_sqr_p25519.S.
/// Square modulo p_25519, z := (x^2) mod p_25519
///
/// Input x[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_sqr_p25519(z: &mut [u64; 4], x: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // First just a near-clone of bignum_sqr_4_8 to get the square, using
        // different registers to collect full product without writeback.

        Q!("    ldp             " c!() ", " l!() ", [" x!() "]"),
        Q!("    ldp             " h!() ", " q!() ", [" x!() ", #16]"),
        Q!("    umull           " u0!() ", " cshort!() ", " cshort!()),
        Q!("    lsr             " t1!() ", " c!() ", #32"),
        Q!("    umull           " u1!() ", " t1short!() ", " t1short!()),
        Q!("    umull           " t1!() ", " cshort!() ", " t1short!()),
        Q!("    adds            " u0!() ", " u0!() ", " t1!() ", lsl #33"),
        Q!("    lsr             " t1!() ", " t1!() ", #31"),
        Q!("    adc             " u1!() ", " u1!() ", " t1!()),
        Q!("    umull           " u2!() ", " lshort!() ", " lshort!()),
        Q!("    lsr             " t1!() ", " l!() ", #32"),
        Q!("    umull           " u3!() ", " t1short!() ", " t1short!()),
        Q!("    umull           " t1!() ", " lshort!() ", " t1short!()),
        Q!("    mul             " t2!() ", " c!() ", " l!()),
        Q!("    umulh           " t3!() ", " c!() ", " l!()),
        Q!("    adds            " u2!() ", " u2!() ", " t1!() ", lsl #33"),
        Q!("    lsr             " t1!() ", " t1!() ", #31"),
        Q!("    adc             " u3!() ", " u3!() ", " t1!()),
        Q!("    adds            " t2!() ", " t2!() ", " t2!()),
        Q!("    adcs            " t3!() ", " t3!() ", " t3!()),
        Q!("    adc             " u3!() ", " u3!() ", xzr"),
        Q!("    adds            " u1!() ", " u1!() ", " t2!()),
        Q!("    adcs            " u2!() ", " u2!() ", " t3!()),
        Q!("    adc             " u3!() ", " u3!() ", xzr"),
        Q!("    umull           " u4!() ", " hshort!() ", " hshort!()),
        Q!("    lsr             " t1!() ", " h!() ", #32"),
        Q!("    umull           " u5!() ", " t1short!() ", " t1short!()),
        Q!("    umull           " t1!() ", " hshort!() ", " t1short!()),
        Q!("    adds            " u4!() ", " u4!() ", " t1!() ", lsl #33"),
        Q!("    lsr             " t1!() ", " t1!() ", #31"),
        Q!("    adc             " u5!() ", " u5!() ", " t1!()),
        Q!("    umull           " u6!() ", " qshort!() ", " qshort!()),
        Q!("    lsr             " t1!() ", " q!() ", #32"),
        Q!("    umull           " u7!() ", " t1short!() ", " t1short!()),
        Q!("    umull           " t1!() ", " qshort!() ", " t1short!()),
        Q!("    mul             " t2!() ", " h!() ", " q!()),
        Q!("    umulh           " t3!() ", " h!() ", " q!()),
        Q!("    adds            " u6!() ", " u6!() ", " t1!() ", lsl #33"),
        Q!("    lsr             " t1!() ", " t1!() ", #31"),
        Q!("    adc             " u7!() ", " u7!() ", " t1!()),
        Q!("    adds            " t2!() ", " t2!() ", " t2!()),
        Q!("    adcs            " t3!() ", " t3!() ", " t3!()),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),
        Q!("    adds            " u5!() ", " u5!() ", " t2!()),
        Q!("    adcs            " u6!() ", " u6!() ", " t3!()),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),
        Q!("    subs            " c!() ", " c!() ", " h!()),
        Q!("    sbcs            " l!() ", " l!() ", " q!()),
        Q!("    csetm           " t3!() ", cc"),
        Q!("    eor             " c!() ", " c!() ", " t3!()),
        Q!("    subs            " c!() ", " c!() ", " t3!()),
        Q!("    eor             " l!() ", " l!() ", " t3!()),
        Q!("    sbc             " l!() ", " l!() ", " t3!()),
        Q!("    adds            " u4!() ", " u4!() ", " u2!()),
        Q!("    adcs            " u5!() ", " u5!() ", " u3!()),
        Q!("    adcs            " u6!() ", " u6!() ", xzr"),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),
        Q!("    umull           " h!() ", " cshort!() ", " cshort!()),
        Q!("    lsr             " u3!() ", " c!() ", #32"),
        Q!("    umull           " q!() ", " u3short!() ", " u3short!()),
        Q!("    umull           " u3!() ", " cshort!() ", " u3short!()),
        Q!("    adds            " h!() ", " h!() ", " u3!() ", lsl #33"),
        Q!("    lsr             " u3!() ", " u3!() ", #31"),
        Q!("    adc             " q!() ", " q!() ", " u3!()),
        Q!("    umull           " t2!() ", " lshort!() ", " lshort!()),
        Q!("    lsr             " u3!() ", " l!() ", #32"),
        Q!("    umull           " t1!() ", " u3short!() ", " u3short!()),
        Q!("    umull           " u3!() ", " lshort!() ", " u3short!()),
        Q!("    mul             " u2!() ", " c!() ", " l!()),
        Q!("    umulh           " t3!() ", " c!() ", " l!()),
        Q!("    adds            " t2!() ", " t2!() ", " u3!() ", lsl #33"),
        Q!("    lsr             " u3!() ", " u3!() ", #31"),
        Q!("    adc             " t1!() ", " t1!() ", " u3!()),
        Q!("    adds            " u2!() ", " u2!() ", " u2!()),
        Q!("    adcs            " t3!() ", " t3!() ", " t3!()),
        Q!("    adc             " t1!() ", " t1!() ", xzr"),
        Q!("    adds            " q!() ", " q!() ", " u2!()),
        Q!("    adcs            " t2!() ", " t2!() ", " t3!()),
        Q!("    adc             " t1!() ", " t1!() ", xzr"),
        Q!("    adds            " u2!() ", " u0!() ", " u4!()),
        Q!("    adcs            " u3!() ", " u1!() ", " u5!()),
        Q!("    adcs            " u4!() ", " u4!() ", " u6!()),
        Q!("    adcs            " u5!() ", " u5!() ", " u7!()),
        Q!("    csetm           " t3!() ", cc"),
        Q!("    subs            " u2!() ", " u2!() ", " h!()),
        Q!("    sbcs            " u3!() ", " u3!() ", " q!()),
        Q!("    sbcs            " u4!() ", " u4!() ", " t2!()),
        Q!("    sbcs            " u5!() ", " u5!() ", " t1!()),
        Q!("    adcs            " u6!() ", " u6!() ", " t3!()),
        Q!("    adc             " u7!() ", " u7!() ", " t3!()),

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
        // clobbers
        out("x10") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x14") _,
        out("x15") _,
        out("x16") _,
        out("x2") _,
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
        bignum_sqr_p25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
