// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply-add modulo the order of the curve25519/edwards25519 basepoint
// Inputs x[4], y[4], c[4]; output z[4]
//
//    extern void bignum_madd_n25519(uint64_t z[static 4], const uint64_t x[static 4],
//                                   const uint64_t y[static 4],
//                                   const uint64_t c[static 4]);
//
// Performs z := (x * y + c) mod n_25519, where the modulus is
// n_25519 = 2^252 + 27742317777372353535851937790883648493, the
// order of the curve25519/edwards25519 basepoint. The result z
// and the inputs x, y and c are all 4 digits (256 bits).
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y, X3 = c
// ----------------------------------------------------------------------------

// Backup of the input pointer so we can modify x0

macro_rules! z {
    () => {
        "x19"
    };
}

// Temporaries for reduction phase

macro_rules! q {
    () => {
        "x2"
    };
}
macro_rules! n0 {
    () => {
        "x3"
    };
}
macro_rules! n1 {
    () => {
        "x4"
    };
}
macro_rules! t0 {
    () => {
        "x5"
    };
}
macro_rules! t1 {
    () => {
        "x6"
    };
}
macro_rules! t2 {
    () => {
        "x7"
    };
}

// Loading large constants

macro_rules! movbig {
    ($nn:expr, $n3:expr, $n2:expr, $n1:expr, $n0:expr) => { Q!(
        "movz " $nn ", " $n0 ";\n"
        "movk " $nn ", " $n1 ", lsl #16;\n"
        "movk " $nn ", " $n2 ", lsl #32;\n"
        "movk " $nn ", " $n3 ", lsl #48"
    )}
}

// Single round of modular reduction mod_n25519, mapping
// [m4;m3;m2;m1;m0] = m to [m3;m2;m1;m0] = m mod n_25519,
// *assuming* the input m < 2^64 * n_25519. This is very
// close to the loop body of the bignum_mod_n25519 function.

macro_rules! reduce {
    ($m4:expr, $m3:expr, $m2:expr, $m1:expr, $m0:expr) => { Q!(
        "extr " q!() ", " $m4 ", " $m3 ", #60;\n"
        "and " $m3 ", " $m3 ", #0x0FFFFFFFFFFFFFFF;\n"
        "sub " q!() ", " q!() ", " $m4 ", lsr #60;\n"
        "and " t0!() ", " $m4 ", #0xF000000000000000;\n"
        "add " $m3 ", " $m3 ", " t0!() ";\n"
        "mul " t0!() ", " n0!() ", " q!() ";\n"
        "mul " t1!() ", " n1!() ", " q!() ";\n"
        "umulh " t2!() ", " n0!() ", " q!() ";\n"
        "adds " t1!() ", " t1!() ", " t2!() ";\n"
        "umulh " t2!() ", " n1!() ", " q!() ";\n"
        "adc " t2!() ", " t2!() ", xzr;\n"
        "subs " $m0 ", " $m0 ", " t0!() ";\n"
        "sbcs " $m1 ", " $m1 ", " t1!() ";\n"
        "sbcs " $m2 ", " $m2 ", " t2!() ";\n"
        "sbcs " $m3 ", " $m3 ", xzr;\n"
        "csel " t0!() ", " n0!() ", xzr, cc;\n"
        "csel " t1!() ", " n1!() ", xzr, cc;\n"
        "adds " $m0 ", " $m0 ", " t0!() ";\n"
        "and " t2!() ", " t0!() ", #0x1000000000000000;\n"
        "adcs " $m1 ", " $m1 ", " t1!() ";\n"
        "adcs " $m2 ", " $m2 ", xzr;\n"
        "adc " $m3 ", " $m3 ", " t2!()
    )}
}

// Special case of "reduce" with m4 = 0. As well as not using m4,
// the quotient selection is slightly simpler, just floor(m/2^252)
// versus min (floor(m/2^252)) (2^63-1).

macro_rules! reduce0 {
    ($m3:expr, $m2:expr, $m1:expr, $m0:expr) => { Q!(
        "lsr " q!() ", " $m3 ", #60;\n"
        "and " $m3 ", " $m3 ", #0x0FFFFFFFFFFFFFFF;\n"
        "mul " t0!() ", " n0!() ", " q!() ";\n"
        "mul " t1!() ", " n1!() ", " q!() ";\n"
        "umulh " t2!() ", " n0!() ", " q!() ";\n"
        "adds " t1!() ", " t1!() ", " t2!() ";\n"
        "umulh " t2!() ", " n1!() ", " q!() ";\n"
        "adc " t2!() ", " t2!() ", xzr;\n"
        "subs " $m0 ", " $m0 ", " t0!() ";\n"
        "sbcs " $m1 ", " $m1 ", " t1!() ";\n"
        "sbcs " $m2 ", " $m2 ", " t2!() ";\n"
        "sbcs " $m3 ", " $m3 ", xzr;\n"
        "csel " t0!() ", " n0!() ", xzr, cc;\n"
        "csel " t1!() ", " n1!() ", xzr, cc;\n"
        "adds " $m0 ", " $m0 ", " t0!() ";\n"
        "and " t2!() ", " t0!() ", #0x1000000000000000;\n"
        "adcs " $m1 ", " $m1 ", " t1!() ";\n"
        "adcs " $m2 ", " $m2 ", xzr;\n"
        "adc " $m3 ", " $m3 ", " t2!()
    )}
}

// Transliterated from s2n-bignum's arm/curve25519/bignum_madd_n25519.S.
/// Multiply-add modulo the order of the curve25519/edwards25519 basepoint
///
/// Inputs x[4], y[4], c[4]; output z[4]
///
/// Performs z := (x * y + c) mod n_25519, where the modulus is
/// n_25519 = 2^252 + 27742317777372353535851937790883648493, the
/// order of the curve25519/edwards25519 basepoint. The result z
/// and the inputs x, y and c are all 4 digits (256 bits).
#[inline(never)]
pub(crate) fn bignum_madd_n25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4], c: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    stp             " "x19, x20, [sp, #-16] !"),

        // Back up the result pointer so we can overwrite x0 in intermediate steps

        Q!("    mov             " z!() ", x0"),

        // First compute [x15;x14;x13;x12;x11;x10;x9;x8] = x * y. This is
        // a basic 2-level Karatsuba multiplier, similar to the start of
        // bignum_mul_p25519, but with changes to the register allocation,
        // which in particular preserve x3/w3 for the next step.

        Q!("    ldp             " "x0, x4, [x1]"),
        Q!("    ldp             " "x5, x6, [x2]"),
        Q!("    umull           " "x8, w0, w5"),
        Q!("    lsr             " "x17, x0, #32"),
        Q!("    umull           " "x7, w17, w5"),
        Q!("    lsr             " "x16, x5, #32"),
        Q!("    umull           " "x9, w16, w17"),
        Q!("    umull           " "x16, w0, w16"),
        Q!("    adds            " "x8, x8, x7, lsl #32"),
        Q!("    lsr             " "x7, x7, #32"),
        Q!("    adc             " "x9, x9, x7"),
        Q!("    adds            " "x8, x8, x16, lsl #32"),
        Q!("    lsr             " "x16, x16, #32"),
        Q!("    adc             " "x9, x9, x16"),
        Q!("    mul             " "x10, x4, x6"),
        Q!("    umulh           " "x11, x4, x6"),
        Q!("    subs            " "x4, x4, x0"),
        Q!("    cneg            " "x4, x4, cc"),
        Q!("    csetm           " "x16, cc"),
        Q!("    adds            " "x10, x10, x9"),
        Q!("    adc             " "x11, x11, xzr"),
        Q!("    subs            " "x0, x5, x6"),
        Q!("    cneg            " "x0, x0, cc"),
        Q!("    cinv            " "x16, x16, cc"),
        Q!("    mul             " "x7, x4, x0"),
        Q!("    umulh           " "x0, x4, x0"),
        Q!("    adds            " "x9, x8, x10"),
        Q!("    adcs            " "x10, x10, x11"),
        Q!("    adc             " "x11, x11, xzr"),
        Q!("    cmn             " "x16, #0x1"),
        Q!("    eor             " "x7, x7, x16"),
        Q!("    adcs            " "x9, x7, x9"),
        Q!("    eor             " "x0, x0, x16"),
        Q!("    adcs            " "x10, x0, x10"),
        Q!("    adc             " "x11, x11, x16"),
        Q!("    ldp             " "x0, x4, [x1, #16]"),
        Q!("    ldp             " "x5, x6, [x2, #16]"),
        Q!("    umull           " "x12, w0, w5"),
        Q!("    lsr             " "x17, x0, #32"),
        Q!("    umull           " "x7, w17, w5"),
        Q!("    lsr             " "x16, x5, #32"),
        Q!("    umull           " "x13, w16, w17"),
        Q!("    umull           " "x16, w0, w16"),
        Q!("    adds            " "x12, x12, x7, lsl #32"),
        Q!("    lsr             " "x7, x7, #32"),
        Q!("    adc             " "x13, x13, x7"),
        Q!("    adds            " "x12, x12, x16, lsl #32"),
        Q!("    lsr             " "x16, x16, #32"),
        Q!("    adc             " "x13, x13, x16"),
        Q!("    mul             " "x14, x4, x6"),
        Q!("    umulh           " "x15, x4, x6"),
        Q!("    subs            " "x4, x4, x0"),
        Q!("    cneg            " "x4, x4, cc"),
        Q!("    csetm           " "x16, cc"),
        Q!("    adds            " "x14, x14, x13"),
        Q!("    adc             " "x15, x15, xzr"),
        Q!("    subs            " "x0, x5, x6"),
        Q!("    cneg            " "x0, x0, cc"),
        Q!("    cinv            " "x16, x16, cc"),
        Q!("    mul             " "x7, x4, x0"),
        Q!("    umulh           " "x0, x4, x0"),
        Q!("    adds            " "x13, x12, x14"),
        Q!("    adcs            " "x14, x14, x15"),
        Q!("    adc             " "x15, x15, xzr"),
        Q!("    cmn             " "x16, #0x1"),
        Q!("    eor             " "x7, x7, x16"),
        Q!("    adcs            " "x13, x7, x13"),
        Q!("    eor             " "x0, x0, x16"),
        Q!("    adcs            " "x14, x0, x14"),
        Q!("    adc             " "x15, x15, x16"),
        Q!("    ldp             " "x0, x4, [x1, #16]"),
        Q!("    ldp             " "x7, x16, [x1]"),
        Q!("    subs            " "x0, x0, x7"),
        Q!("    sbcs            " "x4, x4, x16"),
        Q!("    csetm           " "x16, cc"),
        Q!("    ldp             " "x7, x17, [x2]"),
        Q!("    subs            " "x5, x7, x5"),
        Q!("    sbcs            " "x6, x17, x6"),
        Q!("    csetm           " "x17, cc"),
        Q!("    eor             " "x0, x0, x16"),
        Q!("    subs            " "x0, x0, x16"),
        Q!("    eor             " "x4, x4, x16"),
        Q!("    sbc             " "x4, x4, x16"),
        Q!("    eor             " "x5, x5, x17"),
        Q!("    subs            " "x5, x5, x17"),
        Q!("    eor             " "x6, x6, x17"),
        Q!("    sbc             " "x6, x6, x17"),
        Q!("    eor             " "x16, x17, x16"),
        Q!("    adds            " "x12, x12, x10"),
        Q!("    adcs            " "x13, x13, x11"),
        Q!("    adcs            " "x14, x14, xzr"),
        Q!("    adc             " "x15, x15, xzr"),
        Q!("    mul             " "x2, x0, x5"),
        Q!("    umulh           " "x17, x0, x5"),
        Q!("    mul             " "x7, x4, x6"),
        Q!("    umulh           " "x1, x4, x6"),
        Q!("    subs            " "x4, x4, x0"),
        Q!("    cneg            " "x4, x4, cc"),
        Q!("    csetm           " "x10, cc"),
        Q!("    adds            " "x7, x7, x17"),
        Q!("    adc             " "x1, x1, xzr"),
        Q!("    subs            " "x6, x5, x6"),
        Q!("    cneg            " "x6, x6, cc"),
        Q!("    cinv            " "x10, x10, cc"),
        Q!("    mul             " "x5, x4, x6"),
        Q!("    umulh           " "x6, x4, x6"),
        Q!("    adds            " "x17, x2, x7"),
        Q!("    adcs            " "x7, x7, x1"),
        Q!("    adc             " "x1, x1, xzr"),
        Q!("    cmn             " "x10, #0x1"),
        Q!("    eor             " "x5, x5, x10"),
        Q!("    adcs            " "x17, x5, x17"),
        Q!("    eor             " "x6, x6, x10"),
        Q!("    adcs            " "x7, x6, x7"),
        Q!("    adc             " "x1, x1, x10"),
        Q!("    adds            " "x10, x12, x8"),
        Q!("    adcs            " "x11, x13, x9"),
        Q!("    adcs            " "x12, x14, x12"),
        Q!("    adcs            " "x13, x15, x13"),
        Q!("    adcs            " "x14, x14, xzr"),
        Q!("    adc             " "x15, x15, xzr"),
        Q!("    cmn             " "x16, #0x1"),
        Q!("    eor             " "x2, x2, x16"),
        Q!("    adcs            " "x10, x2, x10"),
        Q!("    eor             " "x17, x17, x16"),
        Q!("    adcs            " "x11, x17, x11"),
        Q!("    eor             " "x7, x7, x16"),
        Q!("    adcs            " "x12, x7, x12"),
        Q!("    eor             " "x1, x1, x16"),
        Q!("    adcs            " "x13, x1, x13"),
        Q!("    adcs            " "x14, x14, x16"),
        Q!("    adc             " "x15, x15, x16"),

        // Add the constant term, so [x15;x14;x13;x12;x11;x10;x9;x8] = x * y + c
        // It's easier to just do this now versus incorporating it into the
        // Karatsuba steps above or deferring it until partway through the
        // reduction, though it does result in a long carry propagation here.

        Q!("    ldp             " "x0, x1, [x3]"),
        Q!("    adds            " "x8, x8, x0"),
        Q!("    adcs            " "x9, x9, x1"),
        Q!("    ldp             " "x0, x1, [x3, #16]"),
        Q!("    adcs            " "x10, x10, x0"),
        Q!("    adcs            " "x11, x11, x1"),
        Q!("    adcs            " "x12, x12, xzr"),
        Q!("    adcs            " "x13, x13, xzr"),
        Q!("    adcs            " "x14, x14, xzr"),
        Q!("    adc             " "x15, x15, xzr"),

        // Now do the modular reduction and write back

        movbig!(n0!(), "#0x5812", "#0x631a", "#0x5cf5", "#0xd3ed"),
        movbig!(n1!(), "#0x14de", "#0xf9de", "#0xa2f7", "#0x9cd6"),

        reduce0!("x15", "x14", "x13", "x12"),
        reduce!("x15", "x14", "x13", "x12", "x11"),
        reduce!("x14", "x13", "x12", "x11", "x10"),
        reduce!("x13", "x12", "x11", "x10", "x9"),
        reduce!("x12", "x11", "x10", "x9", "x8"),

        Q!("    stp             " "x8, x9, [" z!() "]"),
        Q!("    stp             " "x10, x11, [" z!() ", #16]"),

        // Restore registers and return

        Q!("    ldp             " "x19, x20, [sp], #16"),
        inout("x0") z.as_mut_ptr() => _,
        inout("x1") x.as_ptr() => _,
        inout("x2") y.as_ptr() => _,
        inout("x3") c.as_ptr() => _,
        // clobbers
        out("x10") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x14") _,
        out("x15") _,
        out("x16") _,
        out("x17") _,
        out("x20") _,
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
        bignum_madd_n25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
