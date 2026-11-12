// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Projective doubling for edwards25519
// Input p1[12]; output p3[12]
//
// extern void edwards25519_pdouble_alt
//   (uint64_t p3[static 12],const uint64_t p1[static 12]);
//
// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
// Input and output are in pure projective coordinates, representing
// an affine (x,y) by a triple (X,Y,Z) where x = X / Z, y = Y / Z.
//
// Standard ARM ABI: X0 = p3, X1 = p1
// ----------------------------------------------------------------------------

// Size of individual field elements

macro_rules! NUMSIZE {
    () => {
        "32"
    };
}

// Stable homes for input arguments during main code sequence

macro_rules! p3 {
    () => {
        "x17"
    };
}
macro_rules! p1 {
    () => {
        "x19"
    };
}

// Pointers to input and output coordinates

macro_rules! x_1 { () => { Q!(p1!() ", #0") } }
macro_rules! y_1 { () => { Q!(p1!() ", # " NUMSIZE!()) } }
macro_rules! z_1 { () => { Q!(p1!() ", # (2 * " NUMSIZE!() ")") } }

macro_rules! x_3 { () => { Q!(p3!() ", #0") } }
macro_rules! y_3 { () => { Q!(p3!() ", # " NUMSIZE!()) } }
macro_rules! z_3 { () => { Q!(p3!() ", # (2 * " NUMSIZE!() ")") } }

// Pointer-offset pairs for temporaries on stack

macro_rules! t0 { () => { Q!("sp, # (0 * " NUMSIZE!() ")") } }
macro_rules! t1 { () => { Q!("sp, # (1 * " NUMSIZE!() ")") } }
macro_rules! t2 { () => { Q!("sp, # (2 * " NUMSIZE!() ")") } }
macro_rules! t3 { () => { Q!("sp, # (3 * " NUMSIZE!() ")") } }
macro_rules! t4 { () => { Q!("sp, # (4 * " NUMSIZE!() ")") } }

// Total size to reserve on the stack

macro_rules! NSPACE { () => { Q!("5 * " NUMSIZE!()) } }

// Macro wrapping up the basic field operation bignum_mul_p25519_alt, only
// trivially different from a pure function call to that subroutine.

macro_rules! mul_p25519 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "ldp x3, x4, [" $P1 "];\n"
        "ldp x7, x8, [" $P2 "];\n"
        "mul x12, x3, x7;\n"
        "umulh x13, x3, x7;\n"
        "mul x11, x3, x8;\n"
        "umulh x14, x3, x8;\n"
        "adds x13, x13, x11;\n"
        "ldp x9, x10, [" $P2 "+ 16];\n"
        "mul x11, x3, x9;\n"
        "umulh x15, x3, x9;\n"
        "adcs x14, x14, x11;\n"
        "mul x11, x3, x10;\n"
        "umulh x16, x3, x10;\n"
        "adcs x15, x15, x11;\n"
        "adc x16, x16, xzr;\n"
        "ldp x5, x6, [" $P1 "+ 16];\n"
        "mul x11, x4, x7;\n"
        "adds x13, x13, x11;\n"
        "mul x11, x4, x8;\n"
        "adcs x14, x14, x11;\n"
        "mul x11, x4, x9;\n"
        "adcs x15, x15, x11;\n"
        "mul x11, x4, x10;\n"
        "adcs x16, x16, x11;\n"
        "umulh x3, x4, x10;\n"
        "adc x3, x3, xzr;\n"
        "umulh x11, x4, x7;\n"
        "adds x14, x14, x11;\n"
        "umulh x11, x4, x8;\n"
        "adcs x15, x15, x11;\n"
        "umulh x11, x4, x9;\n"
        "adcs x16, x16, x11;\n"
        "adc x3, x3, xzr;\n"
        "mul x11, x5, x7;\n"
        "adds x14, x14, x11;\n"
        "mul x11, x5, x8;\n"
        "adcs x15, x15, x11;\n"
        "mul x11, x5, x9;\n"
        "adcs x16, x16, x11;\n"
        "mul x11, x5, x10;\n"
        "adcs x3, x3, x11;\n"
        "umulh x4, x5, x10;\n"
        "adc x4, x4, xzr;\n"
        "umulh x11, x5, x7;\n"
        "adds x15, x15, x11;\n"
        "umulh x11, x5, x8;\n"
        "adcs x16, x16, x11;\n"
        "umulh x11, x5, x9;\n"
        "adcs x3, x3, x11;\n"
        "adc x4, x4, xzr;\n"
        "mul x11, x6, x7;\n"
        "adds x15, x15, x11;\n"
        "mul x11, x6, x8;\n"
        "adcs x16, x16, x11;\n"
        "mul x11, x6, x9;\n"
        "adcs x3, x3, x11;\n"
        "mul x11, x6, x10;\n"
        "adcs x4, x4, x11;\n"
        "umulh x5, x6, x10;\n"
        "adc x5, x5, xzr;\n"
        "umulh x11, x6, x7;\n"
        "adds x16, x16, x11;\n"
        "umulh x11, x6, x8;\n"
        "adcs x3, x3, x11;\n"
        "umulh x11, x6, x9;\n"
        "adcs x4, x4, x11;\n"
        "adc x5, x5, xzr;\n"
        "mov x7, #0x26;\n"
        "mul x11, x7, x16;\n"
        "umulh x9, x7, x16;\n"
        "adds x12, x12, x11;\n"
        "mul x11, x7, x3;\n"
        "umulh x3, x7, x3;\n"
        "adcs x13, x13, x11;\n"
        "mul x11, x7, x4;\n"
        "umulh x4, x7, x4;\n"
        "adcs x14, x14, x11;\n"
        "mul x11, x7, x5;\n"
        "umulh x5, x7, x5;\n"
        "adcs x15, x15, x11;\n"
        "cset x16, cs;\n"
        "adds x15, x15, x4;\n"
        "adc x16, x16, x5;\n"
        "cmn x15, x15;\n"
        "orr x15, x15, #0x8000000000000000;\n"
        "adc x8, x16, x16;\n"
        "mov x7, #0x13;\n"
        "madd x11, x7, x8, x7;\n"
        "adds x12, x12, x11;\n"
        "adcs x13, x13, x9;\n"
        "adcs x14, x14, x3;\n"
        "adcs x15, x15, xzr;\n"
        "csel x7, x7, xzr, cc;\n"
        "subs x12, x12, x7;\n"
        "sbcs x13, x13, xzr;\n"
        "sbcs x14, x14, xzr;\n"
        "sbc x15, x15, xzr;\n"
        "and x15, x15, #0x7fffffffffffffff;\n"
        "stp x12, x13, [" $P0 "];\n"
        "stp x14, x15, [" $P0 "+ 16]"
    )}
}

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

macro_rules! sqr_4 {
    ($P0:expr, $P1:expr) => { Q!(
        "ldp x2, x3, [" $P1 "];\n"
        "mul x9, x2, x3;\n"
        "umulh x10, x2, x3;\n"
        "ldp x4, x5, [" $P1 "+ 16];\n"
        "mul x11, x2, x5;\n"
        "umulh x12, x2, x5;\n"
        "mul x7, x2, x4;\n"
        "umulh x6, x2, x4;\n"
        "adds x10, x10, x7;\n"
        "adcs x11, x11, x6;\n"
        "mul x7, x3, x4;\n"
        "umulh x6, x3, x4;\n"
        "adc x6, x6, xzr;\n"
        "adds x11, x11, x7;\n"
        "mul x13, x4, x5;\n"
        "umulh x14, x4, x5;\n"
        "adcs x12, x12, x6;\n"
        "mul x7, x3, x5;\n"
        "umulh x6, x3, x5;\n"
        "adc x6, x6, xzr;\n"
        "adds x12, x12, x7;\n"
        "adcs x13, x13, x6;\n"
        "adc x14, x14, xzr;\n"
        "adds x9, x9, x9;\n"
        "adcs x10, x10, x10;\n"
        "adcs x11, x11, x11;\n"
        "adcs x12, x12, x12;\n"
        "adcs x13, x13, x13;\n"
        "adcs x14, x14, x14;\n"
        "cset x6, cs;\n"
        "umulh x7, x2, x2;\n"
        "mul x8, x2, x2;\n"
        "adds x9, x9, x7;\n"
        "mul x7, x3, x3;\n"
        "adcs x10, x10, x7;\n"
        "umulh x7, x3, x3;\n"
        "adcs x11, x11, x7;\n"
        "mul x7, x4, x4;\n"
        "adcs x12, x12, x7;\n"
        "umulh x7, x4, x4;\n"
        "adcs x13, x13, x7;\n"
        "mul x7, x5, x5;\n"
        "adcs x14, x14, x7;\n"
        "umulh x7, x5, x5;\n"
        "adc x6, x6, x7;\n"
        "mov x3, #0x26;\n"
        "mul x7, x3, x12;\n"
        "umulh x4, x3, x12;\n"
        "adds x8, x8, x7;\n"
        "mul x7, x3, x13;\n"
        "umulh x13, x3, x13;\n"
        "adcs x9, x9, x7;\n"
        "mul x7, x3, x14;\n"
        "umulh x14, x3, x14;\n"
        "adcs x10, x10, x7;\n"
        "mul x7, x3, x6;\n"
        "umulh x6, x3, x6;\n"
        "adcs x11, x11, x7;\n"
        "cset x12, cs;\n"
        "adds x11, x11, x14;\n"
        "adc x12, x12, x6;\n"
        "cmn x11, x11;\n"
        "bic x11, x11, #0x8000000000000000;\n"
        "adc x2, x12, x12;\n"
        "mov x3, #0x13;\n"
        "mul x7, x3, x2;\n"
        "adds x8, x8, x7;\n"
        "adcs x9, x9, x4;\n"
        "adcs x10, x10, x13;\n"
        "adc x11, x11, xzr;\n"
        "stp x8, x9, [" $P0 "];\n"
        "stp x10, x11, [" $P0 "+ 16]"
    )}
}

// Plain 4-digit adding without any normalization.
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result,
// indeed one < 2 * p_25519 for normalized inputs.

macro_rules! add_4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "ldp x0, x1, [" $P1 "];\n"
        "ldp x4, x5, [" $P2 "];\n"
        "adds x0, x0, x4;\n"
        "adcs x1, x1, x5;\n"
        "ldp x2, x3, [" $P1 "+ 16];\n"
        "ldp x6, x7, [" $P2 "+ 16];\n"
        "adcs x2, x2, x6;\n"
        "adc x3, x3, x7;\n"
        "stp x0, x1, [" $P0 "];\n"
        "stp x2, x3, [" $P0 "+ 16]"
    )}
}

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

macro_rules! sub_twice4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "ldp x5, x6, [" $P1 "];\n"
        "ldp x4, x3, [" $P2 "];\n"
        "subs x5, x5, x4;\n"
        "sbcs x6, x6, x3;\n"
        "ldp x7, x8, [" $P1 "+ 16];\n"
        "ldp x4, x3, [" $P2 "+ 16];\n"
        "sbcs x7, x7, x4;\n"
        "sbcs x8, x8, x3;\n"
        "mov x4, #38;\n"
        "csel x3, x4, xzr, lo;\n"
        "subs x5, x5, x3;\n"
        "sbcs x6, x6, xzr;\n"
        "sbcs x7, x7, xzr;\n"
        "sbc x8, x8, xzr;\n"
        "stp x5, x6, [" $P0 "];\n"
        "stp x7, x8, [" $P0 "+ 16]"
    )}
}

// Modular addition and doubling with double modulus 2 * p_25519 = 2^256 - 38.
// This only ensures that the result fits in 4 digits, not that it is reduced
// even w.r.t. double modulus. The result is always correct modulo provided
// the sum of the inputs is < 2^256 + 2^256 - 38, so in particular provided
// at least one of them is reduced double modulo.

macro_rules! add_twice4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "ldp x3, x4, [" $P1 "];\n"
        "ldp x7, x8, [" $P2 "];\n"
        "adds x3, x3, x7;\n"
        "adcs x4, x4, x8;\n"
        "ldp x5, x6, [" $P1 "+ 16];\n"
        "ldp x7, x8, [" $P2 "+ 16];\n"
        "adcs x5, x5, x7;\n"
        "adcs x6, x6, x8;\n"
        "mov x9, #38;\n"
        "csel x9, x9, xzr, cs;\n"
        "adds x3, x3, x9;\n"
        "adcs x4, x4, xzr;\n"
        "adcs x5, x5, xzr;\n"
        "adc x6, x6, xzr;\n"
        "stp x3, x4, [" $P0 "];\n"
        "stp x5, x6, [" $P0 "+ 16]"
    )}
}

macro_rules! double_twice4 {
    ($P0:expr, $P1:expr) => { Q!(
        "ldp x3, x4, [" $P1 "];\n"
        "adds x3, x3, x3;\n"
        "adcs x4, x4, x4;\n"
        "ldp x5, x6, [" $P1 "+ 16];\n"
        "adcs x5, x5, x5;\n"
        "adcs x6, x6, x6;\n"
        "mov x9, #38;\n"
        "csel x9, x9, xzr, cs;\n"
        "adds x3, x3, x9;\n"
        "adcs x4, x4, xzr;\n"
        "adcs x5, x5, xzr;\n"
        "adc x6, x6, xzr;\n"
        "stp x3, x4, [" $P0 "];\n"
        "stp x5, x6, [" $P0 "+ 16]"
    )}
}

// Transliterated from s2n-bignum's arm/curve25519/edwards25519_pdouble_alt.S.
/// Projective doubling for edwards25519
///
/// Input p1[12]; output p3[12]
///
/// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
/// Input and output are in pure projective coordinates, representing
/// an affine (x,y) by a triple (X,Y,Z) where x = X / Z, y = Y / Z.
#[inline(never)]
pub(crate) fn edwards25519_pdouble(p3: &mut [u64; 12], p1: &[u64; 12]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Save regs and make room for temporaries

        Q!("    stp             " "x19, x20, [sp, #-16] !"),
        Q!("    sub             " "sp, sp, # (" NSPACE!() "+ 0)"),

        // Move the input arguments to stable places

        Q!("    mov             " p3!() ", x0"),
        Q!("    mov             " p1!() ", x1"),

        // Main sequence

        add_4!(t0!(), x_1!(), y_1!()),
        sqr_4!(t1!(), z_1!()),
        sqr_4!(t2!(), x_1!()),
        sqr_4!(t3!(), y_1!()),
        double_twice4!(t1!(), t1!()),
        sqr_4!(t0!(), t0!()),
        add_twice4!(t4!(), t2!(), t3!()),
        sub_twice4!(t2!(), t2!(), t3!()),
        add_twice4!(t3!(), t1!(), t2!()),
        sub_twice4!(t1!(), t4!(), t0!()),
        mul_p25519!(y_3!(), t2!(), t4!()),
        mul_p25519!(z_3!(), t3!(), t2!()),
        mul_p25519!(x_3!(), t1!(), t3!()),

        // Restore stack and registers

        Q!("    add             " "sp, sp, # (" NSPACE!() "+ 0)"),
        Q!("    ldp             " "x19, x20, [sp], #16"),

        inout("x0") p3.as_mut_ptr() => _,
        inout("x1") p1.as_ptr() => _,
        // clobbers
        out("x10") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x14") _,
        out("x15") _,
        out("x16") _,
        out("x17") _,
        out("x2") _,
        out("x20") _,
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
        edwards25519_pdouble,
        &mut crate::low::abi::Aligned([0; 12]).0,
        &crate::low::abi::Aligned([0; 12]).0
    );
}
