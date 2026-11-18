// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Extended projective doubling for edwards25519
// Input p1[12]; output p3[16]
//
// extern void edwards25519_epdouble
//   (uint64_t p3[static 16],const uint64_t p1[static 12]);
//
// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
// The output p3 is in extended projective coordinates, representing
// affine (x,y) by a quadruple (X,Y,Z,T) where x = X / Z, y = Y / Z
// and x * y = T / Z. The input p1 may also be in the same extended
// projective representation, but the final T field is not used so
// a more basic projective triple (X,Y,Z) suffices.
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
macro_rules! w_3 { () => { Q!(p3!() ", # (3 * " NUMSIZE!() ")") } }

// Pointer-offset pairs for temporaries on stack

macro_rules! t0 { () => { Q!("sp, # (0 * " NUMSIZE!() ")") } }
macro_rules! t1 { () => { Q!("sp, # (1 * " NUMSIZE!() ")") } }
macro_rules! t2 { () => { Q!("sp, # (2 * " NUMSIZE!() ")") } }
macro_rules! t3 { () => { Q!("sp, # (3 * " NUMSIZE!() ")") } }
macro_rules! t4 { () => { Q!("sp, # (4 * " NUMSIZE!() ")") } }

// Total size to reserve on the stack

macro_rules! NSPACE { () => { Q!("5 * " NUMSIZE!()) } }

// Macro wrapping up the basic field operation bignum_mul_p25519, only
// trivially different from a pure function call to that subroutine.

macro_rules! mul_p25519 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "ldp x3, x4, [" $P1 "];\n"
        "ldp x5, x6, [" $P2 "];\n"
        "umull x7, w3, w5;\n"
        "lsr x0, x3, #32;\n"
        "umull x15, w0, w5;\n"
        "lsr x16, x5, #32;\n"
        "umull x8, w16, w0;\n"
        "umull x16, w3, w16;\n"
        "adds x7, x7, x15, lsl #32;\n"
        "lsr x15, x15, #32;\n"
        "adc x8, x8, x15;\n"
        "adds x7, x7, x16, lsl #32;\n"
        "lsr x16, x16, #32;\n"
        "adc x8, x8, x16;\n"
        "mul x9, x4, x6;\n"
        "umulh x10, x4, x6;\n"
        "subs x4, x4, x3;\n"
        "cneg x4, x4, cc;\n"
        "csetm x16, cc;\n"
        "adds x9, x9, x8;\n"
        "adc x10, x10, xzr;\n"
        "subs x3, x5, x6;\n"
        "cneg x3, x3, cc;\n"
        "cinv x16, x16, cc;\n"
        "mul x15, x4, x3;\n"
        "umulh x3, x4, x3;\n"
        "adds x8, x7, x9;\n"
        "adcs x9, x9, x10;\n"
        "adc x10, x10, xzr;\n"
        "cmn x16, #0x1;\n"
        "eor x15, x15, x16;\n"
        "adcs x8, x15, x8;\n"
        "eor x3, x3, x16;\n"
        "adcs x9, x3, x9;\n"
        "adc x10, x10, x16;\n"
        "ldp x3, x4, [" $P1 "+ 16];\n"
        "ldp x5, x6, [" $P2 "+ 16];\n"
        "umull x11, w3, w5;\n"
        "lsr x0, x3, #32;\n"
        "umull x15, w0, w5;\n"
        "lsr x16, x5, #32;\n"
        "umull x12, w16, w0;\n"
        "umull x16, w3, w16;\n"
        "adds x11, x11, x15, lsl #32;\n"
        "lsr x15, x15, #32;\n"
        "adc x12, x12, x15;\n"
        "adds x11, x11, x16, lsl #32;\n"
        "lsr x16, x16, #32;\n"
        "adc x12, x12, x16;\n"
        "mul x13, x4, x6;\n"
        "umulh x14, x4, x6;\n"
        "subs x4, x4, x3;\n"
        "cneg x4, x4, cc;\n"
        "csetm x16, cc;\n"
        "adds x13, x13, x12;\n"
        "adc x14, x14, xzr;\n"
        "subs x3, x5, x6;\n"
        "cneg x3, x3, cc;\n"
        "cinv x16, x16, cc;\n"
        "mul x15, x4, x3;\n"
        "umulh x3, x4, x3;\n"
        "adds x12, x11, x13;\n"
        "adcs x13, x13, x14;\n"
        "adc x14, x14, xzr;\n"
        "cmn x16, #0x1;\n"
        "eor x15, x15, x16;\n"
        "adcs x12, x15, x12;\n"
        "eor x3, x3, x16;\n"
        "adcs x13, x3, x13;\n"
        "adc x14, x14, x16;\n"
        "ldp x3, x4, [" $P1 "+ 16];\n"
        "ldp x15, x16, [" $P1 "];\n"
        "subs x3, x3, x15;\n"
        "sbcs x4, x4, x16;\n"
        "csetm x16, cc;\n"
        "ldp x15, x0, [" $P2 "];\n"
        "subs x5, x15, x5;\n"
        "sbcs x6, x0, x6;\n"
        "csetm x0, cc;\n"
        "eor x3, x3, x16;\n"
        "subs x3, x3, x16;\n"
        "eor x4, x4, x16;\n"
        "sbc x4, x4, x16;\n"
        "eor x5, x5, x0;\n"
        "subs x5, x5, x0;\n"
        "eor x6, x6, x0;\n"
        "sbc x6, x6, x0;\n"
        "eor x16, x0, x16;\n"
        "adds x11, x11, x9;\n"
        "adcs x12, x12, x10;\n"
        "adcs x13, x13, xzr;\n"
        "adc x14, x14, xzr;\n"
        "mul x2, x3, x5;\n"
        "umulh x0, x3, x5;\n"
        "mul x15, x4, x6;\n"
        "umulh x1, x4, x6;\n"
        "subs x4, x4, x3;\n"
        "cneg x4, x4, cc;\n"
        "csetm x9, cc;\n"
        "adds x15, x15, x0;\n"
        "adc x1, x1, xzr;\n"
        "subs x6, x5, x6;\n"
        "cneg x6, x6, cc;\n"
        "cinv x9, x9, cc;\n"
        "mul x5, x4, x6;\n"
        "umulh x6, x4, x6;\n"
        "adds x0, x2, x15;\n"
        "adcs x15, x15, x1;\n"
        "adc x1, x1, xzr;\n"
        "cmn x9, #0x1;\n"
        "eor x5, x5, x9;\n"
        "adcs x0, x5, x0;\n"
        "eor x6, x6, x9;\n"
        "adcs x15, x6, x15;\n"
        "adc x1, x1, x9;\n"
        "adds x9, x11, x7;\n"
        "adcs x10, x12, x8;\n"
        "adcs x11, x13, x11;\n"
        "adcs x12, x14, x12;\n"
        "adcs x13, x13, xzr;\n"
        "adc x14, x14, xzr;\n"
        "cmn x16, #0x1;\n"
        "eor x2, x2, x16;\n"
        "adcs x9, x2, x9;\n"
        "eor x0, x0, x16;\n"
        "adcs x10, x0, x10;\n"
        "eor x15, x15, x16;\n"
        "adcs x11, x15, x11;\n"
        "eor x1, x1, x16;\n"
        "adcs x12, x1, x12;\n"
        "adcs x13, x13, x16;\n"
        "adc x14, x14, x16;\n"
        "mov x3, #0x26;\n"
        "umull x4, w11, w3;\n"
        "add x4, x4, w7, uxtw;\n"
        "lsr x7, x7, #32;\n"
        "lsr x11, x11, #32;\n"
        "umaddl x11, w11, w3, x7;\n"
        "mov x7, x4;\n"
        "umull x4, w12, w3;\n"
        "add x4, x4, w8, uxtw;\n"
        "lsr x8, x8, #32;\n"
        "lsr x12, x12, #32;\n"
        "umaddl x12, w12, w3, x8;\n"
        "mov x8, x4;\n"
        "umull x4, w13, w3;\n"
        "add x4, x4, w9, uxtw;\n"
        "lsr x9, x9, #32;\n"
        "lsr x13, x13, #32;\n"
        "umaddl x13, w13, w3, x9;\n"
        "mov x9, x4;\n"
        "umull x4, w14, w3;\n"
        "add x4, x4, w10, uxtw;\n"
        "lsr x10, x10, #32;\n"
        "lsr x14, x14, #32;\n"
        "umaddl x14, w14, w3, x10;\n"
        "mov x10, x4;\n"
        "lsr x0, x14, #31;\n"
        "mov x5, #0x13;\n"
        "umaddl x5, w5, w0, x5;\n"
        "add x7, x7, x5;\n"
        "adds x7, x7, x11, lsl #32;\n"
        "extr x3, x12, x11, #32;\n"
        "adcs x8, x8, x3;\n"
        "extr x3, x13, x12, #32;\n"
        "adcs x9, x9, x3;\n"
        "extr x3, x14, x13, #32;\n"
        "lsl x5, x0, #63;\n"
        "eor x10, x10, x5;\n"
        "adc x10, x10, x3;\n"
        "mov x3, #0x13;\n"
        "tst x10, #0x8000000000000000;\n"
        "csel x3, x3, xzr, pl;\n"
        "subs x7, x7, x3;\n"
        "sbcs x8, x8, xzr;\n"
        "sbcs x9, x9, xzr;\n"
        "sbc x10, x10, xzr;\n"
        "and x10, x10, #0x7fffffffffffffff;\n"
        "stp x7, x8, [" $P0 "];\n"
        "stp x9, x10, [" $P0 "+ 16]"
    )}
}

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

macro_rules! sqr_4 {
    ($P0:expr, $P1:expr) => { Q!(
        "ldp x10, x11, [" $P1 "];\n"
        "ldp x12, x13, [" $P1 "+ 16];\n"
        "umull x2, w10, w10;\n"
        "lsr x14, x10, #32;\n"
        "umull x3, w14, w14;\n"
        "umull x14, w10, w14;\n"
        "adds x2, x2, x14, lsl #33;\n"
        "lsr x14, x14, #31;\n"
        "adc x3, x3, x14;\n"
        "umull x4, w11, w11;\n"
        "lsr x14, x11, #32;\n"
        "umull x5, w14, w14;\n"
        "umull x14, w11, w14;\n"
        "mul x15, x10, x11;\n"
        "umulh x16, x10, x11;\n"
        "adds x4, x4, x14, lsl #33;\n"
        "lsr x14, x14, #31;\n"
        "adc x5, x5, x14;\n"
        "adds x15, x15, x15;\n"
        "adcs x16, x16, x16;\n"
        "adc x5, x5, xzr;\n"
        "adds x3, x3, x15;\n"
        "adcs x4, x4, x16;\n"
        "adc x5, x5, xzr;\n"
        "umull x6, w12, w12;\n"
        "lsr x14, x12, #32;\n"
        "umull x7, w14, w14;\n"
        "umull x14, w12, w14;\n"
        "adds x6, x6, x14, lsl #33;\n"
        "lsr x14, x14, #31;\n"
        "adc x7, x7, x14;\n"
        "umull x8, w13, w13;\n"
        "lsr x14, x13, #32;\n"
        "umull x9, w14, w14;\n"
        "umull x14, w13, w14;\n"
        "mul x15, x12, x13;\n"
        "umulh x16, x12, x13;\n"
        "adds x8, x8, x14, lsl #33;\n"
        "lsr x14, x14, #31;\n"
        "adc x9, x9, x14;\n"
        "adds x15, x15, x15;\n"
        "adcs x16, x16, x16;\n"
        "adc x9, x9, xzr;\n"
        "adds x7, x7, x15;\n"
        "adcs x8, x8, x16;\n"
        "adc x9, x9, xzr;\n"
        "subs x10, x10, x12;\n"
        "sbcs x11, x11, x13;\n"
        "csetm x16, cc;\n"
        "eor x10, x10, x16;\n"
        "subs x10, x10, x16;\n"
        "eor x11, x11, x16;\n"
        "sbc x11, x11, x16;\n"
        "adds x6, x6, x4;\n"
        "adcs x7, x7, x5;\n"
        "adcs x8, x8, xzr;\n"
        "adc x9, x9, xzr;\n"
        "umull x12, w10, w10;\n"
        "lsr x5, x10, #32;\n"
        "umull x13, w5, w5;\n"
        "umull x5, w10, w5;\n"
        "adds x12, x12, x5, lsl #33;\n"
        "lsr x5, x5, #31;\n"
        "adc x13, x13, x5;\n"
        "umull x15, w11, w11;\n"
        "lsr x5, x11, #32;\n"
        "umull x14, w5, w5;\n"
        "umull x5, w11, w5;\n"
        "mul x4, x10, x11;\n"
        "umulh x16, x10, x11;\n"
        "adds x15, x15, x5, lsl #33;\n"
        "lsr x5, x5, #31;\n"
        "adc x14, x14, x5;\n"
        "adds x4, x4, x4;\n"
        "adcs x16, x16, x16;\n"
        "adc x14, x14, xzr;\n"
        "adds x13, x13, x4;\n"
        "adcs x15, x15, x16;\n"
        "adc x14, x14, xzr;\n"
        "adds x4, x2, x6;\n"
        "adcs x5, x3, x7;\n"
        "adcs x6, x6, x8;\n"
        "adcs x7, x7, x9;\n"
        "csetm x16, cc;\n"
        "subs x4, x4, x12;\n"
        "sbcs x5, x5, x13;\n"
        "sbcs x6, x6, x15;\n"
        "sbcs x7, x7, x14;\n"
        "adcs x8, x8, x16;\n"
        "adc x9, x9, x16;\n"
        "mov x10, #0x26;\n"
        "umull x12, w6, w10;\n"
        "add x12, x12, w2, uxtw;\n"
        "lsr x2, x2, #32;\n"
        "lsr x6, x6, #32;\n"
        "umaddl x6, w6, w10, x2;\n"
        "mov x2, x12;\n"
        "umull x12, w7, w10;\n"
        "add x12, x12, w3, uxtw;\n"
        "lsr x3, x3, #32;\n"
        "lsr x7, x7, #32;\n"
        "umaddl x7, w7, w10, x3;\n"
        "mov x3, x12;\n"
        "umull x12, w8, w10;\n"
        "add x12, x12, w4, uxtw;\n"
        "lsr x4, x4, #32;\n"
        "lsr x8, x8, #32;\n"
        "umaddl x8, w8, w10, x4;\n"
        "mov x4, x12;\n"
        "umull x12, w9, w10;\n"
        "add x12, x12, w5, uxtw;\n"
        "lsr x5, x5, #32;\n"
        "lsr x9, x9, #32;\n"
        "umaddl x9, w9, w10, x5;\n"
        "mov x5, x12;\n"
        "lsr x13, x9, #31;\n"
        "mov x11, #0x13;\n"
        "umull x11, w11, w13;\n"
        "add x2, x2, x11;\n"
        "adds x2, x2, x6, lsl #32;\n"
        "extr x10, x7, x6, #32;\n"
        "adcs x3, x3, x10;\n"
        "extr x10, x8, x7, #32;\n"
        "adcs x4, x4, x10;\n"
        "extr x10, x9, x8, #32;\n"
        "lsl x11, x13, #63;\n"
        "eor x5, x5, x11;\n"
        "adc x5, x5, x10;\n"
        "stp x2, x3, [" $P0 "];\n"
        "stp x4, x5, [" $P0 "+ 16]"
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

// Transliterated from s2n-bignum's arm/curve25519/edwards25519_epdouble.S.
/// Extended projective doubling for edwards25519
///
/// Input p1[12]; output p3[16]
///
/// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
/// The output p3 is in extended projective coordinates, representing
/// affine (x,y) by a quadruple (X,Y,Z,T) where x = X / Z, y = Y / Z
/// and x * y = T / Z. The input p1 may also be in the same extended
/// projective representation, but the final T field is not used so
/// a more basic projective triple (X,Y,Z) suffices.
#[inline(never)]
pub(crate) fn edwards25519_epdouble(p3: &mut [u64; 16], p1: &[u64; 12]) {
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
        mul_p25519!(w_3!(), t1!(), t4!()),
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
        edwards25519_epdouble,
        &mut crate::low::abi::Aligned([0; 16]).0,
        &crate::low::abi::Aligned([0; 12]).0
    );
}
