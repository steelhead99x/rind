// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Extended projective addition for edwards25519
// Inputs p1[16], p2[16]; output p3[16]
//
// extern void edwards25519_epadd_alt
//   (uint64_t p3[static 16],const uint64_t p1[static 16],
//    const uint64_t p2[static 16]);
//
// The output p3 and both inputs p1 and p2 are points (x,y) on
// edwards25519 represented in extended projective quadruples (X,Y,Z,T)
// where x = X / Z, y = Y / Z and x * y = T / Z.
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
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
macro_rules! p2 {
    () => {
        "x20"
    };
}

// Pointers to input and output coordinates

macro_rules! x_1 { () => { Q!(p1!() ", #0") } }
macro_rules! y_1 { () => { Q!(p1!() ", # " NUMSIZE!()) } }
macro_rules! z_1 { () => { Q!(p1!() ", # (2 * " NUMSIZE!() ")") } }
macro_rules! w_1 { () => { Q!(p1!() ", # (3 * " NUMSIZE!() ")") } }

macro_rules! x_2 { () => { Q!(p2!() ", #0") } }
macro_rules! y_2 { () => { Q!(p2!() ", # " NUMSIZE!()) } }
macro_rules! z_2 { () => { Q!(p2!() ", # (2 * " NUMSIZE!() ")") } }
macro_rules! w_2 { () => { Q!(p2!() ", # (3 * " NUMSIZE!() ")") } }

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
macro_rules! t5 { () => { Q!("sp, # (5 * " NUMSIZE!() ")") } }

// Total size to reserve on the stack

macro_rules! NSPACE { () => { Q!("6 * " NUMSIZE!()) } }

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

// A version of multiplication that only guarantees output < 2 * p_25519.
// This basically skips the +1 and final correction in quotient estimation.

macro_rules! mul_4 {
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
        "bic x15, x15, #0x8000000000000000;\n"
        "adc x8, x16, x16;\n"
        "mov x7, #0x13;\n"
        "mul x11, x7, x8;\n"
        "adds x12, x12, x11;\n"
        "adcs x13, x13, x9;\n"
        "adcs x14, x14, x3;\n"
        "adc x15, x15, xzr;\n"
        "stp x12, x13, [" $P0 "];\n"
        "stp x14, x15, [" $P0 "+ 16]"
    )}
}

// Plain 4-digit add and doubling without any normalization
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

macro_rules! double_4 {
    ($P0:expr, $P1:expr) => { Q!(
        "ldp x0, x1, [" $P1 "];\n"
        "adds x0, x0, x0;\n"
        "adcs x1, x1, x1;\n"
        "ldp x2, x3, [" $P1 "+ 16];\n"
        "adcs x2, x2, x2;\n"
        "adc x3, x3, x3;\n"
        "stp x0, x1, [" $P0 "];\n"
        "stp x2, x3, [" $P0 "+ 16]"
    )}
}

// Subtraction of a pair of numbers < p_25519 just sufficient
// to give a 4-digit result. It actually always does (x - z) + (2^255-19)
// which in turn is done by (x - z) - (2^255+19) discarding the 2^256
// implicitly

macro_rules! sub_4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "ldp x5, x6, [" $P1 "];\n"
        "ldp x4, x3, [" $P2 "];\n"
        "subs x5, x5, x4;\n"
        "sbcs x6, x6, x3;\n"
        "ldp x7, x8, [" $P1 "+ 16];\n"
        "ldp x4, x3, [" $P2 "+ 16];\n"
        "sbcs x7, x7, x4;\n"
        "sbcs x8, x8, x3;\n"
        "mov x3, #19;\n"
        "subs x5, x5, x3;\n"
        "sbcs x6, x6, xzr;\n"
        "sbcs x7, x7, xzr;\n"
        "mov x4, #0x8000000000000000;\n"
        "sbc x8, x8, x4;\n"
        "stp x5, x6, [" $P0 "];\n"
        "stp x7, x8, [" $P0 "+ 16]"
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

// Modular addition with inputs double modulus 2 * p_25519 = 2^256 - 38
// and in general only guaranteeing a 4-digit result, not even < 2 * p_25519.

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

// Load the constant k_25519 = 2 * d_25519 using immediate operations

macro_rules! load_k25519 {
    ($P0:expr) => { Q!(
        "movz x0, #0xf159;\n"
        "movz x1, #0xb156;\n"
        "movz x2, #0xd130;\n"
        "movz x3, #0xfce7;\n"
        "movk x0, #0x26b2, lsl #16;\n"
        "movk x1, #0x8283, lsl #16;\n"
        "movk x2, #0xeef3, lsl #16;\n"
        "movk x3, #0x56df, lsl #16;\n"
        "movk x0, #0x9b94, lsl #32;\n"
        "movk x1, #0x149a, lsl #32;\n"
        "movk x2, #0x80f2, lsl #32;\n"
        "movk x3, #0xd9dc, lsl #32;\n"
        "movk x0, #0xebd6, lsl #48;\n"
        "movk x1, #0x00e0, lsl #48;\n"
        "movk x2, #0x198e, lsl #48;\n"
        "movk x3, #0x2406, lsl #48;\n"
        "stp x0, x1, [" $P0 "];\n"
        "stp x2, x3, [" $P0 "+ 16]"
    )}
}

// Transliterated from s2n-bignum's arm/curve25519/edwards25519_epadd_alt.S.
/// Extended projective addition for edwards25519
///
/// Inputs p1[16], p2[16]; output p3[16]
///
/// The output p3 and both inputs p1 and p2 are points (x,y) on
/// edwards25519 represented in extended projective quadruples (X,Y,Z,T)
/// where x = X / Z, y = Y / Z and x * y = T / Z.
#[inline(never)]
pub(crate) fn edwards25519_epadd(p3: &mut [u64; 16], p1: &[u64; 16], p2: &[u64; 16]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Save regs and make room for temporaries

        Q!("    stp             " "x19, x20, [sp, #-16] !"),
        Q!("    sub             " "sp, sp, # (" NSPACE!() "+ 0)"),

        // Move the input arguments to stable places

        Q!("    mov             " p3!() ", x0"),
        Q!("    mov             " p1!() ", x1"),
        Q!("    mov             " p2!() ", x2"),

        // Main sequence

        mul_4!(t0!(), w_1!(), w_2!()),

        sub_4!(t1!(), y_1!(), x_1!()),
        sub_4!(t2!(), y_2!(), x_2!()),
        add_4!(t3!(), y_1!(), x_1!()),
        add_4!(t4!(), y_2!(), x_2!()),
        double_4!(t5!(), z_2!()),

        mul_4!(t1!(), t1!(), t2!()),
        mul_4!(t3!(), t3!(), t4!()),

        load_k25519!(t2!()),
        mul_4!(t2!(), t2!(), t0!()),

        mul_4!(t4!(), z_1!(), t5!()),

        sub_twice4!(t0!(), t3!(), t1!()),
        add_twice4!(t5!(), t3!(), t1!()),
        sub_twice4!(t1!(), t4!(), t2!()),
        add_twice4!(t3!(), t4!(), t2!()),

        mul_p25519!(w_3!(), t0!(), t5!()),
        mul_p25519!(x_3!(), t0!(), t1!()),
        mul_p25519!(y_3!(), t3!(), t5!()),
        mul_p25519!(z_3!(), t1!(), t3!()),

        // Restore stack and registers

        Q!("    add             " "sp, sp, # (" NSPACE!() "+ 0)"),
        Q!("    ldp             " "x19, x20, [sp], #16"),

        inout("x0") p3.as_mut_ptr() => _,
        inout("x1") p1.as_ptr() => _,
        inout("x2") p2.as_ptr() => _,
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
        edwards25519_epadd,
        &mut crate::low::abi::Aligned([0; 16]).0,
        &crate::low::abi::Aligned([0; 16]).0,
        &crate::low::abi::Aligned([0; 16]).0
    );
}
