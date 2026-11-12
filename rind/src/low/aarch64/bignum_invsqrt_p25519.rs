// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Inverse square root modulo p_25519 = 2^255 - 19
// Input x[4]; output function return (Legendre symbol) and z[4]
//
// extern int64_t bignum_invsqrt_p25519_alt(uint64_t z[static 4],const uint64_t x[static 4]);
//
// Given a 4-digit input x, returns a modular inverse square root mod p_25519,
// i.e. a z such that x * z^2 == 1 (mod p_25519), whenever one exists. The
// inverse square root z is chosen so that its LSB is even (note that p_25519-z
// is another possibility). The function return is the Legendre/Jacobi symbol
// (x//p_25519), which indicates whether indeed x has a modular inverse square
// root and hence whether the result is meaningful:
//
//   0: x is divisible by p_25519 so trivially there is no inverse square root
//  +1: x is coprime to p_25519 and z is indeed an inverse square root
//  -1: x is coprime to p_25519 but there is no (inverse or direct) square root
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

// Size in bytes of a 64-bit word

macro_rules! N {
    () => {
        "8"
    };
}

// Pointer-offset pairs for temporaries on stack

macro_rules! a {
    () => {
        "sp, #0"
    };
}
macro_rules! b { () => { Q!("sp, # (4 * " N!() ")") } }
macro_rules! s { () => { Q!("sp, # (8 * " N!() ")") } }
macro_rules! t { () => { Q!("sp, # (12 * " N!() ")") } }

// Other temporary variables in register

macro_rules! res {
    () => {
        "x19"
    };
}

// Total size to reserve on the stack

macro_rules! NSPACE { () => { Q!("16 * " N!()) } }

// Loading large constants

macro_rules! movbig {
    ($nn:expr, $n3:expr, $n2:expr, $n1:expr, $n0:expr) => { Q!(
        "movz " $nn ", " $n0 ";\n"
        "movk " $nn ", " $n1 ", lsl #16;\n"
        "movk " $nn ", " $n2 ", lsl #32;\n"
        "movk " $nn ", " $n3 ", lsl #48"
    )}
}

// Macros wrapping up calls to the local subroutines

macro_rules! mulp {
    ($dest:expr, $src1:expr, $src2:expr) => { Q!(
        "add x0, " $dest ";\n"
        "add x1, " $src1 ";\n"
        "add x2, " $src2 ";\n"
        "bl " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 4, After)
    )}
}

macro_rules! nsqr {
    ($dest:expr, $n:expr, $src:expr) => { Q!(
        "add x0, " $dest ";\n"
        "mov x1, " $n ";\n"
        "add x2, " $src ";\n"
        "bl " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)
    )}
}

// Transliterated from s2n-bignum's arm/curve25519/bignum_invsqrt_p25519_alt.S.
/// Inverse square root modulo p_25519 = 2^255 - 19
///
/// Input x[4]; output function return (Legendre symbol) and z[4]
///
/// Given a 4-digit input x, returns a modular inverse square root mod p_25519,
/// i.e. a z such that x * z^2 == 1 (mod p_25519), whenever one exists. The
/// inverse square root z is chosen so that its LSB is even (note that p_25519-z
/// is another possibility). The function return is the Legendre/Jacobi symbol
/// (x//p_25519), which indicates whether indeed x has a modular inverse square
/// root and hence whether the result is meaningful:
///
///   0: x is divisible by p_25519 so trivially there is no inverse square root
///  +1: x is coprime to p_25519 and z is indeed an inverse square root
///  -1: x is coprime to p_25519 but there is no (inverse or direct) square root
#[inline(never)]
pub(crate) fn bignum_invsqrt_p25519(z: &mut [u64; 4], x: &[u64; 4]) -> u64 {
    let ret: u64;
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Save registers and make room for temporaries

        Q!("    stp             " "x19, x30, [sp, #-16] !"),
        Q!("    sub             " "sp, sp, # (" NSPACE!() "+ 0)"),

        // Save the return pointer for the end so we can overwrite x0 later

        Q!("    mov             " res!() ", x0"),

        // Set up reduced version of the input argument a = x mod p_25519. Then
        // get the candidate inverse square root s = a^{252-3}

        Q!("    ldp             " "x2, x3, [x1]"),
        Q!("    ldp             " "x4, x5, [x1, #16]"),
        Q!("    mov             " "x7, #19"),
        Q!("    lsr             " "x6, x5, #63"),
        Q!("    madd            " "x6, x7, x6, x7"),
        Q!("    adds            " "x2, x2, x6"),
        Q!("    adcs            " "x3, x3, xzr"),
        Q!("    adcs            " "x4, x4, xzr"),
        Q!("    orr             " "x5, x5, #0x8000000000000000"),
        Q!("    adcs            " "x5, x5, xzr"),
        Q!("    csel            " "x6, x7, xzr, lo"),
        Q!("    subs            " "x2, x2, x6"),
        Q!("    sbcs            " "x3, x3, xzr"),
        Q!("    sbcs            " "x4, x4, xzr"),
        Q!("    sbc             " "x5, x5, xzr"),
        Q!("    and             " "x5, x5, #0x7fffffffffffffff"),
        Q!("    stp             " "x2, x3, [" a!() "]"),
        Q!("    stp             " "x4, x5, [" a!() "+ 16]"),

        // Power 2^2 - 1 = 3

        nsqr!(t!(), "1", a!()),
        mulp!(t!(), t!(), a!()),

        // Power 2^4 - 1 = 15

        nsqr!(s!(), "2", t!()),
        mulp!(t!(), s!(), t!()),

        // Power 2^5 - 1 = 31

        nsqr!(s!(), "1", t!()),
        mulp!(b!(), s!(), a!()),

        // Power 2^10 - 1

        nsqr!(s!(), "5", b!()),
        mulp!(t!(), s!(), b!()),

        // Power 2^20 - 1

        nsqr!(s!(), "10", t!()),
        mulp!(t!(), s!(), t!()),

        // Power 2^25 - 1

        nsqr!(s!(), "5", t!()),
        mulp!(b!(), s!(), b!()),

        // Power 2^50 - 1

        nsqr!(s!(), "25", b!()),
        mulp!(t!(), s!(), b!()),

        // Power 2^100 - 1
        nsqr!(s!(), "50", t!()),
        mulp!(t!(), s!(), t!()),

        // Power 2^125 - 1

        nsqr!(s!(), "25", t!()),
        mulp!(b!(), s!(), b!()),

        // Power 2^250 - 1

        nsqr!(s!(), "125", b!()),
        mulp!(b!(), s!(), b!()),

        // Power 2^252 - 3

        nsqr!(s!(), "2", b!()),
        mulp!(s!(), s!(), a!()),

        // s = a^{2^252-3} is now one candidate inverse square root.
        // Generate the other one t = s * j_25519 where j_25519 = sqrt(-1)

        movbig!("x0", "#0xc4ee", "#0x1b27", "#0x4a0e", "#0xa0b0"),
        movbig!("x1", "#0x2f43", "#0x1806", "#0xad2f", "#0xe478"),
        movbig!("x2", "#0x2b4d", "#0x0099", "#0x3dfb", "#0xd7a7"),
        movbig!("x3", "#0x2b83", "#0x2480", "#0x4fc1", "#0xdf0b"),
        Q!("    stp             " "x0, x1, [" t!() "]"),
        Q!("    stp             " "x2, x3, [" t!() "+ 16]"),
        mulp!(t!(), s!(), t!()),

        // Now multiplex between them according to whether a * s^2 = 1

        nsqr!(b!(), "1", s!()),
        mulp!(b!(), a!(), b!()),

        Q!("    ldp             " "x10, x11, [" b!() "]"),
        Q!("    eor             " "x10, x10, #1"),
        Q!("    ldp             " "x12, x13, [" b!() "+ 16]"),
        Q!("    orr             " "x10, x10, x11"),
        Q!("    orr             " "x12, x12, x13"),
        Q!("    orr             " "x10, x10, x12"),
        Q!("    cmp             " "x10, xzr"),

        Q!("    ldp             " "x10, x11, [" s!() "]"),
        Q!("    ldp             " "x14, x15, [" t!() "]"),
        Q!("    csel            " "x10, x10, x14, eq"),
        Q!("    csel            " "x11, x11, x15, eq"),
        Q!("    ldp             " "x12, x13, [" s!() "+ 16]"),
        Q!("    ldp             " "x16, x17, [" t!() "+ 16]"),
        Q!("    csel            " "x12, x12, x16, eq"),
        Q!("    csel            " "x13, x13, x17, eq"),

        // For definiteness, choose "positive" (LSB=0) inverse square root

        Q!("    mov             " "x14, #-19"),
        Q!("    subs            " "x14, x14, x10"),
        Q!("    mov             " "x16, #-1"),
        Q!("    sbcs            " "x15, x16, x11"),
        Q!("    mov             " "x17, #0x7FFFFFFFFFFFFFFF"),
        Q!("    sbcs            " "x16, x16, x12"),
        Q!("    sbc             " "x17, x17, x13"),

        Q!("    tst             " "x10, #1"),
        Q!("    csel            " "x10, x10, x14, eq"),
        Q!("    csel            " "x11, x11, x15, eq"),
        Q!("    csel            " "x12, x12, x16, eq"),
        Q!("    csel            " "x13, x13, x17, eq"),

        Q!("    mov             " "x2, " res!()),
        Q!("    stp             " "x10, x11, [x2]"),
        Q!("    stp             " "x12, x13, [x2, #16]"),

        // Determine if it is indeed an inverse square root, also distinguishing
        // the degenerate x * z^2 == 0 (mod p_25519) case, which is equivalent to
        // x == 0 (mod p_25519). Hence return the Legendre-Jacobi symbol as required.

        Q!("    add             " "x0, " b!()),
        Q!("    mov             " "x1, #1"),
        Q!("    bl              " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),
        mulp!(b!(), a!(), b!()),

        Q!("    ldp             " "x10, x11, [" b!() "]"),
        Q!("    eor             " "x14, x10, #1"),
        Q!("    ldp             " "x12, x13, [" b!() "+ 16]"),
        Q!("    orr             " "x10, x10, x11"),
        Q!("    orr             " "x14, x14, x11"),
        Q!("    orr             " "x12, x12, x13"),
        Q!("    orr             " "x10, x10, x12"),
        Q!("    orr             " "x14, x14, x12"),

        Q!("    cmp             " "x14, xzr"),
        Q!("    mov             " "x0, #1"),
        Q!("    cneg            " "x0, x0, ne"),

        Q!("    cmp             " "x10, xzr"),
        Q!("    csel            " "x0, x0, xzr, ne"),

        // Restore stack and registers

        Q!("    add             " "sp, sp, # (" NSPACE!() "+ 0)"),
        Q!("    ldp             " "x19, x30, [sp], #16"),
        // proc hoisting in -> ret after Lbignum_invsqrt_p25519_alt_nsqr_p25519
        Q!("    b               " Label!("hoist_finish", 3, After)),

        // *************************************************************
        // Local z = x * y
        // *************************************************************

        Q!(Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 4) ":"),

        Q!("    ldp             " "x3, x4, [x1]"),
        Q!("    ldp             " "x7, x8, [x2]"),
        Q!("    mul             " "x12, x3, x7"),
        Q!("    umulh           " "x13, x3, x7"),
        Q!("    mul             " "x11, x3, x8"),
        Q!("    umulh           " "x14, x3, x8"),
        Q!("    adds            " "x13, x13, x11"),
        Q!("    ldp             " "x9, x10, [x2, #16]"),
        Q!("    mul             " "x11, x3, x9"),
        Q!("    umulh           " "x15, x3, x9"),
        Q!("    adcs            " "x14, x14, x11"),
        Q!("    mul             " "x11, x3, x10"),
        Q!("    umulh           " "x16, x3, x10"),
        Q!("    adcs            " "x15, x15, x11"),
        Q!("    adc             " "x16, x16, xzr"),
        Q!("    ldp             " "x5, x6, [x1, #16]"),
        Q!("    mul             " "x11, x4, x7"),
        Q!("    adds            " "x13, x13, x11"),
        Q!("    mul             " "x11, x4, x8"),
        Q!("    adcs            " "x14, x14, x11"),
        Q!("    mul             " "x11, x4, x9"),
        Q!("    adcs            " "x15, x15, x11"),
        Q!("    mul             " "x11, x4, x10"),
        Q!("    adcs            " "x16, x16, x11"),
        Q!("    umulh           " "x3, x4, x10"),
        Q!("    adc             " "x3, x3, xzr"),
        Q!("    umulh           " "x11, x4, x7"),
        Q!("    adds            " "x14, x14, x11"),
        Q!("    umulh           " "x11, x4, x8"),
        Q!("    adcs            " "x15, x15, x11"),
        Q!("    umulh           " "x11, x4, x9"),
        Q!("    adcs            " "x16, x16, x11"),
        Q!("    adc             " "x3, x3, xzr"),
        Q!("    mul             " "x11, x5, x7"),
        Q!("    adds            " "x14, x14, x11"),
        Q!("    mul             " "x11, x5, x8"),
        Q!("    adcs            " "x15, x15, x11"),
        Q!("    mul             " "x11, x5, x9"),
        Q!("    adcs            " "x16, x16, x11"),
        Q!("    mul             " "x11, x5, x10"),
        Q!("    adcs            " "x3, x3, x11"),
        Q!("    umulh           " "x4, x5, x10"),
        Q!("    adc             " "x4, x4, xzr"),
        Q!("    umulh           " "x11, x5, x7"),
        Q!("    adds            " "x15, x15, x11"),
        Q!("    umulh           " "x11, x5, x8"),
        Q!("    adcs            " "x16, x16, x11"),
        Q!("    umulh           " "x11, x5, x9"),
        Q!("    adcs            " "x3, x3, x11"),
        Q!("    adc             " "x4, x4, xzr"),
        Q!("    mul             " "x11, x6, x7"),
        Q!("    adds            " "x15, x15, x11"),
        Q!("    mul             " "x11, x6, x8"),
        Q!("    adcs            " "x16, x16, x11"),
        Q!("    mul             " "x11, x6, x9"),
        Q!("    adcs            " "x3, x3, x11"),
        Q!("    mul             " "x11, x6, x10"),
        Q!("    adcs            " "x4, x4, x11"),
        Q!("    umulh           " "x5, x6, x10"),
        Q!("    adc             " "x5, x5, xzr"),
        Q!("    umulh           " "x11, x6, x7"),
        Q!("    adds            " "x16, x16, x11"),
        Q!("    umulh           " "x11, x6, x8"),
        Q!("    adcs            " "x3, x3, x11"),
        Q!("    umulh           " "x11, x6, x9"),
        Q!("    adcs            " "x4, x4, x11"),
        Q!("    adc             " "x5, x5, xzr"),
        Q!("    mov             " "x7, #38"),
        Q!("    mul             " "x11, x7, x16"),
        Q!("    umulh           " "x9, x7, x16"),
        Q!("    adds            " "x12, x12, x11"),
        Q!("    mul             " "x11, x7, x3"),
        Q!("    umulh           " "x3, x7, x3"),
        Q!("    adcs            " "x13, x13, x11"),
        Q!("    mul             " "x11, x7, x4"),
        Q!("    umulh           " "x4, x7, x4"),
        Q!("    adcs            " "x14, x14, x11"),
        Q!("    mul             " "x11, x7, x5"),
        Q!("    umulh           " "x5, x7, x5"),
        Q!("    adcs            " "x15, x15, x11"),
        Q!("    cset            " "x16, hs"),
        Q!("    adds            " "x15, x15, x4"),
        Q!("    adc             " "x16, x16, x5"),
        Q!("    cmn             " "x15, x15"),
        Q!("    orr             " "x15, x15, #0x8000000000000000"),
        Q!("    adc             " "x8, x16, x16"),
        Q!("    mov             " "x7, #19"),
        Q!("    madd            " "x11, x7, x8, x7"),
        Q!("    adds            " "x12, x12, x11"),
        Q!("    adcs            " "x13, x13, x9"),
        Q!("    adcs            " "x14, x14, x3"),
        Q!("    adcs            " "x15, x15, xzr"),
        Q!("    csel            " "x7, x7, xzr, lo"),
        Q!("    subs            " "x12, x12, x7"),
        Q!("    sbcs            " "x13, x13, xzr"),
        Q!("    sbcs            " "x14, x14, xzr"),
        Q!("    sbc             " "x15, x15, xzr"),
        Q!("    and             " "x15, x15, #0x7fffffffffffffff"),
        Q!("    stp             " "x12, x13, [x0]"),
        Q!("    stp             " "x14, x15, [x0, #16]"),
        Q!("    ret             " ),

        // *************************************************************
        // Local z = 2^n * x
        // *************************************************************

        Q!(Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2) ":"),

        // Copy input argument into [x5;x4;x3;x2] (overwriting input pointer x20

        Q!("    ldp             " "x6, x3, [x2]"),
        Q!("    ldp             " "x4, x5, [x2, #16]"),
        Q!("    mov             " "x2, x6"),

        // Main squaring loop, accumulating in [x5;x4;x3;x2] consistently and
        // only ensuring the intermediates are < 2 * p_25519 = 2^256 - 38

        Q!(Label!("Lbignum_invsqrt_p25519_alt_loop", 5) ":"),
        Q!("    mul             " "x9, x2, x3"),
        Q!("    umulh           " "x10, x2, x3"),
        Q!("    mul             " "x11, x2, x5"),
        Q!("    umulh           " "x12, x2, x5"),
        Q!("    mul             " "x7, x2, x4"),
        Q!("    umulh           " "x6, x2, x4"),
        Q!("    adds            " "x10, x10, x7"),
        Q!("    adcs            " "x11, x11, x6"),
        Q!("    mul             " "x7, x3, x4"),
        Q!("    umulh           " "x6, x3, x4"),
        Q!("    adc             " "x6, x6, xzr"),
        Q!("    adds            " "x11, x11, x7"),
        Q!("    mul             " "x13, x4, x5"),
        Q!("    umulh           " "x14, x4, x5"),
        Q!("    adcs            " "x12, x12, x6"),
        Q!("    mul             " "x7, x3, x5"),
        Q!("    umulh           " "x6, x3, x5"),
        Q!("    adc             " "x6, x6, xzr"),
        Q!("    adds            " "x12, x12, x7"),
        Q!("    adcs            " "x13, x13, x6"),
        Q!("    adc             " "x14, x14, xzr"),
        Q!("    adds            " "x9, x9, x9"),
        Q!("    adcs            " "x10, x10, x10"),
        Q!("    adcs            " "x11, x11, x11"),
        Q!("    adcs            " "x12, x12, x12"),
        Q!("    adcs            " "x13, x13, x13"),
        Q!("    adcs            " "x14, x14, x14"),
        Q!("    cset            " "x6, hs"),
        Q!("    umulh           " "x7, x2, x2"),
        Q!("    mul             " "x8, x2, x2"),
        Q!("    adds            " "x9, x9, x7"),
        Q!("    mul             " "x7, x3, x3"),
        Q!("    adcs            " "x10, x10, x7"),
        Q!("    umulh           " "x7, x3, x3"),
        Q!("    adcs            " "x11, x11, x7"),
        Q!("    mul             " "x7, x4, x4"),
        Q!("    adcs            " "x12, x12, x7"),
        Q!("    umulh           " "x7, x4, x4"),
        Q!("    adcs            " "x13, x13, x7"),
        Q!("    mul             " "x7, x5, x5"),
        Q!("    adcs            " "x14, x14, x7"),
        Q!("    umulh           " "x7, x5, x5"),
        Q!("    adc             " "x6, x6, x7"),
        Q!("    mov             " "x3, #38"),
        Q!("    mul             " "x7, x3, x12"),
        Q!("    umulh           " "x4, x3, x12"),
        Q!("    adds            " "x8, x8, x7"),
        Q!("    mul             " "x7, x3, x13"),
        Q!("    umulh           " "x13, x3, x13"),
        Q!("    adcs            " "x9, x9, x7"),
        Q!("    mul             " "x7, x3, x14"),
        Q!("    umulh           " "x14, x3, x14"),
        Q!("    adcs            " "x10, x10, x7"),
        Q!("    mul             " "x7, x3, x6"),
        Q!("    umulh           " "x6, x3, x6"),
        Q!("    adcs            " "x11, x11, x7"),
        Q!("    cset            " "x12, hs"),
        Q!("    adds            " "x11, x11, x14"),
        Q!("    adc             " "x12, x12, x6"),
        Q!("    cmn             " "x11, x11"),
        Q!("    bic             " "x11, x11, #0x8000000000000000"),
        Q!("    adc             " "x2, x12, x12"),
        Q!("    mov             " "x3, #0x13"),
        Q!("    mul             " "x7, x3, x2"),
        Q!("    adds            " "x2, x8, x7"),
        Q!("    adcs            " "x3, x9, x4"),
        Q!("    adcs            " "x4, x10, x13"),
        Q!("    adc             " "x5, x11, xzr"),

        // Loop as applicable

        Q!("    subs            " "x1, x1, #1"),
        Q!("    bne             " Label!("Lbignum_invsqrt_p25519_alt_loop", 5, Before)),

        // We know the intermediate result x < 2^256 - 38, and now we do strict
        // modular reduction mod 2^255 - 19. Note x < 2^255 - 19 <=> x + 19 < 2^255
        // which is equivalent to a "pl" condition.

        Q!("    adds            " "x6, x2, #19"),
        Q!("    adcs            " "x7, x3, xzr"),
        Q!("    adcs            " "x8, x4, xzr"),
        Q!("    adcs            " "x9, x5, xzr"),

        Q!("    csel            " "x2, x2, x6, pl"),
        Q!("    csel            " "x3, x3, x7, pl"),
        Q!("    csel            " "x4, x4, x8, pl"),
        Q!("    csel            " "x5, x5, x9, pl"),
        Q!("    bic             " "x5, x5, #0x8000000000000000"),

        // Copy result back into destination and return

        Q!("    stp             " "x2, x3, [x0]"),
        Q!("    stp             " "x4, x5, [x0, #16]"),
        Q!("    ret             " ),
        Q!(Label!("hoist_finish", 3) ":"),
        inout("x0") z.as_mut_ptr() => ret,
        inout("x1") x.as_ptr() => _,
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
    ret
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        bignum_invsqrt_p25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
