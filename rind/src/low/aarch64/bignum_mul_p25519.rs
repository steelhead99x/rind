// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply modulo p_25519, z := (x * y) mod p_25519
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_mul_p25519_alt(uint64_t z[static 4],
//                                      const uint64_t x[static 4],
//                                      const uint64_t y[static 4]);
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
macro_rules! a1 {
    () => {
        "x4"
    };
}
macro_rules! a2 {
    () => {
        "x5"
    };
}
macro_rules! a3 {
    () => {
        "x6"
    };
}
macro_rules! b0 {
    () => {
        "x7"
    };
}
macro_rules! b1 {
    () => {
        "x8"
    };
}
macro_rules! b2 {
    () => {
        "x9"
    };
}
macro_rules! b3 {
    () => {
        "x10"
    };
}

macro_rules! l {
    () => {
        "x11"
    };
}

macro_rules! u0 {
    () => {
        "x12"
    };
}
macro_rules! u1 {
    () => {
        "x13"
    };
}
macro_rules! u2 {
    () => {
        "x14"
    };
}
macro_rules! u3 {
    () => {
        "x15"
    };
}
macro_rules! u4 {
    () => {
        "x16"
    };
}

// These alias to the input arguments when no longer needed

macro_rules! u5 {
    () => {
        Q!(a0!())
    };
}
macro_rules! u6 {
    () => {
        Q!(a1!())
    };
}
macro_rules! u7 {
    () => {
        Q!(a2!())
    };
}

macro_rules! c {
    () => {
        Q!(b0!())
    };
}
macro_rules! q {
    () => {
        Q!(b1!())
    };
}
macro_rules! h {
    () => {
        Q!(b2!())
    };
}

// Transliterated from s2n-bignum's arm/curve25519/bignum_mul_p25519_alt.S.
/// Multiply modulo p_25519, z := (x * y) mod p_25519
///
/// Inputs x[4], y[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_mul_p25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Load operands and set up row 0 = [u4;...;u0] = a0 * [b3;...;b0]

        Q!("    ldp             " a0!() ", " a1!() ", [" x!() "]"),
        Q!("    ldp             " b0!() ", " b1!() ", [" y!() "]"),

        Q!("    mul             " u0!() ", " a0!() ", " b0!()),
        Q!("    umulh           " u1!() ", " a0!() ", " b0!()),
        Q!("    mul             " l!() ", " a0!() ", " b1!()),
        Q!("    umulh           " u2!() ", " a0!() ", " b1!()),
        Q!("    adds            " u1!() ", " u1!() ", " l!()),

        Q!("    ldp             " b2!() ", " b3!() ", [" y!() ", #16]"),

        Q!("    mul             " l!() ", " a0!() ", " b2!()),
        Q!("    umulh           " u3!() ", " a0!() ", " b2!()),
        Q!("    adcs            " u2!() ", " u2!() ", " l!()),

        Q!("    mul             " l!() ", " a0!() ", " b3!()),
        Q!("    umulh           " u4!() ", " a0!() ", " b3!()),
        Q!("    adcs            " u3!() ", " u3!() ", " l!()),
        Q!("    adc             " u4!() ", " u4!() ", xzr"),

        Q!("    ldp             " a2!() ", " a3!() ", [" x!() ", #16]"),

        // Row 1 = [u5;...;u0] = [a1;a0] * [b3;...;b0]

        Q!("    mul             " l!() ", " a1!() ", " b0!()),
        Q!("    adds            " u1!() ", " u1!() ", " l!()),
        Q!("    mul             " l!() ", " a1!() ", " b1!()),
        Q!("    adcs            " u2!() ", " u2!() ", " l!()),
        Q!("    mul             " l!() ", " a1!() ", " b2!()),
        Q!("    adcs            " u3!() ", " u3!() ", " l!()),
        Q!("    mul             " l!() ", " a1!() ", " b3!()),
        Q!("    adcs            " u4!() ", " u4!() ", " l!()),
        Q!("    umulh           " u5!() ", " a1!() ", " b3!()),
        Q!("    adc             " u5!() ", " u5!() ", xzr"),

        Q!("    umulh           " l!() ", " a1!() ", " b0!()),
        Q!("    adds            " u2!() ", " u2!() ", " l!()),
        Q!("    umulh           " l!() ", " a1!() ", " b1!()),
        Q!("    adcs            " u3!() ", " u3!() ", " l!()),
        Q!("    umulh           " l!() ", " a1!() ", " b2!()),
        Q!("    adcs            " u4!() ", " u4!() ", " l!()),
        Q!("    adc             " u5!() ", " u5!() ", xzr"),

        // Row 2 = [u6;...;u0] = [a2;a1;a0] * [b3;...;b0]

        Q!("    mul             " l!() ", " a2!() ", " b0!()),
        Q!("    adds            " u2!() ", " u2!() ", " l!()),
        Q!("    mul             " l!() ", " a2!() ", " b1!()),
        Q!("    adcs            " u3!() ", " u3!() ", " l!()),
        Q!("    mul             " l!() ", " a2!() ", " b2!()),
        Q!("    adcs            " u4!() ", " u4!() ", " l!()),
        Q!("    mul             " l!() ", " a2!() ", " b3!()),
        Q!("    adcs            " u5!() ", " u5!() ", " l!()),
        Q!("    umulh           " u6!() ", " a2!() ", " b3!()),
        Q!("    adc             " u6!() ", " u6!() ", xzr"),

        Q!("    umulh           " l!() ", " a2!() ", " b0!()),
        Q!("    adds            " u3!() ", " u3!() ", " l!()),
        Q!("    umulh           " l!() ", " a2!() ", " b1!()),
        Q!("    adcs            " u4!() ", " u4!() ", " l!()),
        Q!("    umulh           " l!() ", " a2!() ", " b2!()),
        Q!("    adcs            " u5!() ", " u5!() ", " l!()),
        Q!("    adc             " u6!() ", " u6!() ", xzr"),

        // Row 3 = [u7;...;u0] = [a3;...a0] * [b3;...;b0]

        Q!("    mul             " l!() ", " a3!() ", " b0!()),
        Q!("    adds            " u3!() ", " u3!() ", " l!()),
        Q!("    mul             " l!() ", " a3!() ", " b1!()),
        Q!("    adcs            " u4!() ", " u4!() ", " l!()),
        Q!("    mul             " l!() ", " a3!() ", " b2!()),
        Q!("    adcs            " u5!() ", " u5!() ", " l!()),
        Q!("    mul             " l!() ", " a3!() ", " b3!()),
        Q!("    adcs            " u6!() ", " u6!() ", " l!()),
        Q!("    umulh           " u7!() ", " a3!() ", " b3!()),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),

        Q!("    umulh           " l!() ", " a3!() ", " b0!()),
        Q!("    adds            " u4!() ", " u4!() ", " l!()),
        Q!("    umulh           " l!() ", " a3!() ", " b1!()),
        Q!("    adcs            " u5!() ", " u5!() ", " l!()),
        Q!("    umulh           " l!() ", " a3!() ", " b2!()),
        Q!("    adcs            " u6!() ", " u6!() ", " l!()),
        Q!("    adc             " u7!() ", " u7!() ", xzr"),

        // Now we have the full 8-digit product 2^256 * h + l where
        // h = [u7,u6,u5,u4] and l = [u3,u2,u1,u0]
        // and this is == 38 * h + l (mod p_25519)

        Q!("    mov             " c!() ", #38"),

        Q!("    mul             " l!() ", " c!() ", " u4!()),
        Q!("    umulh           " h!() ", " c!() ", " u4!()),
        Q!("    adds            " u0!() ", " u0!() ", " l!()),

        Q!("    mul             " l!() ", " c!() ", " u5!()),
        Q!("    umulh           " u5!() ", " c!() ", " u5!()),
        Q!("    adcs            " u1!() ", " u1!() ", " l!()),

        Q!("    mul             " l!() ", " c!() ", " u6!()),
        Q!("    umulh           " u6!() ", " c!() ", " u6!()),
        Q!("    adcs            " u2!() ", " u2!() ", " l!()),

        Q!("    mul             " l!() ", " c!() ", " u7!()),
        Q!("    umulh           " u7!() ", " c!() ", " u7!()),
        Q!("    adcs            " u3!() ", " u3!() ", " l!()),
        Q!("    cset            " u4!() ", cs"),

        // Compute the top part deferring the [u5,h] addition till the following
        // carry chain. This is enough to get a good quotient estimate and saves
        // a couple of instructions.

        Q!("    adds            " u3!() ", " u3!() ", " u6!()),
        Q!("    adc             " u4!() ", " u4!() ", " u7!()),

        // Now we have reduced to 5 digits, 2^255 * H + L = [u4,u3,u2,u1,u0]
        // Use q = H + 1 as the initial quotient estimate, either right or 1 too big.

        Q!("    adds            " "xzr, " u3!() ", " u3!()),
        Q!("    orr             " u3!() ", " u3!() ", #0x8000000000000000"),
        Q!("    adc             " q!() ", " u4!() ", " u4!()),
        Q!("    mov             " c!() ", #19"),
        Q!("    madd            " l!() ", " c!() ", " q!() ", " c!()),
        Q!("    adds            " u0!() ", " u0!() ", " l!()),
        Q!("    adcs            " u1!() ", " u1!() ", " h!()),
        Q!("    adcs            " u2!() ", " u2!() ", " u5!()),
        Q!("    adcs            " u3!() ", " u3!() ", xzr"),

        // Now the effective answer is 2^256 * (CF - 1) + [u3,u2,u1,u0]
        // So we correct if CF = 0 by subtracting 19, either way masking to
        // 255 bits, i.e. by effectively adding p_25519 to the "full" answer

        Q!("    csel            " c!() ", " c!() ", xzr, cc"),
        Q!("    subs            " u0!() ", " u0!() ", " c!()),
        Q!("    sbcs            " u1!() ", " u1!() ", xzr"),
        Q!("    sbcs            " u2!() ", " u2!() ", xzr"),
        Q!("    sbc             " u3!() ", " u3!() ", xzr"),
        Q!("    bic             " u3!() ", " u3!() ", #0x8000000000000000"),

        // Write back and return

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
