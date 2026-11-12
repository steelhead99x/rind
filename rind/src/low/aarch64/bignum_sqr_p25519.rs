// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square modulo p_25519, z := (x^2) mod p_25519
// Input x[4]; output z[4]
//
//    extern void bignum_sqr_p25519_alt(uint64_t z[static 4],
//                                      const uint64_t x[static 4]);
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

macro_rules! a0 {
    () => {
        "x2"
    };
}
macro_rules! a1 {
    () => {
        "x3"
    };
}
macro_rules! a2 {
    () => {
        "x4"
    };
}
macro_rules! a3 {
    () => {
        "x5"
    };
}

macro_rules! h {
    () => {
        "x6"
    };
}
macro_rules! l {
    () => {
        "x7"
    };
}

macro_rules! u0 {
    () => {
        "x8"
    };
}
macro_rules! u1 {
    () => {
        "x9"
    };
}
macro_rules! u2 {
    () => {
        "x10"
    };
}
macro_rules! u3 {
    () => {
        "x11"
    };
}
macro_rules! u4 {
    () => {
        "x12"
    };
}
macro_rules! u5 {
    () => {
        "x13"
    };
}
macro_rules! u6 {
    () => {
        "x14"
    };
}

// Just aliases

macro_rules! q {
    () => {
        Q!(a0!())
    };
}
macro_rules! c {
    () => {
        Q!(a1!())
    };
}
macro_rules! t {
    () => {
        Q!(a2!())
    };
}
macro_rules! u7 {
    () => {
        Q!(h!())
    };
}

// Transliterated from s2n-bignum's arm/curve25519/bignum_sqr_p25519_alt.S.
/// Square modulo p_25519, z := (x^2) mod p_25519
///
/// Input x[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_sqr_p25519(z: &mut [u64; 4], x: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Load all the elements, set up an initial window [u6;...u1] = [23;03;01]
        // and chain in the addition of 02 + 12 + 13 (no carry-out is possible).
        // This gives all the "heterogeneous" terms of the squaring ready to double

        Q!("    ldp             " a0!() ", " a1!() ", [" x!() "]"),

        Q!("    mul             " u1!() ", " a0!() ", " a1!()),
        Q!("    umulh           " u2!() ", " a0!() ", " a1!()),

        Q!("    ldp             " a2!() ", " a3!() ", [" x!() ", #16]"),

        Q!("    mul             " u3!() ", " a0!() ", " a3!()),
        Q!("    umulh           " u4!() ", " a0!() ", " a3!()),

        Q!("    mul             " l!() ", " a0!() ", " a2!()),
        Q!("    umulh           " h!() ", " a0!() ", " a2!()),
        Q!("    adds            " u2!() ", " u2!() ", " l!()),

        Q!("    adcs            " u3!() ", " u3!() ", " h!()),
        Q!("    mul             " l!() ", " a1!() ", " a2!()),
        Q!("    umulh           " h!() ", " a1!() ", " a2!()),
        Q!("    adc             " h!() ", " h!() ", xzr"),
        Q!("    adds            " u3!() ", " u3!() ", " l!()),

        Q!("    mul             " u5!() ", " a2!() ", " a3!()),
        Q!("    umulh           " u6!() ", " a2!() ", " a3!()),

        Q!("    adcs            " u4!() ", " u4!() ", " h!()),
        Q!("    mul             " l!() ", " a1!() ", " a3!()),
        Q!("    umulh           " h!() ", " a1!() ", " a3!()),
        Q!("    adc             " h!() ", " h!() ", xzr"),
        Q!("    adds            " u4!() ", " u4!() ", " l!()),

        Q!("    adcs            " u5!() ", " u5!() ", " h!()),
        Q!("    adc             " u6!() ", " u6!() ", xzr"),

        // Now just double it; this simple approach seems to work better than extr

        Q!("    adds            " u1!() ", " u1!() ", " u1!()),
        Q!("    adcs            " u2!() ", " u2!() ", " u2!()),
        Q!("    adcs            " u3!() ", " u3!() ", " u3!()),
        Q!("    adcs            " u4!() ", " u4!() ", " u4!()),
        Q!("    adcs            " u5!() ", " u5!() ", " u5!()),
        Q!("    adcs            " u6!() ", " u6!() ", " u6!()),
        Q!("    cset            " u7!() ", cs"),

        // Add the homogeneous terms 00 + 11 + 22 + 33

        Q!("    umulh           " l!() ", " a0!() ", " a0!()),
        Q!("    mul             " u0!() ", " a0!() ", " a0!()),
        Q!("    adds            " u1!() ", " u1!() ", " l!()),

        Q!("    mul             " l!() ", " a1!() ", " a1!()),
        Q!("    adcs            " u2!() ", " u2!() ", " l!()),
        Q!("    umulh           " l!() ", " a1!() ", " a1!()),
        Q!("    adcs            " u3!() ", " u3!() ", " l!()),

        Q!("    mul             " l!() ", " a2!() ", " a2!()),
        Q!("    adcs            " u4!() ", " u4!() ", " l!()),
        Q!("    umulh           " l!() ", " a2!() ", " a2!()),
        Q!("    adcs            " u5!() ", " u5!() ", " l!()),

        Q!("    mul             " l!() ", " a3!() ", " a3!()),
        Q!("    adcs            " u6!() ", " u6!() ", " l!()),
        Q!("    umulh           " l!() ", " a3!() ", " a3!()),
        Q!("    adc             " u7!() ", " u7!() ", " l!()),

        // Now we have the full 8-digit product 2^256 * h + l where
        // h = [u7,u6,u5,u4] and l = [u3,u2,u1,u0]
        // and this is == 38 * h + l (mod p_25519)

        Q!("    mov             " c!() ", #38"),

        Q!("    mul             " l!() ", " c!() ", " u4!()),
        Q!("    umulh           " t!() ", " c!() ", " u4!()),
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

        // Compute the top part deferring the [u5,t] addition till the following
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
        Q!("    adcs            " u1!() ", " u1!() ", " t!()),
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
        // clobbers
        out("x10") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x14") _,
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
