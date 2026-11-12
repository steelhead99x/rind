// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Subtract modulo p_25519, z := (x - y) mod p_25519
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_sub_p25519(uint64_t z[static 4], const uint64_t x[static 4],
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
macro_rules! c {
    () => {
        "x3"
    };
}
macro_rules! l {
    () => {
        "x4"
    };
}
macro_rules! d0 {
    () => {
        "x5"
    };
}
macro_rules! d1 {
    () => {
        "x6"
    };
}
macro_rules! d2 {
    () => {
        "x7"
    };
}
macro_rules! d3 {
    () => {
        "x8"
    };
}

// Transliterated from s2n-bignum's arm/curve25519/bignum_sub_p25519.S.
/// Subtract modulo p_25519, z := (x - y) mod p_25519
///
/// Inputs x[4], y[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_sub_p25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // First just subtract the numbers as [d3; d2; d1; d0] = x - y,
        // with the inverted carry flag meaning CF <=> x >= y.

        Q!("    ldp             " d0!() ", " d1!() ", [" x!() "]"),
        Q!("    ldp             " l!() ", " c!() ", [" y!() "]"),
        Q!("    subs            " d0!() ", " d0!() ", " l!()),
        Q!("    sbcs            " d1!() ", " d1!() ", " c!()),
        Q!("    ldp             " d2!() ", " d3!() ", [" x!() ", #16]"),
        Q!("    ldp             " l!() ", " c!() ", [" y!() ", #16]"),
        Q!("    sbcs            " d2!() ", " d2!() ", " l!()),
        Q!("    sbcs            " d3!() ", " d3!() ", " c!()),

        // Now if x < y we want to add back p_25519, which staying within 255 bits
        // means subtracting 19, since p_25519 = 2^255 - 19.
        // Let c be that constant 19 when x < y, zero otherwise.

        Q!("    mov             " l!() ", #19"),
        Q!("    csel            " c!() ", " l!() ", xzr, cc"),

        // Correct by adding the optional constant and masking to 255 bits

        Q!("    subs            " d0!() ", " d0!() ", " c!()),
        Q!("    sbcs            " d1!() ", " d1!() ", xzr"),
        Q!("    sbcs            " d2!() ", " d2!() ", xzr"),
        Q!("    sbc             " d3!() ", " d3!() ", xzr"),
        Q!("    and             " d3!() ", " d3!() ", #0x7FFFFFFFFFFFFFFF"),

        // Store the result

        Q!("    stp             " d0!() ", " d1!() ", [" z!() "]"),
        Q!("    stp             " d2!() ", " d3!() ", [" z!() ", #16]"),

        inout("x0") z.as_mut_ptr() => _,
        inout("x1") x.as_ptr() => _,
        inout("x2") y.as_ptr() => _,
        // clobbers
        out("x3") _,
        out("x4") _,
        out("x5") _,
        out("x6") _,
        out("x7") _,
        out("x8") _,
            )
    };
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        bignum_sub_p25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
