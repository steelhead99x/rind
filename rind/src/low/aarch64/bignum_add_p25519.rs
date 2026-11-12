// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add modulo p_25519, z := (x + y) mod p_25519, assuming x and y reduced
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_add_p25519(uint64_t z[static 4], const uint64_t x[static 4],
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
macro_rules! d0 {
    () => {
        "x3"
    };
}
macro_rules! d1 {
    () => {
        "x4"
    };
}
macro_rules! d2 {
    () => {
        "x5"
    };
}
macro_rules! d3 {
    () => {
        "x6"
    };
}
macro_rules! c0 {
    () => {
        "x7"
    };
}
macro_rules! c1 {
    () => {
        "x8"
    };
}
macro_rules! c2 {
    () => {
        "x9"
    };
}
macro_rules! c3 {
    () => {
        "x10"
    };
}

// Transliterated from s2n-bignum's arm/curve25519/bignum_add_p25519.S.
/// Add modulo p_25519, z := (x + y) mod p_25519, assuming x and y reduced
///
/// Inputs x[4], y[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_add_p25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Add as [d3; d2; d1; d0] = x + y; since we assume x, y < 2^255 - 19
        // this sum fits in 256 bits

        Q!("    ldp             " d0!() ", " d1!() ", [" x!() "]"),
        Q!("    ldp             " c0!() ", " c1!() ", [" y!() "]"),
        Q!("    adds            " d0!() ", " d0!() ", " c0!()),
        Q!("    adcs            " d1!() ", " d1!() ", " c1!()),
        Q!("    ldp             " d2!() ", " d3!() ", [" x!() ", #16]"),
        Q!("    ldp             " c0!() ", " c1!() ", [" y!() ", #16]"),
        Q!("    adcs            " d2!() ", " d2!() ", " c0!()),
        Q!("    adc             " d3!() ", " d3!() ", " c1!()),

        // Now x + y >= 2^255 - 19 <=> x + y + (2^255 + 19) >= 2^256
        // Form [c3; c2; c1; c0] = (x + y) + (2^255 + 19), with CF for the comparison

        Q!("    mov             " c3!() ", #0x8000000000000000"),
        Q!("    adds            " c0!() ", " d0!() ", #19"),
        Q!("    adcs            " c1!() ", " d1!() ", xzr"),
        Q!("    adcs            " c2!() ", " d2!() ", xzr"),
        Q!("    adcs            " c3!() ", " d3!() ", " c3!()),

        // If the comparison holds, select [c3; c2; c1; c0]. There's no need to mask
        // it since in this case it is ((x + y) + (2^255 + 19)) - 2^256 because the
        // top carry is lost, which is the desired (x + y) - (2^255 - 19).

        Q!("    csel            " d0!() ", " d0!() ", " c0!() ", cc"),
        Q!("    csel            " d1!() ", " d1!() ", " c1!() ", cc"),
        Q!("    csel            " d2!() ", " d2!() ", " c2!() ", cc"),
        Q!("    csel            " d3!() ", " d3!() ", " c3!() ", cc"),

        // Store the result

        Q!("    stp             " d0!() ", " d1!() ", [" z!() "]"),
        Q!("    stp             " d2!() ", " d3!() ", [" z!() ", #16]"),

        inout("x0") z.as_mut_ptr() => _,
        inout("x1") x.as_ptr() => _,
        inout("x2") y.as_ptr() => _,
        // clobbers
        out("x10") _,
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
        bignum_add_p25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
