// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square z := x^2
// Input x[n]; output z[k]
//
//    extern void bignum_sqr(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x);
//
// Does the "z := x^2" operation where x is n digits and result z is k.
// Truncates the result in general unless k >= 2 * n
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = n, X3 = x
// ----------------------------------------------------------------------------

macro_rules! p {
    () => {
        "x0"
    };
}
macro_rules! z {
    () => {
        "x1"
    };
}
macro_rules! n {
    () => {
        "x2"
    };
}
macro_rules! x {
    () => {
        "x3"
    };
}

macro_rules! l {
    () => {
        "x4"
    };
}
macro_rules! h {
    () => {
        "x5"
    };
}
macro_rules! c {
    () => {
        "x6"
    };
}
macro_rules! k {
    () => {
        "x7"
    };
}
macro_rules! i {
    () => {
        "x8"
    };
}
macro_rules! a {
    () => {
        "x9"
    };
}
macro_rules! b {
    () => {
        "x10"
    };
}
macro_rules! d {
    () => {
        "x11"
    };
}
macro_rules! y {
    () => {
        "x12"
    };
}
macro_rules! htop {
    () => {
        "x13"
    };
}
macro_rules! hh {
    () => {
        "x14"
    };
}
macro_rules! ll {
    () => {
        "x15"
    };
}

// Transliterated from s2n-bignum's arm/generic/bignum_sqr.S.
/// Square z := x^2
///
/// Input x[n]; output z[k]
///
/// Does the "z := x^2" operation where x is n digits and result z is k.
/// Truncates the result in general unless k >= 2 * n
#[inline(never)]
pub(crate) fn bignum_sqr(z: &mut [u64], x: &[u64]) {
    assert!(z.len() >= 2 * x.len());
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // If p = 0 the result is trivial and nothing needs doing

        Q!("    cbz             " p!() ", " Label!("Lbignum_sqr_end", 2, After)),

        // initialize (hh,ll) = 0

        Q!("    mov             " ll!() ", xzr"),
        Q!("    mov             " hh!() ", xzr"),

        // Iterate outer loop from k = 0 ... k = p - 1 producing result digits

        Q!("    mov             " k!() ", xzr"),
        Q!(Label!("Lbignum_sqr_outerloop", 3) ":"),

        // First let bot = MAX 0 (k + 1 - n) and top = MIN (k + 1) n
        // We want to accumulate all x[i] * x[k - i] for bot <= i < top
        // For the optimization of squaring we avoid duplication and do
        // 2 * x[i] * x[k - i] for i < htop, where htop = MIN ((k+1)/2) n
        // Initialize i = bot; in fact just compute bot as i directly.

        Q!("    add             " i!() ", " k!() ", #1"),
        Q!("    lsr             " htop!() ", " i!() ", #1"),
        Q!("    cmp             " htop!() ", " n!()),
        Q!("    csel            " htop!() ", " htop!() ", " n!() ", cc"),
        Q!("    subs            " i!() ", " i!() ", " n!()),
        Q!("    csel            " i!() ", " i!() ", xzr, cs"),

        // Initialize the three-part local sum (c,h,l)

        Q!("    mov             " l!() ", xzr"),
        Q!("    mov             " h!() ", xzr"),
        Q!("    mov             " c!() ", xzr"),

        // If htop <= bot then main doubled part of the sum is empty

        Q!("    cmp             " htop!() ", " i!()),
        Q!("    bls             " Label!("Lbignum_sqr_nosumming", 4, After)),

        // Use a moving pointer for [y] = x[k-i] for the cofactor

        Q!("    sub             " y!() ", " k!() ", " i!()),
        Q!("    lsl             " y!() ", " y!() ", #3"),
        Q!("    add             " y!() ", " x!() ", " y!()),

        // Do the main part of the sum x[i] * x[k - i] for 2 * i < k

        Q!(Label!("Lbignum_sqr_innerloop", 5) ":"),
        Q!("    ldr             " a!() ", [" x!() ", " i!() ", lsl #3]"),
        Q!("    ldr             " b!() ", [" y!() "], #-8"),
        Q!("    mul             " d!() ", " a!() ", " b!()),
        Q!("    umulh           " a!() ", " a!() ", " b!()),
        Q!("    adds            " l!() ", " l!() ", " d!()),
        Q!("    adcs            " h!() ", " h!() ", " a!()),
        Q!("    adc             " c!() ", " c!() ", xzr"),
        Q!("    add             " i!() ", " i!() ", #1"),
        Q!("    cmp             " i!() ", " htop!()),
        Q!("    bne             " Label!("Lbignum_sqr_innerloop", 5, Before)),

        // Now double it

        Q!("    adds            " l!() ", " l!() ", " l!()),
        Q!("    adcs            " h!() ", " h!() ", " h!()),
        Q!("    adc             " c!() ", " c!() ", " c!()),

        // If k is even (which means 2 * i = k) and i < n add the extra x[i]^2 term

        Q!(Label!("Lbignum_sqr_nosumming", 4) ":"),

        Q!("    ands            " "xzr, " k!() ", #1"),
        Q!("    bne             " Label!("Lbignum_sqr_innerend", 6, After)),
        Q!("    cmp             " i!() ", " n!()),
        Q!("    bcs             " Label!("Lbignum_sqr_innerend", 6, After)),

        Q!("    ldr             " a!() ", [" x!() ", " i!() ", lsl #3]"),
        Q!("    mul             " d!() ", " a!() ", " a!()),
        Q!("    umulh           " a!() ", " a!() ", " a!()),
        Q!("    adds            " ll!() ", " ll!() ", " d!()),
        Q!("    adcs            " hh!() ", " hh!() ", " a!()),
        Q!("    adc             " c!() ", " c!() ", xzr"),

        // Now add the local sum into the global sum, store and shift

        Q!(Label!("Lbignum_sqr_innerend", 6) ":"),
        Q!("    adds            " l!() ", " l!() ", " ll!()),
        Q!("    str             " l!() ", [" z!() ", " k!() ", lsl #3]"),
        Q!("    adcs            " ll!() ", " h!() ", " hh!()),
        Q!("    adc             " hh!() ", " c!() ", xzr"),

        Q!("    add             " k!() ", " k!() ", #1"),
        Q!("    cmp             " k!() ", " p!()),
        Q!("    bcc             " Label!("Lbignum_sqr_outerloop", 3, Before)),

        Q!(Label!("Lbignum_sqr_end", 2) ":"),
        inout("x0") z.len() => _,
        inout("x1") z.as_mut_ptr() => _,
        inout("x2") x.len() => _,
        inout("x3") x.as_ptr() => _,
        // clobbers
        out("x10") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x14") _,
        out("x15") _,
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
    crate::low::abi::call!(bignum_sqr, &mut [0; 8], &[1, 2, 3, 4]);
}
