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
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

macro_rules! z {
    () => {
        "rdi"
    };
}
macro_rules! x {
    () => {
        "rsi"
    };
}
macro_rules! y {
    () => {
        "rdx"
    };
}

macro_rules! d0 {
    () => {
        "r8"
    };
}
macro_rules! d1 {
    () => {
        "r9"
    };
}
macro_rules! d2 {
    () => {
        "r10"
    };
}
macro_rules! d3 {
    () => {
        "r11"
    };
}

// These also re-use inputs x and y when safe to do so

macro_rules! c0 {
    () => {
        "rax"
    };
}
macro_rules! c1 {
    () => {
        "rcx"
    };
}
macro_rules! c2 {
    () => {
        "rsi"
    };
}
macro_rules! c3 {
    () => {
        "rdx"
    };
}
macro_rules! c0short {
    () => {
        "eax"
    };
}
macro_rules! c1short {
    () => {
        "ecx"
    };
}
macro_rules! c2short {
    () => {
        "esi"
    };
}
macro_rules! c3short {
    () => {
        "edx"
    };
}

// Transliterated from s2n-bignum's x86/curve25519/bignum_add_p25519.S.
/// Add modulo p_25519, z := (x + y) mod p_25519, assuming x and y reduced
///
/// Inputs x[4], y[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_add_p25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Add as [d3; d2; d1; d0] = x + y; since we assume x, y < 2^255 - 19
        // this sum fits in 256 bits.

        Q!("    mov             " d0!() ", [" x!() "]"),
        Q!("    add             " d0!() ", [" y!() "]"),
        Q!("    mov             " d1!() ", [" x!() "+ 8]"),
        Q!("    adc             " d1!() ", [" y!() "+ 8]"),
        Q!("    mov             " d2!() ", [" x!() "+ 16]"),
        Q!("    adc             " d2!() ", [" y!() "+ 16]"),
        Q!("    mov             " d3!() ", [" x!() "+ 24]"),
        Q!("    adc             " d3!() ", [" y!() "+ 24]"),

        // Now x + y >= 2^255 - 19 <=> x + y + 19 >= 2^255.
        // Form [c3; c2; c1; c0] = (x + y) + 19

        Q!("    mov             " c0short!() ", 19"),
        Q!("    xor             " c1short!() ", " c1short!()),
        Q!("    xor             " c2short!() ", " c2short!()),
        Q!("    xor             " c3short!() ", " c3short!()),

        Q!("    add             " c0!() ", " d0!()),
        Q!("    adc             " c1!() ", " d1!()),
        Q!("    adc             " c2!() ", " d2!()),
        Q!("    adc             " c3!() ", " d3!()),

        // Test the top bit to see if this is >= 2^255, and clear it as a masking
        // so that in that case the result is exactly (x + y) - (2^255 - 19).
        // Then select the output according to that top bit as that or just x + y.

        Q!("    btr             " c3!() ", 63"),
        Q!("    cmovc           " d0!() ", " c0!()),
        Q!("    cmovc           " d1!() ", " c1!()),
        Q!("    cmovc           " d2!() ", " c2!()),
        Q!("    cmovc           " d3!() ", " c3!()),

        // Store the result

        Q!("    mov             " "[" z!() "], " d0!()),
        Q!("    mov             " "[" z!() "+ 8], " d1!()),
        Q!("    mov             " "[" z!() "+ 16], " d2!()),
        Q!("    mov             " "[" z!() "+ 24], " d3!()),

        inout("rdi") z.as_mut_ptr() => _,
        inout("rsi") x.as_ptr() => _,
        inout("rdx") y.as_ptr() => _,
        // clobbers
        out("r10") _,
        out("r11") _,
        out("r8") _,
        out("r9") _,
        out("rax") _,
        out("rcx") _,
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
