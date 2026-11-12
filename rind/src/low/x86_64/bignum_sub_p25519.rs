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

macro_rules! zero {
    () => {
        "rax"
    };
}
macro_rules! zeroe {
    () => {
        "eax"
    };
}
macro_rules! c {
    () => {
        "rcx"
    };
}
macro_rules! cshort {
    () => {
        "ecx"
    };
}

// Transliterated from s2n-bignum's x86/curve25519/bignum_sub_p25519.S.
/// Subtract modulo p_25519, z := (x - y) mod p_25519
///
/// Inputs x[4], y[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_sub_p25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Load and subtract the two inputs as [d3;d2;d1;d0] = x - y (modulo 2^256)

        Q!("    mov             " d0!() ", [" x!() "]"),
        Q!("    sub             " d0!() ", [" y!() "]"),
        Q!("    mov             " d1!() ", [" x!() "+ 8]"),
        Q!("    sbb             " d1!() ", [" y!() "+ 8]"),
        Q!("    mov             " d2!() ", [" x!() "+ 16]"),
        Q!("    sbb             " d2!() ", [" y!() "+ 16]"),
        Q!("    mov             " d3!() ", [" x!() "+ 24]"),
        Q!("    sbb             " d3!() ", [" y!() "+ 24]"),

        // Now if x < y we want to add back p_25519, which staying within 4 digits
        // means subtracting 19, since p_25519 = 2^255 - 19.
        // Let c be that constant 19 when x < y, zero otherwise.

        Q!("    sbb             " c!() ", " c!()),
        Q!("    xor             " zeroe!() ", " zeroe!()),
        Q!("    and             " c!() ", 19"),

        // Correct by adding the optional constant and masking to 255 bits

        Q!("    sub             " d0!() ", " c!()),
        Q!("    mov             " "[" z!() "], " d0!()),
        Q!("    sbb             " d1!() ", " zero!()),
        Q!("    mov             " "[" z!() "+ 8], " d1!()),
        Q!("    sbb             " d2!() ", " zero!()),
        Q!("    mov             " "[" z!() "+ 16], " d2!()),
        Q!("    sbb             " d3!() ", " zero!()),
        Q!("    btr             " d3!() ", 63"),
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
        bignum_sub_p25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
