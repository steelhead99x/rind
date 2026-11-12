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
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
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

// Re-use input pointer later for constant

macro_rules! d {
    () => {
        "rsi"
    };
}
macro_rules! c {
    () => {
        "rcx"
    };
}

macro_rules! dshort {
    () => {
        "esi"
    };
}

// Macro for the key "multiply and add to (c,h,l)" step, for square term

macro_rules! combadd1 {
    ($c:expr, $h:expr, $l:expr, $numa:expr) => { Q!(
        "mov rax, " $numa ";\n"
        "mul rax;\n"
        "add " $l ", rax;\n"
        "adc " $h ", rdx;\n"
        "adc " $c ", 0"
    )}
}

// A short form where we don't expect a top carry

macro_rules! combads {
    ($h:expr, $l:expr, $numa:expr) => { Q!(
        "mov rax, " $numa ";\n"
        "mul rax;\n"
        "add " $l ", rax;\n"
        "adc " $h ", rdx"
    )}
}

// A version doubling before adding, for non-square terms

macro_rules! combadd2 {
    ($c:expr, $h:expr, $l:expr, $numa:expr, $numb:expr) => { Q!(
        "mov rax, " $numa ";\n"
        "mul QWORD PTR " $numb ";\n"
        "add rax, rax;\n"
        "adc rdx, rdx;\n"
        "adc " $c ", 0;\n"
        "add " $l ", rax;\n"
        "adc " $h ", rdx;\n"
        "adc " $c ", 0"
    )}
}

// Transliterated from s2n-bignum's x86/curve25519/bignum_sqr_p25519_alt.S.
/// Square modulo p_25519, z := (x^2) mod p_25519
///
/// Input x[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_sqr_p25519_alt(z: &mut [u64; 4], x: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Save more registers to play with

        Q!("    push            " "r12"),
        Q!("    push            " "r13"),
        Q!("    push            " "r14"),
        Q!("    push            " "r15"),

        // Result term 0

        Q!("    mov             " "rax, [" x!() "]"),
        Q!("    mul             " "rax"),

        Q!("    mov             " "r8, rax"),
        Q!("    mov             " "r9, rdx"),
        Q!("    xor             " "r10, r10"),

        // Result term 1

        Q!("    xor             " "r11, r11"),
        combadd2!("r11", "r10", "r9", Q!("[" x!() "]"), Q!("[" x!() "+" "8" "]")),

        // Result term 2

        Q!("    xor             " "r12, r12"),
        combadd1!("r12", "r11", "r10", Q!("[" x!() "+" "8" "]")),
        combadd2!("r12", "r11", "r10", Q!("[" x!() "]"), Q!("[" x!() "+" "16" "]")),

        // Result term 3

        Q!("    xor             " "r13, r13"),
        combadd2!("r13", "r12", "r11", Q!("[" x!() "]"), Q!("[" x!() "+" "24" "]")),
        combadd2!("r13", "r12", "r11", Q!("[" x!() "+" "8" "]"), Q!("[" x!() "+" "16" "]")),

        // Result term 4

        Q!("    xor             " "r14, r14"),
        combadd2!("r14", "r13", "r12", Q!("[" x!() "+" "8" "]"), Q!("[" x!() "+" "24" "]")),
        combadd1!("r14", "r13", "r12", Q!("[" x!() "+" "16" "]")),

        // Result term 5

        Q!("    xor             " "r15, r15"),
        combadd2!("r15", "r14", "r13", Q!("[" x!() "+" "16" "]"), Q!("[" x!() "+" "24" "]")),

        // Result term 6

        combads!("r15", "r14", Q!("[" x!() "+" "24" "]")),

        // Now we have the full 8-digit product 2^256 * h + l where
        // h = [r15,r14,r13,r12] and l = [r11,r10,r9,r8]
        // and this is == 38 * h + l (mod p_25519)

        Q!("    mov             " dshort!() ", 38"),

        Q!("    mov             " "rax, r12"),
        Q!("    mul             " d!()),
        Q!("    add             " "r8, rax"),
        Q!("    adc             " "r9, rdx"),
        Q!("    sbb             " c!() ", " c!()),

        Q!("    mov             " "rax, r13"),
        Q!("    mul             " d!()),
        Q!("    sub             " "rdx, " c!()),
        Q!("    add             " "r9, rax"),
        Q!("    adc             " "r10, rdx"),
        Q!("    sbb             " c!() ", " c!()),

        Q!("    mov             " "rax, r14"),
        Q!("    mul             " d!()),
        Q!("    sub             " "rdx, " c!()),
        Q!("    add             " "r10, rax"),
        Q!("    adc             " "r11, rdx"),
        Q!("    sbb             " c!() ", " c!()),

        Q!("    mov             " "rax, r15"),
        Q!("    mul             " d!()),
        Q!("    sub             " "rdx, " c!()),
        Q!("    xor             " c!() ", " c!()),
        Q!("    add             " "r11, rax"),
        Q!("    mov             " "r12, rdx"),
        Q!("    adc             " "r12, " c!()),

        // Now we have reduced to 5 digits, 2^255 * h + l = [r12,r11,r10,r9,r8]
        // Use q = h + 1 as the initial quotient estimate, either right or 1 too big.

        Q!("    shld            " "r12, r11, 1"),
        Q!("    lea             " "rax, [r12 + 1]"),
        Q!("    mov             " dshort!() ", 19"),
        Q!("    bts             " "r11, 63"),
        Q!("    imul            " "rax, " d!()),
        Q!("    add             " "r8, rax"),
        Q!("    adc             " "r9, " c!()),
        Q!("    adc             " "r10, " c!()),
        Q!("    adc             " "r11, " c!()),

        // Now the effective answer is 2^256 * (CF - 1) + [u3,u2,u1,u0]
        // So we correct if CF = 0 by subtracting 19, either way masking to
        // 255 bits, i.e. by effectively adding p_25519 to the "full" answer

        Q!("    sbb             " "rax, rax"),
        Q!("    not             " "rax"),
        Q!("    and             " "rax, " d!()),
        Q!("    sub             " "r8, rax"),
        Q!("    sbb             " "r9, " c!()),
        Q!("    sbb             " "r10, " c!()),
        Q!("    sbb             " "r11, " c!()),
        Q!("    btr             " "r11, 63"),

        // Write everything back

        Q!("    mov             " "[" z!() "], r8"),
        Q!("    mov             " "[" z!() "+ 8], r9"),
        Q!("    mov             " "[" z!() "+ 16], r10"),
        Q!("    mov             " "[" z!() "+ 24], r11"),

        // Restore registers and return

        Q!("    pop             " "r15"),
        Q!("    pop             " "r14"),
        Q!("    pop             " "r13"),
        Q!("    pop             " "r12"),

        inout("rdi") z.as_mut_ptr() => _,
        inout("rsi") x.as_ptr() => _,
        // clobbers
        out("r10") _,
        out("r11") _,
        out("r12") _,
        out("r13") _,
        out("r14") _,
        out("r15") _,
        out("r8") _,
        out("r9") _,
        out("rax") _,
        out("rcx") _,
        out("rdx") _,
            )
    };
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        bignum_sqr_p25519_alt,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
