// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Inverse square root modulo p_25519 = 2^255 - 19
// Input x[4]; output function return (Legendre symbol) and z[4]
//
// extern int64_t bignum_invsqrt_p25519_alt(uint64_t z[static 4],
//                                          const uint64_t x[static 4]);
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
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
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
        "rsp + 0"
    };
}
macro_rules! b { () => { Q!("rsp + (4 * " N!() ")") } }
macro_rules! s { () => { Q!("rsp + (8 * " N!() ")") } }
macro_rules! t { () => { Q!("rsp + (12 * " N!() ")") } }
macro_rules! u { () => { Q!("rsp + (16 * " N!() ")") } }
macro_rules! res { () => { Q!("QWORD PTR [rsp + (20 * " N!() ")]") } }

// Total size to reserve on the stack

macro_rules! NSPACE { () => { Q!("22 * " N!()) } }

// Corrupted versions when stack is down 8 more

macro_rules! u8 { () => { Q!("rsp + (17 * " N!() ")") } }

// Syntactic variants to make x86_att version simpler to generate

macro_rules! A {
    () => {
        "0"
    };
}
macro_rules! B { () => { Q!("(4 * " N!() ")") } }
macro_rules! S { () => { Q!("(8 * " N!() ")") } }
macro_rules! T { () => { Q!("(12 * " N!() ")") } }
macro_rules! U { () => { Q!("(16 * " N!() ")") } }
macro_rules! U8 { () => { Q!("(17 * " N!() ")") } }

// Transliterated from s2n-bignum's x86/curve25519/bignum_invsqrt_p25519_alt.S.
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
pub(crate) fn bignum_invsqrt_p25519_alt(z: &mut [u64; 4], x: &[u64; 4]) -> u64 {
    let ret: u64;
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // In this case the Windows form literally makes a subroutine call.
        // This avoids hassle arising from subroutine offsets

        // Save registers and make room for temporaries

        Q!("    push            " "rbx"),
        Q!("    push            " "rbp"),
        Q!("    push            " "r12"),
        Q!("    push            " "r13"),
        Q!("    push            " "r14"),
        Q!("    push            " "r15"),

        Q!("    sub             " "rsp, " NSPACE!()),

        // Save the return pointer for the end so we can overwrite rdi later

        Q!("    mov             " res!() ", rdi"),

        // Set up reduced version of the input argument a = x mod p_25519. Then
        // get the candidate inverse square root s = a^{252-3}

        Q!("    mov             " "rdx, [rsi]"),
        Q!("    mov             " "rcx, [rsi + 0x8]"),
        Q!("    mov             " "r8, [rsi + 0x10]"),
        Q!("    mov             " "r9, [rsi + 0x18]"),
        Q!("    mov             " "eax, 0x1"),
        Q!("    xor             " "r10d, r10d"),
        Q!("    bts             " "r9, 0x3f"),
        Q!("    adc             " "rax, r10"),
        Q!("    imul            " "rax, rax, 0x13"),
        Q!("    add             " "rdx, rax"),
        Q!("    adc             " "rcx, r10"),
        Q!("    adc             " "r8, r10"),
        Q!("    adc             " "r9, r10"),
        Q!("    mov             " "eax, 0x13"),
        Q!("    cmovb           " "rax, r10"),
        Q!("    sub             " "rdx, rax"),
        Q!("    sbb             " "rcx, r10"),
        Q!("    sbb             " "r8, r10"),
        Q!("    sbb             " "r9, r10"),
        Q!("    btr             " "r9, 0x3f"),
        Q!("    mov             " "[rsp + " A!() "], rdx"),
        Q!("    mov             " "[rsp + " A!() "+ 0x8], rcx"),
        Q!("    mov             " "[rsp + " A!() "+ 0x10], r8"),
        Q!("    mov             " "[rsp + " A!() "+ 0x18], r9"),

        // Power 2^2 - 1 = 3

        Q!("    lea             " "rdi, [rsp + " T!() "]"),
        Q!("    mov             " "rsi, 1"),
        Q!("    lea             " "rdx, [rsp + " A!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " T!() "]"),
        Q!("    lea             " "rsi, [rsp + " T!() "]"),
        Q!("    lea             " "rdx, [rsp + " A!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^4 - 1 = 15

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 2"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " T!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^5 - 1 = 31

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 1"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " B!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " A!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^10 - 1

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 5"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " T!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^20 - 1

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 10"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " T!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^25 - 1

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 5"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " B!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^50 - 1

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 25"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " T!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^100 - 1

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 50"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " T!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^125 - 1

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 25"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " B!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^250 - 1

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 125"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " B!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Power 2^252 - 3

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    mov             " "rsi, 2"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " S!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " A!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // s = a^{2^252-3} is now one candidate inverse square root.
        // Generate the other one t = s * j_25519 where j_25519 = sqrt(-1)

        Q!("    mov             " "rax, 0xc4ee1b274a0ea0b0"),
        Q!("    mov             " "[rsp + " T!() "], rax"),
        Q!("    mov             " "rax, 0x2f431806ad2fe478"),
        Q!("    mov             " "[rsp + " T!() "+ 8], rax"),
        Q!("    mov             " "rax, 0x2b4d00993dfbd7a7"),
        Q!("    mov             " "[rsp + " T!() "+ 16], rax"),
        Q!("    mov             " "rax, 0x2b8324804fc1df0b"),
        Q!("    mov             " "[rsp + " T!() "+ 24], rax"),

        Q!("    lea             " "rdi, [rsp + " T!() "]"),
        Q!("    lea             " "rsi, [rsp + " S!() "]"),
        Q!("    lea             " "rdx, [rsp + " T!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        // Now multiplex between them according to whether a * s^2 = 1

        Q!("    lea             " "rdi, [rsp + " B!() "]"),
        Q!("    mov             " "rsi, 1"),
        Q!("    lea             " "rdx, [rsp + " S!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " B!() "]"),
        Q!("    lea             " "rsi, [rsp + " A!() "]"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        Q!("    mov             " "rax, [rsp + " B!() "]"),
        Q!("    xor             " "rax, 1"),
        Q!("    mov             " "rbx, [rsp + " B!() "+ 8]"),
        Q!("    or              " "rax, rbx"),
        Q!("    mov             " "rcx, [rsp + " B!() "+ 16]"),
        Q!("    mov             " "rdx, [rsp + " B!() "+ 24]"),
        Q!("    or              " "rcx, rdx"),
        Q!("    or              " "rax, rcx"),

        Q!("    mov             " "rax, [rsp + " S!() "]"),
        Q!("    mov             " "rbx, [rsp + " T!() "]"),
        Q!("    cmovnz          " "rax, rbx"),
        Q!("    mov             " "rbx, [rsp + " S!() "+ 8]"),
        Q!("    mov             " "rcx, [rsp + " T!() "+ 8]"),
        Q!("    cmovnz          " "rbx, rcx"),
        Q!("    mov             " "rcx, [rsp + " S!() "+ 16]"),
        Q!("    mov             " "rdx, [rsp + " T!() "+ 16]"),
        Q!("    cmovnz          " "rcx, rdx"),
        Q!("    mov             " "rbp, [rsp + " S!() "+ 24]"),
        Q!("    mov             " "rdx, [rsp + " T!() "+ 24]"),
        Q!("    cmovnz          " "rbp, rdx"),

        // For definiteness, choose "positive" (LSB=0) inverse square root

        Q!("    xor             " "edx, edx"),
        Q!("    lea             " "r8, [rdx -19]"),
        Q!("    lea             " "r11, [rdx -1]"),
        Q!("    mov             " "r9, r11"),
        Q!("    mov             " "r10, r11"),
        Q!("    btr             " "r11, 63"),

        Q!("    sub             " "r8, rax"),
        Q!("    sbb             " "r9, rbx"),
        Q!("    sbb             " "r10, rcx"),
        Q!("    sbb             " "r11, rbp"),

        Q!("    mov             " "rdx, " res!()),
        Q!("    test            " "rax, 1"),
        Q!("    cmovnz          " "rax, r8"),
        Q!("    mov             " "[rdx], rax"),
        Q!("    cmovnz          " "rbx, r9"),
        Q!("    mov             " "[rdx + 8], rbx"),
        Q!("    cmovnz          " "rcx, r10"),
        Q!("    mov             " "[rdx + 16], rcx"),
        Q!("    cmovnz          " "rbp, r11"),
        Q!("    mov             " "[rdx + 24], rbp"),

        // Determine if it is indeed an inverse square root, also distinguishing
        // the degenerate x * z^2 == 0 (mod p_25519) case, which is equivalent to
        // x == 0 (mod p_25519). Hence return the Legendre-Jacobi symbol as required.

        Q!("    lea             " "rdi, [rsp + " B!() "]"),
        Q!("    mov             " "rsi, 1"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2, After)),

        Q!("    lea             " "rdi, [rsp + " B!() "]"),
        Q!("    lea             " "rsi, [rsp + " A!() "]"),
        Q!("    lea             " "rdx, [rsp + " B!() "]"),
        Q!("    call            " Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3, After)),

        Q!("    mov             " "rax, 1"),
        Q!("    mov             " "rbp, [rsp + " B!() "]"),
        Q!("    xor             " "rax, rbp"),
        Q!("    mov             " "rbx, [rsp + " B!() "+ 8]"),
        Q!("    or              " "rax, rbx"),
        Q!("    or              " "rbp, rbx"),
        Q!("    mov             " "rcx, [rsp + " B!() "+ 16]"),
        Q!("    mov             " "rdx, [rsp + " B!() "+ 24]"),
        Q!("    or              " "rcx, rdx"),
        Q!("    or              " "rax, rcx"),
        Q!("    or              " "rbp, rcx"),

        Q!("    neg             " "rax"),
        Q!("    sbb             " "rax, rax"),
        Q!("    lea             " "rax, [rax + rax + 1]"),

        Q!("    test            " "rbp, rbp"),
        Q!("    cmovz           " "rax, rbp"),

        // Restore stack and registers

        Q!("    add             " "rsp, " NSPACE!()),

        Q!("    pop             " "r15"),
        Q!("    pop             " "r14"),
        Q!("    pop             " "r13"),
        Q!("    pop             " "r12"),
        Q!("    pop             " "rbp"),
        Q!("    pop             " "rbx"),
        // proc hoisting in -> ret after Lbignum_invsqrt_p25519_alt_nsqr_p25519
        Q!("    jmp             " Label!("hoist_finish", 4, After)),

        // *************************************************************
        // Local z = x * y
        // *************************************************************

        Q!(Label!("Lbignum_invsqrt_p25519_alt_mul_p25519", 3) ":"),

        Q!("    mov             " "rcx, rdx"),
        Q!("    mov             " "rax, [rsi]"),
        Q!("    mul             " "QWORD PTR [rcx]"),
        Q!("    mov             " "r8, rax"),
        Q!("    mov             " "r9, rdx"),
        Q!("    xor             " "r10, r10"),
        Q!("    xor             " "r11, r11"),
        Q!("    mov             " "rax, [rsi]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x8]"),
        Q!("    add             " "r9, rax"),
        Q!("    adc             " "r10, rdx"),
        Q!("    mov             " "rax, [rsi + 0x8]"),
        Q!("    mul             " "QWORD PTR [rcx]"),
        Q!("    add             " "r9, rax"),
        Q!("    adc             " "r10, rdx"),
        Q!("    adc             " "r11, 0x0"),
        Q!("    xor             " "r12, r12"),
        Q!("    mov             " "rax, [rsi]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x10]"),
        Q!("    add             " "r10, rax"),
        Q!("    adc             " "r11, rdx"),
        Q!("    adc             " "r12, r12"),
        Q!("    mov             " "rax, [rsi + 0x8]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x8]"),
        Q!("    add             " "r10, rax"),
        Q!("    adc             " "r11, rdx"),
        Q!("    adc             " "r12, 0x0"),
        Q!("    mov             " "rax, [rsi + 0x10]"),
        Q!("    mul             " "QWORD PTR [rcx]"),
        Q!("    add             " "r10, rax"),
        Q!("    adc             " "r11, rdx"),
        Q!("    adc             " "r12, 0x0"),
        Q!("    xor             " "r13, r13"),
        Q!("    mov             " "rax, [rsi]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x18]"),
        Q!("    add             " "r11, rax"),
        Q!("    adc             " "r12, rdx"),
        Q!("    adc             " "r13, r13"),
        Q!("    mov             " "rax, [rsi + 0x8]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x10]"),
        Q!("    add             " "r11, rax"),
        Q!("    adc             " "r12, rdx"),
        Q!("    adc             " "r13, 0x0"),
        Q!("    mov             " "rax, [rsi + 0x10]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x8]"),
        Q!("    add             " "r11, rax"),
        Q!("    adc             " "r12, rdx"),
        Q!("    adc             " "r13, 0x0"),
        Q!("    mov             " "rax, [rsi + 0x18]"),
        Q!("    mul             " "QWORD PTR [rcx]"),
        Q!("    add             " "r11, rax"),
        Q!("    adc             " "r12, rdx"),
        Q!("    adc             " "r13, 0x0"),
        Q!("    xor             " "r14, r14"),
        Q!("    mov             " "rax, [rsi + 0x8]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x18]"),
        Q!("    add             " "r12, rax"),
        Q!("    adc             " "r13, rdx"),
        Q!("    adc             " "r14, r14"),
        Q!("    mov             " "rax, [rsi + 0x10]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x10]"),
        Q!("    add             " "r12, rax"),
        Q!("    adc             " "r13, rdx"),
        Q!("    adc             " "r14, 0x0"),
        Q!("    mov             " "rax, [rsi + 0x18]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x8]"),
        Q!("    add             " "r12, rax"),
        Q!("    adc             " "r13, rdx"),
        Q!("    adc             " "r14, 0x0"),
        Q!("    xor             " "r15, r15"),
        Q!("    mov             " "rax, [rsi + 0x10]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x18]"),
        Q!("    add             " "r13, rax"),
        Q!("    adc             " "r14, rdx"),
        Q!("    adc             " "r15, r15"),
        Q!("    mov             " "rax, [rsi + 0x18]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x10]"),
        Q!("    add             " "r13, rax"),
        Q!("    adc             " "r14, rdx"),
        Q!("    adc             " "r15, 0x0"),
        Q!("    mov             " "rax, [rsi + 0x18]"),
        Q!("    mul             " "QWORD PTR [rcx + 0x18]"),
        Q!("    add             " "r14, rax"),
        Q!("    adc             " "r15, rdx"),
        Q!("    mov             " "esi, 0x26"),
        Q!("    mov             " "rax, r12"),
        Q!("    mul             " "rsi"),
        Q!("    add             " "r8, rax"),
        Q!("    adc             " "r9, rdx"),
        Q!("    sbb             " "rcx, rcx"),
        Q!("    mov             " "rax, r13"),
        Q!("    mul             " "rsi"),
        Q!("    sub             " "rdx, rcx"),
        Q!("    add             " "r9, rax"),
        Q!("    adc             " "r10, rdx"),
        Q!("    sbb             " "rcx, rcx"),
        Q!("    mov             " "rax, r14"),
        Q!("    mul             " "rsi"),
        Q!("    sub             " "rdx, rcx"),
        Q!("    add             " "r10, rax"),
        Q!("    adc             " "r11, rdx"),
        Q!("    sbb             " "rcx, rcx"),
        Q!("    mov             " "rax, r15"),
        Q!("    mul             " "rsi"),
        Q!("    sub             " "rdx, rcx"),
        Q!("    xor             " "rcx, rcx"),
        Q!("    add             " "r11, rax"),
        Q!("    mov             " "r12, rdx"),
        Q!("    adc             " "r12, rcx"),
        Q!("    shld            " "r12, r11, 0x1"),
        Q!("    lea             " "rax, [r12 + 0x1]"),
        Q!("    mov             " "esi, 0x13"),
        Q!("    bts             " "r11, 0x3f"),
        Q!("    imul            " "rax, rsi"),
        Q!("    add             " "r8, rax"),
        Q!("    adc             " "r9, rcx"),
        Q!("    adc             " "r10, rcx"),
        Q!("    adc             " "r11, rcx"),
        Q!("    sbb             " "rax, rax"),
        Q!("    not             " "rax"),
        Q!("    and             " "rax, rsi"),
        Q!("    sub             " "r8, rax"),
        Q!("    sbb             " "r9, rcx"),
        Q!("    sbb             " "r10, rcx"),
        Q!("    sbb             " "r11, rcx"),
        Q!("    btr             " "r11, 0x3f"),
        Q!("    mov             " "[rdi], r8"),
        Q!("    mov             " "[rdi + 0x8], r9"),
        Q!("    mov             " "[rdi + 0x10], r10"),
        Q!("    mov             " "[rdi + 0x18], r11"),
        Q!("    ret             " ),

        // *************************************************************
        // Local z = 2^n * x
        // *************************************************************

        Q!(Label!("Lbignum_invsqrt_p25519_alt_nsqr_p25519", 2) ":"),

        // Copy input argument into u

        Q!("    mov             " "rax, [rdx]"),
        Q!("    mov             " "rbx, [rdx + 8]"),
        Q!("    mov             " "rcx, [rdx + 16]"),
        Q!("    mov             " "rdx, [rdx + 24]"),
        Q!("    mov             " "[rsp + " U8!() "], rax"),
        Q!("    mov             " "[rsp + " U8!() "+ 8], rbx"),
        Q!("    mov             " "[rsp + " U8!() "+ 16], rcx"),
        Q!("    mov             " "[rsp + " U8!() "+ 24], rdx"),

        // Main squaring loop, accumulating in u consistently  and
        // only ensuring the intermediates are < 2 * p_25519 = 2^256 - 38

        Q!(Label!("Lbignum_invsqrt_p25519_alt_loop", 5) ":"),
        Q!("    mov             " "rax, [rsp + " U8!() "]"),
        Q!("    mul             " "rax"),
        Q!("    mov             " "r8, rax"),
        Q!("    mov             " "r9, rdx"),
        Q!("    xor             " "r10, r10"),
        Q!("    xor             " "r11, r11"),
        Q!("    mov             " "rax, [rsp + " U8!() "]"),
        Q!("    mul             " "QWORD PTR [rsp + " U8!() "+ 0x8]"),
        Q!("    add             " "rax, rax"),
        Q!("    adc             " "rdx, rdx"),
        Q!("    adc             " "r11, 0x0"),
        Q!("    add             " "r9, rax"),
        Q!("    adc             " "r10, rdx"),
        Q!("    adc             " "r11, 0x0"),
        Q!("    xor             " "r12, r12"),
        Q!("    mov             " "rax, [rsp + " U8!() "+ 0x8]"),
        Q!("    mul             " "rax"),
        Q!("    add             " "r10, rax"),
        Q!("    adc             " "r11, rdx"),
        Q!("    adc             " "r12, 0x0"),
        Q!("    mov             " "rax, [rsp + " U8!() "]"),
        Q!("    mul             " "QWORD PTR [rsp + " U8!() "+ 0x10]"),
        Q!("    add             " "rax, rax"),
        Q!("    adc             " "rdx, rdx"),
        Q!("    adc             " "r12, 0x0"),
        Q!("    add             " "r10, rax"),
        Q!("    adc             " "r11, rdx"),
        Q!("    adc             " "r12, 0x0"),
        Q!("    xor             " "r13, r13"),
        Q!("    mov             " "rax, [rsp + " U8!() "]"),
        Q!("    mul             " "QWORD PTR [rsp + " U8!() "+ 0x18]"),
        Q!("    add             " "rax, rax"),
        Q!("    adc             " "rdx, rdx"),
        Q!("    adc             " "r13, 0x0"),
        Q!("    add             " "r11, rax"),
        Q!("    adc             " "r12, rdx"),
        Q!("    adc             " "r13, 0x0"),
        Q!("    mov             " "rax, [rsp + " U8!() "+ 0x8]"),
        Q!("    mul             " "QWORD PTR [rsp + " U8!() "+ 0x10]"),
        Q!("    add             " "rax, rax"),
        Q!("    adc             " "rdx, rdx"),
        Q!("    adc             " "r13, 0x0"),
        Q!("    add             " "r11, rax"),
        Q!("    adc             " "r12, rdx"),
        Q!("    adc             " "r13, 0x0"),
        Q!("    xor             " "r14, r14"),
        Q!("    mov             " "rax, [rsp + " U8!() "+ 0x8]"),
        Q!("    mul             " "QWORD PTR [rsp + " U8!() "+ 0x18]"),
        Q!("    add             " "rax, rax"),
        Q!("    adc             " "rdx, rdx"),
        Q!("    adc             " "r14, 0x0"),
        Q!("    add             " "r12, rax"),
        Q!("    adc             " "r13, rdx"),
        Q!("    adc             " "r14, 0x0"),
        Q!("    mov             " "rax, [rsp + " U8!() "+ 0x10]"),
        Q!("    mul             " "rax"),
        Q!("    add             " "r12, rax"),
        Q!("    adc             " "r13, rdx"),
        Q!("    adc             " "r14, 0x0"),
        Q!("    xor             " "r15, r15"),
        Q!("    mov             " "rax, [rsp + " U8!() "+ 0x10]"),
        Q!("    mul             " "QWORD PTR [rsp + " U8!() "+ 0x18]"),
        Q!("    add             " "rax, rax"),
        Q!("    adc             " "rdx, rdx"),
        Q!("    adc             " "r15, 0x0"),
        Q!("    add             " "r13, rax"),
        Q!("    adc             " "r14, rdx"),
        Q!("    adc             " "r15, 0x0"),
        Q!("    mov             " "rax, [rsp + " U8!() "+ 0x18]"),
        Q!("    mul             " "rax"),
        Q!("    add             " "r14, rax"),
        Q!("    adc             " "r15, rdx"),
        Q!("    mov             " "ebx, 0x26"),
        Q!("    mov             " "rax, r12"),
        Q!("    mul             " "rbx"),
        Q!("    add             " "r8, rax"),
        Q!("    adc             " "r9, rdx"),
        Q!("    sbb             " "rcx, rcx"),
        Q!("    mov             " "rax, r13"),
        Q!("    mul             " "rbx"),
        Q!("    sub             " "rdx, rcx"),
        Q!("    add             " "r9, rax"),
        Q!("    adc             " "r10, rdx"),
        Q!("    sbb             " "rcx, rcx"),
        Q!("    mov             " "rax, r14"),
        Q!("    mul             " "rbx"),
        Q!("    sub             " "rdx, rcx"),
        Q!("    add             " "r10, rax"),
        Q!("    adc             " "r11, rdx"),
        Q!("    sbb             " "rcx, rcx"),
        Q!("    mov             " "rax, r15"),
        Q!("    mul             " "rbx"),
        Q!("    sub             " "rdx, rcx"),
        Q!("    xor             " "rcx, rcx"),
        Q!("    add             " "r11, rax"),
        Q!("    mov             " "r12, rdx"),
        Q!("    adc             " "r12, rcx"),
        Q!("    shld            " "r12, r11, 0x1"),
        Q!("    btr             " "r11, 0x3f"),
        Q!("    mov             " "edx, 0x13"),
        Q!("    imul            " "rdx, r12"),
        Q!("    add             " "r8, rdx"),
        Q!("    adc             " "r9, rcx"),
        Q!("    adc             " "r10, rcx"),
        Q!("    adc             " "r11, rcx"),
        Q!("    mov             " "[rsp + " U8!() "], r8"),
        Q!("    mov             " "[rsp + " U8!() "+ 0x8], r9"),
        Q!("    mov             " "[rsp + " U8!() "+ 0x10], r10"),
        Q!("    mov             " "[rsp + " U8!() "+ 0x18], r11"),

        // Loop as applicable

        Q!("    dec             " "rsi"),
        Q!("    jnz             " Label!("Lbignum_invsqrt_p25519_alt_loop", 5, Before)),

        // We know the intermediate result x < 2^256 - 38, and now we do strict
        // modular reduction mod 2^255 - 19. Note x < 2^255 - 19 <=> x + 19 < 2^255
        // which is equivalent to a "ns" condition. We just use the results where
        // they were in registers [r11;r10;r9;r8] instead of re-loading them.

        Q!("    mov             " "eax, 19"),
        Q!("    xor             " "ebx, ebx"),
        Q!("    xor             " "ecx, ecx"),
        Q!("    xor             " "edx, edx"),
        Q!("    add             " "rax, r8"),
        Q!("    adc             " "rbx, r9"),
        Q!("    adc             " "rcx, r10"),
        Q!("    adc             " "rdx, r11"),

        Q!("    cmovns          " "rax, r8"),
        Q!("    cmovns          " "rbx, r9"),
        Q!("    cmovns          " "rcx, r10"),
        Q!("    cmovns          " "rdx, r11"),
        Q!("    btr             " "rdx, 63"),
        Q!("    mov             " "[rdi], rax"),
        Q!("    mov             " "[rdi + 8], rbx"),
        Q!("    mov             " "[rdi + 16], rcx"),
        Q!("    mov             " "[rdi + 24], rdx"),
        Q!("    ret             " ),
        Q!(Label!("hoist_finish", 4) ":"),
        inout("rdi") z.as_mut_ptr() => _,
        inout("rsi") x.as_ptr() => _,
        out("rax") ret,
        // clobbers
        out("r10") _,
        out("r11") _,
        out("r12") _,
        out("r13") _,
        out("r14") _,
        out("r15") _,
        out("r8") _,
        out("r9") _,
        out("rcx") _,
        out("rdx") _,
            )
    };
    ret
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        bignum_invsqrt_p25519_alt,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
