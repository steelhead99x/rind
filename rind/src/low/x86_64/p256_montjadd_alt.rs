// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on NIST curve P-256 in Montgomery-Jacobian coordinates
//
//    extern void p256_montjadd_alt(uint64_t p3[static 12],
//                                  const uint64_t p1[static 12],
//                                  const uint64_t p2[static 12]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------

// Size of individual field elements

macro_rules! NUMSIZE {
    () => {
        "32"
    };
}

// Pointer-offset pairs for inputs and outputs
// These assume rdi = p3, rsi = p1 and rbp = p2,
// which needs to be set up explicitly before use.
// The first two hold initially, and the second is
// set up by copying the initial rdx input to rbp.
// Thereafter, no code macro modifies any of them.

macro_rules! x_1 {
    () => {
        "rsi + 0"
    };
}
macro_rules! y_1 { () => { Q!("rsi + " NUMSIZE!()) } }
macro_rules! z_1 { () => { Q!("rsi + (2 * " NUMSIZE!() ")") } }

macro_rules! x_2 {
    () => {
        "rbp + 0"
    };
}
macro_rules! y_2 { () => { Q!("rbp + " NUMSIZE!()) } }
macro_rules! z_2 { () => { Q!("rbp + (2 * " NUMSIZE!() ")") } }

macro_rules! x_3 {
    () => {
        "rdi + 0"
    };
}
macro_rules! y_3 { () => { Q!("rdi + " NUMSIZE!()) } }
macro_rules! z_3 { () => { Q!("rdi + (2 * " NUMSIZE!() ")") } }

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

macro_rules! z1sq { () => { Q!("rsp + (" NUMSIZE!() "* 0)") } }
macro_rules! ww { () => { Q!("rsp + (" NUMSIZE!() "* 0)") } }
macro_rules! resx { () => { Q!("rsp + (" NUMSIZE!() "* 0)") } }

macro_rules! yd { () => { Q!("rsp + (" NUMSIZE!() "* 1)") } }
macro_rules! y2a { () => { Q!("rsp + (" NUMSIZE!() "* 1)") } }

macro_rules! x2a { () => { Q!("rsp + (" NUMSIZE!() "* 2)") } }
macro_rules! zzx2 { () => { Q!("rsp + (" NUMSIZE!() "* 2)") } }

macro_rules! zz { () => { Q!("rsp + (" NUMSIZE!() "* 3)") } }
macro_rules! t1 { () => { Q!("rsp + (" NUMSIZE!() "* 3)") } }

macro_rules! t2 { () => { Q!("rsp + (" NUMSIZE!() "* 4)") } }
macro_rules! x1a { () => { Q!("rsp + (" NUMSIZE!() "* 4)") } }
macro_rules! zzx1 { () => { Q!("rsp + (" NUMSIZE!() "* 4)") } }
macro_rules! resy { () => { Q!("rsp + (" NUMSIZE!() "* 4)") } }

macro_rules! xd { () => { Q!("rsp + (" NUMSIZE!() "* 5)") } }
macro_rules! z2sq { () => { Q!("rsp + (" NUMSIZE!() "* 5)") } }
macro_rules! resz { () => { Q!("rsp + (" NUMSIZE!() "* 5)") } }

macro_rules! y1a { () => { Q!("rsp + (" NUMSIZE!() "* 6)") } }

macro_rules! NSPACE { () => { Q!(NUMSIZE!() "* 7") } }

// Corresponds exactly to bignum_montmul_p256_alt

macro_rules! montmul_p256 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov rbx, [" $P2 "];\n"
        "mov rax, [" $P1 "];\n"
        "mul rbx;\n"
        "mov r8, rax;\n"
        "mov r9, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rbx;\n"
        "xor r10d, r10d;\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul rbx;\n"
        "xor r11d, r11d;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul rbx;\n"
        "xor r12d, r12d;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "mov rbx, [" $P2 "+ 0x8];\n"
        "xor r13d, r13d;\n"
        "mov rax, [" $P1 "];\n"
        "mul rbx;\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "sbb r14, r14;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rbx;\n"
        "sub rdx, r14;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "sbb r14, r14;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul rbx;\n"
        "sub rdx, r14;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "sbb r14, r14;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul rbx;\n"
        "sub rdx, r14;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "xor r14d, r14d;\n"
        "mov rbx, 0x100000000;\n"
        "mov rax, r8;\n"
        "mul rbx;\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "sbb r15, r15;\n"
        "mov rax, r9;\n"
        "mul rbx;\n"
        "sub rdx, r15;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "sbb r15, r15;\n"
        "not rbx;\n"
        "lea rbx, [rbx + 0x2];\n"
        "mov rax, r8;\n"
        "mul rbx;\n"
        "sub rdx, r15;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "sbb r15, r15;\n"
        "mov rax, r9;\n"
        "mul rbx;\n"
        "sub rdx, r15;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, r14;\n"
        "mov rbx, [" $P2 "+ 0x10];\n"
        "xor r15d, r15d;\n"
        "mov rax, [" $P1 "];\n"
        "mul rbx;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "sbb r8, r8;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rbx;\n"
        "sub rdx, r8;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "sbb r8, r8;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul rbx;\n"
        "sub rdx, r8;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "sbb r8, r8;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul rbx;\n"
        "sub rdx, r8;\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, r15;\n"
        "mov rbx, [" $P2 "+ 0x18];\n"
        "xor r8d, r8d;\n"
        "mov rax, [" $P1 "];\n"
        "mul rbx;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "sbb r9, r9;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rbx;\n"
        "sub rdx, r9;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "sbb r9, r9;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul rbx;\n"
        "sub rdx, r9;\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "sbb r9, r9;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul rbx;\n"
        "sub rdx, r9;\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, r8;\n"
        "xor r9d, r9d;\n"
        "mov rbx, 0x100000000;\n"
        "mov rax, r10;\n"
        "mul rbx;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "sbb rcx, rcx;\n"
        "mov rax, r11;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "sbb rcx, rcx;\n"
        "not rbx;\n"
        "lea rbx, [rbx + 0x2];\n"
        "mov rax, r10;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "sbb rcx, rcx;\n"
        "mov rax, r11;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, r9;\n"
        "mov ecx, 0x1;\n"
        "add rcx, r12;\n"
        "dec rbx;\n"
        "adc rbx, r13;\n"
        "dec r9;\n"
        "mov rax, r9;\n"
        "adc r9, r14;\n"
        "mov r11d, 0xfffffffe;\n"
        "adc r11, r15;\n"
        "adc rax, r8;\n"
        "cmovb r12, rcx;\n"
        "cmovb r13, rbx;\n"
        "cmovb r14, r9;\n"
        "cmovb r15, r11;\n"
        "mov [" $P0 "], r12;\n"
        "mov [" $P0 "+ 0x8], r13;\n"
        "mov [" $P0 "+ 0x10], r14;\n"
        "mov [" $P0 "+ 0x18], r15"
    )}
}

// Corresponds exactly to bignum_montsqr_p256_alt

macro_rules! montsqr_p256 {
    ($P0:expr, $P1:expr) => { Q!(
        "mov rax, [" $P1 "];\n"
        "mov rbx, rax;\n"
        "mul rax;\n"
        "mov r8, rax;\n"
        "mov r15, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rbx;\n"
        "mov r9, rax;\n"
        "mov r10, rdx;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mov r13, rax;\n"
        "mul rbx;\n"
        "mov r11, rax;\n"
        "mov r12, rdx;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mov rbx, rax;\n"
        "mul r13;\n"
        "mov r13, rax;\n"
        "mov r14, rdx;\n"
        "mov rax, [" $P1 "];\n"
        "mul rbx;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "sbb rcx, rcx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "sbb rcx, rcx;\n"
        "mov rbx, [" $P1 "+ 0x18];\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "xor ecx, ecx;\n"
        "add r9, r9;\n"
        "adc r10, r10;\n"
        "adc r11, r11;\n"
        "adc r12, r12;\n"
        "adc r13, r13;\n"
        "adc r14, r14;\n"
        "adc rcx, rcx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rax;\n"
        "add r9, r15;\n"
        "adc r10, rax;\n"
        "adc r11, rdx;\n"
        "sbb r15, r15;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul rax;\n"
        "neg r15;\n"
        "adc r12, rax;\n"
        "adc r13, rdx;\n"
        "sbb r15, r15;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul rax;\n"
        "neg r15;\n"
        "adc r14, rax;\n"
        "adc rdx, rcx;\n"
        "mov r15, rdx;\n"
        "mov rbx, 0x100000000;\n"
        "mov rax, r8;\n"
        "mul rbx;\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "sbb rcx, rcx;\n"
        "mov rax, r9;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "sbb rcx, rcx;\n"
        "not rbx;\n"
        "lea rbx, [rbx + 0x2];\n"
        "mov rax, r8;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "sbb rcx, rcx;\n"
        "xor r8d, r8d;\n"
        "mov rax, r9;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, r8;\n"
        "adc r15, r8;\n"
        "adc r8, r8;\n"
        "mov rbx, 0x100000000;\n"
        "mov rax, r10;\n"
        "mul rbx;\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "sbb rcx, rcx;\n"
        "mov rax, r11;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "sbb rcx, rcx;\n"
        "not rbx;\n"
        "lea rbx, [rbx + 0x2];\n"
        "mov rax, r10;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "sbb rcx, rcx;\n"
        "xor r9d, r9d;\n"
        "mov rax, r11;\n"
        "mul rbx;\n"
        "sub rdx, rcx;\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, r9;\n"
        "mov ecx, 0x1;\n"
        "add rcx, r12;\n"
        "lea rbx, [rbx -0x1];\n"
        "adc rbx, r13;\n"
        "lea r9, [r9 -0x1];\n"
        "mov rax, r9;\n"
        "adc r9, r14;\n"
        "mov r11d, 0xfffffffe;\n"
        "adc r11, r15;\n"
        "adc rax, r8;\n"
        "cmovb r12, rcx;\n"
        "cmovb r13, rbx;\n"
        "cmovb r14, r9;\n"
        "cmovb r15, r11;\n"
        "mov [" $P0 "], r12;\n"
        "mov [" $P0 "+ 0x8], r13;\n"
        "mov [" $P0 "+ 0x10], r14;\n"
        "mov [" $P0 "+ 0x18], r15"
    )}
}

// Corresponds exactly to bignum_sub_p256

macro_rules! sub_p256 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov rax, [" $P1 "];\n"
        "sub rax, [" $P2 "];\n"
        "mov rcx, [" $P1 "+ 0x8];\n"
        "sbb rcx, [" $P2 "+ 0x8];\n"
        "mov r8, [" $P1 "+ 0x10];\n"
        "sbb r8, [" $P2 "+ 0x10];\n"
        "mov r9, [" $P1 "+ 0x18];\n"
        "sbb r9, [" $P2 "+ 0x18];\n"
        "mov r10d, 0xffffffff;\n"
        "sbb r11, r11;\n"
        "xor rdx, rdx;\n"
        "and r10, r11;\n"
        "sub rdx, r10;\n"
        "add rax, r11;\n"
        "mov [" $P0 "], rax;\n"
        "adc rcx, r10;\n"
        "mov [" $P0 "+ 0x8], rcx;\n"
        "adc r8, 0x0;\n"
        "mov [" $P0 "+ 0x10], r8;\n"
        "adc r9, rdx;\n"
        "mov [" $P0 "+ 0x18], r9"
    )}
}

// Additional macros to help with final multiplexing

macro_rules! load4 {
    ($r0:expr, $r1:expr, $r2:expr, $r3:expr, $P:expr) => { Q!(
        "mov " $r0 ", [" $P "];\n"
        "mov " $r1 ", [" $P "+ 8];\n"
        "mov " $r2 ", [" $P "+ 16];\n"
        "mov " $r3 ", [" $P "+ 24]"
    )}
}

macro_rules! store4 {
    ($P:expr, $r0:expr, $r1:expr, $r2:expr, $r3:expr) => { Q!(
        "mov [" $P "], " $r0 ";\n"
        "mov [" $P "+ 8], " $r1 ";\n"
        "mov [" $P "+ 16], " $r2 ";\n"
        "mov [" $P "+ 24], " $r3
    )}
}

macro_rules! czload4 {
    ($r0:expr, $r1:expr, $r2:expr, $r3:expr, $P:expr) => { Q!(
        "cmovz " $r0 ", [" $P "];\n"
        "cmovz " $r1 ", [" $P "+ 8];\n"
        "cmovz " $r2 ", [" $P "+ 16];\n"
        "cmovz " $r3 ", [" $P "+ 24]"
    )}
}

macro_rules! muxload4 {
    ($r0:expr, $r1:expr, $r2:expr, $r3:expr, $P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov " $r0 ", [" $P0 "];\n"
        "cmovb " $r0 ", [" $P1 "];\n"
        "cmovnbe " $r0 ", [" $P2 "];\n"
        "mov " $r1 ", [" $P0 "+ 8];\n"
        "cmovb " $r1 ", [" $P1 "+ 8];\n"
        "cmovnbe " $r1 ", [" $P2 "+ 8];\n"
        "mov " $r2 ", [" $P0 "+ 16];\n"
        "cmovb " $r2 ", [" $P1 "+ 16];\n"
        "cmovnbe " $r2 ", [" $P2 "+ 16];\n"
        "mov " $r3 ", [" $P0 "+ 24];\n"
        "cmovb " $r3 ", [" $P1 "+ 24];\n"
        "cmovnbe " $r3 ", [" $P2 "+ 24]"
    )}
}

// Transliterated from s2n-bignum's x86/p256/p256_montjadd_alt.S.
/// Point addition on NIST curve P-256 in Montgomery-Jacobian coordinates
///
/// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
/// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256.
/// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
#[inline(never)]
pub(crate) fn p256_montjadd_alt(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 12]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Save registers and make room on stack for temporary variables
        // Put the input y in rbp where it lasts as long as it's needed.

        Q!("    push            " "rbx"),
        Q!("    push            " "rbp"),
        Q!("    push            " "r12"),
        Q!("    push            " "r13"),
        Q!("    push            " "r14"),
        Q!("    push            " "r15"),

        Q!("    sub             " "rsp, " NSPACE!()),

        Q!("    mov             " "rbp, rdx"),

        // Main code, just a sequence of basic field operations
        // 12 * multiply + 4 * square + 7 * subtract

        montsqr_p256!(z1sq!(), z_1!()),
        montsqr_p256!(z2sq!(), z_2!()),

        montmul_p256!(y1a!(), z_2!(), y_1!()),
        montmul_p256!(y2a!(), z_1!(), y_2!()),

        montmul_p256!(x2a!(), z1sq!(), x_2!()),
        montmul_p256!(x1a!(), z2sq!(), x_1!()),
        montmul_p256!(y2a!(), z1sq!(), y2a!()),
        montmul_p256!(y1a!(), z2sq!(), y1a!()),

        sub_p256!(xd!(), x2a!(), x1a!()),
        sub_p256!(yd!(), y2a!(), y1a!()),

        montsqr_p256!(zz!(), xd!()),
        montsqr_p256!(ww!(), yd!()),

        montmul_p256!(zzx1!(), zz!(), x1a!()),
        montmul_p256!(zzx2!(), zz!(), x2a!()),

        sub_p256!(resx!(), ww!(), zzx1!()),
        sub_p256!(t1!(), zzx2!(), zzx1!()),

        montmul_p256!(xd!(), xd!(), z_1!()),

        sub_p256!(resx!(), resx!(), zzx2!()),

        sub_p256!(t2!(), zzx1!(), resx!()),

        montmul_p256!(t1!(), t1!(), y1a!()),

        montmul_p256!(resz!(), xd!(), z_2!()),
        montmul_p256!(t2!(), yd!(), t2!()),

        sub_p256!(resy!(), t2!(), t1!()),

        // Load in the z coordinates of the inputs to check for P1 = 0 and P2 = 0
        // The condition codes get set by a comparison (P2 != 0) - (P1 != 0)
        // So "NBE" <=> ~(CF \/ ZF) <=> P1 = 0 /\ ~(P2 = 0)
        // and "B"  <=> CF          <=> ~(P1 = 0) /\ P2 = 0
        // and "Z"  <=> ZF          <=> (P1 = 0 <=> P2 = 0)

        load4!("r8", "r9", "r10", "r11", z_1!()),

        Q!("    mov             " "rax, r8"),
        Q!("    mov             " "rdx, r9"),
        Q!("    or              " "rax, r10"),
        Q!("    or              " "rdx, r11"),
        Q!("    or              " "rax, rdx"),
        Q!("    neg             " "rax"),
        Q!("    sbb             " "rax, rax"),

        load4!("r12", "r13", "r14", "r15", z_2!()),

        Q!("    mov             " "rbx, r12"),
        Q!("    mov             " "rdx, r13"),
        Q!("    or              " "rbx, r14"),
        Q!("    or              " "rdx, r15"),
        Q!("    or              " "rbx, rdx"),
        Q!("    neg             " "rbx"),
        Q!("    sbb             " "rbx, rbx"),

        Q!("    cmp             " "rbx, rax"),

        // Multiplex the outputs accordingly, re-using the z's in registers

        Q!("    cmovb           " "r12, r8"),
        Q!("    cmovb           " "r13, r9"),
        Q!("    cmovb           " "r14, r10"),
        Q!("    cmovb           " "r15, r11"),

        czload4!("r12", "r13", "r14", "r15", resz!()),

        muxload4!("rax", "rbx", "rcx", "rdx", resx!(), x_1!(), x_2!()),
        muxload4!("r8", "r9", "r10", "r11", resy!(), y_1!(), y_2!()),

        // Finally store back the multiplexed values

        store4!(x_3!(), "rax", "rbx", "rcx", "rdx"),
        store4!(y_3!(), "r8", "r9", "r10", "r11"),
        store4!(z_3!(), "r12", "r13", "r14", "r15"),

        // Restore stack and registers

        Q!("    add             " "rsp, " NSPACE!()),
        Q!("    pop             " "r15"),
        Q!("    pop             " "r14"),
        Q!("    pop             " "r13"),
        Q!("    pop             " "r12"),
        Q!("    pop             " "rbp"),
        Q!("    pop             " "rbx"),

        inout("rdi") p3.as_mut_ptr() => _,
        inout("rsi") p1.as_ptr() => _,
        inout("rdx") p2.as_ptr() => _,
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
            )
    };
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        p256_montjadd_alt,
        &mut crate::low::abi::Aligned([0; 12]).0,
        &crate::low::abi::Aligned([0; 12]).0,
        &crate::low::abi::Aligned([0; 12]).0
    );
}
