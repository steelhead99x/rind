// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jmixadd_alt(uint64_t p3[static 27],
//                                 const uint64_t p1[static 27],
//                                 const uint64_t p2[static 18]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity. It is assumed that
// all the coordinates of the input points p1 and p2 are fully reduced
// mod p_521, that the z coordinate of p1 is nonzero and that neither
// p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine
// point as".
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------

// Size of individual field elements

macro_rules! NUMSIZE {
    () => {
        "72"
    };
}

// Stable homes for input arguments during main code sequence
// These are where they arrive except for input_y, initially in rdx

macro_rules! input_z {
    () => {
        "rdi"
    };
}
macro_rules! input_x {
    () => {
        "rsi"
    };
}
macro_rules! input_y {
    () => {
        "rcx"
    };
}

// Pointer-offset pairs for inputs and outputs

macro_rules! x_1 { () => { Q!(input_x!() "+ 0") } }
macro_rules! y_1 { () => { Q!(input_x!() "+ " NUMSIZE!()) } }
macro_rules! z_1 { () => { Q!(input_x!() "+ (2 * " NUMSIZE!() ")") } }

macro_rules! x_2 { () => { Q!(input_y!() "+ 0") } }
macro_rules! y_2 { () => { Q!(input_y!() "+ " NUMSIZE!()) } }

macro_rules! x_3 { () => { Q!(input_z!() "+ 0") } }
macro_rules! y_3 { () => { Q!(input_z!() "+ " NUMSIZE!()) } }
macro_rules! z_3 { () => { Q!(input_z!() "+ (2 * " NUMSIZE!() ")") } }

// Pointer-offset pairs for temporaries, with some aliasing
// The tmp field is internal storage for field mul and sqr.
// NSPACE is the total stack needed for these temporaries

macro_rules! zp2 { () => { Q!("rsp + (" NUMSIZE!() "* 0)") } }
macro_rules! ww { () => { Q!("rsp + (" NUMSIZE!() "* 0)") } }
macro_rules! resx { () => { Q!("rsp + (" NUMSIZE!() "* 0)") } }

macro_rules! yd { () => { Q!("rsp + (" NUMSIZE!() "* 1)") } }
macro_rules! y2a { () => { Q!("rsp + (" NUMSIZE!() "* 1)") } }

macro_rules! x2a { () => { Q!("rsp + (" NUMSIZE!() "* 2)") } }
macro_rules! zzx2 { () => { Q!("rsp + (" NUMSIZE!() "* 2)") } }

macro_rules! zz { () => { Q!("rsp + (" NUMSIZE!() "* 3)") } }
macro_rules! t1 { () => { Q!("rsp + (" NUMSIZE!() "* 3)") } }

macro_rules! t2 { () => { Q!("rsp + (" NUMSIZE!() "* 4)") } }
macro_rules! zzx1 { () => { Q!("rsp + (" NUMSIZE!() "* 4)") } }
macro_rules! resy { () => { Q!("rsp + (" NUMSIZE!() "* 4)") } }

macro_rules! xd { () => { Q!("rsp + (" NUMSIZE!() "* 5)") } }
macro_rules! resz { () => { Q!("rsp + (" NUMSIZE!() "* 5)") } }

macro_rules! tmp { () => { Q!("rsp + (" NUMSIZE!() "* 6)") } }

macro_rules! NSPACE { () => { Q!(NUMSIZE!() "* 7") } }

// Corresponds exactly to bignum_mul_p521_alt except temp storage

macro_rules! mul_p521 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "mov [rsp + 432], rax;\n"
        "mov r9, rdx;\n"
        "xor r10, r10;\n"
        "xor r11, r11;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, r11;\n"
        "mov [rsp + 440], r9;\n"
        "xor r12, r12;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, r12;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov [rsp + 448], r10;\n"
        "xor r13, r13;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, r13;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, 0x0;\n"
        "mov [rsp + 456], r11;\n"
        "xor r14, r14;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, r14;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov [rsp + 464], r12;\n"
        "xor r15, r15;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, r15;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, 0x0;\n"
        "mov [rsp + 472], r13;\n"
        "xor r8, r8;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, r8;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov [rsp + 480], r14;\n"
        "xor r9, r9;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "adc r9, r9;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "adc r9, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "adc r9, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "adc r9, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "adc r9, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "adc r9, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "adc r9, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "adc r9, 0x0;\n"
        "mov [rsp + 488], r15;\n"
        "xor r10, r10;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P2 "+ 0x40];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, r10;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "mul QWORD PTR [" $P2 "];\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov [rsp + 496], r8;\n"
        "xor r11, r11;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P2 "+ 0x40];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, r11;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "mul QWORD PTR [" $P2 "+ 0x8];\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, 0x0;\n"
        "xor r12, r12;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P2 "+ 0x40];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, r12;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "mul QWORD PTR [" $P2 "+ 0x10];\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "xor r13, r13;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P2 "+ 0x40];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, r13;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, 0x0;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "mul QWORD PTR [" $P2 "+ 0x18];\n"
        "add r11, rax;\n"
        "adc r12, rdx;\n"
        "adc r13, 0x0;\n"
        "xor r14, r14;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P2 "+ 0x40];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, r14;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "mul QWORD PTR [" $P2 "+ 0x20];\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "xor r15, r15;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P2 "+ 0x40];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, r15;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, 0x0;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "mul QWORD PTR [" $P2 "+ 0x28];\n"
        "add r13, rax;\n"
        "adc r14, rdx;\n"
        "adc r15, 0x0;\n"
        "xor r8, r8;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P2 "+ 0x40];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, r8;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "mul QWORD PTR [" $P2 "+ 0x30];\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P2 "+ 0x40];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "mul QWORD PTR [" $P2 "+ 0x38];\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "imul rax, [" $P2 "+ 0x40];\n"
        "add rax, r8;\n"
        "mov r8, [rsp + 496];\n"
        "mov rdx, r8;\n"
        "and rdx, 0x1ff;\n"
        "shrd r8, r9, 0x9;\n"
        "shrd r9, r10, 0x9;\n"
        "shrd r10, r11, 0x9;\n"
        "shrd r11, r12, 0x9;\n"
        "shrd r12, r13, 0x9;\n"
        "shrd r13, r14, 0x9;\n"
        "shrd r14, r15, 0x9;\n"
        "shrd r15, rax, 0x9;\n"
        "shr rax, 0x9;\n"
        "add rdx, rax;\n"
        "stc;\n"
        "adc r8, [rsp + 432];\n"
        "adc r9, [rsp + 440];\n"
        "adc r10, [rsp + 448];\n"
        "adc r11, [rsp + 456];\n"
        "adc r12, [rsp + 464];\n"
        "adc r13, [rsp + 472];\n"
        "adc r14, [rsp + 480];\n"
        "adc r15, [rsp + 488];\n"
        "adc rdx, 0xfffffffffffffe00;\n"
        "cmc;\n"
        "sbb r8, 0x0;\n"
        "mov [" $P0 "], r8;\n"
        "sbb r9, 0x0;\n"
        "mov [" $P0 "+ 0x8], r9;\n"
        "sbb r10, 0x0;\n"
        "mov [" $P0 "+ 0x10], r10;\n"
        "sbb r11, 0x0;\n"
        "mov [" $P0 "+ 0x18], r11;\n"
        "sbb r12, 0x0;\n"
        "mov [" $P0 "+ 0x20], r12;\n"
        "sbb r13, 0x0;\n"
        "mov [" $P0 "+ 0x28], r13;\n"
        "sbb r14, 0x0;\n"
        "mov [" $P0 "+ 0x30], r14;\n"
        "sbb r15, 0x0;\n"
        "mov [" $P0 "+ 0x38], r15;\n"
        "sbb rdx, 0x0;\n"
        "and rdx, 0x1ff;\n"
        "mov [" $P0 "+ 0x40], rdx"
    )}
}

// Corresponds to bignum_sqr_p521_alt except rbp is used
// in place of rcx and the output as temp storage location

macro_rules! sqr_p521 {
    ($P0:expr, $P1:expr) => { Q!(
        "mov rax, [" $P1 "];\n"
        "mul rax;\n"
        "mov [rsp + 432], rax;\n"
        "mov r9, rdx;\n"
        "xor r10, r10;\n"
        "xor r11, r11;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P1 "+ 0x8];\n"
        "add rax, rax;\n"
        "adc rdx, rdx;\n"
        "adc r11, 0x0;\n"
        "add r9, rax;\n"
        "adc r10, rdx;\n"
        "adc r11, 0x0;\n"
        "mov [rsp + 440], r9;\n"
        "xor r12, r12;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul rax;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P1 "+ 0x10];\n"
        "add rax, rax;\n"
        "adc rdx, rdx;\n"
        "adc r12, 0x0;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov [rsp + 448], r10;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P1 "+ 0x18];\n"
        "xor r13, r13;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P1 "+ 0x10];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r13, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r13, r13;\n"
        "add r11, rbx;\n"
        "adc r12, rbp;\n"
        "adc r13, 0x0;\n"
        "mov [rsp + 456], r11;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P1 "+ 0x20];\n"
        "xor r14, r14;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P1 "+ 0x18];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r14, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r14, r14;\n"
        "add r12, rbx;\n"
        "adc r13, rbp;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul rax;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov [rsp + 464], r12;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P1 "+ 0x28];\n"
        "xor r15, r15;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P1 "+ 0x20];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r15, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P1 "+ 0x18];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r15, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r15, r15;\n"
        "add r13, rbx;\n"
        "adc r14, rbp;\n"
        "adc r15, 0x0;\n"
        "mov [rsp + 472], r13;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P1 "+ 0x30];\n"
        "xor r8, r8;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P1 "+ 0x28];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P1 "+ 0x20];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r8, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r8, r8;\n"
        "add r14, rbx;\n"
        "adc r15, rbp;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul rax;\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov [rsp + 480], r14;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P1 "+ 0x38];\n"
        "xor r9, r9;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P1 "+ 0x30];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r9, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P1 "+ 0x28];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r9, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P1 "+ 0x20];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r9, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r9, r9;\n"
        "add r15, rbx;\n"
        "adc r8, rbp;\n"
        "adc r9, 0x0;\n"
        "mov [rsp + 488], r15;\n"
        "mov rax, [" $P1 "];\n"
        "mul QWORD PTR [" $P1 "+ 0x40];\n"
        "xor r10, r10;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P1 "+ 0x38];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P1 "+ 0x30];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P1 "+ 0x28];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r10, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r10, r10;\n"
        "add r8, rbx;\n"
        "adc r9, rbp;\n"
        "adc r10, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul rax;\n"
        "add r8, rax;\n"
        "adc r9, rdx;\n"
        "adc r10, 0x0;\n"
        "mov [rsp + 496], r8;\n"
        "mov rax, [" $P1 "+ 0x8];\n"
        "mul QWORD PTR [" $P1 "+ 0x40];\n"
        "xor r11, r11;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P1 "+ 0x38];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P1 "+ 0x30];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P1 "+ 0x28];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r11, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r11, r11;\n"
        "add r9, rbx;\n"
        "adc r10, rbp;\n"
        "adc r11, 0x0;\n"
        "mov rax, [" $P1 "+ 0x10];\n"
        "mul QWORD PTR [" $P1 "+ 0x40];\n"
        "xor r12, r12;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P1 "+ 0x38];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P1 "+ 0x30];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r12, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r12, r12;\n"
        "add r10, rbx;\n"
        "adc r11, rbp;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul rax;\n"
        "add r10, rax;\n"
        "adc r11, rdx;\n"
        "adc r12, 0x0;\n"
        "mov rax, [" $P1 "+ 0x18];\n"
        "mul QWORD PTR [" $P1 "+ 0x40];\n"
        "xor r13, r13;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P1 "+ 0x38];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r13, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P1 "+ 0x30];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r13, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r13, r13;\n"
        "add r11, rbx;\n"
        "adc r12, rbp;\n"
        "adc r13, 0x0;\n"
        "mov rax, [" $P1 "+ 0x20];\n"
        "mul QWORD PTR [" $P1 "+ 0x40];\n"
        "xor r14, r14;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P1 "+ 0x38];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r14, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r14, r14;\n"
        "add r12, rbx;\n"
        "adc r13, rbp;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul rax;\n"
        "add r12, rax;\n"
        "adc r13, rdx;\n"
        "adc r14, 0x0;\n"
        "mov rax, [" $P1 "+ 0x28];\n"
        "mul QWORD PTR [" $P1 "+ 0x40];\n"
        "xor r15, r15;\n"
        "mov rbx, rax;\n"
        "mov rbp, rdx;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P1 "+ 0x38];\n"
        "add rbx, rax;\n"
        "adc rbp, rdx;\n"
        "adc r15, 0x0;\n"
        "add rbx, rbx;\n"
        "adc rbp, rbp;\n"
        "adc r15, r15;\n"
        "add r13, rbx;\n"
        "adc r14, rbp;\n"
        "adc r15, 0x0;\n"
        "xor r8, r8;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul rax;\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x30];\n"
        "mul QWORD PTR [" $P1 "+ 0x40];\n"
        "add rax, rax;\n"
        "adc rdx, rdx;\n"
        "adc r8, 0x0;\n"
        "add r14, rax;\n"
        "adc r15, rdx;\n"
        "adc r8, 0x0;\n"
        "mov rax, [" $P1 "+ 0x38];\n"
        "mul QWORD PTR [" $P1 "+ 0x40];\n"
        "add rax, rax;\n"
        "adc rdx, rdx;\n"
        "add r15, rax;\n"
        "adc r8, rdx;\n"
        "mov rax, [" $P1 "+ 0x40];\n"
        "imul rax, rax;\n"
        "add rax, r8;\n"
        "mov r8, [rsp + 496];\n"
        "mov rdx, r8;\n"
        "and rdx, 0x1ff;\n"
        "shrd r8, r9, 0x9;\n"
        "shrd r9, r10, 0x9;\n"
        "shrd r10, r11, 0x9;\n"
        "shrd r11, r12, 0x9;\n"
        "shrd r12, r13, 0x9;\n"
        "shrd r13, r14, 0x9;\n"
        "shrd r14, r15, 0x9;\n"
        "shrd r15, rax, 0x9;\n"
        "shr rax, 0x9;\n"
        "add rdx, rax;\n"
        "stc;\n"
        "adc r8, [rsp + 432];\n"
        "adc r9, [rsp + 440];\n"
        "adc r10, [rsp + 448];\n"
        "adc r11, [rsp + 456];\n"
        "adc r12, [rsp + 464];\n"
        "adc r13, [rsp + 472];\n"
        "adc r14, [rsp + 480];\n"
        "adc r15, [rsp + 488];\n"
        "adc rdx, 0xfffffffffffffe00;\n"
        "cmc;\n"
        "sbb r8, 0x0;\n"
        "mov [" $P0 "], r8;\n"
        "sbb r9, 0x0;\n"
        "mov [" $P0 "+ 0x8], r9;\n"
        "sbb r10, 0x0;\n"
        "mov [" $P0 "+ 0x10], r10;\n"
        "sbb r11, 0x0;\n"
        "mov [" $P0 "+ 0x18], r11;\n"
        "sbb r12, 0x0;\n"
        "mov [" $P0 "+ 0x20], r12;\n"
        "sbb r13, 0x0;\n"
        "mov [" $P0 "+ 0x28], r13;\n"
        "sbb r14, 0x0;\n"
        "mov [" $P0 "+ 0x30], r14;\n"
        "sbb r15, 0x0;\n"
        "mov [" $P0 "+ 0x38], r15;\n"
        "sbb rdx, 0x0;\n"
        "and rdx, 0x1ff;\n"
        "mov [" $P0 "+ 0x40], rdx;\n"
    )}
}
// Corresponds exactly to bignum_sub_p521

macro_rules! sub_p521 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov rax, [" $P1 "];\n"
        "sub rax, [" $P2 "];\n"
        "mov rdx, [" $P1 "+ 0x8];\n"
        "sbb rdx, [" $P2 "+ 0x8];\n"
        "mov r8, [" $P1 "+ 0x10];\n"
        "sbb r8, [" $P2 "+ 0x10];\n"
        "mov r9, [" $P1 "+ 0x18];\n"
        "sbb r9, [" $P2 "+ 0x18];\n"
        "mov r10, [" $P1 "+ 0x20];\n"
        "sbb r10, [" $P2 "+ 0x20];\n"
        "mov r11, [" $P1 "+ 0x28];\n"
        "sbb r11, [" $P2 "+ 0x28];\n"
        "mov r12, [" $P1 "+ 0x30];\n"
        "sbb r12, [" $P2 "+ 0x30];\n"
        "mov r13, [" $P1 "+ 0x38];\n"
        "sbb r13, [" $P2 "+ 0x38];\n"
        "mov r14, [" $P1 "+ 0x40];\n"
        "sbb r14, [" $P2 "+ 0x40];\n"
        "sbb rax, 0x0;\n"
        "mov [" $P0 "], rax;\n"
        "sbb rdx, 0x0;\n"
        "mov [" $P0 "+ 0x8], rdx;\n"
        "sbb r8, 0x0;\n"
        "mov [" $P0 "+ 0x10], r8;\n"
        "sbb r9, 0x0;\n"
        "mov [" $P0 "+ 0x18], r9;\n"
        "sbb r10, 0x0;\n"
        "mov [" $P0 "+ 0x20], r10;\n"
        "sbb r11, 0x0;\n"
        "mov [" $P0 "+ 0x28], r11;\n"
        "sbb r12, 0x0;\n"
        "mov [" $P0 "+ 0x30], r12;\n"
        "sbb r13, 0x0;\n"
        "mov [" $P0 "+ 0x38], r13;\n"
        "sbb r14, 0x0;\n"
        "and r14, 0x1ff;\n"
        "mov [" $P0 "+ 0x40], r14"
    )}
}

// Additional macros to help with final multiplexing

macro_rules! testzero9 {
    ($P:expr) => { Q!(
        "mov rax, [" $P "];\n"
        "mov rbx, [" $P "+ 8];\n"
        "mov rdx, [" $P "+ 16];\n"
        "mov rbp, [" $P "+ 24];\n"
        "or rax, [" $P "+ 32];\n"
        "or rbx, [" $P "+ 40];\n"
        "or rdx, [" $P "+ 48];\n"
        "or rbp, [" $P "+ 56];\n"
        "or rax, rbx;\n"
        "or rdx, rbp;\n"
        "or rax, [" $P "+ 64];\n"
        "or rax, rdx"
    )}
}

macro_rules! mux9 {
    ($P0:expr, $PNE:expr, $PEQ:expr) => { Q!(
        "mov rax, [" $PNE "];\n"
        "mov rbx, [" $PEQ "];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "], rax;\n"
        "mov rax, [" $PNE "+ 8];\n"
        "mov rbx, [" $PEQ "+ 8];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 8], rax;\n"
        "mov rax, [" $PNE "+ 16];\n"
        "mov rbx, [" $PEQ "+ 16];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 16], rax;\n"
        "mov rax, [" $PNE "+ 24];\n"
        "mov rbx, [" $PEQ "+ 24];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 24], rax;\n"
        "mov rax, [" $PNE "+ 32];\n"
        "mov rbx, [" $PEQ "+ 32];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 32], rax;\n"
        "mov rax, [" $PNE "+ 40];\n"
        "mov rbx, [" $PEQ "+ 40];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 40], rax;\n"
        "mov rax, [" $PNE "+ 48];\n"
        "mov rbx, [" $PEQ "+ 48];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 48], rax;\n"
        "mov rax, [" $PNE "+ 56];\n"
        "mov rbx, [" $PEQ "+ 56];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 56], rax;\n"
        "mov rax, [" $PNE "+ 64];\n"
        "mov rbx, [" $PEQ "+ 64];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 64], rax"
    )}
}

macro_rules! mux9c {
    ($P0:expr, $PNE:expr) => { Q!(
        "mov rax, [" $PNE "];\n"
        "mov ebx, 1;\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "], rax;\n"
        "mov rax, [" $PNE "+ 8];\n"
        "mov ebx, 0;\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 8], rax;\n"
        "mov rax, [" $PNE "+ 16];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 16], rax;\n"
        "mov rax, [" $PNE "+ 24];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 24], rax;\n"
        "mov rax, [" $PNE "+ 32];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 32], rax;\n"
        "mov rax, [" $PNE "+ 40];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 40], rax;\n"
        "mov rax, [" $PNE "+ 48];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 48], rax;\n"
        "mov rax, [" $PNE "+ 56];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 56], rax;\n"
        "mov rax, [" $PNE "+ 64];\n"
        "cmovz rax, rbx;\n"
        "mov [" $P0 "+ 64], rax"
    )}
}

macro_rules! copy9 {
    ($P0:expr, $P1:expr) => { Q!(
        "mov rax, [" $P1 "];\n"
        "mov [" $P0 "], rax;\n"
        "mov rax, [" $P1 "+ 8];\n"
        "mov [" $P0 "+ 8], rax;\n"
        "mov rax, [" $P1 "+ 16];\n"
        "mov [" $P0 "+ 16], rax;\n"
        "mov rax, [" $P1 "+ 24];\n"
        "mov [" $P0 "+ 24], rax;\n"
        "mov rax, [" $P1 "+ 32];\n"
        "mov [" $P0 "+ 32], rax;\n"
        "mov rax, [" $P1 "+ 40];\n"
        "mov [" $P0 "+ 40], rax;\n"
        "mov rax, [" $P1 "+ 48];\n"
        "mov [" $P0 "+ 48], rax;\n"
        "mov rax, [" $P1 "+ 56];\n"
        "mov [" $P0 "+ 56], rax;\n"
        "mov rax, [" $P1 "+ 64];\n"
        "mov [" $P0 "+ 64], rax"
    )}
}

// Transliterated from s2n-bignum's x86/p521/p521_jmixadd_alt.S.
/// Point mixed addition on NIST curve P-521 in Jacobian coordinates
///
/// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
/// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
/// The "mixed" part means that p2 only has x and y coordinates, with the
/// implicit z coordinate assumed to be the identity. It is assumed that
/// all the coordinates of the input points p1 and p2 are fully reduced
/// mod p_521, that the z coordinate of p1 is nonzero and that neither
/// p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine
/// point as".
#[inline(never)]
pub(crate) fn p521_jmixadd_alt(p3: &mut [u64; 27], p1: &[u64; 27], p2: &[u64; 18]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Save registers and make room on stack for temporary variables

        Q!("    push            " "rbx"),
        Q!("    push            " "rbp"),
        Q!("    push            " "r12"),
        Q!("    push            " "r13"),
        Q!("    push            " "r14"),
        Q!("    push            " "r15"),

        Q!("    sub             " "rsp, " NSPACE!()),

        // Move the input arguments to stable places (two are already there)

        Q!("    mov             " input_y!() ", rdx"),

        // Main code, just a sequence of basic field operations

        sqr_p521!(zp2!(), z_1!()),
        mul_p521!(y2a!(), z_1!(), y_2!()),

        mul_p521!(x2a!(), zp2!(), x_2!()),
        mul_p521!(y2a!(), zp2!(), y2a!()),

        sub_p521!(xd!(), x2a!(), x_1!()),
        sub_p521!(yd!(), y2a!(), y_1!()),

        sqr_p521!(zz!(), xd!()),
        sqr_p521!(ww!(), yd!()),

        mul_p521!(zzx1!(), zz!(), x_1!()),
        mul_p521!(zzx2!(), zz!(), x2a!()),

        sub_p521!(resx!(), ww!(), zzx1!()),
        sub_p521!(t1!(), zzx2!(), zzx1!()),

        mul_p521!(resz!(), xd!(), z_1!()),

        sub_p521!(resx!(), resx!(), zzx2!()),

        sub_p521!(t2!(), zzx1!(), resx!()),

        mul_p521!(t1!(), t1!(), y_1!()),
        mul_p521!(t2!(), yd!(), t2!()),

        sub_p521!(resy!(), t2!(), t1!()),

        // Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        testzero9!(z_1!()),

        // Multiplex: if p1 <> 0 just copy the computed result from the staging area.
        // If p1 = 0 then return the point p2 augmented with an extra z = 1
        // coordinate, hence giving 0 + p2 = p2 for the final result.

        mux9!(resx!(), resx!(), x_2!()),
        mux9!(resy!(), resy!(), y_2!()),

        copy9!(x_3!(), resx!()),
        copy9!(y_3!(), resy!()),

        mux9c!(z_3!(), resz!()),

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
        p521_jmixadd_alt,
        &mut crate::low::abi::Aligned([0; 27]).0,
        &crate::low::abi::Aligned([0; 27]).0,
        &crate::low::abi::Aligned([0; 18]).0
    );
}
