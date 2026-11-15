// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jadd(uint64_t p3[static 27], const uint64_t p1[static 27],
//                          const uint64_t p2[static 27]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input points p1 and p2 are
// fully reduced mod p_521, that both z coordinates are nonzero and
// that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents
// the same affine point as".
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
macro_rules! z_2 { () => { Q!(input_y!() "+ (2 * " NUMSIZE!() ")") } }

macro_rules! x_3 { () => { Q!(input_z!() "+ 0") } }
macro_rules! y_3 { () => { Q!(input_z!() "+ " NUMSIZE!()) } }
macro_rules! z_3 { () => { Q!(input_z!() "+ (2 * " NUMSIZE!() ")") } }

// Pointer-offset pairs for temporaries, with some aliasing
// The tmp field is internal storage for field mul and sqr.
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

macro_rules! tmp { () => { Q!("rsp + (" NUMSIZE!() "* 7)") } }

macro_rules! NSPACE {
    () => {
        "568"
    };
}

// Corresponds exactly to bignum_mul_p521

macro_rules! mul_p521 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "xor ebp, ebp;\n"
        "mov rdx, [" $P2 "];\n"
        "mulx r9, r8, [" $P1 "];\n"
        "mov [rsp + 504], r8;\n"
        "mulx r10, rbx, [" $P1 "+ 0x8];\n"
        "adc r9, rbx;\n"
        "mulx r11, rbx, [" $P1 "+ 0x10];\n"
        "adc r10, rbx;\n"
        "mulx r12, rbx, [" $P1 "+ 0x18];\n"
        "adc r11, rbx;\n"
        "mulx r13, rbx, [" $P1 "+ 0x20];\n"
        "adc r12, rbx;\n"
        "mulx r14, rbx, [" $P1 "+ 0x28];\n"
        "adc r13, rbx;\n"
        "mulx r15, rbx, [" $P1 "+ 0x30];\n"
        "adc r14, rbx;\n"
        "mulx r8, rbx, [" $P1 "+ 0x38];\n"
        "adc r15, rbx;\n"
        "adc r8, rbp;\n"
        "mov rdx, [" $P2 "+ 0x8];\n"
        "xor ebp, ebp;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mov [rsp + 512], r9;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mulx r9, rax, [" $P1 "+ 0x38];\n"
        "adcx r8, rax;\n"
        "adox r9, rbp;\n"
        "adc r9, rbp;\n"
        "mov rdx, [" $P2 "+ 0x10];\n"
        "xor ebp, ebp;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mov [rsp + 520], r10;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx r10, rax, [" $P1 "+ 0x38];\n"
        "adcx r9, rax;\n"
        "adox r10, rbp;\n"
        "adc r10, rbp;\n"
        "mov rdx, [" $P2 "+ 0x18];\n"
        "xor ebp, ebp;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mov [rsp + 528], r11;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx r11, rax, [" $P1 "+ 0x38];\n"
        "adcx r10, rax;\n"
        "adox r11, rbp;\n"
        "adc r11, rbp;\n"
        "mov rdx, [" $P2 "+ 0x20];\n"
        "xor ebp, ebp;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mov [rsp + 536], r12;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx r12, rax, [" $P1 "+ 0x38];\n"
        "adcx r11, rax;\n"
        "adox r12, rbp;\n"
        "adc r12, rbp;\n"
        "mov rdx, [" $P2 "+ 0x28];\n"
        "xor ebp, ebp;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mov [rsp + 544], r13;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx r13, rax, [" $P1 "+ 0x38];\n"
        "adcx r12, rax;\n"
        "adox r13, rbp;\n"
        "adc r13, rbp;\n"
        "mov rdx, [" $P2 "+ 0x30];\n"
        "xor ebp, ebp;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mov [rsp + 552], r14;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx r14, rax, [" $P1 "+ 0x38];\n"
        "adcx r13, rax;\n"
        "adox r14, rbp;\n"
        "adc r14, rbp;\n"
        "mov rdx, [" $P2 "+ 0x38];\n"
        "xor ebp, ebp;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mov [rsp + 560], r15;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx r15, rax, [" $P1 "+ 0x38];\n"
        "adcx r14, rax;\n"
        "adox r15, rbp;\n"
        "adc r15, rbp;\n"
        "mov rdx, [" $P1 "+ 0x40];\n"
        "xor ebp, ebp;\n"
        "mulx rbx, rax, [" $P2 "];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P2 "+ 0x8];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P2 "+ 0x10];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P2 "+ 0x18];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P2 "+ 0x20];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P2 "+ 0x28];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx rbx, rax, [" $P2 "+ 0x30];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P2 "+ 0x38];\n"
        "adcx r15, rax;\n"
        "adox rbx, rbp;\n"
        "adc rbp, rbx;\n"
        "mov rdx, [" $P2 "+ 0x40];\n"
        "xor eax, eax;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x38];\n"
        "adcx r15, rax;\n"
        "adox rbp, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x40];\n"
        "adc rbp, rax;\n"
        "mov rax, r8;\n"
        "and rax, 0x1ff;\n"
        "shrd r8, r9, 0x9;\n"
        "shrd r9, r10, 0x9;\n"
        "shrd r10, r11, 0x9;\n"
        "shrd r11, r12, 0x9;\n"
        "shrd r12, r13, 0x9;\n"
        "shrd r13, r14, 0x9;\n"
        "shrd r14, r15, 0x9;\n"
        "shrd r15, rbp, 0x9;\n"
        "shr rbp, 0x9;\n"
        "add rbp, rax;\n"
        "stc;\n"
        "adc r8, [rsp + 504];\n"
        "adc r9, [rsp + 512];\n"
        "adc r10, [rsp + 520];\n"
        "adc r11, [rsp + 528];\n"
        "adc r12, [rsp + 536];\n"
        "adc r13, [rsp + 544];\n"
        "adc r14, [rsp + 552];\n"
        "adc r15, [rsp + 560];\n"
        "adc rbp, 0xfffffffffffffe00;\n"
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
        "sbb rbp, 0x0;\n"
        "and rbp, 0x1ff;\n"
        "mov [" $P0 "+ 0x40], rbp"
    )}
}

// Corresponds exactly to bignum_sqr_p521

macro_rules! sqr_p521 {
    ($P0:expr, $P1:expr) => { Q!(
        "xor ebp, ebp;\n"
        "mov rdx, [" $P1 "];\n"
        "mulx rax, r9, [" $P1 "+ 0x8];\n"
        "mov [rsp + 512], r9;\n"
        "mulx rbx, r10, [" $P1 "+ 0x10];\n"
        "adcx r10, rax;\n"
        "mov [rsp + 520], r10;\n"
        "mulx rax, r11, [" $P1 "+ 0x18];\n"
        "adcx r11, rbx;\n"
        "mulx rbx, r12, [" $P1 "+ 0x20];\n"
        "adcx r12, rax;\n"
        "mulx rax, r13, [" $P1 "+ 0x28];\n"
        "adcx r13, rbx;\n"
        "mulx rbx, r14, [" $P1 "+ 0x30];\n"
        "adcx r14, rax;\n"
        "mulx r8, r15, [" $P1 "+ 0x38];\n"
        "adcx r15, rbx;\n"
        "adcx r8, rbp;\n"
        "xor ebp, ebp;\n"
        "mov rdx, [" $P1 "+ 0x8];\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mov [rsp + 528], r11;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mov [rsp + 536], r12;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mulx r9, rax, [" $P1 "+ 0x38];\n"
        "adcx r8, rax;\n"
        "adox r9, rbp;\n"
        "mov rdx, [" $P1 "+ 0x20];\n"
        "mulx r10, rax, [" $P1 "+ 0x28];\n"
        "adcx r9, rax;\n"
        "adox r10, rbp;\n"
        "adcx r10, rbp;\n"
        "xor ebp, ebp;\n"
        "mov rdx, [" $P1 "+ 0x10];\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mov [rsp + 544], r13;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mov [rsp + 552], r14;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x38];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mov rdx, [" $P1 "+ 0x30];\n"
        "mulx r11, rax, [" $P1 "+ 0x20];\n"
        "adcx r10, rax;\n"
        "adox r11, rbp;\n"
        "mulx r12, rax, [" $P1 "+ 0x28];\n"
        "adcx r11, rax;\n"
        "adox r12, rbp;\n"
        "adcx r12, rbp;\n"
        "xor ebp, ebp;\n"
        "mov rdx, [" $P1 "+ 0x18];\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r15, rax;\n"
        "adox r8, rbx;\n"
        "mov [rsp + 560], r15;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x38];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mov rdx, [" $P1 "+ 0x38];\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx r13, rax, [" $P1 "+ 0x28];\n"
        "adcx r12, rax;\n"
        "adox r13, rbp;\n"
        "mulx r14, rax, [" $P1 "+ 0x30];\n"
        "adcx r13, rax;\n"
        "adox r14, rbp;\n"
        "adcx r14, rbp;\n"
        "xor ebp, ebp;\n"
        "mov rdx, [" $P1 "];\n"
        "mulx rbx, rax, rdx;\n"
        "mov [rsp + 504], rax;\n"
        "mov rax, [rsp + 512];\n"
        "adcx rax, rax;\n"
        "adox rax, rbx;\n"
        "mov [rsp + 512], rax;\n"
        "mov rax, [rsp + 520];\n"
        "mov rdx, [" $P1 "+ 0x8];\n"
        "mulx rbx, rdx, rdx;\n"
        "adcx rax, rax;\n"
        "adox rax, rdx;\n"
        "mov [rsp + 520], rax;\n"
        "mov rax, [rsp + 528];\n"
        "adcx rax, rax;\n"
        "adox rax, rbx;\n"
        "mov [rsp + 528], rax;\n"
        "mov rax, [rsp + 536];\n"
        "mov rdx, [" $P1 "+ 0x10];\n"
        "mulx rbx, rdx, rdx;\n"
        "adcx rax, rax;\n"
        "adox rax, rdx;\n"
        "mov [rsp + 536], rax;\n"
        "mov rax, [rsp + 544];\n"
        "adcx rax, rax;\n"
        "adox rax, rbx;\n"
        "mov [rsp + 544], rax;\n"
        "mov rax, [rsp + 552];\n"
        "mov rdx, [" $P1 "+ 0x18];\n"
        "mulx rbx, rdx, rdx;\n"
        "adcx rax, rax;\n"
        "adox rax, rdx;\n"
        "mov [rsp + 552], rax;\n"
        "mov rax, [rsp + 560];\n"
        "adcx rax, rax;\n"
        "adox rax, rbx;\n"
        "mov [rsp + 560], rax;\n"
        "mov rdx, [" $P1 "+ 0x20];\n"
        "mulx rbx, rdx, rdx;\n"
        "adcx r8, r8;\n"
        "adox r8, rdx;\n"
        "adcx r9, r9;\n"
        "adox r9, rbx;\n"
        "mov rdx, [" $P1 "+ 0x28];\n"
        "mulx rbx, rdx, rdx;\n"
        "adcx r10, r10;\n"
        "adox r10, rdx;\n"
        "adcx r11, r11;\n"
        "adox r11, rbx;\n"
        "mov rdx, [" $P1 "+ 0x30];\n"
        "mulx rbx, rdx, rdx;\n"
        "adcx r12, r12;\n"
        "adox r12, rdx;\n"
        "adcx r13, r13;\n"
        "adox r13, rbx;\n"
        "mov rdx, [" $P1 "+ 0x38];\n"
        "mulx r15, rdx, rdx;\n"
        "adcx r14, r14;\n"
        "adox r14, rdx;\n"
        "adcx r15, rbp;\n"
        "adox r15, rbp;\n"
        "mov rdx, [" $P1 "+ 0x40];\n"
        "mov rbp, rdx;\n"
        "imul rbp, rbp;\n"
        "add rdx, rdx;\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x18];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x20];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x28];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x30];\n"
        "adcx r14, rax;\n"
        "adox r15, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x38];\n"
        "adcx r15, rax;\n"
        "adox rbp, rbx;\n"
        "adc rbp, 0x0;\n"
        "mov rax, r8;\n"
        "and rax, 0x1ff;\n"
        "shrd r8, r9, 0x9;\n"
        "shrd r9, r10, 0x9;\n"
        "shrd r10, r11, 0x9;\n"
        "shrd r11, r12, 0x9;\n"
        "shrd r12, r13, 0x9;\n"
        "shrd r13, r14, 0x9;\n"
        "shrd r14, r15, 0x9;\n"
        "shrd r15, rbp, 0x9;\n"
        "shr rbp, 0x9;\n"
        "add rbp, rax;\n"
        "stc;\n"
        "adc r8, [rsp + 504];\n"
        "adc r9, [rsp + 512];\n"
        "adc r10, [rsp + 520];\n"
        "adc r11, [rsp + 528];\n"
        "adc r12, [rsp + 536];\n"
        "adc r13, [rsp + 544];\n"
        "adc r14, [rsp + 552];\n"
        "adc r15, [rsp + 560];\n"
        "adc rbp, 0xfffffffffffffe00;\n"
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
        "sbb rbp, 0x0;\n"
        "and rbp, 0x1ff;\n"
        "mov [" $P0 "+ 0x40], rbp"
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

macro_rules! load9 {
    ($r0:expr, $r1:expr, $r2:expr, $r3:expr, $r4:expr, $r5:expr, $r6:expr, $r7:expr, $ra:expr, $P:expr) => { Q!(
        "mov " $r0 ", [" $P "];\n"
        "mov " $r1 ", [" $P "+ 8];\n"
        "mov " $r2 ", [" $P "+ 16];\n"
        "mov " $r3 ", [" $P "+ 24];\n"
        "mov " $r4 ", [" $P "+ 32];\n"
        "mov " $r5 ", [" $P "+ 40];\n"
        "mov " $r6 ", [" $P "+ 48];\n"
        "mov " $r7 ", [" $P "+ 56];\n"
        "mov " $ra ", [" $P "+ 64]"
    )}
}

macro_rules! store9 {
    ($P:expr, $r0:expr, $r1:expr, $r2:expr, $r3:expr, $r4:expr, $r5:expr, $r6:expr, $r7:expr, $ra:expr) => { Q!(
        "mov [" $P "], " $r0 ";\n"
        "mov [" $P "+ 8], " $r1 ";\n"
        "mov [" $P "+ 16], " $r2 ";\n"
        "mov [" $P "+ 24], " $r3 ";\n"
        "mov [" $P "+ 32], " $r4 ";\n"
        "mov [" $P "+ 40], " $r5 ";\n"
        "mov [" $P "+ 48], " $r6 ";\n"
        "mov [" $P "+ 56], " $r7 ";\n"
        "mov [" $P "+ 64], " $ra
    )}
}

macro_rules! muxload9 {
    ($r0:expr, $r1:expr, $r2:expr, $r3:expr, $r4:expr, $r5:expr, $r6:expr, $r7:expr, $ra:expr, $P0:expr, $P1:expr, $P2:expr) => { Q!(
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
        "cmovnbe " $r3 ", [" $P2 "+ 24];\n"
        "mov " $r4 ", [" $P0 "+ 32];\n"
        "cmovb " $r4 ", [" $P1 "+ 32];\n"
        "cmovnbe " $r4 ", [" $P2 "+ 32];\n"
        "mov " $r5 ", [" $P0 "+ 40];\n"
        "cmovb " $r5 ", [" $P1 "+ 40];\n"
        "cmovnbe " $r5 ", [" $P2 "+ 40];\n"
        "mov " $r6 ", [" $P0 "+ 48];\n"
        "cmovb " $r6 ", [" $P1 "+ 48];\n"
        "cmovnbe " $r6 ", [" $P2 "+ 48];\n"
        "mov " $r7 ", [" $P0 "+ 56];\n"
        "cmovb " $r7 ", [" $P1 "+ 56];\n"
        "cmovnbe " $r7 ", [" $P2 "+ 56];\n"
        "mov " $ra ", [" $P0 "+ 64];\n"
        "cmovb " $ra ", [" $P1 "+ 64];\n"
        "cmovnbe " $ra ", [" $P2 "+ 64]"
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

// Transliterated from s2n-bignum's x86/p521/p521_jadd.S.
/// Point addition on NIST curve P-521 in Jacobian coordinates
///
/// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
/// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
/// It is assumed that all coordinates of the input points p1 and p2 are
/// fully reduced mod p_521, that both z coordinates are nonzero and
/// that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents
/// the same affine point as".
#[inline(never)]
pub(crate) fn p521_jadd(p3: &mut [u64; 27], p1: &[u64; 27], p2: &[u64; 27]) {
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

        sqr_p521!(z1sq!(), z_1!()),
        sqr_p521!(z2sq!(), z_2!()),

        mul_p521!(y1a!(), z_2!(), y_1!()),
        mul_p521!(y2a!(), z_1!(), y_2!()),

        mul_p521!(x2a!(), z1sq!(), x_2!()),
        mul_p521!(x1a!(), z2sq!(), x_1!()),
        mul_p521!(y2a!(), z1sq!(), y2a!()),
        mul_p521!(y1a!(), z2sq!(), y1a!()),

        sub_p521!(xd!(), x2a!(), x1a!()),
        sub_p521!(yd!(), y2a!(), y1a!()),

        sqr_p521!(zz!(), xd!()),
        sqr_p521!(ww!(), yd!()),

        mul_p521!(zzx1!(), zz!(), x1a!()),
        mul_p521!(zzx2!(), zz!(), x2a!()),

        sub_p521!(resx!(), ww!(), zzx1!()),
        sub_p521!(t1!(), zzx2!(), zzx1!()),

        mul_p521!(xd!(), xd!(), z_1!()),

        sub_p521!(resx!(), resx!(), zzx2!()),

        sub_p521!(t2!(), zzx1!(), resx!()),

        mul_p521!(t1!(), t1!(), y1a!()),
        mul_p521!(resz!(), xd!(), z_2!()),
        mul_p521!(t2!(), yd!(), t2!()),

        sub_p521!(resy!(), t2!(), t1!()),

        // Load in the z coordinates of the inputs to check for P1 = 0 and P2 = 0
        // The condition codes get set by a comparison (P2 != 0) - (P1 != 0)
        // So "NBE" <=> ~(CF \/ ZF) <=> P1 = 0 /\ ~(P2 = 0)
        // and "B"  <=> CF          <=> ~(P1 = 0) /\ P2 = 0
        // and "Z"  <=> ZF          <=> (P1 = 0 <=> P2 = 0)

        load9!("r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rbp", z_1!()),
        Q!("    or              " "r8, r9"),
        Q!("    or              " "r10, r11"),
        Q!("    or              " "r12, r13"),
        Q!("    or              " "r14, r15"),
        Q!("    or              " "r8, r10"),
        Q!("    or              " "r12, r14"),
        Q!("    or              " "r8, rbp"),
        Q!("    or              " "r8, r12"),
        Q!("    neg             " "r8"),
        Q!("    sbb             " "rax, rax"),

        load9!("r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rbp", z_2!()),
        Q!("    or              " "r8, r9"),
        Q!("    or              " "r10, r11"),
        Q!("    or              " "r12, r13"),
        Q!("    or              " "r14, r15"),
        Q!("    or              " "r8, r10"),
        Q!("    or              " "r12, r14"),
        Q!("    or              " "r8, rbp"),
        Q!("    or              " "r8, r12"),
        Q!("    neg             " "r8"),
        Q!("    sbb             " "rdx, rdx"),

        Q!("    cmp             " "rdx, rax"),

        // Multiplex the outputs accordingly. Re-store them in resz until there
        // are no more loads, so there are no assumptions on input-output aliasing

        muxload9!("r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rbp", resy!(), y_1!(), y_2!()),
        store9!(resy!(), "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rbp"),
        muxload9!("r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rbp", resz!(), z_1!(), z_2!()),
        store9!(resz!(), "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rbp"),
        muxload9!("r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rbp", resx!(), x_1!(), x_2!()),
        store9!(x_3!(), "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rbp"),
        copy9!(y_3!(), resy!()),
        copy9!(z_3!(), resz!()),

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
    if !(std::arch::is_x86_feature_detected!("adx") && std::arch::is_x86_feature_detected!("bmi2"))
    {
        return;
    }
    crate::low::abi::call!(
        p521_jadd,
        &mut crate::low::abi::Aligned([0; 27]).0,
        &crate::low::abi::Aligned([0; 27]).0,
        &crate::low::abi::Aligned([0; 27]).0
    );
}
