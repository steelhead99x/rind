// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Extended projective addition for edwards25519
// Inputs p1[16], p2[16]; output p3[16]
//
// extern void edwards25519_epadd
//   (uint64_t p3[static 16],const uint64_t p1[static 16],
//    const uint64_t p2[static 16]);
//
// The output p3 and both inputs p1 and p2 are points (x,y) on
// edwards25519 represented in extended projective quadruples (X,Y,Z,T)
// where x = X / Z, y = Y / Z and x * y = T / Z.
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

// Registers used for inputs and outputs within basic operations.
// Here p1 and p3 are where the parameters come in anyway;
// the p2 = rbp assignment is set up at the beginning.

macro_rules! p3 {
    () => {
        "rdi"
    };
}
macro_rules! p1 {
    () => {
        "rsi"
    };
}
macro_rules! p2 {
    () => {
        "rbp"
    };
}

// Pointers to input and output coordinates

macro_rules! x_1 { () => { Q!(p1!() "+ 0") } }
macro_rules! y_1 { () => { Q!(p1!() "+ " NUMSIZE!()) } }
macro_rules! z_1 { () => { Q!(p1!() "+ (2 * " NUMSIZE!() ")") } }
macro_rules! w_1 { () => { Q!(p1!() "+ (3 * " NUMSIZE!() ")") } }

macro_rules! x_2 { () => { Q!(p2!() "+ 0") } }
macro_rules! y_2 { () => { Q!(p2!() "+ " NUMSIZE!()) } }
macro_rules! z_2 { () => { Q!(p2!() "+ (2 * " NUMSIZE!() ")") } }
macro_rules! w_2 { () => { Q!(p2!() "+ (3 * " NUMSIZE!() ")") } }

macro_rules! x_3 { () => { Q!(p3!() "+ 0") } }
macro_rules! y_3 { () => { Q!(p3!() "+ " NUMSIZE!()) } }
macro_rules! z_3 { () => { Q!(p3!() "+ (2 * " NUMSIZE!() ")") } }
macro_rules! w_3 { () => { Q!(p3!() "+ (3 * " NUMSIZE!() ")") } }

// Pointer-offset pairs for temporaries on stack

macro_rules! t0 { () => { Q!("rsp + (0 * " NUMSIZE!() ")") } }
macro_rules! t1 { () => { Q!("rsp + (1 * " NUMSIZE!() ")") } }
macro_rules! t2 { () => { Q!("rsp + (2 * " NUMSIZE!() ")") } }
macro_rules! t3 { () => { Q!("rsp + (3 * " NUMSIZE!() ")") } }
macro_rules! t4 { () => { Q!("rsp + (4 * " NUMSIZE!() ")") } }
macro_rules! t5 { () => { Q!("rsp + (5 * " NUMSIZE!() ")") } }

// Total size to reserve on the stack

macro_rules! NSPACE { () => { Q!("6 * " NUMSIZE!()) } }

// Macro wrapping up the basic field multiplication, only trivially
// different from a pure function call to bignum_mul_p25519.

macro_rules! mul_p25519 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "xor esi, esi;\n"
        "mov rdx, [" $P2 "];\n"
        "mulx r9, r8, [" $P1 "];\n"
        "mulx r10, rax, [" $P1 "+ 0x8];\n"
        "add r9, rax;\n"
        "mulx r11, rax, [" $P1 "+ 0x10];\n"
        "adc r10, rax;\n"
        "mulx r12, rax, [" $P1 "+ 0x18];\n"
        "adc r11, rax;\n"
        "adc r12, rsi;\n"
        "xor esi, esi;\n"
        "mov rdx, [" $P2 "+ 0x8];\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx r13, rax, [" $P1 "+ 0x18];\n"
        "adcx r12, rax;\n"
        "adox r13, rsi;\n"
        "adcx r13, rsi;\n"
        "xor esi, esi;\n"
        "mov rdx, [" $P2 "+ 0x10];\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx r14, rax, [" $P1 "+ 0x18];\n"
        "adcx r13, rax;\n"
        "adox r14, rsi;\n"
        "adcx r14, rsi;\n"
        "xor esi, esi;\n"
        "mov rdx, [" $P2 "+ 0x18];\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx r15, rax, [" $P1 "+ 0x18];\n"
        "adcx r14, rax;\n"
        "adox r15, rsi;\n"
        "adcx r15, rsi;\n"
        "mov edx, 0x26;\n"
        "xor esi, esi;\n"
        "mulx rbx, rax, r12;\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, r13;\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, r14;\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx r12, rax, r15;\n"
        "adcx r11, rax;\n"
        "adox r12, rsi;\n"
        "adcx r12, rsi;\n"
        "shld r12, r11, 0x1;\n"
        "mov edx, 0x13;\n"
        "inc r12;\n"
        "bts r11, 63;\n"
        "mulx rbx, rax, r12;\n"
        "add r8, rax;\n"
        "adc r9, rbx;\n"
        "adc r10, rsi;\n"
        "adc r11, rsi;\n"
        "sbb rax, rax;\n"
        "not rax;\n"
        "and rax, rdx;\n"
        "sub r8, rax;\n"
        "sbb r9, rsi;\n"
        "sbb r10, rsi;\n"
        "sbb r11, rsi;\n"
        "btr r11, 63;\n"
        "mov [" $P0 "], r8;\n"
        "mov [" $P0 "+ 0x8], r9;\n"
        "mov [" $P0 "+ 0x10], r10;\n"
        "mov [" $P0 "+ 0x18], r11"
    )}
}

// A version of multiplication that only guarantees output < 2 * p_25519.
// This basically skips the +1 and final correction in quotient estimation.

macro_rules! mul_4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "xor ecx, ecx;\n"
        "mov rdx, [" $P2 "];\n"
        "mulx r9, r8, [" $P1 "];\n"
        "mulx r10, rax, [" $P1 "+ 0x8];\n"
        "add r9, rax;\n"
        "mulx r11, rax, [" $P1 "+ 0x10];\n"
        "adc r10, rax;\n"
        "mulx r12, rax, [" $P1 "+ 0x18];\n"
        "adc r11, rax;\n"
        "adc r12, rcx;\n"
        "xor ecx, ecx;\n"
        "mov rdx, [" $P2 "+ 0x8];\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx r13, rax, [" $P1 "+ 0x18];\n"
        "adcx r12, rax;\n"
        "adox r13, rcx;\n"
        "adcx r13, rcx;\n"
        "xor ecx, ecx;\n"
        "mov rdx, [" $P2 "+ 0x10];\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx r14, rax, [" $P1 "+ 0x18];\n"
        "adcx r13, rax;\n"
        "adox r14, rcx;\n"
        "adcx r14, rcx;\n"
        "xor ecx, ecx;\n"
        "mov rdx, [" $P2 "+ 0x18];\n"
        "mulx rbx, rax, [" $P1 "];\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x8];\n"
        "adcx r12, rax;\n"
        "adox r13, rbx;\n"
        "mulx rbx, rax, [" $P1 "+ 0x10];\n"
        "adcx r13, rax;\n"
        "adox r14, rbx;\n"
        "mulx r15, rax, [" $P1 "+ 0x18];\n"
        "adcx r14, rax;\n"
        "adox r15, rcx;\n"
        "adcx r15, rcx;\n"
        "mov edx, 0x26;\n"
        "xor ecx, ecx;\n"
        "mulx rbx, rax, r12;\n"
        "adcx r8, rax;\n"
        "adox r9, rbx;\n"
        "mulx rbx, rax, r13;\n"
        "adcx r9, rax;\n"
        "adox r10, rbx;\n"
        "mulx rbx, rax, r14;\n"
        "adcx r10, rax;\n"
        "adox r11, rbx;\n"
        "mulx r12, rax, r15;\n"
        "adcx r11, rax;\n"
        "adox r12, rcx;\n"
        "adcx r12, rcx;\n"
        "shld r12, r11, 0x1;\n"
        "btr r11, 0x3f;\n"
        "mov edx, 0x13;\n"
        "imul rdx, r12;\n"
        "add r8, rdx;\n"
        "adc r9, rcx;\n"
        "adc r10, rcx;\n"
        "adc r11, rcx;\n"
        "mov [" $P0 "], r8;\n"
        "mov [" $P0 "+ 0x8], r9;\n"
        "mov [" $P0 "+ 0x10], r10;\n"
        "mov [" $P0 "+ 0x18], r11"
    )}
}

// Plain 4-digit add and doubling without any normalization
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result,
// indeed one < 2 * p_25519 for normalized inputs.

macro_rules! add_4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov rax, [" $P1 "];\n"
        "add rax, [" $P2 "];\n"
        "mov [" $P0 "], rax;\n"
        "mov rax, [" $P1 "+ 8];\n"
        "adc rax, [" $P2 "+ 8];\n"
        "mov [" $P0 "+ 8], rax;\n"
        "mov rax, [" $P1 "+ 16];\n"
        "adc rax, [" $P2 "+ 16];\n"
        "mov [" $P0 "+ 16], rax;\n"
        "mov rax, [" $P1 "+ 24];\n"
        "adc rax, [" $P2 "+ 24];\n"
        "mov [" $P0 "+ 24], rax"
    )}
}

macro_rules! double_4 {
    ($P0:expr, $P1:expr) => { Q!(
        "mov rax, [" $P1 "];\n"
        "add rax, rax;\n"
        "mov [" $P0 "], rax;\n"
        "mov rax, [" $P1 "+ 8];\n"
        "adc rax, rax;\n"
        "mov [" $P0 "+ 8], rax;\n"
        "mov rax, [" $P1 "+ 16];\n"
        "adc rax, rax;\n"
        "mov [" $P0 "+ 16], rax;\n"
        "mov rax, [" $P1 "+ 24];\n"
        "adc rax, rax;\n"
        "mov [" $P0 "+ 24], rax"
    )}
}

// Subtraction of a pair of numbers < p_25519 just sufficient
// to give a 4-digit result. It actually always does (x - z) + (2^255-19)
// which in turn is done by (x - z) - (2^255+19) discarding the 2^256
// implicitly

macro_rules! sub_4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov r8, [" $P1 "];\n"
        "sub r8, [" $P2 "];\n"
        "mov r9, [" $P1 "+ 8];\n"
        "sbb r9, [" $P2 "+ 8];\n"
        "mov r10, [" $P1 "+ 16];\n"
        "sbb r10, [" $P2 "+ 16];\n"
        "mov rax, [" $P1 "+ 24];\n"
        "sbb rax, [" $P2 "+ 24];\n"
        "sub r8, 19;\n"
        "mov [" $P0 "], r8;\n"
        "sbb r9, 0;\n"
        "mov [" $P0 "+ 8], r9;\n"
        "sbb r10, 0;\n"
        "mov [" $P0 "+ 16], r10;\n"
        "sbb rax, 0;\n"
        "btc rax, 63;\n"
        "mov [" $P0 "+ 24], rax"
    )}
}

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

macro_rules! sub_twice4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov r8, [" $P1 "];\n"
        "xor ebx, ebx;\n"
        "sub r8, [" $P2 "];\n"
        "mov r9, [" $P1 "+ 8];\n"
        "sbb r9, [" $P2 "+ 8];\n"
        "mov ecx, 38;\n"
        "mov r10, [" $P1 "+ 16];\n"
        "sbb r10, [" $P2 "+ 16];\n"
        "mov rax, [" $P1 "+ 24];\n"
        "sbb rax, [" $P2 "+ 24];\n"
        "cmovnc rcx, rbx;\n"
        "sub r8, rcx;\n"
        "sbb r9, rbx;\n"
        "sbb r10, rbx;\n"
        "sbb rax, rbx;\n"
        "mov [" $P0 "], r8;\n"
        "mov [" $P0 "+ 8], r9;\n"
        "mov [" $P0 "+ 16], r10;\n"
        "mov [" $P0 "+ 24], rax"
    )}
}

// Modular addition with inputs double modulus 2 * p_25519 = 2^256 - 38
// and in general only guaranteeing a 4-digit result, not even < 2 * p_25519.

macro_rules! add_twice4 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "mov r8, [" $P1 "];\n"
        "xor ecx, ecx;\n"
        "add r8, [" $P2 "];\n"
        "mov r9, [" $P1 "+ 0x8];\n"
        "adc r9, [" $P2 "+ 0x8];\n"
        "mov r10, [" $P1 "+ 0x10];\n"
        "adc r10, [" $P2 "+ 0x10];\n"
        "mov r11, [" $P1 "+ 0x18];\n"
        "adc r11, [" $P2 "+ 0x18];\n"
        "mov eax, 38;\n"
        "cmovnc rax, rcx;\n"
        "add r8, rax;\n"
        "adc r9, rcx;\n"
        "adc r10, rcx;\n"
        "adc r11, rcx;\n"
        "mov [" $P0 "], r8;\n"
        "mov [" $P0 "+ 0x8], r9;\n"
        "mov [" $P0 "+ 0x10], r10;\n"
        "mov [" $P0 "+ 0x18], r11"
    )}
}

// Load the constant k_25519 = 2 * d_25519 using immediate operations

macro_rules! load_k25519 {
    ($P0:expr) => { Q!(
        "mov rax, 0xebd69b9426b2f159;\n"
        "mov [" $P0 "], rax;\n"
        "mov rax, 0x00e0149a8283b156;\n"
        "mov [" $P0 "+ 8], rax;\n"
        "mov rax, 0x198e80f2eef3d130;\n"
        "mov [" $P0 "+ 16], rax;\n"
        "mov rax, 0x2406d9dc56dffce7;\n"
        "mov [" $P0 "+ 24], rax"
    )}
}

// Transliterated from s2n-bignum's x86/curve25519/edwards25519_epadd.S.
/// Extended projective addition for edwards25519
///
/// Inputs p1[16], p2[16]; output p3[16]
///
/// The output p3 and both inputs p1 and p2 are points (x,y) on
/// edwards25519 represented in extended projective quadruples (X,Y,Z,T)
/// where x = X / Z, y = Y / Z and x * y = T / Z.
#[inline(never)]
pub(crate) fn edwards25519_epadd(p3: &mut [u64; 16], p1: &[u64; 16], p2: &[u64; 16]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Save registers, make room for temps, preserve input arguments.

        Q!("    push            " "rbx"),
        Q!("    push            " "rbp"),
        Q!("    push            " "r12"),
        Q!("    push            " "r13"),
        Q!("    push            " "r14"),
        Q!("    push            " "r15"),

        Q!("    sub             " "rsp, " NSPACE!()),

        // Main sequence of operations. after setting up p2 in its register

        Q!("    mov             " p2!() ", rdx"),

        mul_4!(t0!(), w_1!(), w_2!()),

        sub_4!(t1!(), y_1!(), x_1!()),
        sub_4!(t2!(), y_2!(), x_2!()),
        add_4!(t3!(), y_1!(), x_1!()),
        add_4!(t4!(), y_2!(), x_2!()),
        double_4!(t5!(), z_2!()),

        mul_4!(t1!(), t1!(), t2!()),
        mul_4!(t3!(), t3!(), t4!()),

        load_k25519!(t2!()),
        mul_4!(t2!(), t2!(), t0!()),

        mul_4!(t4!(), z_1!(), t5!()),

        sub_twice4!(t0!(), t3!(), t1!()),
        add_twice4!(t5!(), t3!(), t1!()),
        sub_twice4!(t1!(), t4!(), t2!()),
        add_twice4!(t3!(), t4!(), t2!()),

        mul_p25519!(w_3!(), t0!(), t5!()),
        mul_p25519!(x_3!(), t0!(), t1!()),
        mul_p25519!(y_3!(), t3!(), t5!()),
        mul_p25519!(z_3!(), t1!(), t3!()),

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
        edwards25519_epadd,
        &mut crate::low::abi::Aligned([0; 16]).0,
        &crate::low::abi::Aligned([0; 16]).0,
        &crate::low::abi::Aligned([0; 16]).0
    );
}
