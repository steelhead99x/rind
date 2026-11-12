// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Extended projective doubling for edwards25519
// Input p1[12]; output p3[16]
//
// extern void edwards25519_epdouble
//   (uint64_t p3[static 16],const uint64_t p1[static 12]);
//
// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
// The output p3 is in extended projective coordinates, representing
// affine (x,y) by a quadruple (X,Y,Z,T) where x = X / Z, y = Y / Z
// and x * y = T / Z. The input p1 may also be in the same extended
// projective representation, but the final T field is not used so
// a more basic projective triple (X,Y,Z) suffices.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------

// Size of individual field elements

macro_rules! NUMSIZE {
    () => {
        "32"
    };
}

// Registers used for inputs and outputs within basic operations.
// Here p1 and p3 are where the parameters come in anyway.

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

// Pointers to input and output coordinates

macro_rules! x_1 { () => { Q!(p1!() "+ 0") } }
macro_rules! y_1 { () => { Q!(p1!() "+ " NUMSIZE!()) } }
macro_rules! z_1 { () => { Q!(p1!() "+ (2 * " NUMSIZE!() ")") } }

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

// Total size to reserve on the stack

macro_rules! NSPACE { () => { Q!("5 * " NUMSIZE!()) } }

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

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

macro_rules! sqr_4 {
    ($P0:expr, $P1:expr) => { Q!(
        "mov rdx, [" $P1 "];\n"
        "mulx r15, r8, rdx;\n"
        "mulx r10, r9, [" $P1 "+ 0x8];\n"
        "mulx r12, r11, [" $P1 "+ 0x18];\n"
        "mov rdx, [" $P1 "+ 0x10];\n"
        "mulx r14, r13, [" $P1 "+ 0x18];\n"
        "xor ebx, ebx;\n"
        "mulx rcx, rax, [" $P1 "];\n"
        "adcx r10, rax;\n"
        "adox r11, rcx;\n"
        "mulx rcx, rax, [" $P1 "+ 0x8];\n"
        "adcx r11, rax;\n"
        "adox r12, rcx;\n"
        "mov rdx, [" $P1 "+ 0x18];\n"
        "mulx rcx, rax, [" $P1 "+ 0x8];\n"
        "adcx r12, rax;\n"
        "adox r13, rcx;\n"
        "adcx r13, rbx;\n"
        "adox r14, rbx;\n"
        "adc r14, rbx;\n"
        "xor ebx, ebx;\n"
        "adcx r9, r9;\n"
        "adox r9, r15;\n"
        "mov rdx, [" $P1 "+ 0x8];\n"
        "mulx rdx, rax, rdx;\n"
        "adcx r10, r10;\n"
        "adox r10, rax;\n"
        "adcx r11, r11;\n"
        "adox r11, rdx;\n"
        "mov rdx, [" $P1 "+ 0x10];\n"
        "mulx rdx, rax, rdx;\n"
        "adcx r12, r12;\n"
        "adox r12, rax;\n"
        "adcx r13, r13;\n"
        "adox r13, rdx;\n"
        "mov rdx, [" $P1 "+ 0x18];\n"
        "mulx r15, rax, rdx;\n"
        "adcx r14, r14;\n"
        "adox r14, rax;\n"
        "adcx r15, rbx;\n"
        "adox r15, rbx;\n"
        "mov edx, 0x26;\n"
        "xor ebx, ebx;\n"
        "mulx rcx, rax, r12;\n"
        "adcx r8, rax;\n"
        "adox r9, rcx;\n"
        "mulx rcx, rax, r13;\n"
        "adcx r9, rax;\n"
        "adox r10, rcx;\n"
        "mulx rcx, rax, r14;\n"
        "adcx r10, rax;\n"
        "adox r11, rcx;\n"
        "mulx r12, rax, r15;\n"
        "adcx r11, rax;\n"
        "adox r12, rbx;\n"
        "adcx r12, rbx;\n"
        "shld r12, r11, 0x1;\n"
        "btr r11, 0x3f;\n"
        "mov edx, 0x13;\n"
        "imul rdx, r12;\n"
        "add r8, rdx;\n"
        "adc r9, rbx;\n"
        "adc r10, rbx;\n"
        "adc r11, rbx;\n"
        "mov [" $P0 "], r8;\n"
        "mov [" $P0 "+ 0x8], r9;\n"
        "mov [" $P0 "+ 0x10], r10;\n"
        "mov [" $P0 "+ 0x18], r11"
    )}
}

// Plain 4-digit add without any normalization
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

// Modular addition and doubling with double modulus 2 * p_25519 = 2^256 - 38.
// This only ensures that the result fits in 4 digits, not that it is reduced
// even w.r.t. double modulus. The result is always correct modulo provided
// the sum of the inputs is < 2^256 + 2^256 - 38, so in particular provided
// at least one of them is reduced double modulo.

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

macro_rules! double_twice4 {
    ($P0:expr, $P1:expr) => { Q!(
        "mov r8, [" $P1 "];\n"
        "xor ecx, ecx;\n"
        "add r8, r8;\n"
        "mov r9, [" $P1 "+ 0x8];\n"
        "adc r9, r9;\n"
        "mov r10, [" $P1 "+ 0x10];\n"
        "adc r10, r10;\n"
        "mov r11, [" $P1 "+ 0x18];\n"
        "adc r11, r11;\n"
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

// Transliterated from s2n-bignum's x86/curve25519/edwards25519_epdouble.S.
/// Extended projective doubling for edwards25519
///
/// Input p1[12]; output p3[16]
///
/// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
/// The output p3 is in extended projective coordinates, representing
/// affine (x,y) by a quadruple (X,Y,Z,T) where x = X / Z, y = Y / Z
/// and x * y = T / Z. The input p1 may also be in the same extended
/// projective representation, but the final T field is not used so
/// a more basic projective triple (X,Y,Z) suffices.
#[inline(never)]
pub(crate) fn edwards25519_epdouble(p3: &mut [u64; 16], p1: &[u64; 12]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Save registers, make room for temps, preserve input arguments.

        Q!("    push            " "rbx"),
        Q!("    push            " "r12"),
        Q!("    push            " "r13"),
        Q!("    push            " "r14"),
        Q!("    push            " "r15"),

        Q!("    sub             " "rsp, " NSPACE!()),

        // Main sequence

        add_4!(t0!(), x_1!(), y_1!()),
        sqr_4!(t1!(), z_1!()),
        sqr_4!(t2!(), x_1!()),
        sqr_4!(t3!(), y_1!()),
        double_twice4!(t1!(), t1!()),
        sqr_4!(t0!(), t0!()),
        add_twice4!(t4!(), t2!(), t3!()),
        sub_twice4!(t2!(), t2!(), t3!()),
        add_twice4!(t3!(), t1!(), t2!()),
        sub_twice4!(t1!(), t4!(), t0!()),
        mul_p25519!(y_3!(), t2!(), t4!()),
        mul_p25519!(z_3!(), t3!(), t2!()),
        mul_p25519!(w_3!(), t1!(), t4!()),
        mul_p25519!(x_3!(), t1!(), t3!()),

        // Restore stack and registers

        Q!("    add             " "rsp, " NSPACE!()),

        Q!("    pop             " "r15"),
        Q!("    pop             " "r14"),
        Q!("    pop             " "r13"),
        Q!("    pop             " "r12"),
        Q!("    pop             " "rbx"),

        inout("rdi") p3.as_mut_ptr() => _,
        inout("rsi") p1.as_ptr() => _,
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
    if !(std::arch::is_x86_feature_detected!("adx") && std::arch::is_x86_feature_detected!("bmi2"))
    {
        return;
    }
    crate::low::abi::call!(
        edwards25519_epdouble,
        &mut crate::low::abi::Aligned([0; 16]).0,
        &crate::low::abi::Aligned([0; 12]).0
    );
}
