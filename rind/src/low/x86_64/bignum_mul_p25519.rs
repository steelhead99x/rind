// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply modulo p_25519, z := (x * y) mod p_25519
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_mul_p25519(uint64_t z[static 4], const uint64_t x[static 4],
//                                  const uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

// These are actually right

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

// Copied in or set up

macro_rules! y {
    () => {
        "rcx"
    };
}

// A zero register

macro_rules! zero {
    () => {
        "rbp"
    };
}
macro_rules! zeroe {
    () => {
        "ebp"
    };
}

// mulpadd(high,low,m) adds rdx * m to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries.

macro_rules! mulpadd {
    ($high:expr, $low:expr, $m:expr) => { Q!(
        "mulx rbx, rax, " $m ";\n"
        "adcx " $low ", rax;\n"
        "adox " $high ", rbx"
    )}
}

// mulpade(high,low,m) adds rdx * m to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax as a temporary, assuming high created from scratch
// and that zero has value zero.

macro_rules! mulpade {
    ($high:expr, $low:expr, $m:expr) => { Q!(
        "mulx " $high ", rax, " $m ";\n"
        "adcx " $low ", rax;\n"
        "adox " $high ", " zero!()
    )}
}

// Transliterated from s2n-bignum's x86/curve25519/bignum_mul_p25519.S.
/// Multiply modulo p_25519, z := (x * y) mod p_25519
///
/// Inputs x[4], y[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_mul_p25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Save more registers to play with

        Q!("    push            " "rbx"),
        Q!("    push            " "rbp"),
        Q!("    push            " "r12"),
        Q!("    push            " "r13"),
        Q!("    push            " "r14"),
        Q!("    push            " "r15"),

        // Copy y into a safe register to start with

        Q!("    mov             " y!() ", rdx"),

        // Zero a register, which also makes sure we don't get a fake carry-in

        Q!("    xor             " zeroe!() ", " zeroe!()),

        // Do the zeroth row, which is a bit different

        Q!("    mov             " "rdx, [" y!() "]"),

        Q!("    mulx            " "r9, r8, [" x!() "]"),
        Q!("    mulx            " "r10, rax, [" x!() "+ 8]"),
        Q!("    add             " "r9, rax"),
        Q!("    mulx            " "r11, rax, [" x!() "+ 16]"),
        Q!("    adc             " "r10, rax"),
        Q!("    mulx            " "r12, rax, [" x!() "+ 24]"),
        Q!("    adc             " "r11, rax"),
        Q!("    adc             " "r12, " zero!()),

        // Add row 1

        Q!("    xor             " zeroe!() ", " zeroe!()),
        Q!("    mov             " "rdx, [" y!() "+ 8]"),
        mulpadd!("r10", "r9", Q!("[" x!() "]")),
        mulpadd!("r11", "r10", Q!("[" x!() "+" "8" "]")),
        mulpadd!("r12", "r11", Q!("[" x!() "+" "16" "]")),
        mulpade!("r13", "r12", Q!("[" x!() "+" "24" "]")),
        Q!("    adc             " "r13, " zero!()),

        // Add row 2

        Q!("    xor             " zeroe!() ", " zeroe!()),
        Q!("    mov             " "rdx, [" y!() "+ 16]"),
        mulpadd!("r11", "r10", Q!("[" x!() "]")),
        mulpadd!("r12", "r11", Q!("[" x!() "+" "8" "]")),
        mulpadd!("r13", "r12", Q!("[" x!() "+" "16" "]")),
        mulpade!("r14", "r13", Q!("[" x!() "+" "24" "]")),
        Q!("    adc             " "r14, " zero!()),

        // Add row 3; also use an early 38*r15+r11 to get a quotient estimate q
        // and then squeeze in a 19 * q computation to inject into the next
        // double-carry chain. At the end rcx = q and rax = 19 * q.

        Q!("    xor             " zeroe!() ", " zeroe!()),
        Q!("    mov             " "rdx, [" y!() "+ 24]"),

        mulpadd!("r12", "r11", Q!("[" x!() "]")),

        Q!("    mulx            " "r15, rcx, [" x!() "+ 24]"),

        mulpadd!("r13", "r12", Q!("[" x!() "+" "8" "]")),
        mulpadd!("r14", "r13", Q!("[" x!() "+" "16" "]")),

        Q!("    mov             " "edx, 38"),
        Q!("    mulx            " "rbx, rax, r15"),

        Q!("    adcx            " "r14, rcx"),
        Q!("    adox            " "r15, " zero!()),
        Q!("    adc             " "r15, " zero!()),

        Q!("    add             " "rax, r11"),
        Q!("    adc             " "rbx, " zero!()),
        Q!("    bt              " "rax, 63"),
        Q!("    adc             " "rbx, rbx"),
        Q!("    lea             " "rcx, [rbx + 1]"),
        Q!("    imul            " "rcx, 19"),

        // Now we have the full 8-digit product 2^256 * h + l where
        // h = [r15,r14,r13,r12] and l = [r11,r10,r9,r8]
        // and this is == 38 * h + l (mod p_25519)
        // We add in the precalculated 19 * q as well.
        // This is kept in 4 words since we have enough information there.

        Q!("    xor             " zeroe!() ", " zeroe!()),
        Q!("    adox            " "r8, rcx"),
        mulpadd!("r9", "r8", "r12"),
        mulpadd!("r10", "r9", "r13"),
        mulpadd!("r11", "r10", "r14"),
        Q!("    mulx            " "rbx, rax, r15"),
        Q!("    adc             " "r11, rax"),

        // We still haven't made the -2^255 * q contribution yet. Since we
        // are now safely in 4 words we just need a single bit of q, and we
        // can actually use the LSB of rcx = 19 * q since 19 is odd. And we
        // don't literally need to subtract, just to see whether we would
        // have a top 1 bit if we did, meaning we need to correct in the
        // last step by adding 2^255 - 19.

        Q!("    shl             " "rcx, 63"),
        Q!("    cmp             " "r11, rcx"),
        Q!("    mov             " "eax, 19"),
        Q!("    cmovns          " "rax, " zero!()),

        // Now make that possible correction and finally mask to 255 bits

        Q!("    sub             " "r8, rax"),
        Q!("    sbb             " "r9, " zero!()),
        Q!("    sbb             " "r10, " zero!()),
        Q!("    sbb             " "r11, " zero!()),
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
        Q!("    pop             " "rbp"),
        Q!("    pop             " "rbx"),

        inout("rdi") z.as_mut_ptr() => _,
        inout("rsi") x.as_ptr() => _,
        inout("rdx") y.as_ptr() => _,
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
        bignum_mul_p25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
