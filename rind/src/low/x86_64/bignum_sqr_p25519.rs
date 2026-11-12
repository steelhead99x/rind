// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square modulo p_25519, z := (x^2) mod p_25519
// Input x[4]; output z[4]
//
//    extern void bignum_sqr_p25519(uint64_t z[static 4], const uint64_t x[static 4]);
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

// Use this fairly consistently for a zero

macro_rules! zero {
    () => {
        "rbx"
    };
}
macro_rules! zeroe {
    () => {
        "ebx"
    };
}

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rcx as temporaries

macro_rules! mulpadd {
    ($high:expr, $low:expr, $m:expr) => { Q!(
        "mulx rcx, rax, " $m ";\n"
        "adcx " $low ", rax;\n"
        "adox " $high ", rcx"
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

// Transliterated from s2n-bignum's x86/curve25519/bignum_sqr_p25519.S.
/// Square modulo p_25519, z := (x^2) mod p_25519
///
/// Input x[4]; output z[4]
#[inline(never)]
pub(crate) fn bignum_sqr_p25519(z: &mut [u64; 4], x: &[u64; 4]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        // Save more registers to play with

        Q!("    push            " "rbx"),
        Q!("    push            " "r12"),
        Q!("    push            " "r13"),
        Q!("    push            " "r14"),
        Q!("    push            " "r15"),

        // Compute [r15;r8] = [00] which we use later, but mainly
        // set up an initial window [r14;...;r9] = [23;03;01]

        Q!("    mov             " "rdx, [" x!() "]"),
        Q!("    mulx            " "r15, r8, rdx"),
        Q!("    mulx            " "r10, r9, [" x!() "+ 8]"),
        Q!("    mulx            " "r12, r11, [" x!() "+ 24]"),
        Q!("    mov             " "rdx, [" x!() "+ 16]"),
        Q!("    mulx            " "r14, r13, [" x!() "+ 24]"),

        // Clear our zero register, and also initialize the flags for the carry chain

        Q!("    xor             " zeroe!() ", " zeroe!()),

        // Chain in the addition of 02 + 12 + 13 to that window (no carry-out possible)
        // This gives all the "heterogeneous" terms of the squaring ready to double

        mulpadd!("r11", "r10", Q!("[" x!() "]")),
        mulpadd!("r12", "r11", Q!("[" x!() "+" "8" "]")),
        Q!("    mov             " "rdx, [" x!() "+ 24]"),
        mulpadd!("r13", "r12", Q!("[" x!() "+" "8" "]")),
        Q!("    adcx            " "r13, " zero!()),
        Q!("    adox            " "r14, " zero!()),
        Q!("    adc             " "r14, " zero!()),

        // Double and add to the 00 + 11 + 22 + 33 terms, while also
        // pre-estimating the quotient from early results.

        Q!("    xor             " zeroe!() ", " zeroe!()),
        Q!("    adcx            " "r9, r9"),
        Q!("    adox            " "r9, r15"),
        Q!("    mov             " "rdx, [" x!() "+ 8]"),
        Q!("    mulx            " "rcx, rax, rdx"),
        Q!("    adcx            " "r10, r10"),
        Q!("    adox            " "r10, rax"),
        Q!("    adcx            " "r11, r11"),
        Q!("    adox            " "r11, rcx"),
        Q!("    mov             " "rdx, [" x!() "+ 16]"),
        Q!("    mulx            " "rcx, rax, rdx"),
        Q!("    adcx            " "r12, r12"),
        Q!("    adox            " "r12, rax"),
        Q!("    adcx            " "r13, r13"),
        Q!("    adox            " "r13, rcx"),
        Q!("    mov             " "rdx, [" x!() "+ 24]"),
        Q!("    mulx            " "r15, rax, rdx"),

        Q!("    mov             " "edx, 38"),
        Q!("    mulx            " "rcx, rdx, r15"),

        Q!("    adcx            " "r14, r14"),
        Q!("    adox            " "r14, rax"),
        Q!("    adcx            " "r15, " zero!()),
        Q!("    adox            " "r15, " zero!()),

        Q!("    add             " "rdx, r11"),
        Q!("    adc             " "rcx, " zero!()),
        Q!("    shld            " "rcx, rdx, 1"),
        Q!("    lea             " "rbx, [rcx + 1]"),
        Q!("    imul            " "rbx, 19"),

        // Now we have the full 8-digit product 2^256 * h + l where
        // h = [r15,r14,r13,r12] and l = [r11,r10,r9,r8]
        // and this is == 38 * h + l (mod p_25519)
        // We add in the precalculated 19 * q as well.
        // This is kept in 4 words since we have enough information there.

        Q!("    xor             " "eax, eax"),
        Q!("    adox            " "r8, rbx"),
        Q!("    mov             " "edx, 38"),
        mulpadd!("r9", "r8", "r12"),
        mulpadd!("r10", "r9", "r13"),
        mulpadd!("r11", "r10", "r14"),
        Q!("    mulx            " "rcx, rax, r15"),
        Q!("    adc             " "r11, rax"),

        // We still haven't made the -2^255 * q contribution yet. Since we
        // are now safely in 4 words we just need a single bit of q, and we
        // can actually use the LSB of rcx = 19 * q since 19 is odd. And we
        // don't literally need to subtract, just to see whether we would
        // have a top 1 bit if we did, meaning we need to correct in the
        // last step by adding 2^255 - 19.

        Q!("    xor             " "ecx, ecx"),
        Q!("    shl             " "rbx, 63"),
        Q!("    cmp             " "r11, rbx"),
        Q!("    mov             " "eax, 19"),
        Q!("    cmovns          " "rax, rcx"),

        // Now make that possible correction and finally mask to 255 bits

        Q!("    sub             " "r8, rax"),
        Q!("    sbb             " "r9, rcx"),
        Q!("    sbb             " "r10, rcx"),
        Q!("    sbb             " "r11, rcx"),
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
        Q!("    pop             " "rbx"),

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
    if !(std::arch::is_x86_feature_detected!("adx") && std::arch::is_x86_feature_detected!("bmi2"))
    {
        return;
    }
    crate::low::abi::call!(
        bignum_sqr_p25519,
        &mut crate::low::abi::Aligned([0; 4]).0,
        &crate::low::abi::Aligned([0; 4]).0
    );
}
