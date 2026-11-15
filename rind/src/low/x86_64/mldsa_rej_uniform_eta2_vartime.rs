// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Rejection sampling of eta=2 secret coefficients for ML-DSA (x86_64 AVX2)
//
// Extracts 4-bit nibbles from the input byte buffer, accepts those < 15, and
// maps an accepted nibble n to the coefficient 2 - (n mod 5) via a centered
// modulo-5 reduction, producing values in [-2, 2]. Fills the output array
// r[256] with the accepted coefficients in order of appearance, returning the
// total number written (max 256).
//
// extern uint64_t mldsa_rej_uniform_eta2_VARIABLE_TIME_x86
//                     (int32_t r[static 256],
//                      const uint8_t buf[static 136],
//                      const uint8_t table[static 2048]);
//
// The input buffer buf is a fixed MLD_AVX2_REJ_UNIFORM_ETA2_BUFLEN = 136
// bytes; the table argument is a specific precomputed 256x8 = 2048-byte table
// (mldsa_rej_uniform_table), defined in the proof / test code.
//
// Like mlkem_rej_uniform, this is *not* a constant-time function: the time
// taken depends on how many buffer elements pass the < 15 filter.
//
// Standard x86-64 ABI: RDI = r, RSI = buf, RDX = table
// Microsoft x64 ABI:   RCX = r, RDX = buf, R8 = table
// ----------------------------------------------------------------------------

// This implementation is derived from the public domain AVX2 Dilithium
// implementation (pq-crystals/dilithium) via the mldsa-native project.

// Transliterated from s2n-bignum's x86/mldsa/mldsa_rej_uniform_eta2_VARIABLE_TIME.S.
/// Rejection sampling of eta=2 secret coefficients for ML-DSA (x86_64 AVX2)
///
/// Extracts 4-bit nibbles from the input byte buffer, accepts those < 15, and
/// maps an accepted nibble n to the coefficient 2 - (n mod 5) via a centered
/// modulo-5 reduction, producing values in [-2, 2]. Fills the output array
/// r[256] with the accepted coefficients in order of appearance, returning the
/// total number written (max 256).
///
/// The input buffer buf is a fixed MLD_AVX2_REJ_UNIFORM_ETA2_BUFLEN = 136
/// bytes; the table argument is a specific precomputed 256x8 = 2048-byte table
/// (mldsa_rej_uniform_table), defined in the proof / test code.
///
/// Like mlkem_rej_uniform, this is *not* a constant-time function: the time
/// taken depends on how many buffer elements pass the < 15 filter.
#[inline(never)]
pub(crate) fn mldsa_rej_uniform_eta2_vartime(
    r: &mut [i32; 256],
    buf: &[u8; 136],
    table: &[u8; 2048],
) -> u64 {
    let ret: u64;
    assert!((r.as_mut_ptr() as usize).is_multiple_of(32));
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        Q!("    endbr64         " ),

        Q!("    mov             " "r8d, 0xf0f0f0f"),
        Q!("    vmovd           " "xmm3, r8d"),
        Q!("    vpbroadcastd    " "ymm3, xmm3"),
        Q!("    mov             " "r8d, 0x2020202"),
        Q!("    vmovd           " "xmm4, r8d"),
        Q!("    vpbroadcastd    " "ymm4, xmm4"),
        Q!("    mov             " "r8d, 0xf0f0f0f"),
        Q!("    vmovd           " "xmm5, r8d"),
        Q!("    vpbroadcastd    " "ymm5, xmm5"),
        Q!("    mov             " "r8d, 0xffffe660"),
        Q!("    vpinsrw         " "xmm6, xmm6, r8d, 0x0"),
        Q!("    vpbroadcastw    " "ymm6, xmm6"),
        Q!("    mov             " "r8d, 0x5"),
        Q!("    vpinsrw         " "xmm7, xmm7, r8d, 0x0"),
        Q!("    vpbroadcastw    " "ymm7, xmm7"),
        Q!("    xor             " "eax, eax"),
        Q!("    xor             " "ecx, ecx"),

        Q!(Label!("Lmldsa_rej_uniform_eta2_x86_loop", 2) ":"),
        Q!("    cmp             " "eax, 0xf8"),
        Q!("    ja              " Label!("Lmldsa_rej_uniform_eta2_x86_scalar", 3, After)),
        Q!("    cmp             " "ecx, 0x78"),
        Q!("    ja              " Label!("Lmldsa_rej_uniform_eta2_x86_scalar", 3, After)),
        Q!("    vpmovzxbw       " "ymm0, [rsi + rcx]"),
        Q!("    vpsllw          " "ymm1, ymm0, 0x4"),
        Q!("    vpor            " "ymm0, ymm0, ymm1"),
        Q!("    vpand           " "ymm0, ymm0, ymm3"),
        Q!("    vpsubb          " "ymm1, ymm0, ymm5"),
        Q!("    vpsubb          " "ymm0, ymm4, ymm0"),
        Q!("    vpmovmskb       " "r8d, ymm1"),
        Q!("    vextracti128    " "xmm8, ymm0, 0x0"),
        Q!("    movzx           " "r10d, r8b"),
        Q!("    vmovq           " "xmm9, [rdx + 8 * r10]"),
        Q!("    vpshufb         " "xmm9, xmm8, xmm9"),
        Q!("    vpmovsxbd       " "ymm1, xmm9"),
        Q!("    vpmulhrsw       " "ymm2, ymm1, ymm6"),
        Q!("    vpmullw         " "ymm2, ymm2, ymm7"),
        Q!("    vpaddd          " "ymm1, ymm1, ymm2"),
        Q!("    vmovdqu         " "[rdi + 4 * rax], ymm1"),
        Q!("    popcnt          " "r9d, r10d"),
        Q!("    add             " "eax, r9d"),
        Q!("    shr             " "r8d, 0x8"),
        Q!("    add             " "ecx, 0x4"),
        Q!("    cmp             " "eax, 0xf8"),
        Q!("    ja              " Label!("Lmldsa_rej_uniform_eta2_x86_scalar", 3, After)),
        Q!("    vpsrldq         " "xmm8, xmm8, 0x8"),
        Q!("    movzx           " "r10d, r8b"),
        Q!("    vmovq           " "xmm9, [rdx + 8 * r10]"),
        Q!("    vpshufb         " "xmm9, xmm8, xmm9"),
        Q!("    vpmovsxbd       " "ymm1, xmm9"),
        Q!("    vpmulhrsw       " "ymm2, ymm1, ymm6"),
        Q!("    vpmullw         " "ymm2, ymm2, ymm7"),
        Q!("    vpaddd          " "ymm1, ymm1, ymm2"),
        Q!("    vmovdqu         " "[rdi + 4 * rax], ymm1"),
        Q!("    popcnt          " "r9d, r10d"),
        Q!("    add             " "eax, r9d"),
        Q!("    shr             " "r8d, 0x8"),
        Q!("    add             " "ecx, 0x4"),
        Q!("    cmp             " "eax, 0xf8"),
        Q!("    ja              " Label!("Lmldsa_rej_uniform_eta2_x86_scalar", 3, After)),
        Q!("    vextracti128    " "xmm8, ymm0, 0x1"),
        Q!("    movzx           " "r10d, r8b"),
        Q!("    vmovq           " "xmm9, [rdx + 8 * r10]"),
        Q!("    vpshufb         " "xmm9, xmm8, xmm9"),
        Q!("    vpmovsxbd       " "ymm1, xmm9"),
        Q!("    vpmulhrsw       " "ymm2, ymm1, ymm6"),
        Q!("    vpmullw         " "ymm2, ymm2, ymm7"),
        Q!("    vpaddd          " "ymm1, ymm1, ymm2"),
        Q!("    vmovdqu         " "[rdi + 4 * rax], ymm1"),
        Q!("    popcnt          " "r9d, r10d"),
        Q!("    add             " "eax, r9d"),
        Q!("    shr             " "r8d, 0x8"),
        Q!("    add             " "ecx, 0x4"),
        Q!("    cmp             " "eax, 0xf8"),
        Q!("    ja              " Label!("Lmldsa_rej_uniform_eta2_x86_scalar", 3, After)),
        Q!("    vpsrldq         " "xmm8, xmm8, 0x8"),
        Q!("    movzx           " "r10d, r8b"),
        Q!("    vmovq           " "xmm9, [rdx + 8 * r10]"),
        Q!("    vpshufb         " "xmm9, xmm8, xmm9"),
        Q!("    vpmovsxbd       " "ymm1, xmm9"),
        Q!("    vpmulhrsw       " "ymm2, ymm1, ymm6"),
        Q!("    vpmullw         " "ymm2, ymm2, ymm7"),
        Q!("    vpaddd          " "ymm1, ymm1, ymm2"),
        Q!("    vmovdqu         " "[rdi + 4 * rax], ymm1"),
        Q!("    popcnt          " "r9d, r10d"),
        Q!("    add             " "eax, r9d"),
        Q!("    add             " "ecx, 0x4"),
        Q!("    jmp             " Label!("Lmldsa_rej_uniform_eta2_x86_loop", 2, Before)),

        Q!(Label!("Lmldsa_rej_uniform_eta2_x86_scalar", 3) ":"),
        Q!("    cmp             " "eax, 0x100"),
        Q!("    jae             " Label!("Lmldsa_rej_uniform_eta2_x86_done", 4, After)),
        Q!("    cmp             " "ecx, 0x88"),
        Q!("    jae             " Label!("Lmldsa_rej_uniform_eta2_x86_done", 4, After)),
        Q!("    movzx           " "r11d, BYTE PTR [rsi + rcx]"),
        Q!("    inc             " "ecx"),
        Q!("    mov             " "r10d, r11d"),
        Q!("    and             " "r10d, 0xf"),
        Q!("    cmp             " "r10d, 0xf"),
        Q!("    jae             " Label!("Lmldsa_rej_uniform_eta2_x86_high_nibble", 5, After)),
        Q!("    mov             " "r11d, r10d"),
        Q!("    imul            " "r11d, r11d, 0xcd"),
        Q!("    shr             " "r11d, 0xa"),
        Q!("    imul            " "r11d, r11d, 0x5"),
        Q!("    sub             " "r10d, r11d"),
        Q!("    mov             " "r11d, 0x2"),
        Q!("    sub             " "r11d, r10d"),
        Q!("    mov             " "[rdi + 4 * rax], r11d"),
        Q!("    inc             " "eax"),
        Q!("    cmp             " "eax, 0x100"),
        Q!("    jae             " Label!("Lmldsa_rej_uniform_eta2_x86_done", 4, After)),

        Q!(Label!("Lmldsa_rej_uniform_eta2_x86_high_nibble", 5) ":"),
        Q!("    movzx           " "r11d, BYTE PTR [rsi + rcx -0x1]"),
        Q!("    shr             " "r11d, 0x4"),
        Q!("    and             " "r11d, 0xf"),
        Q!("    cmp             " "r11d, 0xf"),
        Q!("    jae             " Label!("Lmldsa_rej_uniform_eta2_x86_scalar", 3, Before)),
        Q!("    mov             " "r10d, r11d"),
        Q!("    imul            " "r10d, r10d, 0xcd"),
        Q!("    shr             " "r10d, 0xa"),
        Q!("    imul            " "r10d, r10d, 0x5"),
        Q!("    sub             " "r11d, r10d"),
        Q!("    mov             " "r10d, 0x2"),
        Q!("    sub             " "r10d, r11d"),
        Q!("    mov             " "[rdi + 4 * rax], r10d"),
        Q!("    inc             " "eax"),
        Q!("    jmp             " Label!("Lmldsa_rej_uniform_eta2_x86_scalar", 3, Before)),

        Q!(Label!("Lmldsa_rej_uniform_eta2_x86_done", 4) ":"),

        Q!("    vzeroupper      " ),
        inout("rdi") r.as_mut_ptr() => _,
        inout("rsi") buf.as_ptr() => _,
        inout("rdx") table.as_ptr() => _,
        out("rax") ret,
        // clobbers
        out("r10") _,
        out("r11") _,
        out("r8") _,
        out("r9") _,
        out("rcx") _,
        out("zmm0") _,
        out("zmm1") _,
        out("zmm10") _,
        out("zmm11") _,
        out("zmm12") _,
        out("zmm13") _,
        out("zmm14") _,
        out("zmm15") _,
        out("zmm2") _,
        out("zmm3") _,
        out("zmm4") _,
        out("zmm5") _,
        out("zmm6") _,
        out("zmm7") _,
        out("zmm8") _,
        out("zmm9") _,
            )
    };
    ret
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    if !(std::arch::is_x86_feature_detected!("avx2")
        && std::arch::is_x86_feature_detected!("popcnt"))
    {
        return;
    }
    crate::low::abi::call!(
        mldsa_rej_uniform_eta2_vartime,
        &mut crate::low::abi::Aligned([0; 256]).0,
        &crate::low::abi::Aligned([0; 136]).0,
        &crate::low::abi::Aligned([0; 2048]).0
    );
}
