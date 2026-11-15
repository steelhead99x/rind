// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Rejection sampling with eta=4 for ML-DSA (parameter set 65).
//
// Extracts up to 256 coefficients in the range [-4, 4] from a buffer of
// SHAKE256 output bytes. Each input byte contributes two 4-bit nibbles; a
// nibble is accepted iff its value is < 9 (rejection sampling for uniform
// distribution on {0, ..., 8}), and the accepted value n is mapped to
// (4 - n) stored as int32. Uses a 256-entry lookup table (table[i] is a
// 16-byte TBL index permutation for the 8-bit acceptance mask i) to
// compact accepted nibbles via NEON TBL/TBL2.
//
// Inputs:
//   r[256]    (int32_t, output)  — sampled coefficients; at most `outlen`
//                                  written
//   buf       (const uint8_t*)   — SHAKE256 output, buflen bytes
//   buflen    (unsigned)         — number of bytes in buf (must be 8-divisible,
//                                  >= 8)
//   table[4096] (const uint8_t*) — 256 × 16-byte TBL permutation table
//
// Output:
//   return value (uint64_t)       — number of coefficients written (<= 256)
//
// extern uint64_t mldsa_rej_uniform_eta4_VARIABLE_TIME
//      (int32_t r[static 256], const uint8_t *buf, unsigned buflen,
//       const uint8_t table[static 4096]);
//
// Standard ARM ABI: X0 = r, X1 = buf, X2 = buflen, X3 = table
// Uses 576 bytes of stack as scratch for nibble packing.
// ----------------------------------------------------------------------------

// Transliterated from s2n-bignum's arm/mldsa/mldsa_rej_uniform_eta4_VARIABLE_TIME.S.
/// Rejection sampling with eta=4 for ML-DSA (parameter set 65).
///
/// Extracts up to 256 coefficients in the range [-4, 4] from a buffer of
/// SHAKE256 output bytes. Each input byte contributes two 4-bit nibbles; a
/// nibble is accepted iff its value is < 9 (rejection sampling for uniform
/// distribution on {0, ..., 8}), and the accepted value n is mapped to
/// (4 - n) stored as int32. Uses a 256-entry lookup table (table[i] is a
/// 16-byte TBL index permutation for the 8-bit acceptance mask i) to
/// compact accepted nibbles via NEON TBL/TBL2.
///
/// Inputs:
/// r[256]    (int32_t, output)  — sampled coefficients; at most `outlen`
/// written
/// buf       (const uint8_t*)   — SHAKE256 output, buflen bytes
/// buflen    (unsigned)         — number of bytes in buf (must be 8-divisible,
/// \>= 8)
///   table[4096] (const uint8_t*) — 256 × 16-byte TBL permutation table
///
/// Output:
/// return value (uint64_t)       — number of coefficients written (<= 256)
#[inline(never)]
pub(crate) fn mldsa_rej_uniform_eta4_vartime(
    r: &mut [i32; 256],
    buf: &[u8; 272],
    table: &[i8; 4096],
) -> u64 {
    let ret: u64;
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // This matches the code in the mldsa-native repository
        // https://github.com/pq-code-package/mldsa-native/blob/main/mldsa/src/native/aarch64/src/rej_uniform_eta4_asm.S

        Q!("    sub             " "sp, sp, #0x240"),
        Q!("    mov             " "x7, #0x1"),
        Q!("    movk            " "x7, #0x2, lsl #16"),
        Q!("    movk            " "x7, #0x4, lsl #32"),
        Q!("    movk            " "x7, #0x8, lsl #48"),
        Q!("    mov             " "v31.d[0], x7"),
        Q!("    mov             " "x7, #0x10"),
        Q!("    movk            " "x7, #0x20, lsl #16"),
        Q!("    movk            " "x7, #0x40, lsl #32"),
        Q!("    movk            " "x7, #0x80, lsl #48"),
        Q!("    mov             " "v31.d[1], x7"),
        Q!("    movi            " "v30.8h, #0x9"),
        Q!("    movi            " "v7.8h, #0x4"),
        Q!("    mov             " "x8, sp"),
        Q!("    mov             " "x7, x8"),
        Q!("    mov             " "x11, #0x0"),
        Q!("    eor             " "v16.16b, v16.16b, v16.16b"),

        Q!(Label!("Lrej_uniform_eta4_initial_zero", 2) ":"),
        Q!("    str             " "q16, [x7], #0x40"),
        Q!("    stur            " "q16, [x7, #-0x30]"),
        Q!("    stur            " "q16, [x7, #-0x20]"),
        Q!("    stur            " "q16, [x7, #-0x10]"),
        Q!("    add             " "x11, x11, #0x20"),
        Q!("    cmp             " "x11, #0x100"),
        Q!("    b.lt            " Label!("Lrej_uniform_eta4_initial_zero", 2, Before)),

        Q!("    mov             " "x7, x8"),
        Q!("    mov             " "x9, #0x0"),
        Q!("    mov             " "x4, #0x100"),

        Q!(Label!("Lrej_uniform_eta4_loop8", 3) ":"),
        Q!("    cmp             " "x9, x4"),
        Q!("    b.hs            " Label!("Lrej_uniform_eta4_memory_copy", 4, After)),
        Q!("    sub             " "x2, x2, #0x8"),
        Q!("    ld1             " "{{ v0.8b }}, [x1], #8"),
        Q!("    movi            " "v26.8b, #0xf"),
        Q!("    and             " "v27.8b, v0.8b, v26.8b"),
        Q!("    ushr            " "v28.8b, v0.8b, #0x4"),
        Q!("    zip1            " "v26.8b, v27.8b, v28.8b"),
        Q!("    zip2            " "v29.8b, v27.8b, v28.8b"),
        Q!("    ushll           " "v16.8h, v26.8b, #0x0"),
        Q!("    ushll           " "v17.8h, v29.8b, #0x0"),
        Q!("    cmhi            " "v4.8h, v30.8h, v16.8h"),
        Q!("    cmhi            " "v5.8h, v30.8h, v17.8h"),
        Q!("    and             " "v4.16b, v4.16b, v31.16b"),
        Q!("    and             " "v5.16b, v5.16b, v31.16b"),
        Q!("    uaddlv          " "s20, v4.8h"),
        Q!("    uaddlv          " "s21, v5.8h"),
        Q!("    fmov            " "w12, s20"),
        Q!("    fmov            " "w13, s21"),
        Q!("    ldr             " "q24, [x3, x12, lsl #4]"),
        Q!("    ldr             " "q25, [x3, x13, lsl #4]"),
        Q!("    cnt             " "v4.16b, v4.16b"),
        Q!("    cnt             " "v5.16b, v5.16b"),
        Q!("    uaddlv          " "s20, v4.8h"),
        Q!("    uaddlv          " "s21, v5.8h"),
        Q!("    fmov            " "w12, s20"),
        Q!("    fmov            " "w13, s21"),
        Q!("    tbl             " "v16.16b, {{ v16.16b }}, v24.16b"),
        Q!("    tbl             " "v17.16b, {{ v17.16b }}, v25.16b"),
        Q!("    st1             " "{{ v16.8h }}, [x7]"),
        Q!("    add             " "x7, x7, x12, lsl #1"),
        Q!("    st1             " "{{ v17.8h }}, [x7]"),
        Q!("    add             " "x7, x7, x13, lsl #1"),
        Q!("    add             " "x12, x12, x13"),
        Q!("    add             " "x9, x9, x12"),
        Q!("    cmp             " "x2, #0x8"),
        Q!("    b.hs            " Label!("Lrej_uniform_eta4_loop8", 3, Before)),

        Q!(Label!("Lrej_uniform_eta4_memory_copy", 4) ":"),
        Q!("    cmp             " "x9, x4"),
        Q!("    csel            " "x9, x9, x4, lo"),
        Q!("    mov             " "x11, #0x0"),
        Q!("    mov             " "x7, x8"),

        Q!(Label!("Lrej_uniform_eta4_final_copy", 5) ":"),
        Q!("    ldr             " "q16, [x7], #0x20"),
        Q!("    ldur            " "q18, [x7, #-0x10]"),
        Q!("    sub             " "v16.8h, v7.8h, v16.8h"),
        Q!("    sub             " "v18.8h, v7.8h, v18.8h"),
        Q!("    sshll2          " "v17.4s, v16.8h, #0x0"),
        Q!("    sshll           " "v16.4s, v16.4h, #0x0"),
        Q!("    sshll2          " "v19.4s, v18.8h, #0x0"),
        Q!("    sshll           " "v18.4s, v18.4h, #0x0"),
        Q!("    str             " "q16, [x0], #0x40"),
        Q!("    stur            " "q17, [x0, #-0x30]"),
        Q!("    stur            " "q18, [x0, #-0x20]"),
        Q!("    stur            " "q19, [x0, #-0x10]"),
        Q!("    add             " "x11, x11, #0x10"),
        Q!("    cmp             " "x11, #0x100"),
        Q!("    b.lt            " Label!("Lrej_uniform_eta4_final_copy", 5, Before)),
        Q!("    mov             " "x0, x9"),
        Q!("    add             " "sp, sp, #0x240"),
        inout("x0") r.as_mut_ptr() => ret,
        inout("x1") buf.as_ptr() => _,
        inout("x2") buf.len() => _,
        inout("x3") table.as_ptr() => _,
        // clobbers
        out("v0") _,
        out("v16") _,
        out("v17") _,
        out("v18") _,
        out("v19") _,
        out("v20") _,
        out("v21") _,
        out("v24") _,
        out("v25") _,
        out("v26") _,
        out("v27") _,
        out("v28") _,
        out("v29") _,
        out("v30") _,
        out("v31") _,
        out("v4") _,
        out("v5") _,
        out("v7") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x4") _,
        out("x7") _,
        out("x8") _,
        out("x9") _,
            )
    };
    ret
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        mldsa_rej_uniform_eta4_vartime,
        &mut crate::low::abi::Aligned([0; 256]).0,
        &crate::low::abi::Aligned([0; 272]).0,
        &crate::low::abi::Aligned([0; 4096]).0
    );
}
