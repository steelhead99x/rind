// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Scalar product of 2-element polynomial vectors in NTT domain, with mulcache
// Inputs a[512], b[512], bt[256] (signed 16-bit words); output r[256] (signed 16-bit words)
//
// The inputs a and b are considered as 2-element vectors of linear
// polynomials in the NTT domain (in Montgomery form), and the bt
// argument an analogous 2-element vector of mulcaches for the bi:
//
//   a0 = a[0..255], a1 = a[256..511]
//   b0 = b[0..255], b1 = b[256..511]
//   bt0 = bt[0..127], bt1 = bt[128..255]
//
// Scalar multiplication of those 2-element vectors is performed,
// with base multiplication in Fq[X]/(X^2-zeta^i'), with zeta^i'
// being a power of zeta = 17, with i bit-reversed as used for NTTs,
// making use of the mulcache for optimization.
//
// All input elements are assumed <= 2^12 and the bts are
// assumed to be as computed by mlkem_mulcache_compute.
//
// extern void mlkem_basemul_k2
//      (int16_t r[static 256],const int16_t a[static 512],
//       const int16_t b[static 512], const int16_t bt[static 256]);
//
// Standard ARM ABI: X0 = r, X1 = a, X2 = b, X3 = bt
// ----------------------------------------------------------------------------

// Transliterated from s2n-bignum's arm/mlkem/mlkem_basemul_k2.S.
/// Scalar product of 2-element polynomial vectors in NTT domain, with mulcache
///
/// Inputs a[512], b[512], bt[256] (signed 16-bit words); output r[256] (signed 16-bit words)
///
/// The inputs a and b are considered as 2-element vectors of linear
/// polynomials in the NTT domain (in Montgomery form), and the bt
/// argument an analogous 2-element vector of mulcaches for the bi:
///
///   a0 = a[0..255], a1 = a[256..511]
///   b0 = b[0..255], b1 = b[256..511]
///   bt0 = bt[0..127], bt1 = bt[128..255]
///
/// Scalar multiplication of those 2-element vectors is performed,
/// with base multiplication in Fq[X]/(X^2-zeta^i'), with zeta^i'
/// being a power of zeta = 17, with i bit-reversed as used for NTTs,
/// making use of the mulcache for optimization.
///
/// All input elements are assumed <= 2^12 and the bts are
/// assumed to be as computed by mlkem_mulcache_compute.
#[inline(never)]
pub(crate) fn mlkem_basemul_k2(
    r: &mut [i16; 256],
    a: &[i16; 512],
    b: &[i16; 512],
    bt: &[i16; 256],
) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // This matches the code in the mlkem-native repository
        // https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/native/aarch64/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S

        Q!("    sub             " "sp, sp, # (64 + 0)"),
        Q!("    stp             " "d8, d9, [sp, # (0)]"),
        Q!("    stp             " "d10, d11, [sp, # (0x10)]"),
        Q!("    stp             " "d12, d13, [sp, # (0x20)]"),
        Q!("    stp             " "d14, d15, [sp, # (0x30)]"),
        Q!("    mov             " "w14, #0xd01"),
        Q!("    dup             " "v0.8h, w14"),
        Q!("    mov             " "w14, #0xcff"),
        Q!("    dup             " "v2.8h, w14"),
        Q!("    add             " "x4, x1, #0x200"),
        Q!("    add             " "x5, x2, #0x200"),
        Q!("    add             " "x6, x3, #0x100"),
        Q!("    mov             " "x13, #0x10"),
        Q!("    ldr             " "q9, [x4], #0x20"),
        Q!("    ldur            " "q5, [x4, #-0x10]"),
        Q!("    ldr             " "q11, [x5], #0x20"),
        Q!("    uzp1            " "v23.8h, v9.8h, v5.8h"),
        Q!("    uzp2            " "v9.8h, v9.8h, v5.8h"),
        Q!("    ldr             " "q5, [x2], #0x20"),
        Q!("    ldur            " "q7, [x5, #-0x10]"),
        Q!("    ldur            " "q21, [x2, #-0x10]"),
        Q!("    uzp2            " "v10.8h, v11.8h, v7.8h"),
        Q!("    uzp1            " "v11.8h, v11.8h, v7.8h"),
        Q!("    uzp1            " "v7.8h, v5.8h, v21.8h"),
        Q!("    uzp2            " "v5.8h, v5.8h, v21.8h"),
        Q!("    ldr             " "q21, [x1], #0x20"),
        Q!("    ldur            " "q25, [x1, #-0x10]"),
        Q!("    ld1             " "{{ v6.8h }}, [x3], #16"),
        Q!("    uzp1            " "v26.8h, v21.8h, v25.8h"),
        Q!("    uzp2            " "v21.8h, v21.8h, v25.8h"),
        Q!("    smull           " "v25.4s, v26.4h, v5.4h"),
        Q!("    smull2          " "v5.4s, v26.8h, v5.8h"),
        Q!("    smull           " "v19.4s, v26.4h, v7.4h"),
        Q!("    smull2          " "v26.4s, v26.8h, v7.8h"),
        Q!("    smlal           " "v25.4s, v21.4h, v7.4h"),
        Q!("    smlal2          " "v5.4s, v21.8h, v7.8h"),
        Q!("    smlal           " "v19.4s, v21.4h, v6.4h"),
        Q!("    smlal2          " "v26.4s, v21.8h, v6.8h"),
        Q!("    smlal           " "v25.4s, v23.4h, v10.4h"),
        Q!("    smlal2          " "v5.4s, v23.8h, v10.8h"),
        Q!("    smlal           " "v19.4s, v23.4h, v11.4h"),
        Q!("    smlal2          " "v26.4s, v23.8h, v11.8h"),
        Q!("    ld1             " "{{ v23.8h }}, [x6], #16"),
        Q!("    smlal           " "v25.4s, v9.4h, v11.4h"),
        Q!("    smlal2          " "v5.4s, v9.8h, v11.8h"),
        Q!("    smlal2          " "v26.4s, v9.8h, v23.8h"),
        Q!("    smlal           " "v19.4s, v9.4h, v23.4h"),
        Q!("    ldr             " "q9, [x4], #0x20"),
        Q!("    uzp1            " "v11.8h, v25.8h, v5.8h"),
        Q!("    uzp1            " "v23.8h, v19.8h, v26.8h"),
        Q!("    mul             " "v11.8h, v11.8h, v2.8h"),
        Q!("    mul             " "v23.8h, v23.8h, v2.8h"),
        Q!("    ldr             " "q7, [x5], #0x20"),
        Q!("    smlal2          " "v5.4s, v11.8h, v0.8h"),
        Q!("    smlal           " "v25.4s, v11.4h, v0.4h"),
        Q!("    ldr             " "q11, [x2], #0x20"),
        Q!("    ldur            " "q21, [x2, #-0x10]"),
        Q!("    ldur            " "q6, [x4, #-0x10]"),
        Q!("    uzp1            " "v17.8h, v11.8h, v21.8h"),
        Q!("    ldr             " "q10, [x1], #0x20"),
        Q!("    ldur            " "q29, [x1, #-0x10]"),
        Q!("    uzp2            " "v11.8h, v11.8h, v21.8h"),
        Q!("    uzp1            " "v13.8h, v9.8h, v6.8h"),
        Q!("    uzp1            " "v3.8h, v10.8h, v29.8h"),
        Q!("    uzp2            " "v10.8h, v10.8h, v29.8h"),
        Q!("    smull           " "v12.4s, v3.4h, v11.4h"),
        Q!("    smull2          " "v11.4s, v3.8h, v11.8h"),
        Q!("    ldur            " "q21, [x5, #-0x10]"),
        Q!("    smlal           " "v12.4s, v10.4h, v17.4h"),
        Q!("    smlal2          " "v11.4s, v10.8h, v17.8h"),
        Q!("    uzp2            " "v29.8h, v7.8h, v21.8h"),
        Q!("    uzp1            " "v15.8h, v7.8h, v21.8h"),
        Q!("    smlal           " "v12.4s, v13.4h, v29.4h"),
        Q!("    smlal2          " "v11.4s, v13.8h, v29.8h"),
        Q!("    uzp2            " "v28.8h, v9.8h, v6.8h"),
        Q!("    smlal2          " "v26.4s, v23.8h, v0.8h"),
        Q!("    smlal           " "v12.4s, v28.4h, v15.4h"),
        Q!("    smlal2          " "v11.4s, v28.8h, v15.8h"),
        Q!("    smlal           " "v19.4s, v23.4h, v0.4h"),
        Q!("    uzp2            " "v27.8h, v25.8h, v5.8h"),
        Q!("    smull           " "v23.4s, v3.4h, v17.4h"),
        Q!("    uzp1            " "v9.8h, v12.8h, v11.8h"),
        Q!("    uzp2            " "v19.8h, v19.8h, v26.8h"),
        Q!("    mul             " "v14.8h, v9.8h, v2.8h"),
        Q!("    ld1             " "{{ v22.8h }}, [x6], #16"),
        Q!("    zip2            " "v9.8h, v19.8h, v27.8h"),
        Q!("    smlal2          " "v11.4s, v14.8h, v0.8h"),
        Q!("    ld1             " "{{ v4.8h }}, [x3], #16"),
        Q!("    sub             " "x13, x13, #0x2"),

        Q!(Label!("Lmlkem_basemul_k2_loop", 2) ":"),
        Q!("    smull2          " "v20.4s, v3.8h, v17.8h"),
        Q!("    ldr             " "q18, [x4], #0x20"),
        Q!("    ldr             " "q30, [x5], #0x20"),
        Q!("    smlal2          " "v20.4s, v10.8h, v4.8h"),
        Q!("    smlal           " "v12.4s, v14.4h, v0.4h"),
        Q!("    smlal           " "v23.4s, v10.4h, v4.4h"),
        Q!("    str             " "q9, [x0, #0x10]"),
        Q!("    smlal2          " "v20.4s, v13.8h, v15.8h"),
        Q!("    ldr             " "q8, [x2], #0x20"),
        Q!("    smlal           " "v23.4s, v13.4h, v15.4h"),
        Q!("    smlal2          " "v20.4s, v28.8h, v22.8h"),
        Q!("    zip1            " "v26.8h, v19.8h, v27.8h"),
        Q!("    ldur            " "q9, [x2, #-0x10]"),
        Q!("    smlal           " "v23.4s, v28.4h, v22.4h"),
        Q!("    uzp2            " "v27.8h, v12.8h, v11.8h"),
        Q!("    uzp1            " "v17.8h, v8.8h, v9.8h"),
        Q!("    uzp2            " "v4.8h, v8.8h, v9.8h"),
        Q!("    uzp1            " "v5.8h, v23.8h, v20.8h"),
        Q!("    str             " "q26, [x0], #0x20"),
        Q!("    mul             " "v31.8h, v5.8h, v2.8h"),
        Q!("    ldur            " "q19, [x4, #-0x10]"),
        Q!("    ldr             " "q29, [x1], #0x20"),
        Q!("    ldur            " "q12, [x1, #-0x10]"),
        Q!("    smlal2          " "v20.4s, v31.8h, v0.8h"),
        Q!("    uzp1            " "v13.8h, v18.8h, v19.8h"),
        Q!("    uzp1            " "v3.8h, v29.8h, v12.8h"),
        Q!("    uzp2            " "v10.8h, v29.8h, v12.8h"),
        Q!("    smull           " "v12.4s, v3.4h, v4.4h"),
        Q!("    smull2          " "v11.4s, v3.8h, v4.8h"),
        Q!("    ldur            " "q5, [x5, #-0x10]"),
        Q!("    smlal           " "v12.4s, v10.4h, v17.4h"),
        Q!("    smlal2          " "v11.4s, v10.8h, v17.8h"),
        Q!("    uzp2            " "v14.8h, v30.8h, v5.8h"),
        Q!("    uzp1            " "v15.8h, v30.8h, v5.8h"),
        Q!("    smlal           " "v12.4s, v13.4h, v14.4h"),
        Q!("    smlal2          " "v11.4s, v13.8h, v14.8h"),
        Q!("    uzp2            " "v28.8h, v18.8h, v19.8h"),
        Q!("    smlal           " "v23.4s, v31.4h, v0.4h"),
        Q!("    smlal           " "v12.4s, v28.4h, v15.4h"),
        Q!("    smlal2          " "v11.4s, v28.8h, v15.8h"),
        Q!("    ld1             " "{{ v22.8h }}, [x6], #16"),
        Q!("    uzp2            " "v19.8h, v23.8h, v20.8h"),
        Q!("    uzp1            " "v1.8h, v12.8h, v11.8h"),
        Q!("    smull           " "v23.4s, v3.4h, v17.4h"),
        Q!("    mul             " "v14.8h, v1.8h, v2.8h"),
        Q!("    zip2            " "v9.8h, v19.8h, v27.8h"),
        Q!("    ld1             " "{{ v4.8h }}, [x3], #16"),
        Q!("    smlal2          " "v11.4s, v14.8h, v0.8h"),
        Q!("    sub             " "x13, x13, #0x1"),
        Q!("    cbnz            " "x13, " Label!("Lmlkem_basemul_k2_loop", 2, Before)),
        Q!("    smull2          " "v5.4s, v3.8h, v17.8h"),
        Q!("    smlal           " "v12.4s, v14.4h, v0.4h"),
        Q!("    smlal           " "v23.4s, v10.4h, v4.4h"),
        Q!("    str             " "q9, [x0, #0x10]"),
        Q!("    smlal2          " "v5.4s, v10.8h, v4.8h"),
        Q!("    uzp2            " "v11.8h, v12.8h, v11.8h"),
        Q!("    zip1            " "v9.8h, v19.8h, v27.8h"),
        Q!("    smlal           " "v23.4s, v13.4h, v15.4h"),
        Q!("    smlal2          " "v5.4s, v13.8h, v15.8h"),
        Q!("    str             " "q9, [x0], #0x20"),
        Q!("    smlal           " "v23.4s, v28.4h, v22.4h"),
        Q!("    smlal2          " "v5.4s, v28.8h, v22.8h"),
        Q!("    uzp1            " "v9.8h, v23.8h, v5.8h"),
        Q!("    mul             " "v9.8h, v9.8h, v2.8h"),
        Q!("    smlal2          " "v5.4s, v9.8h, v0.8h"),
        Q!("    smlal           " "v23.4s, v9.4h, v0.4h"),
        Q!("    uzp2            " "v9.8h, v23.8h, v5.8h"),
        Q!("    zip2            " "v5.8h, v9.8h, v11.8h"),
        Q!("    zip1            " "v9.8h, v9.8h, v11.8h"),
        Q!("    str             " "q5, [x0, #0x10]"),
        Q!("    str             " "q9, [x0], #0x20"),
        Q!("    ldp             " "d8, d9, [sp, # (0 + 0)]"),
        Q!("    ldp             " "d10, d11, [sp, # (0x10 + 0)]"),
        Q!("    ldp             " "d12, d13, [sp, # (0x20 + 0)]"),
        Q!("    ldp             " "d14, d15, [sp, # (0x30 + 0)]"),
        Q!("    add             " "sp, sp, # (64 + 0)"),
        inout("x0") r.as_mut_ptr() => _,
        inout("x1") a.as_ptr() => _,
        inout("x2") b.as_ptr() => _,
        inout("x3") bt.as_ptr() => _,
        // clobbers
        out("v0") _,
        out("v1") _,
        out("v10") _,
        out("v11") _,
        out("v12") _,
        out("v13") _,
        out("v14") _,
        out("v15") _,
        out("v17") _,
        out("v18") _,
        out("v19") _,
        out("v2") _,
        out("v20") _,
        out("v21") _,
        out("v22") _,
        out("v23") _,
        out("v25") _,
        out("v26") _,
        out("v27") _,
        out("v28") _,
        out("v29") _,
        out("v3") _,
        out("v30") _,
        out("v31") _,
        out("v4") _,
        out("v5") _,
        out("v6") _,
        out("v7") _,
        out("v8") _,
        out("v9") _,
        out("x13") _,
        out("x14") _,
        out("x4") _,
        out("x5") _,
        out("x6") _,
            )
    };
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        mlkem_basemul_k2,
        &mut crate::low::abi::Aligned([0; 256]).0,
        &crate::low::abi::Aligned([0; 512]).0,
        &crate::low::abi::Aligned([0; 512]).0,
        &crate::low::abi::Aligned([0; 256]).0
    );
}
