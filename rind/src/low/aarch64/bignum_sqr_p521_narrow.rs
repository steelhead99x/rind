// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square modulo p_521, z := (x^2) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_sqr_p521(uint64_t z[static 9], const uint64_t x[static 9]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

// bignum_sqr_p521 is functionally equivalent to unopt/bignum_sqr_p521_base.
// It is written in a way that
// 1. A subset of scalar multiplications in bignum_montmul_p384 are carefully
//    chosen and vectorized
// 2. The vectorized assembly is rescheduled using the SLOTHY superoptimizer.
//    https://github.com/slothy-optimizer/slothy
//
// The output program of step 1. is as follows:
//
//        stp     x19, x20, [sp, #-16]!
//        stp     x21, x22, [sp, #-16]!
//        stp     x23, x24, [sp, #-16]!
//        ldp x20, x19, [x1]
//        ldr q23, [x1]
//        ldr q1, [x1]
//        ldr q16, [x1]
//        ldp x14, x12, [x1, #16]
//        ldr q28, [x1, #16]
//        ldr q31, [x1, #16]
//        ldp x9, x2, [x1, #32]
//        ldr q29, [x1, #32]
//        ldr q4, [x1, #32]
//        ldr q5, [x1]
//        ldr q2, [x1, #32]
//        ldp x6, x13, [x1, #48]
//        ldr q24, [x1, #48]
//        ldr q27, [x1, #48]
//        ldr q0, [x1, #16]
//        ldr q30, [x1, #48]
//        mul x17, x9, x6
//        mul x10, x2, x13
//        umulh x24, x9, x6
//        subs x4, x9, x2
//        cneg x4, x4, cc
//        csetm x16, cc
//        subs x3, x13, x6
//        cneg x23, x3, cc
//        mul x3, x4, x23
//        umulh x4, x4, x23
//        cinv x22, x16, cc
//        eor x23, x3, x22
//        eor x16, x4, x22
//        adds x3, x17, x24
//        adc x24, x24, xzr
//        umulh x4, x2, x13
//        adds x3, x3, x10
//        adcs x24, x24, x4
//        adc x4, x4, xzr
//        adds x24, x24, x10
//        adc x10, x4, xzr
//        cmn x22, #0x1
//        adcs x4, x3, x23
//        adcs x24, x24, x16
//        adc x10, x10, x22
//        adds x8, x17, x17
//        adcs x22, x4, x4
//        adcs x5, x24, x24
//        adcs x11, x10, x10
//        adc x23, xzr, xzr
//        movi v25.2D, #0xffffffff
//        uzp2 v19.4S, v4.4S, v4.4S
//        xtn v26.2S, v29.2D
//        xtn v22.2S, v4.2D
//        rev64 v4.4S, v4.4S
//        umull v7.2D, v26.2S, v22.2S
//        umull v21.2D, v26.2S, v19.2S
//        uzp2 v17.4S, v29.4S, v29.4S
//        mul v4.4S, v4.4S, v29.4S
//        usra v21.2D, v7.2D, #32
//        umull v18.2D, v17.2S, v19.2S
//        uaddlp v4.2D, v4.4S
//        and v7.16B, v21.16B, v25.16B
//        umlal v7.2D, v17.2S, v22.2S
//        shl v4.2D, v4.2D, #32
//        usra v18.2D, v21.2D, #32
//        umlal v4.2D, v26.2S, v22.2S
//        usra v18.2D, v7.2D, #32
//        mov x15, v4.d[0]
//        mov x16, v4.d[1]
//        mul x3, x9, x2
//        mov x10, v18.d[0]
//        mov x17, v18.d[1]
//        umulh x4, x9, x2
//        adds x24, x10, x3
//        adcs x10, x16, x4
//        adc x17, x17, xzr
//        adds x7, x24, x3
//        adcs x10, x10, x4
//        adc x17, x17, xzr
//        adds x8, x8, x10
//        adcs x22, x22, x17
//        adcs x21, x5, xzr
//        adcs x5, x11, xzr
//        adc x11, x23, xzr
//        movi v25.2D, #0xffffffff
//        uzp2 v19.4S, v27.4S, v27.4S
//        xtn v26.2S, v24.2D
//        xtn v22.2S, v27.2D
//        rev64 v4.4S, v27.4S
//        umull v7.2D, v26.2S, v22.2S
//        umull v21.2D, v26.2S, v19.2S
//        uzp2 v17.4S, v24.4S, v24.4S
//        mul v4.4S, v4.4S, v24.4S
//        usra v21.2D, v7.2D, #32
//        umull v18.2D, v17.2S, v19.2S
//        uaddlp v4.2D, v4.4S
//        and v7.16B, v21.16B, v25.16B
//        umlal v7.2D, v17.2S, v22.2S
//        shl v4.2D, v4.2D, #32
//        usra v18.2D, v21.2D, #32
//        umlal v4.2D, v26.2S, v22.2S
//        usra v18.2D, v7.2D, #32
//        mov x23, v4.d[0]
//        mov x16, v4.d[1]
//        mul x3, x6, x13
//        mov x10, v18.d[0]
//        mov x17, v18.d[1]
//        umulh x4, x6, x13
//        adds x24, x10, x3
//        adcs x10, x16, x4
//        adc x17, x17, xzr
//        adds x24, x24, x3
//        adcs x10, x10, x4
//        adc x17, x17, xzr
//        adds x23, x23, x21
//        adcs x16, x24, x5
//        adcs x3, x10, x11
//        adc x21, x17, xzr
//        ldr x17, [x1, #64]
//        add x5, x17, x17
//        mul x11, x17, x17
//        and x17, x20, #0xfffffffffffff
//        mul x4, x5, x17
//        extr x17, x19, x20, #52
//        and x17, x17, #0xfffffffffffff
//        mul x10, x5, x17
//        lsr x17, x4, #52
//        add x24, x10, x17
//        lsl x17, x4, #12
//        extr x17, x24, x17, #12
//        adds x15, x15, x17
//        extr x17, x14, x19, #40
//        and x17, x17, #0xfffffffffffff
//        mul x10, x5, x17
//        lsr x17, x24, #52
//        add x4, x10, x17
//        lsl x17, x24, #12
//        extr x17, x4, x17, #24
//        adcs x7, x7, x17
//        extr x17, x12, x14, #28
//        and x17, x17, #0xfffffffffffff
//        mul x10, x5, x17
//        lsr x17, x4, #52
//        add x24, x10, x17
//        lsl x17, x4, #12
//        extr x17, x24, x17, #36
//        adcs x8, x8, x17
//        extr x17, x9, x12, #16
//        and x17, x17, #0xfffffffffffff
//        mul x10, x5, x17
//        lsr x17, x24, #52
//        add x4, x10, x17
//        lsl x17, x24, #12
//        extr x17, x4, x17, #48
//        adcs x22, x22, x17
//        lsr x17, x9, #4
//        and x17, x17, #0xfffffffffffff
//        mul x10, x5, x17
//        lsr x17, x4, #52
//        add x24, x10, x17
//        lsl x17, x4, #12
//        extr x4, x24, x17, #60
//        extr x17, x2, x9, #56
//        and x17, x17, #0xfffffffffffff
//        mul x10, x5, x17
//        lsr x17, x24, #52
//        add x24, x10, x17
//        lsl x17, x4, #8
//        extr x17, x24, x17, #8
//        adcs x23, x23, x17
//        extr x17, x6, x2, #44
//        and x17, x17, #0xfffffffffffff
//        mul x10, x5, x17
//        lsr x17, x24, #52
//        add x4, x10, x17
//        lsl x17, x24, #12
//        extr x17, x4, x17, #20
//        adcs x16, x16, x17
//        extr x17, x13, x6, #32
//        and x17, x17, #0xfffffffffffff
//        mul x10, x5, x17
//        lsr x17, x4, #52
//        add x24, x10, x17
//        lsl x17, x4, #12
//        extr x17, x24, x17, #32
//        adcs x3, x3, x17
//        lsr x17, x13, #20
//        mul x10, x5, x17
//        lsr x17, x24, #52
//        add x10, x10, x17
//        lsl x17, x24, #12
//        extr x17, x10, x17, #44
//        adcs x4, x21, x17
//        lsr x17, x10, #44
//        adc x24, x11, x17
//        extr x10, x7, x15, #9
//        extr x17, x8, x7, #9
//        stp x10, x17, [x0]                       // @slothy:writes=buffer0
//        extr x10, x22, x8, #9
//        extr x17, x23, x22, #9
//        stp x10, x17, [x0, #16]                  // @slothy:writes=buffer16
//        extr x10, x16, x23, #9
//        extr x17, x3, x16, #9
//        stp x10, x17, [x0, #32]                  // @slothy:writes=buffer32
//        extr x10, x4, x3, #9
//        extr x17, x24, x4, #9
//        stp x10, x17, [x0, #48]                  // @slothy:writes=buffer48
//        and x10, x15, #0x1ff
//        lsr x17, x24, #9
//        add x17, x10, x17
//        str x17, [x0, #64]                       // @slothy:writes=buffer64
//        uzp1 v17.4S, v28.4S, v23.4S
//        rev64 v4.4S, v28.4S
//        uzp1 v7.4S, v23.4S, v23.4S
//        mul v4.4S, v4.4S, v23.4S
//        uaddlp v4.2D, v4.4S
//        shl v4.2D, v4.2D, #32
//        umlal v4.2D, v7.2S, v17.2S
//        mov x8, v4.d[0]
//        mov x22, v4.d[1]
//        umulh x23, x20, x14
//        subs x17, x20, x19
//        cneg x4, x17, cc
//        csetm x24, cc
//        subs x17, x12, x14
//        cneg x17, x17, cc
//        mul x10, x4, x17
//        umulh x17, x4, x17
//        cinv x16, x24, cc
//        eor x3, x10, x16
//        eor x4, x17, x16
//        adds x24, x8, x23
//        adc x10, x23, xzr
//        umulh x17, x19, x12
//        adds x24, x24, x22
//        adcs x10, x10, x17
//        adc x17, x17, xzr
//        adds x10, x10, x22
//        adc x17, x17, xzr
//        cmn x16, #0x1
//        adcs x24, x24, x3
//        adcs x10, x10, x4
//        adc x17, x17, x16
//        adds x15, x8, x8
//        adcs x7, x24, x24
//        adcs x8, x10, x10
//        adcs x22, x17, x17
//        adc x23, xzr, xzr
//        movi v25.2D, #0xffffffff
//        uzp2 v19.4S, v16.4S, v16.4S
//        xtn v26.2S, v1.2D
//        xtn v22.2S, v16.2D
//        rev64 v4.4S, v16.4S
//        umull v7.2D, v26.2S, v22.2S
//        umull v21.2D, v26.2S, v19.2S
//        uzp2 v17.4S, v1.4S, v1.4S
//        mul v4.4S, v4.4S, v1.4S
//        usra v21.2D, v7.2D, #32
//        umull v18.2D, v17.2S, v19.2S
//        uaddlp v4.2D, v4.4S
//        and v7.16B, v21.16B, v25.16B
//        umlal v7.2D, v17.2S, v22.2S
//        shl v4.2D, v4.2D, #32
//        usra v18.2D, v21.2D, #32
//        umlal v4.2D, v26.2S, v22.2S
//        usra v18.2D, v7.2D, #32
//        mov x21, v4.d[0]
//        mov x16, v4.d[1]
//        mul x3, x20, x19
//        mov x10, v18.d[0]
//        mov x17, v18.d[1]
//        umulh x4, x20, x19
//        adds x24, x10, x3
//        adcs x10, x16, x4
//        adc x17, x17, xzr
//        adds x5, x24, x3
//        adcs x10, x10, x4
//        adc x17, x17, xzr
//        adds x11, x15, x10
//        adcs x15, x7, x17
//        adcs x7, x8, xzr
//        adcs x8, x22, xzr
//        adc x22, x23, xzr
//        xtn v7.2S, v31.2D
//        shrn v4.2S, v31.2D, #32
//        umull v4.2D, v7.2S, v4.2S
//        shl v4.2D, v4.2D, #33
//        umlal v4.2D, v7.2S, v7.2S
//        mov x23, v4.d[0]
//        mov x16, v4.d[1]
//        mul x3, x14, x12
//        umulh x10, x14, x14
//        umulh x17, x12, x12
//        umulh x4, x14, x12
//        adds x24, x10, x3
//        adcs x10, x16, x4
//        adc x17, x17, xzr
//        adds x24, x24, x3
//        adcs x10, x10, x4
//        adc x17, x17, xzr
//        adds x16, x23, x7
//        adcs x3, x24, x8
//        adcs x4, x10, x22
//        adc x24, x17, xzr
//        ldp x10, x17, [x0]                       // @slothy:reads=buffer0
//        adds x10, x10, x21
//        adcs x17, x17, x5
//        stp x10, x17, [x0]                       // @slothy:writes=buffer0
//        ldp x10, x17, [x0, #16]                  // @slothy:reads=buffer16
//        adcs x10, x10, x11
//        adcs x17, x17, x15
//        stp x10, x17, [x0, #16]                  // @slothy:writes=buffer16
//        ldp x10, x17, [x0, #32]                  // @slothy:reads=buffer32
//        adcs x10, x10, x16
//        adcs x17, x17, x3
//        stp x10, x17, [x0, #32]                  // @slothy:writes=buffer32
//        ldp x10, x17, [x0, #48]                  // @slothy:reads=buffer48
//        adcs x10, x10, x4
//        adcs x17, x17, x24
//        stp x10, x17, [x0, #48]                  // @slothy:writes=buffer48
//        ldr x17, [x0, #64]                       // @slothy:reads=buffer64
//        adc x17, x17, xzr
//        str x17, [x0, #64]                       // @slothy:writes=buffer64
//        movi v25.2D, #0xffffffff
//        uzp2 v19.4S, v2.4S, v2.4S
//        xtn v26.2S, v5.2D
//        xtn v22.2S, v2.2D
//        rev64 v4.4S, v2.4S
//        umull v7.2D, v26.2S, v22.2S
//        umull v21.2D, v26.2S, v19.2S
//        uzp2 v17.4S, v5.4S, v5.4S
//        mul v4.4S, v4.4S, v5.4S
//        usra v21.2D, v7.2D, #32
//        umull v18.2D, v17.2S, v19.2S
//        uaddlp v4.2D, v4.4S
//        and v7.16B, v21.16B, v25.16B
//        umlal v7.2D, v17.2S, v22.2S
//        shl v4.2D, v4.2D, #32
//        usra v18.2D, v21.2D, #32
//        umlal v4.2D, v26.2S, v22.2S
//        usra v18.2D, v7.2D, #32
//        mov x5, v4.d[0]
//        mov x4, v4.d[1]
//        movi v25.2D, #0xffffffff
//        uzp2 v17.4S, v30.4S, v30.4S
//        xtn v19.2S, v0.2D
//        xtn v26.2S, v30.2D
//        rev64 v4.4S, v30.4S
//        umull v7.2D, v19.2S, v26.2S
//        umull v22.2D, v19.2S, v17.2S
//        uzp2 v21.4S, v0.4S, v0.4S
//        mul v4.4S, v4.4S, v0.4S
//        usra v22.2D, v7.2D, #32
//        umull v17.2D, v21.2S, v17.2S
//        uaddlp v4.2D, v4.4S
//        and v7.16B, v22.16B, v25.16B
//        umlal v7.2D, v21.2S, v26.2S
//        shl v4.2D, v4.2D, #32
//        usra v17.2D, v22.2D, #32
//        umlal v4.2D, v19.2S, v26.2S
//        usra v17.2D, v7.2D, #32
//        mov x24, v4.d[0]
//        mov x10, v4.d[1]
//        mov x17, v18.d[0]
//        adds x4, x4, x17
//        mov x17, v18.d[1]
//        adcs x24, x24, x17
//        mov x17, v17.d[0]
//        adcs x10, x10, x17
//        mov x17, v17.d[1]
//        adc x17, x17, xzr
//        adds x15, x4, x5
//        adcs x4, x24, x4
//        adcs x24, x10, x24
//        adcs x10, x17, x10
//        adc x17, xzr, x17
//        adds x7, x4, x5
//        adcs x8, x24, x15
//        adcs x22, x10, x4
//        adcs x23, x17, x24
//        adcs x16, xzr, x10
//        adc x3, xzr, x17
//        subs x17, x14, x12
//        cneg x24, x17, cc
//        csetm x4, cc
//        subs x17, x13, x6
//        cneg x10, x17, cc
//        mul x17, x24, x10
//        umulh x24, x24, x10
//        cinv x10, x4, cc
//        cmn x10, #0x1
//        eor x17, x17, x10
//        adcs x23, x23, x17
//        eor x17, x24, x10
//        adcs x16, x16, x17
//        adc x3, x3, x10
//        subs x17, x20, x19
//        cneg x24, x17, cc
//        csetm x4, cc
//        subs x17, x2, x9
//        cneg x10, x17, cc
//        mul x17, x24, x10
//        umulh x24, x24, x10
//        cinv x10, x4, cc
//        cmn x10, #0x1
//        eor x17, x17, x10
//        adcs x11, x15, x17
//        eor x17, x24, x10
//        adcs x15, x7, x17
//        adcs x7, x8, x10
//        adcs x22, x22, x10
//        adcs x23, x23, x10
//        adcs x16, x16, x10
//        adc x3, x3, x10
//        subs x17, x19, x12
//        cneg x24, x17, cc
//        csetm x4, cc
//        subs x17, x13, x2
//        cneg x10, x17, cc
//        mul x17, x24, x10
//        umulh x24, x24, x10
//        cinv x10, x4, cc
//        cmn x10, #0x1
//        eor x17, x17, x10
//        adcs x8, x22, x17
//        eor x17, x24, x10
//        adcs x23, x23, x17
//        adcs x16, x16, x10
//        adc x3, x3, x10
//        subs x17, x20, x14
//        cneg x24, x17, cc
//        csetm x4, cc
//        subs x17, x6, x9
//        cneg x10, x17, cc
//        mul x17, x24, x10
//        umulh x24, x24, x10
//        cinv x10, x4, cc
//        cmn x10, #0x1
//        eor x17, x17, x10
//        adcs x22, x15, x17
//        eor x17, x24, x10
//        adcs x4, x7, x17
//        adcs x24, x8, x10
//        adcs x23, x23, x10
//        adcs x16, x16, x10
//        adc x3, x3, x10
//        subs x12, x20, x12
//        cneg x10, x12, cc
//        csetm x17, cc
//        subs x12, x13, x9
//        cneg x9, x12, cc
//        mul x12, x10, x9
//        umulh x13, x10, x9
//        cinv x9, x17, cc
//        cmn x9, #0x1
//        eor x12, x12, x9
//        adcs x4, x4, x12
//        eor x12, x13, x9
//        adcs x24, x24, x12
//        adcs x10, x23, x9
//        adcs x17, x16, x9
//        adc x13, x3, x9
//        subs x19, x19, x14
//        cneg x12, x19, cc
//        csetm x9, cc
//        subs x6, x6, x2
//        cneg x14, x6, cc
//        mul x19, x12, x14
//        umulh x12, x12, x14
//        cinv x14, x9, cc
//        cmn x14, #0x1
//        eor x19, x19, x14
//        adcs x23, x4, x19
//        eor x19, x12, x14
//        adcs x16, x24, x19
//        adcs x6, x10, x14
//        adcs x2, x17, x14
//        adc x9, x13, x14
//        ldp x12, x14, [x0]                       // @slothy:reads=buffer0
//        extr x19, x6, x16, #8
//        adds x10, x19, x12
//        extr x19, x2, x6, #8
//        adcs x17, x19, x14
//        ldp x14, x12, [x0, #16]                  // @slothy:reads=buffer16
//        extr x19, x9, x2, #8
//        adcs x13, x19, x14
//        and x14, x17, x13
//        lsr x19, x9, #8
//        adcs x6, x19, x12
//        and x9, x14, x6
//        ldp x14, x12, [x0, #32]                  // @slothy:reads=buffer32
//        lsl x19, x5, #1
//        adcs x2, x19, x14
//        and x14, x9, x2
//        extr x19, x11, x5, #63
//        adcs x3, x19, x12
//        and x9, x14, x3
//        ldp x14, x12, [x0, #48]                  // @slothy:reads=buffer48
//        extr x19, x22, x11, #63
//        adcs x4, x19, x14
//        and x14, x9, x4
//        extr x19, x23, x22, #63
//        adcs x24, x19, x12
//        and x12, x14, x24
//        ldr x14, [x0, #64]                       // @slothy:reads=buffer64
//        extr x19, x16, x23, #63
//        and x19, x19, #0x1ff
//        adc x19, x14, x19
//        lsr x14, x19, #9
//        orr x19, x19, #0xfffffffffffffe00
//        cmp xzr, xzr
//        adcs xzr, x10, x14
//        adcs xzr, x12, xzr
//        adcs xzr, x19, xzr
//        adcs x10, x10, x14
//        adcs x17, x17, xzr
//        adcs x13, x13, xzr
//        adcs x6, x6, xzr
//        adcs x2, x2, xzr
//        adcs x9, x3, xzr
//        adcs x12, x4, xzr
//        adcs x14, x24, xzr
//        adc x19, x19, xzr
//        and x19, x19, #0x1ff
//        stp x10, x17, [x0]                       // @slothy:writes=buffer0
//        stp x13, x6, [x0, #16]                   // @slothy:writes=buffer16
//        stp x2, x9, [x0, #32]                    // @slothy:writes=buffer32
//        stp x12, x14, [x0, #48]                  // @slothy:writes=buffer48
//        str x19, [x0, #64]                       // @slothy:writes=buffer64
//        ldp     x23, x24, [sp], #16
//        ldp     x21, x22, [sp], #16
//        ldp     x19, x20, [sp], #16
//        ret
//
// The bash script used for step 2 is as follows:
//
//        # Store the assembly instructions except the last 'ret',
//        # callee-register store/loads as, say, 'input.S'.
//        export OUTPUTS="[hint_buffer0,hint_buffer16,hint_buffer32,hint_buffer48,hint_buffer64]"
//        export RESERVED_REGS="[x18,x25,x26,x27,x28,x29,x30,sp,q8,q9,q10,q11,q12,q13,q14,q15,v8,v9,v10,v11,v12,v13,v14,v15]"
//        <s2n-bignum>/tools/external/slothy.sh input.S my_out_dir
//        # my_out_dir/3.opt.s is the optimized assembly. Its output may differ
//        # from this file since the sequence is non-deterministically chosen.
//        # Please add 'ret' at the end of the output assembly.

// Transliterated from s2n-bignum's arm/p521/bignum_sqr_p521.S.
/// Square modulo p_521, z := (x^2) mod p_521, assuming x reduced
///
/// Input x[9]; output z[9]
#[inline(never)]
pub(crate) fn bignum_sqr_p521(z: &mut [u64; 9], x: &[u64; 9]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Save registers

        Q!("    stp             " "x19, x20, [sp, #-16] !"),
        Q!("    stp             " "x21, x22, [sp, #-16] !"),
        Q!("    stp             " "x23, x24, [sp, #-16] !"),

        Q!("    ldr             " "q23, [x1, #32]"),
        Q!("    ldp             " "x9, x2, [x1, #32]"),
        Q!("    ldr             " "q16, [x1, #32]"),
        Q!("    ldr             " "q20, [x1, #48]"),
        Q!("    ldp             " "x6, x13, [x1, #48]"),
        Q!("    rev64           " "v2.4S, v23.4S"),
        Q!("    mul             " "x14, x9, x2"),
        Q!("    ldr             " "q31, [x1, #48]"),
        Q!("    subs            " "x22, x9, x2"),
        Q!("    uzp2            " "v26.4S, v23.4S, v23.4S"),
        Q!("    mul             " "v30.4S, v2.4S, v16.4S"),
        Q!("    xtn             " "v0.2S, v20.2D"),
        Q!("    csetm           " "x12, cc"),
        Q!("    xtn             " "v21.2S, v16.2D"),
        Q!("    xtn             " "v23.2S, v23.2D"),
        Q!("    umulh           " "x10, x9, x6"),
        Q!("    rev64           " "v27.4S, v31.4S"),
        Q!("    umull           " "v2.2D, v21.2S, v26.2S"),
        Q!("    cneg            " "x23, x22, cc"),
        Q!("    uaddlp          " "v25.2D, v30.4S"),
        Q!("    umull           " "v18.2D, v21.2S, v23.2S"),
        Q!("    mul             " "x22, x9, x6"),
        Q!("    mul             " "v6.4S, v27.4S, v20.4S"),
        Q!("    uzp2            " "v17.4S, v20.4S, v20.4S"),
        Q!("    shl             " "v20.2D, v25.2D, #32"),
        Q!("    uzp2            " "v27.4S, v31.4S, v31.4S"),
        Q!("    mul             " "x16, x2, x13"),
        Q!("    umlal           " "v20.2D, v21.2S, v23.2S"),
        Q!("    usra            " "v2.2D, v18.2D, #32"),
        Q!("    adds            " "x8, x22, x10"),
        Q!("    umull           " "v25.2D, v17.2S, v27.2S"),
        Q!("    xtn             " "v31.2S, v31.2D"),
        Q!("    movi            " "v1.2D, #0xffffffff"),
        Q!("    adc             " "x3, x10, xzr"),
        Q!("    umulh           " "x21, x2, x13"),
        Q!("    uzp2            " "v21.4S, v16.4S, v16.4S"),
        Q!("    umull           " "v18.2D, v0.2S, v27.2S"),
        Q!("    subs            " "x19, x13, x6"),
        Q!("    and             " "v7.16B, v2.16B, v1.16B"),
        Q!("    umull           " "v27.2D, v0.2S, v31.2S"),
        Q!("    cneg            " "x20, x19, cc"),
        Q!("    movi            " "v30.2D, #0xffffffff"),
        Q!("    umull           " "v16.2D, v21.2S, v26.2S"),
        Q!("    umlal           " "v7.2D, v21.2S, v23.2S"),
        Q!("    mul             " "x19, x23, x20"),
        Q!("    cinv            " "x7, x12, cc"),
        Q!("    uaddlp          " "v6.2D, v6.4S"),
        Q!("    eor             " "x12, x19, x7"),
        Q!("    adds            " "x11, x8, x16"),
        Q!("    umulh           " "x10, x23, x20"),
        Q!("    ldr             " "q1, [x1]"),
        Q!("    usra            " "v16.2D, v2.2D, #32"),
        Q!("    adcs            " "x19, x3, x21"),
        Q!("    shl             " "v2.2D, v6.2D, #32"),
        Q!("    adc             " "x20, x21, xzr"),
        Q!("    adds            " "x17, x19, x16"),
        Q!("    usra            " "v18.2D, v27.2D, #32"),
        Q!("    adc             " "x19, x20, xzr"),
        Q!("    cmn             " "x7, #0x1"),
        Q!("    umlal           " "v2.2D, v0.2S, v31.2S"),
        Q!("    umulh           " "x16, x9, x2"),
        Q!("    adcs            " "x8, x11, x12"),
        Q!("    usra            " "v16.2D, v7.2D, #32"),
        Q!("    ldr             " "x12, [x1, #64]"),
        Q!("    eor             " "x20, x10, x7"),
        Q!("    umulh           " "x10, x6, x13"),
        Q!("    mov             " "x23, v2.d[0]"),
        Q!("    mov             " "x3, v2.d[1]"),
        Q!("    adcs            " "x21, x17, x20"),
        Q!("    usra            " "v25.2D, v18.2D, #32"),
        Q!("    and             " "v23.16B, v18.16B, v30.16B"),
        Q!("    adc             " "x7, x19, x7"),
        Q!("    adds            " "x22, x22, x22"),
        Q!("    ldr             " "q7, [x1, #16]"),
        Q!("    adcs            " "x17, x8, x8"),
        Q!("    umlal           " "v23.2D, v17.2S, v31.2S"),
        Q!("    mov             " "x19, v16.d[0]"),
        Q!("    mul             " "x11, x12, x12"),
        Q!("    ldr             " "q4, [x1]"),
        Q!("    usra            " "v25.2D, v23.2D, #32"),
        Q!("    add             " "x5, x12, x12"),
        Q!("    adcs            " "x15, x21, x21"),
        Q!("    ldr             " "q28, [x1]"),
        Q!("    mov             " "x12, v20.d[1]"),
        Q!("    adcs            " "x24, x7, x7"),
        Q!("    mov             " "x21, v16.d[1]"),
        Q!("    adc             " "x4, xzr, xzr"),
        Q!("    adds            " "x19, x19, x14"),
        Q!("    ldr             " "q18, [x1, #16]"),
        Q!("    xtn             " "v26.2S, v1.2D"),
        Q!("    adcs            " "x8, x12, x16"),
        Q!("    adc             " "x21, x21, xzr"),
        Q!("    adds            " "x7, x19, x14"),
        Q!("    xtn             " "v23.2S, v7.2D"),
        Q!("    rev64           " "v21.4S, v28.4S"),
        Q!("    adcs            " "x12, x8, x16"),
        Q!("    ldp             " "x20, x19, [x1]"),
        Q!("    mov             " "x16, v25.d[1]"),
        Q!("    xtn             " "v22.2S, v28.2D"),
        Q!("    adc             " "x14, x21, xzr"),
        Q!("    adds            " "x8, x22, x12"),
        Q!("    uzp2            " "v24.4S, v28.4S, v28.4S"),
        Q!("    rev64           " "v28.4S, v18.4S"),
        Q!("    mul             " "x12, x6, x13"),
        Q!("    mul             " "v16.4S, v21.4S, v1.4S"),
        Q!("    shrn            " "v31.2S, v7.2D, #32"),
        Q!("    adcs            " "x22, x17, x14"),
        Q!("    mov             " "x14, v25.d[0]"),
        Q!("    and             " "x21, x20, #0xfffffffffffff"),
        Q!("    umull           " "v17.2D, v26.2S, v24.2S"),
        Q!("    ldr             " "q2, [x1, #32]"),
        Q!("    adcs            " "x17, x15, xzr"),
        Q!("    ldr             " "q30, [x1, #48]"),
        Q!("    umull           " "v7.2D, v26.2S, v22.2S"),
        Q!("    adcs            " "x15, x24, xzr"),
        Q!("    ldr             " "q0, [x1, #16]"),
        Q!("    movi            " "v6.2D, #0xffffffff"),
        Q!("    adc             " "x4, x4, xzr"),
        Q!("    adds            " "x14, x14, x12"),
        Q!("    uzp1            " "v27.4S, v18.4S, v4.4S"),
        Q!("    uzp2            " "v19.4S, v1.4S, v1.4S"),
        Q!("    adcs            " "x24, x3, x10"),
        Q!("    mul             " "x3, x5, x21"),
        Q!("    umull           " "v29.2D, v23.2S, v31.2S"),
        Q!("    ldr             " "q5, [x1]"),
        Q!("    adc             " "x21, x16, xzr"),
        Q!("    adds            " "x16, x14, x12"),
        Q!("    extr            " "x12, x19, x20, #52"),
        Q!("    umull           " "v18.2D, v19.2S, v24.2S"),
        Q!("    adcs            " "x24, x24, x10"),
        Q!("    and             " "x10, x12, #0xfffffffffffff"),
        Q!("    ldp             " "x14, x12, [x1, #16]"),
        Q!("    usra            " "v17.2D, v7.2D, #32"),
        Q!("    adc             " "x21, x21, xzr"),
        Q!("    adds            " "x23, x23, x17"),
        Q!("    mul             " "x17, x5, x10"),
        Q!("    shl             " "v21.2D, v29.2D, #33"),
        Q!("    lsl             " "x10, x3, #12"),
        Q!("    lsr             " "x1, x3, #52"),
        Q!("    rev64           " "v29.4S, v2.4S"),
        Q!("    uaddlp          " "v25.2D, v16.4S"),
        Q!("    add             " "x17, x17, x1"),
        Q!("    adcs            " "x16, x16, x15"),
        Q!("    extr            " "x3, x14, x19, #40"),
        Q!("    mov             " "x15, v20.d[0]"),
        Q!("    extr            " "x10, x17, x10, #12"),
        Q!("    and             " "x3, x3, #0xfffffffffffff"),
        Q!("    shl             " "v3.2D, v25.2D, #32"),
        Q!("    and             " "v6.16B, v17.16B, v6.16B"),
        Q!("    mul             " "x1, x5, x3"),
        Q!("    usra            " "v18.2D, v17.2D, #32"),
        Q!("    adcs            " "x3, x24, x4"),
        Q!("    extr            " "x4, x12, x14, #28"),
        Q!("    umlal           " "v6.2D, v19.2S, v22.2S"),
        Q!("    xtn             " "v20.2S, v2.2D"),
        Q!("    umlal           " "v3.2D, v26.2S, v22.2S"),
        Q!("    movi            " "v26.2D, #0xffffffff"),
        Q!("    lsr             " "x24, x17, #52"),
        Q!("    and             " "x4, x4, #0xfffffffffffff"),
        Q!("    uzp2            " "v19.4S, v2.4S, v2.4S"),
        Q!("    add             " "x1, x1, x24"),
        Q!("    mul             " "x24, x5, x4"),
        Q!("    lsl             " "x4, x17, #12"),
        Q!("    xtn             " "v24.2S, v5.2D"),
        Q!("    extr            " "x17, x1, x4, #24"),
        Q!("    adc             " "x21, x21, xzr"),
        Q!("    umlal           " "v21.2D, v23.2S, v23.2S"),
        Q!("    adds            " "x4, x15, x10"),
        Q!("    lsl             " "x10, x1, #12"),
        Q!("    adcs            " "x15, x7, x17"),
        Q!("    mul             " "v23.4S, v28.4S, v4.4S"),
        Q!("    and             " "x7, x4, #0x1ff"),
        Q!("    lsr             " "x17, x1, #52"),
        Q!("    umulh           " "x1, x19, x12"),
        Q!("    uzp2            " "v17.4S, v5.4S, v5.4S"),
        Q!("    extr            " "x4, x15, x4, #9"),
        Q!("    add             " "x24, x24, x17"),
        Q!("    mul             " "v29.4S, v29.4S, v5.4S"),
        Q!("    extr            " "x17, x24, x10, #36"),
        Q!("    extr            " "x10, x9, x12, #16"),
        Q!("    uzp1            " "v28.4S, v4.4S, v4.4S"),
        Q!("    adcs            " "x17, x8, x17"),
        Q!("    and             " "x8, x10, #0xfffffffffffff"),
        Q!("    umull           " "v16.2D, v24.2S, v20.2S"),
        Q!("    extr            " "x10, x17, x15, #9"),
        Q!("    mul             " "x15, x5, x8"),
        Q!("    stp             " "x4, x10, [x0]"),
        Q!("    lsl             " "x4, x24, #12"),
        Q!("    lsr             " "x8, x9, #4"),
        Q!("    uaddlp          " "v4.2D, v23.4S"),
        Q!("    and             " "x8, x8, #0xfffffffffffff"),
        Q!("    umull           " "v23.2D, v24.2S, v19.2S"),
        Q!("    mul             " "x8, x5, x8"),
        Q!("    extr            " "x10, x2, x9, #56"),
        Q!("    lsr             " "x24, x24, #52"),
        Q!("    and             " "x10, x10, #0xfffffffffffff"),
        Q!("    add             " "x15, x15, x24"),
        Q!("    extr            " "x4, x15, x4, #48"),
        Q!("    mul             " "x24, x5, x10"),
        Q!("    lsr             " "x10, x15, #52"),
        Q!("    usra            " "v23.2D, v16.2D, #32"),
        Q!("    add             " "x10, x8, x10"),
        Q!("    shl             " "v4.2D, v4.2D, #32"),
        Q!("    adcs            " "x22, x22, x4"),
        Q!("    extr            " "x4, x6, x2, #44"),
        Q!("    lsl             " "x15, x15, #12"),
        Q!("    lsr             " "x8, x10, #52"),
        Q!("    extr            " "x15, x10, x15, #60"),
        Q!("    and             " "x10, x4, #0xfffffffffffff"),
        Q!("    umlal           " "v4.2D, v28.2S, v27.2S"),
        Q!("    add             " "x8, x24, x8"),
        Q!("    extr            " "x4, x13, x6, #32"),
        Q!("    mul             " "x24, x5, x10"),
        Q!("    uzp2            " "v16.4S, v30.4S, v30.4S"),
        Q!("    lsl             " "x10, x15, #8"),
        Q!("    rev64           " "v28.4S, v30.4S"),
        Q!("    and             " "x15, x4, #0xfffffffffffff"),
        Q!("    extr            " "x4, x8, x10, #8"),
        Q!("    mul             " "x10, x5, x15"),
        Q!("    lsl             " "x15, x8, #12"),
        Q!("    adcs            " "x23, x23, x4"),
        Q!("    lsr             " "x4, x8, #52"),
        Q!("    lsr             " "x8, x13, #20"),
        Q!("    add             " "x4, x24, x4"),
        Q!("    mul             " "x8, x5, x8"),
        Q!("    lsr             " "x24, x4, #52"),
        Q!("    extr            " "x15, x4, x15, #20"),
        Q!("    lsl             " "x4, x4, #12"),
        Q!("    add             " "x10, x10, x24"),
        Q!("    adcs            " "x15, x16, x15"),
        Q!("    extr            " "x4, x10, x4, #32"),
        Q!("    umulh           " "x5, x20, x14"),
        Q!("    adcs            " "x3, x3, x4"),
        Q!("    usra            " "v18.2D, v6.2D, #32"),
        Q!("    lsl             " "x16, x10, #12"),
        Q!("    extr            " "x24, x15, x23, #9"),
        Q!("    lsr             " "x10, x10, #52"),
        Q!("    uzp2            " "v27.4S, v0.4S, v0.4S"),
        Q!("    add             " "x8, x8, x10"),
        Q!("    extr            " "x10, x3, x15, #9"),
        Q!("    extr            " "x4, x22, x17, #9"),
        Q!("    and             " "v25.16B, v23.16B, v26.16B"),
        Q!("    lsr             " "x17, x8, #44"),
        Q!("    extr            " "x15, x8, x16, #44"),
        Q!("    extr            " "x16, x23, x22, #9"),
        Q!("    xtn             " "v7.2S, v30.2D"),
        Q!("    mov             " "x8, v4.d[0]"),
        Q!("    stp             " "x24, x10, [x0, #32]"),
        Q!("    uaddlp          " "v30.2D, v29.4S"),
        Q!("    stp             " "x4, x16, [x0, #16]"),
        Q!("    umulh           " "x24, x20, x19"),
        Q!("    adcs            " "x15, x21, x15"),
        Q!("    adc             " "x16, x11, x17"),
        Q!("    subs            " "x11, x20, x19"),
        Q!("    xtn             " "v5.2S, v0.2D"),
        Q!("    csetm           " "x17, cc"),
        Q!("    extr            " "x3, x15, x3, #9"),
        Q!("    mov             " "x22, v4.d[1]"),
        Q!("    cneg            " "x21, x11, cc"),
        Q!("    subs            " "x10, x12, x14"),
        Q!("    mul             " "v31.4S, v28.4S, v0.4S"),
        Q!("    cneg            " "x10, x10, cc"),
        Q!("    cinv            " "x11, x17, cc"),
        Q!("    shl             " "v4.2D, v30.2D, #32"),
        Q!("    umull           " "v28.2D, v5.2S, v16.2S"),
        Q!("    extr            " "x23, x16, x15, #9"),
        Q!("    adds            " "x4, x8, x5"),
        Q!("    mul             " "x17, x21, x10"),
        Q!("    umull           " "v22.2D, v5.2S, v7.2S"),
        Q!("    adc             " "x15, x5, xzr"),
        Q!("    adds            " "x4, x4, x22"),
        Q!("    uaddlp          " "v2.2D, v31.4S"),
        Q!("    lsr             " "x5, x16, #9"),
        Q!("    adcs            " "x16, x15, x1"),
        Q!("    mov             " "x15, v18.d[0]"),
        Q!("    adc             " "x1, x1, xzr"),
        Q!("    umulh           " "x10, x21, x10"),
        Q!("    adds            " "x22, x16, x22"),
        Q!("    umlal           " "v4.2D, v24.2S, v20.2S"),
        Q!("    umull           " "v30.2D, v27.2S, v16.2S"),
        Q!("    stp             " "x3, x23, [x0, #48]"),
        Q!("    add             " "x3, x7, x5"),
        Q!("    adc             " "x16, x1, xzr"),
        Q!("    usra            " "v28.2D, v22.2D, #32"),
        Q!("    mul             " "x23, x20, x19"),
        Q!("    eor             " "x1, x17, x11"),
        Q!("    cmn             " "x11, #0x1"),
        Q!("    mov             " "x17, v18.d[1]"),
        Q!("    umull           " "v18.2D, v17.2S, v19.2S"),
        Q!("    adcs            " "x7, x4, x1"),
        Q!("    eor             " "x1, x10, x11"),
        Q!("    umlal           " "v25.2D, v17.2S, v20.2S"),
        Q!("    movi            " "v16.2D, #0xffffffff"),
        Q!("    adcs            " "x22, x22, x1"),
        Q!("    usra            " "v18.2D, v23.2D, #32"),
        Q!("    umulh           " "x4, x14, x14"),
        Q!("    adc             " "x1, x16, x11"),
        Q!("    adds            " "x10, x8, x8"),
        Q!("    shl             " "v23.2D, v2.2D, #32"),
        Q!("    str             " "x3, [x0, #64]"),
        Q!("    adcs            " "x5, x7, x7"),
        Q!("    and             " "v16.16B, v28.16B, v16.16B"),
        Q!("    usra            " "v30.2D, v28.2D, #32"),
        Q!("    adcs            " "x7, x22, x22"),
        Q!("    mov             " "x21, v3.d[1]"),
        Q!("    adcs            " "x11, x1, x1"),
        Q!("    umlal           " "v16.2D, v27.2S, v7.2S"),
        Q!("    adc             " "x22, xzr, xzr"),
        Q!("    adds            " "x16, x15, x23"),
        Q!("    mul             " "x8, x14, x12"),
        Q!("    umlal           " "v23.2D, v5.2S, v7.2S"),
        Q!("    usra            " "v18.2D, v25.2D, #32"),
        Q!("    umulh           " "x15, x14, x12"),
        Q!("    adcs            " "x21, x21, x24"),
        Q!("    usra            " "v30.2D, v16.2D, #32"),
        Q!("    adc             " "x1, x17, xzr"),
        Q!("    adds            " "x3, x16, x23"),
        Q!("    adcs            " "x21, x21, x24"),
        Q!("    adc             " "x1, x1, xzr"),
        Q!("    adds            " "x24, x10, x21"),
        Q!("    umulh           " "x21, x12, x12"),
        Q!("    adcs            " "x16, x5, x1"),
        Q!("    adcs            " "x10, x7, xzr"),
        Q!("    mov             " "x17, v21.d[1]"),
        Q!("    adcs            " "x23, x11, xzr"),
        Q!("    adc             " "x5, x22, xzr"),
        Q!("    adds            " "x1, x4, x8"),
        Q!("    adcs            " "x22, x17, x15"),
        Q!("    ldp             " "x17, x4, [x0]"),
        Q!("    mov             " "x11, v21.d[0]"),
        Q!("    adc             " "x21, x21, xzr"),
        Q!("    adds            " "x1, x1, x8"),
        Q!("    adcs            " "x15, x22, x15"),
        Q!("    adc             " "x8, x21, xzr"),
        Q!("    adds            " "x22, x11, x10"),
        Q!("    mov             " "x21, v3.d[0]"),
        Q!("    adcs            " "x11, x1, x23"),
        Q!("    ldp             " "x1, x10, [x0, #16]"),
        Q!("    adcs            " "x15, x15, x5"),
        Q!("    adc             " "x7, x8, xzr"),
        Q!("    adds            " "x8, x17, x21"),
        Q!("    mov             " "x23, v4.d[1]"),
        Q!("    ldp             " "x5, x21, [x0, #32]"),
        Q!("    adcs            " "x17, x4, x3"),
        Q!("    ldr             " "x4, [x0, #64]"),
        Q!("    mov             " "x3, v18.d[0]"),
        Q!("    adcs            " "x24, x1, x24"),
        Q!("    stp             " "x8, x17, [x0]"),
        Q!("    adcs            " "x17, x10, x16"),
        Q!("    ldp             " "x1, x16, [x0, #48]"),
        Q!("    adcs            " "x5, x5, x22"),
        Q!("    adcs            " "x8, x21, x11"),
        Q!("    stp             " "x5, x8, [x0, #32]"),
        Q!("    adcs            " "x1, x1, x15"),
        Q!("    mov             " "x15, v23.d[1]"),
        Q!("    adcs            " "x21, x16, x7"),
        Q!("    stp             " "x1, x21, [x0, #48]"),
        Q!("    adc             " "x10, x4, xzr"),
        Q!("    subs            " "x7, x14, x12"),
        Q!("    mov             " "x16, v18.d[1]"),
        Q!("    cneg            " "x5, x7, cc"),
        Q!("    csetm           " "x4, cc"),
        Q!("    subs            " "x11, x13, x6"),
        Q!("    mov             " "x8, v23.d[0]"),
        Q!("    cneg            " "x7, x11, cc"),
        Q!("    cinv            " "x21, x4, cc"),
        Q!("    mov             " "x11, v30.d[0]"),
        Q!("    adds            " "x4, x23, x3"),
        Q!("    mul             " "x22, x5, x7"),
        Q!("    mov             " "x23, v30.d[1]"),
        Q!("    adcs            " "x8, x8, x16"),
        Q!("    adcs            " "x16, x15, x11"),
        Q!("    adc             " "x11, x23, xzr"),
        Q!("    umulh           " "x3, x5, x7"),
        Q!("    stp             " "x24, x17, [x0, #16]"),
        Q!("    mov             " "x5, v4.d[0]"),
        Q!("    subs            " "x15, x20, x19"),
        Q!("    cneg            " "x7, x15, cc"),
        Q!("    str             " "x10, [x0, #64]"),
        Q!("    csetm           " "x1, cc"),
        Q!("    subs            " "x24, x2, x9"),
        Q!("    cneg            " "x17, x24, cc"),
        Q!("    cinv            " "x15, x1, cc"),
        Q!("    adds            " "x23, x4, x5"),
        Q!("    umulh           " "x1, x7, x17"),
        Q!("    adcs            " "x24, x8, x4"),
        Q!("    adcs            " "x10, x16, x8"),
        Q!("    eor             " "x8, x22, x21"),
        Q!("    adcs            " "x16, x11, x16"),
        Q!("    mul             " "x22, x7, x17"),
        Q!("    eor             " "x17, x1, x15"),
        Q!("    adc             " "x1, xzr, x11"),
        Q!("    adds            " "x11, x24, x5"),
        Q!("    eor             " "x7, x3, x21"),
        Q!("    adcs            " "x3, x10, x23"),
        Q!("    adcs            " "x24, x16, x24"),
        Q!("    adcs            " "x4, x1, x10"),
        Q!("    eor             " "x10, x22, x15"),
        Q!("    adcs            " "x16, xzr, x16"),
        Q!("    adc             " "x1, xzr, x1"),
        Q!("    cmn             " "x21, #0x1"),
        Q!("    adcs            " "x8, x4, x8"),
        Q!("    adcs            " "x22, x16, x7"),
        Q!("    adc             " "x7, x1, x21"),
        Q!("    subs            " "x21, x19, x12"),
        Q!("    csetm           " "x4, cc"),
        Q!("    cneg            " "x1, x21, cc"),
        Q!("    subs            " "x21, x13, x2"),
        Q!("    cinv            " "x16, x4, cc"),
        Q!("    cneg            " "x4, x21, cc"),
        Q!("    cmn             " "x15, #0x1"),
        Q!("    adcs            " "x21, x23, x10"),
        Q!("    mul             " "x23, x1, x4"),
        Q!("    adcs            " "x11, x11, x17"),
        Q!("    adcs            " "x3, x3, x15"),
        Q!("    umulh           " "x1, x1, x4"),
        Q!("    adcs            " "x24, x24, x15"),
        Q!("    adcs            " "x8, x8, x15"),
        Q!("    adcs            " "x22, x22, x15"),
        Q!("    eor             " "x17, x23, x16"),
        Q!("    adc             " "x15, x7, x15"),
        Q!("    subs            " "x7, x20, x14"),
        Q!("    cneg            " "x7, x7, cc"),
        Q!("    csetm           " "x4, cc"),
        Q!("    subs            " "x10, x20, x12"),
        Q!("    cneg            " "x23, x10, cc"),
        Q!("    csetm           " "x10, cc"),
        Q!("    subs            " "x12, x6, x9"),
        Q!("    cinv            " "x20, x4, cc"),
        Q!("    cneg            " "x12, x12, cc"),
        Q!("    cmn             " "x16, #0x1"),
        Q!("    eor             " "x1, x1, x16"),
        Q!("    adcs            " "x17, x24, x17"),
        Q!("    mul             " "x4, x7, x12"),
        Q!("    adcs            " "x8, x8, x1"),
        Q!("    umulh           " "x1, x7, x12"),
        Q!("    adcs            " "x24, x22, x16"),
        Q!("    adc             " "x7, x15, x16"),
        Q!("    subs            " "x12, x13, x9"),
        Q!("    cneg            " "x12, x12, cc"),
        Q!("    cinv            " "x13, x10, cc"),
        Q!("    subs            " "x19, x19, x14"),
        Q!("    mul             " "x9, x23, x12"),
        Q!("    cneg            " "x19, x19, cc"),
        Q!("    csetm           " "x10, cc"),
        Q!("    eor             " "x16, x1, x20"),
        Q!("    subs            " "x22, x6, x2"),
        Q!("    umulh           " "x12, x23, x12"),
        Q!("    eor             " "x1, x4, x20"),
        Q!("    cinv            " "x4, x10, cc"),
        Q!("    cneg            " "x22, x22, cc"),
        Q!("    cmn             " "x20, #0x1"),
        Q!("    adcs            " "x15, x11, x1"),
        Q!("    eor             " "x6, x12, x13"),
        Q!("    adcs            " "x10, x3, x16"),
        Q!("    adcs            " "x17, x17, x20"),
        Q!("    eor             " "x23, x9, x13"),
        Q!("    adcs            " "x2, x8, x20"),
        Q!("    mul             " "x11, x19, x22"),
        Q!("    adcs            " "x24, x24, x20"),
        Q!("    adc             " "x7, x7, x20"),
        Q!("    cmn             " "x13, #0x1"),
        Q!("    adcs            " "x3, x10, x23"),
        Q!("    umulh           " "x22, x19, x22"),
        Q!("    adcs            " "x17, x17, x6"),
        Q!("    eor             " "x12, x22, x4"),
        Q!("    extr            " "x22, x15, x21, #63"),
        Q!("    adcs            " "x8, x2, x13"),
        Q!("    extr            " "x21, x21, x5, #63"),
        Q!("    ldp             " "x16, x23, [x0]"),
        Q!("    adcs            " "x20, x24, x13"),
        Q!("    eor             " "x1, x11, x4"),
        Q!("    adc             " "x6, x7, x13"),
        Q!("    cmn             " "x4, #0x1"),
        Q!("    ldp             " "x2, x7, [x0, #16]"),
        Q!("    adcs            " "x1, x3, x1"),
        Q!("    extr            " "x19, x1, x15, #63"),
        Q!("    adcs            " "x14, x17, x12"),
        Q!("    extr            " "x1, x14, x1, #63"),
        Q!("    lsl             " "x17, x5, #1"),
        Q!("    adcs            " "x8, x8, x4"),
        Q!("    extr            " "x12, x8, x14, #8"),
        Q!("    ldp             " "x15, x11, [x0, #32]"),
        Q!("    adcs            " "x9, x20, x4"),
        Q!("    adc             " "x3, x6, x4"),
        Q!("    adds            " "x16, x12, x16"),
        Q!("    extr            " "x6, x9, x8, #8"),
        Q!("    ldp             " "x14, x12, [x0, #48]"),
        Q!("    extr            " "x8, x3, x9, #8"),
        Q!("    adcs            " "x20, x6, x23"),
        Q!("    ldr             " "x24, [x0, #64]"),
        Q!("    lsr             " "x6, x3, #8"),
        Q!("    adcs            " "x8, x8, x2"),
        Q!("    and             " "x2, x1, #0x1ff"),
        Q!("    and             " "x1, x20, x8"),
        Q!("    adcs            " "x4, x6, x7"),
        Q!("    adcs            " "x3, x17, x15"),
        Q!("    and             " "x1, x1, x4"),
        Q!("    adcs            " "x9, x21, x11"),
        Q!("    and             " "x1, x1, x3"),
        Q!("    adcs            " "x6, x22, x14"),
        Q!("    and             " "x1, x1, x9"),
        Q!("    and             " "x21, x1, x6"),
        Q!("    adcs            " "x14, x19, x12"),
        Q!("    adc             " "x1, x24, x2"),
        Q!("    cmp             " "xzr, xzr"),
        Q!("    orr             " "x12, x1, #0xfffffffffffffe00"),
        Q!("    lsr             " "x1, x1, #9"),
        Q!("    adcs            " "xzr, x16, x1"),
        Q!("    and             " "x21, x21, x14"),
        Q!("    adcs            " "xzr, x21, xzr"),
        Q!("    adcs            " "xzr, x12, xzr"),
        Q!("    adcs            " "x21, x16, x1"),
        Q!("    adcs            " "x1, x20, xzr"),
        Q!("    adcs            " "x19, x8, xzr"),
        Q!("    stp             " "x21, x1, [x0]"),
        Q!("    adcs            " "x1, x4, xzr"),
        Q!("    adcs            " "x21, x3, xzr"),
        Q!("    stp             " "x19, x1, [x0, #16]"),
        Q!("    adcs            " "x1, x9, xzr"),
        Q!("    stp             " "x21, x1, [x0, #32]"),
        Q!("    adcs            " "x21, x6, xzr"),
        Q!("    adcs            " "x1, x14, xzr"),
        Q!("    stp             " "x21, x1, [x0, #48]"),
        Q!("    adc             " "x1, x12, xzr"),
        Q!("    and             " "x1, x1, #0x1ff"),
        Q!("    str             " "x1, [x0, #64]"),

        // Restore regs and return

        Q!("    ldp             " "x23, x24, [sp], #16"),
        Q!("    ldp             " "x21, x22, [sp], #16"),
        Q!("    ldp             " "x19, x20, [sp], #16"),

        inout("x0") z.as_mut_ptr() => _,
        inout("x1") x.as_ptr() => _,
        // clobbers
        out("v0") _,
        out("v1") _,
        out("v16") _,
        out("v17") _,
        out("v18") _,
        out("v19") _,
        out("v2") _,
        out("v20") _,
        out("v21") _,
        out("v22") _,
        out("v23") _,
        out("v24") _,
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
        out("x10") _,
        out("x11") _,
        out("x12") _,
        out("x13") _,
        out("x14") _,
        out("x15") _,
        out("x16") _,
        out("x17") _,
        out("x2") _,
        out("x20") _,
        out("x21") _,
        out("x22") _,
        out("x23") _,
        out("x24") _,
        out("x3") _,
        out("x4") _,
        out("x5") _,
        out("x6") _,
        out("x7") _,
        out("x8") _,
        out("x9") _,
            )
    };
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn abi() {
    crate::low::abi::call!(
        bignum_sqr_p521,
        &mut crate::low::abi::Aligned([0; 9]).0,
        &crate::low::abi::Aligned([0; 9]).0
    );
}
