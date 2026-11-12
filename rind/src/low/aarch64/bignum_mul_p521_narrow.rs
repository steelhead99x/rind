// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
//
//    extern void bignum_mul_p521(uint64_t z[static 9], const uint64_t x[static 9],
//                                const uint64_t y[static 9]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------

// bignum_mul_p521 is functionally equivalent to unopt/bignum_mul_p521_base.
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
//        stp     x25, x26, [sp, #-16]!
//        sub     sp, sp, #80
//        ldp x15, x21, [x1]
//        ldp x10, x17, [x1, #16]
//        ldp x13, x16, [x2]
//        ldr q18, [x1]
//        ldr q28, [x2]
//        ldp x5, x20, [x2, #16]
//        movi v16.2D, #0x00000000ffffffff
//        uzp2 v7.4S, v28.4S, v28.4S
//        xtn v4.2S, v18.2D
//        xtn v1.2S, v28.2D
//        rev64 v27.4S, v28.4S
//        umull v21.2D, v4.2S, v1.2S
//        umull v28.2D, v4.2S, v7.2S
//        uzp2 v5.4S, v18.4S, v18.4S
//        mul v18.4S, v27.4S, v18.4S
//        usra v28.2D, v21.2D, #32
//        umull v29.2D, v5.2S, v7.2S
//        uaddlp v18.2D, v18.4S
//        and v16.16B, v28.16B, v16.16B
//        umlal v16.2D, v5.2S, v1.2S
//        shl v18.2D, v18.2D, #32
//        usra v29.2D, v28.2D, #32
//        umlal v18.2D, v4.2S, v1.2S
//        usra v29.2D, v16.2D, #32
//        mov x8, v18.d[0]
//        mov x9, v18.d[1]
//        mul x6, x10, x5
//        mul x19, x17, x20
//        mov x14, v29.d[0]
//        adds x9, x9, x14
//        mov x14, v29.d[1]
//        adcs x6, x6, x14
//        umulh x14, x10, x5
//        adcs x19, x19, x14
//        umulh x14, x17, x20
//        adc x14, x14, xzr
//        adds x11, x9, x8
//        adcs x9, x6, x9
//        adcs x6, x19, x6
//        adcs x19, x14, x19
//        adc x14, xzr, x14
//        adds x3, x9, x8
//        adcs x24, x6, x11
//        adcs x9, x19, x9
//        adcs x6, x14, x6
//        adcs x19, xzr, x19
//        adc x14, xzr, x14
//        subs x4, x10, x17
//        cneg x4, x4, cc
//        csetm x7, cc
//        subs x23, x20, x5
//        cneg x23, x23, cc
//        mul x22, x4, x23
//        umulh x4, x4, x23
//        cinv x7, x7, cc
//        cmn x7, #0x1
//        eor x23, x22, x7
//        adcs x6, x6, x23
//        eor x4, x4, x7
//        adcs x19, x19, x4
//        adc x14, x14, x7
//        subs x4, x15, x21
//        cneg x4, x4, cc
//        csetm x7, cc
//        subs x23, x16, x13
//        cneg x23, x23, cc
//        mul x22, x4, x23
//        umulh x4, x4, x23
//        cinv x7, x7, cc
//        cmn x7, #0x1
//        eor x23, x22, x7
//        adcs x11, x11, x23
//        eor x4, x4, x7
//        adcs x3, x3, x4
//        adcs x24, x24, x7
//        adcs x9, x9, x7
//        adcs x6, x6, x7
//        adcs x19, x19, x7
//        adc x14, x14, x7
//        subs x4, x21, x17
//        cneg x4, x4, cc
//        csetm x7, cc
//        subs x23, x20, x16
//        cneg x23, x23, cc
//        mul x22, x4, x23
//        umulh x4, x4, x23
//        cinv x7, x7, cc
//        cmn x7, #0x1
//        eor x23, x22, x7
//        adcs x9, x9, x23
//        eor x4, x4, x7
//        adcs x6, x6, x4
//        adcs x19, x19, x7
//        adc x14, x14, x7
//        subs x4, x15, x10
//        cneg x4, x4, cc
//        csetm x7, cc
//        subs x23, x5, x13
//        cneg x23, x23, cc
//        mul x22, x4, x23
//        umulh x4, x4, x23
//        cinv x7, x7, cc
//        cmn x7, #0x1
//        eor x23, x22, x7
//        adcs x3, x3, x23
//        eor x4, x4, x7
//        adcs x24, x24, x4
//        adcs x9, x9, x7
//        adcs x6, x6, x7
//        adcs x19, x19, x7
//        adc x14, x14, x7
//        subs x17, x15, x17
//        cneg x17, x17, cc
//        csetm x4, cc
//        subs x13, x20, x13
//        cneg x13, x13, cc
//        mul x20, x17, x13
//        umulh x17, x17, x13
//        cinv x13, x4, cc
//        cmn x13, #0x1
//        eor x20, x20, x13
//        adcs x20, x24, x20
//        eor x17, x17, x13
//        adcs x17, x9, x17
//        adcs x9, x6, x13
//        adcs x6, x19, x13
//        adc x13, x14, x13
//        subs x21, x21, x10
//        cneg x21, x21, cc
//        csetm x10, cc
//        subs x16, x5, x16
//        cneg x16, x16, cc
//        mul x5, x21, x16
//        umulh x21, x21, x16
//        cinv x10, x10, cc
//        cmn x10, #0x1
//        eor x16, x5, x10
//        adcs x16, x20, x16
//        eor x21, x21, x10
//        adcs x21, x17, x21
//        adcs x17, x9, x10
//        adcs x5, x6, x10
//        adc x10, x13, x10
//        lsl x13, x8, #9
//        extr x20, x11, x8, #55
//        extr x8, x3, x11, #55
//        extr x9, x16, x3, #55
//        lsr x16, x16, #55
//        stp x21, x17, [sp]                       // @slothy:writes=stack0
//        stp x5, x10, [sp, #16]                   // @slothy:writes=stack16
//        stp x13, x20, [sp, #32]                  // @slothy:writes=stack32
//        stp x8, x9, [sp, #48]                    // @slothy:writes=stack48
//        str x16, [sp, #64]                       // @slothy:writes=stack64
//        ldp x21, x10, [x1, #32]
//        ldp x17, x13, [x1, #48]
//        ldp x16, x5, [x2, #32]
//        ldr q18, [x1, #32]
//        ldr q28, [x2, #32]
//        ldp x20, x8, [x2, #48]
//        movi v16.2D, #0x00000000ffffffff
//        uzp2 v7.4S, v28.4S, v28.4S
//        xtn v4.2S, v18.2D
//        xtn v1.2S, v28.2D
//        rev64 v28.4S, v28.4S
//        umull v27.2D, v4.2S, v1.2S
//        umull v29.2D, v4.2S, v7.2S
//        uzp2 v21.4S, v18.4S, v18.4S
//        mul v28.4S, v28.4S, v18.4S
//        usra v29.2D, v27.2D, #32
//        umull v18.2D, v21.2S, v7.2S
//        uaddlp v28.2D, v28.4S
//        and v16.16B, v29.16B, v16.16B
//        umlal v16.2D, v21.2S, v1.2S
//        shl v28.2D, v28.2D, #32
//        usra v18.2D, v29.2D, #32
//        umlal v28.2D, v4.2S, v1.2S
//        usra v18.2D, v16.2D, #32
//        mov x9, v28.d[0]
//        mov x6, v28.d[1]
//        mul x19, x17, x20
//        mul x14, x13, x8
//        mov x11, v18.d[0]
//        adds x6, x6, x11
//        mov x11, v18.d[1]
//        adcs x19, x19, x11
//        umulh x11, x17, x20
//        adcs x14, x14, x11
//        umulh x11, x13, x8
//        adc x11, x11, xzr
//        adds x3, x6, x9
//        adcs x6, x19, x6
//        adcs x19, x14, x19
//        adcs x14, x11, x14
//        adc x11, xzr, x11
//        adds x24, x6, x9
//        adcs x4, x19, x3
//        adcs x6, x14, x6
//        adcs x19, x11, x19
//        adcs x14, xzr, x14
//        adc x11, xzr, x11
//        subs x7, x17, x13
//        cneg x7, x7, cc
//        csetm x23, cc
//        subs x22, x8, x20
//        cneg x22, x22, cc
//        mul x12, x7, x22
//        umulh x7, x7, x22
//        cinv x23, x23, cc
//        cmn x23, #0x1
//        eor x22, x12, x23
//        adcs x19, x19, x22
//        eor x7, x7, x23
//        adcs x14, x14, x7
//        adc x11, x11, x23
//        subs x7, x21, x10
//        cneg x7, x7, cc
//        csetm x23, cc
//        subs x22, x5, x16
//        cneg x22, x22, cc
//        mul x12, x7, x22
//        umulh x7, x7, x22
//        cinv x23, x23, cc
//        cmn x23, #0x1
//        eor x22, x12, x23
//        adcs x3, x3, x22
//        eor x7, x7, x23
//        adcs x24, x24, x7
//        adcs x4, x4, x23
//        adcs x6, x6, x23
//        adcs x19, x19, x23
//        adcs x14, x14, x23
//        adc x11, x11, x23
//        subs x7, x10, x13
//        cneg x7, x7, cc
//        csetm x23, cc
//        subs x22, x8, x5
//        cneg x22, x22, cc
//        mul x12, x7, x22
//        umulh x7, x7, x22
//        cinv x23, x23, cc
//        cmn x23, #0x1
//        eor x22, x12, x23
//        adcs x6, x6, x22
//        eor x7, x7, x23
//        adcs x19, x19, x7
//        adcs x14, x14, x23
//        adc x11, x11, x23
//        subs x7, x21, x17
//        cneg x7, x7, cc
//        csetm x23, cc
//        subs x22, x20, x16
//        cneg x22, x22, cc
//        mul x12, x7, x22
//        umulh x7, x7, x22
//        cinv x23, x23, cc
//        cmn x23, #0x1
//        eor x22, x12, x23
//        adcs x24, x24, x22
//        eor x7, x7, x23
//        adcs x4, x4, x7
//        adcs x6, x6, x23
//        adcs x19, x19, x23
//        adcs x14, x14, x23
//        adc x11, x11, x23
//        subs x7, x21, x13
//        cneg x7, x7, cc
//        csetm x23, cc
//        subs x22, x8, x16
//        cneg x22, x22, cc
//        mul x12, x7, x22
//        umulh x7, x7, x22
//        cinv x23, x23, cc
//        cmn x23, #0x1
//        eor x22, x12, x23
//        adcs x4, x4, x22
//        eor x7, x7, x23
//        adcs x6, x6, x7
//        adcs x19, x19, x23
//        adcs x14, x14, x23
//        adc x11, x11, x23
//        subs x7, x10, x17
//        cneg x7, x7, cc
//        csetm x23, cc
//        subs x22, x20, x5
//        cneg x22, x22, cc
//        mul x12, x7, x22
//        umulh x7, x7, x22
//        cinv x23, x23, cc
//        cmn x23, #0x1
//        eor x22, x12, x23
//        adcs x4, x4, x22
//        eor x7, x7, x23
//        adcs x6, x6, x7
//        adcs x19, x19, x23
//        adcs x14, x14, x23
//        adc x11, x11, x23
//        ldp x7, x23, [sp]                        // @slothy:reads=stack0
//        adds x9, x9, x7
//        adcs x3, x3, x23
//        stp x9, x3, [sp]                         // @slothy:writes=stack0
//        ldp x9, x3, [sp, #16]                    // @slothy:reads=stack16
//        adcs x9, x24, x9
//        adcs x3, x4, x3
//        stp x9, x3, [sp, #16]                    // @slothy:writes=stack16
//        ldp x9, x3, [sp, #32]                    // @slothy:reads=stack32
//        adcs x9, x6, x9
//        adcs x6, x19, x3
//        stp x9, x6, [sp, #32]                    // @slothy:writes=stack32
//        ldp x9, x6, [sp, #48]                    // @slothy:reads=stack48
//        adcs x9, x14, x9
//        adcs x6, x11, x6
//        stp x9, x6, [sp, #48]                    // @slothy:writes=stack48
//        ldr x9, [sp, #64]                        // @slothy:reads=stack64
//        adc x9, x9, xzr
//        str x9, [sp, #64]                        // @slothy:writes=stack64
//        ldp x9, x6, [x1]
//        subs x21, x21, x9
//        sbcs x10, x10, x6
//        ldp x9, x6, [x1, #16]
//        sbcs x17, x17, x9
//        sbcs x13, x13, x6
//        csetm x9, cc
//        ldp x6, x19, [x2]
//        subs x16, x6, x16
//        sbcs x5, x19, x5
//        ldp x6, x19, [x2, #16]
//        sbcs x20, x6, x20
//        sbcs x8, x19, x8
//        csetm x6, cc
//        eor x21, x21, x9
//        subs x21, x21, x9
//        eor x10, x10, x9
//        sbcs x10, x10, x9
//        eor x17, x17, x9
//        sbcs x17, x17, x9
//        eor x13, x13, x9
//        sbc x13, x13, x9
//        eor x16, x16, x6
//        subs x16, x16, x6
//        eor x5, x5, x6
//        sbcs x5, x5, x6
//        eor x20, x20, x6
//        sbcs x20, x20, x6
//        eor x8, x8, x6
//        sbc x8, x8, x6
//        eor x9, x6, x9
//        mul x6, x21, x16
//        mul x19, x10, x5
//        mul x14, x17, x20
//        mul x11, x13, x8
//        umulh x3, x21, x16
//        adds x19, x19, x3
//        umulh x3, x10, x5
//        adcs x14, x14, x3
//        umulh x3, x17, x20
//        adcs x11, x11, x3
//        umulh x3, x13, x8
//        adc x3, x3, xzr
//        adds x24, x19, x6
//        adcs x19, x14, x19
//        adcs x14, x11, x14
//        adcs x11, x3, x11
//        adc x3, xzr, x3
//        adds x4, x19, x6
//        adcs x7, x14, x24
//        adcs x19, x11, x19
//        adcs x14, x3, x14
//        adcs x11, xzr, x11
//        adc x3, xzr, x3
//        subs x23, x17, x13
//        cneg x23, x23, cc
//        csetm x22, cc
//        subs x12, x8, x20
//        cneg x12, x12, cc
//        mul x15, x23, x12
//        umulh x23, x23, x12
//        cinv x22, x22, cc
//        cmn x22, #0x1
//        eor x12, x15, x22
//        adcs x14, x14, x12
//        eor x23, x23, x22
//        adcs x11, x11, x23
//        adc x3, x3, x22
//        subs x23, x21, x10
//        cneg x23, x23, cc
//        csetm x22, cc
//        subs x12, x5, x16
//        cneg x12, x12, cc
//        mul x15, x23, x12
//        umulh x23, x23, x12
//        cinv x22, x22, cc
//        cmn x22, #0x1
//        eor x12, x15, x22
//        adcs x24, x24, x12
//        eor x23, x23, x22
//        adcs x4, x4, x23
//        adcs x7, x7, x22
//        adcs x19, x19, x22
//        adcs x14, x14, x22
//        adcs x11, x11, x22
//        adc x3, x3, x22
//        subs x23, x10, x13
//        cneg x23, x23, cc
//        csetm x22, cc
//        subs x12, x8, x5
//        cneg x12, x12, cc
//        mul x15, x23, x12
//        umulh x23, x23, x12
//        cinv x22, x22, cc
//        cmn x22, #0x1
//        eor x12, x15, x22
//        adcs x19, x19, x12
//        eor x23, x23, x22
//        adcs x14, x14, x23
//        adcs x11, x11, x22
//        adc x3, x3, x22
//        subs x23, x21, x17
//        cneg x23, x23, cc
//        csetm x22, cc
//        subs x12, x20, x16
//        cneg x12, x12, cc
//        mul x15, x23, x12
//        umulh x23, x23, x12
//        cinv x22, x22, cc
//        cmn x22, #0x1
//        eor x12, x15, x22
//        adcs x4, x4, x12
//        eor x23, x23, x22
//        adcs x7, x7, x23
//        adcs x19, x19, x22
//        adcs x14, x14, x22
//        adcs x11, x11, x22
//        adc x3, x3, x22
//        subs x21, x21, x13
//        cneg x21, x21, cc
//        csetm x13, cc
//        subs x16, x8, x16
//        cneg x16, x16, cc
//        mul x8, x21, x16
//        umulh x21, x21, x16
//        cinv x13, x13, cc
//        cmn x13, #0x1
//        eor x16, x8, x13
//        adcs x16, x7, x16
//        eor x21, x21, x13
//        adcs x21, x19, x21
//        adcs x8, x14, x13
//        adcs x19, x11, x13
//        adc x13, x3, x13
//        subs x10, x10, x17
//        cneg x10, x10, cc
//        csetm x17, cc
//        subs x5, x20, x5
//        cneg x5, x5, cc
//        mul x20, x10, x5
//        umulh x10, x10, x5
//        cinv x17, x17, cc
//        cmn x17, #0x1
//        eor x5, x20, x17
//        adcs x16, x16, x5
//        eor x10, x10, x17
//        adcs x21, x21, x10
//        adcs x10, x8, x17
//        adcs x5, x19, x17
//        adc x17, x13, x17
//        ldp x13, x20, [sp]                       // @slothy:reads=stack0
//        ldp x8, x19, [sp, #16]                   // @slothy:reads=stack16
//        eor x6, x6, x9
//        adds x6, x6, x13
//        eor x14, x24, x9
//        adcs x14, x14, x20
//        eor x11, x4, x9
//        adcs x11, x11, x8
//        eor x16, x16, x9
//        adcs x16, x16, x19
//        eor x21, x21, x9
//        ldp x3, x24, [sp, #32]                   // @slothy:reads=stack32
//        ldp x4, x7, [sp, #48]                    // @slothy:reads=stack48
//        ldr x23, [sp, #64]                       // @slothy:reads=stack64
//        adcs x21, x21, x3
//        eor x10, x10, x9
//        adcs x10, x10, x24
//        eor x5, x5, x9
//        adcs x5, x5, x4
//        eor x17, x17, x9
//        adcs x17, x17, x7
//        adc x22, x23, xzr
//        adds x21, x21, x13
//        adcs x10, x10, x20
//        adcs x13, x5, x8
//        adcs x17, x17, x19
//        and x5, x9, #0x1ff
//        lsl x20, x6, #9
//        orr x5, x20, x5
//        adcs x5, x3, x5
//        extr x20, x14, x6, #55
//        adcs x20, x24, x20
//        extr x8, x11, x14, #55
//        adcs x8, x4, x8
//        extr x9, x16, x11, #55
//        adcs x9, x7, x9
//        lsr x16, x16, #55
//        adc x16, x16, x23
//        ldr x6, [x2, #64]
//        ldp x19, x14, [x1]
//        and x11, x19, #0xfffffffffffff
//        mul x11, x6, x11
//        ldr x3, [x1, #64]
//        ldp x24, x4, [x2]
//        and x7, x24, #0xfffffffffffff
//        mul x7, x3, x7
//        add x11, x11, x7
//        extr x19, x14, x19, #52
//        and x19, x19, #0xfffffffffffff
//        mul x19, x6, x19
//        extr x24, x4, x24, #52
//        and x24, x24, #0xfffffffffffff
//        mul x24, x3, x24
//        add x19, x19, x24
//        lsr x24, x11, #52
//        add x19, x19, x24
//        lsl x11, x11, #12
//        extr x11, x19, x11, #12
//        adds x21, x21, x11
//        ldp x11, x24, [x1, #16]
//        ldp x7, x23, [x2, #16]
//        extr x14, x11, x14, #40
//        and x14, x14, #0xfffffffffffff
//        mul x14, x6, x14
//        extr x4, x7, x4, #40
//        and x4, x4, #0xfffffffffffff
//        mul x4, x3, x4
//        add x14, x14, x4
//        lsr x4, x19, #52
//        add x14, x14, x4
//        lsl x19, x19, #12
//        extr x19, x14, x19, #24
//        adcs x10, x10, x19
//        extr x19, x24, x11, #28
//        and x19, x19, #0xfffffffffffff
//        mul x19, x6, x19
//        extr x11, x23, x7, #28
//        and x11, x11, #0xfffffffffffff
//        mul x11, x3, x11
//        add x19, x19, x11
//        lsr x11, x14, #52
//        add x19, x19, x11
//        lsl x14, x14, #12
//        extr x14, x19, x14, #36
//        adcs x13, x13, x14
//        and x14, x10, x13
//        ldp x11, x4, [x1, #32]
//        ldp x7, x12, [x2, #32]
//        extr x24, x11, x24, #16
//        and x24, x24, #0xfffffffffffff
//        mul x24, x6, x24
//        extr x23, x7, x23, #16
//        and x23, x23, #0xfffffffffffff
//        mul x23, x3, x23
//        add x24, x24, x23
//        lsl x23, x22, #48
//        add x24, x24, x23
//        lsr x23, x19, #52
//        add x24, x24, x23
//        lsl x19, x19, #12
//        extr x19, x24, x19, #48
//        adcs x17, x17, x19
//        and x19, x14, x17
//        lsr x14, x11, #4
//        and x14, x14, #0xfffffffffffff
//        mul x14, x6, x14
//        lsr x23, x7, #4
//        and x23, x23, #0xfffffffffffff
//        mul x23, x3, x23
//        add x14, x14, x23
//        lsr x23, x24, #52
//        add x14, x14, x23
//        lsl x24, x24, #12
//        extr x24, x14, x24, #60
//        extr x11, x4, x11, #56
//        and x11, x11, #0xfffffffffffff
//        mul x11, x6, x11
//        extr x7, x12, x7, #56
//        and x7, x7, #0xfffffffffffff
//        mul x7, x3, x7
//        add x11, x11, x7
//        lsr x14, x14, #52
//        add x14, x11, x14
//        lsl x11, x24, #8
//        extr x11, x14, x11, #8
//        adcs x5, x5, x11
//        and x19, x19, x5
//        ldp x11, x24, [x1, #48]
//        ldp x2, x7, [x2, #48]
//        extr x4, x11, x4, #44
//        and x4, x4, #0xfffffffffffff
//        mul x4, x6, x4
//        extr x23, x2, x12, #44
//        and x23, x23, #0xfffffffffffff
//        mul x23, x3, x23
//        add x4, x4, x23
//        lsr x23, x14, #52
//        add x4, x4, x23
//        lsl x14, x14, #12
//        extr x14, x4, x14, #20
//        adcs x20, x20, x14
//        and x19, x19, x20
//        extr x14, x24, x11, #32
//        and x14, x14, #0xfffffffffffff
//        mul x14, x6, x14
//        extr x2, x7, x2, #32
//        and x2, x2, #0xfffffffffffff
//        mul x2, x3, x2
//        add x2, x14, x2
//        lsr x14, x4, #52
//        add x2, x2, x14
//        lsl x14, x4, #12
//        extr x14, x2, x14, #32
//        adcs x8, x8, x14
//        and x19, x19, x8
//        lsr x14, x24, #20
//        mul x14, x6, x14
//        lsr x11, x7, #20
//        mul x11, x3, x11
//        add x14, x14, x11
//        lsr x11, x2, #52
//        add x14, x14, x11
//        lsl x2, x2, #12
//        extr x2, x14, x2, #44
//        adcs x9, x9, x2
//        and x2, x19, x9
//        mul x6, x6, x3
//        lsr x19, x14, #44
//        add x6, x6, x19
//        adc x16, x16, x6
//        lsr x6, x16, #9
//        orr x16, x16, #0xfffffffffffffe00
//        cmp xzr, xzr
//        adcs xzr, x21, x6
//        adcs xzr, x2, xzr
//        adcs xzr, x16, xzr
//        adcs x21, x21, x6
//        adcs x10, x10, xzr
//        adcs x13, x13, xzr
//        adcs x17, x17, xzr
//        adcs x5, x5, xzr
//        adcs x20, x20, xzr
//        adcs x8, x8, xzr
//        adcs x9, x9, xzr
//        adc x16, x16, xzr
//        and x2, x21, #0x1ff
//        extr x21, x10, x21, #9
//        extr x10, x13, x10, #9
//        stp x21, x10, [x0]                       // @slothy:writes=buffer0
//        extr x21, x17, x13, #9
//        extr x10, x5, x17, #9
//        stp x21, x10, [x0, #16]                  // @slothy:writes=buffer16
//        extr x21, x20, x5, #9
//        extr x10, x8, x20, #9
//        stp x21, x10, [x0, #32]                  // @slothy:writes=buffer32
//        extr x21, x9, x8, #9
//        extr x10, x16, x9, #9
//        stp x21, x10, [x0, #48]                  // @slothy:writes=buffer48
//        str x2, [x0, #64]                        // @slothy:writes=buffer64
//        add     sp, sp, #80
//        ldp     x25, x26, [sp], #16
//        ldp     x23, x24, [sp], #16
//        ldp     x21, x22, [sp], #16
//        ldp     x19, x20, [sp], #16
//        ret
//
// The bash script used for step 2 is as follows:
//
//        # Store the assembly instructions except the last 'ret',
//        # callee-register store/loads and add/sub sp #80 as, say, 'input.S'.
//        export OUTPUTS="[hint_buffer0,hint_buffer16,hint_buffer32,hint_buffer48,hint_buffer64]"
//        export RESERVED_REGS="[x18,x27,x28,x29,x30,sp,q8,q9,q10,q11,q12,q13,q14,q15,v8,v9,v10,v11,v12,v13,v14,v15]"
//        <s2n-bignum>/tools/external/slothy.sh input.S my_out_dir
//        # my_out_dir/3.opt.s is the optimized assembly. Its output may differ
//        # from this file since the sequence is non-deterministically chosen.
//        # Please add 'ret' at the end of the output assembly.

// Transliterated from s2n-bignum's arm/p521/bignum_mul_p521.S.
/// Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced
///
/// Inputs x[9], y[9]; output z[9]
#[inline(never)]
pub(crate) fn bignum_mul_p521(z: &mut [u64; 9], x: &[u64; 9], y: &[u64; 9]) {
    // SAFETY: inline assembly. see [crate::low::inline_assembly_safety] for safety info.
    unsafe {
        core::arch::asm!(

        // Save registers and make space for the temporary buffer

        Q!("    stp             " "x19, x20, [sp, #-16] !"),
        Q!("    stp             " "x21, x22, [sp, #-16] !"),
        Q!("    stp             " "x23, x24, [sp, #-16] !"),
        Q!("    stp             " "x25, x26, [sp, #-16] !"),
        Q!("    sub             " "sp, sp, # (80 + 0)"),

        Q!("    ldr             " "q6, [x2]"),
        Q!("    ldp             " "x10, x17, [x1, #16]"),
        Q!("    ldr             " "q4, [x1]"),
        Q!("    ldr             " "q16, [x2, #32]"),
        Q!("    ldp             " "x5, x20, [x2, #16]"),
        Q!("    ldr             " "q2, [x1, #32]"),
        Q!("    movi            " "v31.2D, #0x00000000ffffffff"),
        Q!("    uzp2            " "v17.4S, v6.4S, v6.4S"),
        Q!("    rev64           " "v7.4S, v6.4S"),
        Q!("    ldp             " "x15, x21, [x1]"),
        Q!("    xtn             " "v25.2S, v6.2D"),
        Q!("    xtn             " "v22.2S, v4.2D"),
        Q!("    subs            " "x14, x10, x17"),
        Q!("    mul             " "v7.4S, v7.4S, v4.4S"),
        Q!("    csetm           " "x8, cc"),
        Q!("    rev64           " "v3.4S, v16.4S"),
        Q!("    xtn             " "v1.2S, v16.2D"),
        Q!("    ldp             " "x13, x16, [x2]"),
        Q!("    mul             " "x26, x10, x5"),
        Q!("    uzp2            " "v16.4S, v16.4S, v16.4S"),
        Q!("    uaddlp          " "v26.2D, v7.4S"),
        Q!("    cneg            " "x4, x14, cc"),
        Q!("    subs            " "x24, x15, x21"),
        Q!("    xtn             " "v5.2S, v2.2D"),
        Q!("    mul             " "v28.4S, v3.4S, v2.4S"),
        Q!("    shl             " "v26.2D, v26.2D, #32"),
        Q!("    mul             " "x22, x17, x20"),
        Q!("    umull           " "v20.2D, v22.2S, v25.2S"),
        Q!("    uzp2            " "v6.4S, v4.4S, v4.4S"),
        Q!("    umull           " "v18.2D, v22.2S, v17.2S"),
        Q!("    uzp2            " "v4.4S, v2.4S, v2.4S"),
        Q!("    cneg            " "x14, x24, cc"),
        Q!("    csetm           " "x7, cc"),
        Q!("    umulh           " "x11, x17, x20"),
        Q!("    usra            " "v18.2D, v20.2D, #32"),
        Q!("    uaddlp          " "v7.2D, v28.4S"),
        Q!("    subs            " "x19, x16, x13"),
        Q!("    umlal           " "v26.2D, v22.2S, v25.2S"),
        Q!("    cneg            " "x19, x19, cc"),
        Q!("    shl             " "v28.2D, v7.2D, #32"),
        Q!("    umull           " "v7.2D, v5.2S, v1.2S"),
        Q!("    umull           " "v30.2D, v5.2S, v16.2S"),
        Q!("    cinv            " "x6, x7, cc"),
        Q!("    mul             " "x25, x14, x19"),
        Q!("    umlal           " "v28.2D, v5.2S, v1.2S"),
        Q!("    umull           " "v21.2D, v6.2S, v17.2S"),
        Q!("    umulh           " "x14, x14, x19"),
        Q!("    usra            " "v30.2D, v7.2D, #32"),
        Q!("    subs            " "x9, x20, x5"),
        Q!("    and             " "v29.16B, v18.16B, v31.16B"),
        Q!("    cinv            " "x23, x8, cc"),
        Q!("    mov             " "x8, v26.d[1]"),
        Q!("    cneg            " "x12, x9, cc"),
        Q!("    usra            " "v21.2D, v18.2D, #32"),
        Q!("    umlal           " "v29.2D, v6.2S, v25.2S"),
        Q!("    mul             " "x24, x4, x12"),
        Q!("    umull           " "v18.2D, v4.2S, v16.2S"),
        Q!("    movi            " "v25.2D, #0x00000000ffffffff"),
        Q!("    eor             " "x9, x14, x6"),
        Q!("    and             " "v7.16B, v30.16B, v25.16B"),
        Q!("    usra            " "v21.2D, v29.2D, #32"),
        Q!("    umulh           " "x7, x10, x5"),
        Q!("    usra            " "v18.2D, v30.2D, #32"),
        Q!("    umlal           " "v7.2D, v4.2S, v1.2S"),
        Q!("    mov             " "x19, v21.d[0]"),
        Q!("    umulh           " "x3, x4, x12"),
        Q!("    mov             " "x14, v21.d[1]"),
        Q!("    usra            " "v18.2D, v7.2D, #32"),
        Q!("    adds            " "x4, x8, x19"),
        Q!("    mov             " "x8, v26.d[0]"),
        Q!("    adcs            " "x19, x26, x14"),
        Q!("    adcs            " "x14, x22, x7"),
        Q!("    adc             " "x12, x11, xzr"),
        Q!("    adds            " "x11, x4, x8"),
        Q!("    adcs            " "x26, x19, x4"),
        Q!("    adcs            " "x22, x14, x19"),
        Q!("    eor             " "x4, x24, x23"),
        Q!("    adcs            " "x14, x12, x14"),
        Q!("    eor             " "x7, x25, x6"),
        Q!("    adc             " "x25, xzr, x12"),
        Q!("    eor             " "x19, x3, x23"),
        Q!("    adds            " "x3, x26, x8"),
        Q!("    adcs            " "x24, x22, x11"),
        Q!("    adcs            " "x12, x14, x26"),
        Q!("    adcs            " "x22, x25, x22"),
        Q!("    adcs            " "x26, xzr, x14"),
        Q!("    adc             " "x14, xzr, x25"),
        Q!("    cmn             " "x23, #0x1"),
        Q!("    adcs            " "x22, x22, x4"),
        Q!("    adcs            " "x19, x26, x19"),
        Q!("    adc             " "x25, x14, x23"),
        Q!("    subs            " "x14, x21, x17"),
        Q!("    cneg            " "x23, x14, cc"),
        Q!("    csetm           " "x26, cc"),
        Q!("    subs            " "x4, x20, x16"),
        Q!("    cneg            " "x14, x4, cc"),
        Q!("    cinv            " "x4, x26, cc"),
        Q!("    cmn             " "x6, #0x1"),
        Q!("    adcs            " "x11, x11, x7"),
        Q!("    mul             " "x7, x23, x14"),
        Q!("    adcs            " "x9, x3, x9"),
        Q!("    adcs            " "x26, x24, x6"),
        Q!("    umulh           " "x3, x23, x14"),
        Q!("    adcs            " "x14, x12, x6"),
        Q!("    adcs            " "x22, x22, x6"),
        Q!("    adcs            " "x12, x19, x6"),
        Q!("    extr            " "x24, x11, x8, #55"),
        Q!("    adc             " "x6, x25, x6"),
        Q!("    subs            " "x19, x15, x17"),
        Q!("    csetm           " "x17, cc"),
        Q!("    cneg            " "x23, x19, cc"),
        Q!("    subs            " "x19, x20, x13"),
        Q!("    lsl             " "x25, x8, #9"),
        Q!("    eor             " "x8, x7, x4"),
        Q!("    cneg            " "x20, x19, cc"),
        Q!("    umulh           " "x7, x23, x20"),
        Q!("    cinv            " "x19, x17, cc"),
        Q!("    subs            " "x17, x15, x10"),
        Q!("    csetm           " "x15, cc"),
        Q!("    stp             " "x25, x24, [sp, #32]"),
        Q!("    cneg            " "x24, x17, cc"),
        Q!("    mul             " "x20, x23, x20"),
        Q!("    subs            " "x25, x5, x13"),
        Q!("    cneg            " "x13, x25, cc"),
        Q!("    cinv            " "x15, x15, cc"),
        Q!("    mul             " "x25, x24, x13"),
        Q!("    subs            " "x21, x21, x10"),
        Q!("    csetm           " "x23, cc"),
        Q!("    cneg            " "x17, x21, cc"),
        Q!("    subs            " "x21, x5, x16"),
        Q!("    umulh           " "x13, x24, x13"),
        Q!("    cinv            " "x10, x23, cc"),
        Q!("    cneg            " "x23, x21, cc"),
        Q!("    cmn             " "x4, #0x1"),
        Q!("    adcs            " "x14, x14, x8"),
        Q!("    eor             " "x21, x3, x4"),
        Q!("    adcs            " "x21, x22, x21"),
        Q!("    eor             " "x5, x20, x19"),
        Q!("    adcs            " "x24, x12, x4"),
        Q!("    mul             " "x12, x17, x23"),
        Q!("    eor             " "x8, x25, x15"),
        Q!("    adc             " "x25, x6, x4"),
        Q!("    cmn             " "x15, #0x1"),
        Q!("    adcs            " "x6, x9, x8"),
        Q!("    ldp             " "x20, x8, [x2, #48]"),
        Q!("    eor             " "x9, x13, x15"),
        Q!("    adcs            " "x4, x26, x9"),
        Q!("    umulh           " "x26, x17, x23"),
        Q!("    ldp             " "x17, x13, [x1, #48]"),
        Q!("    adcs            " "x9, x14, x15"),
        Q!("    adcs            " "x16, x21, x15"),
        Q!("    adcs            " "x14, x24, x15"),
        Q!("    eor             " "x21, x7, x19"),
        Q!("    mul             " "x23, x17, x20"),
        Q!("    adc             " "x24, x25, x15"),
        Q!("    cmn             " "x19, #0x1"),
        Q!("    adcs            " "x7, x4, x5"),
        Q!("    adcs            " "x9, x9, x21"),
        Q!("    umulh           " "x3, x13, x8"),
        Q!("    adcs            " "x16, x16, x19"),
        Q!("    adcs            " "x22, x14, x19"),
        Q!("    eor             " "x5, x12, x10"),
        Q!("    adc             " "x12, x24, x19"),
        Q!("    cmn             " "x10, #0x1"),
        Q!("    adcs            " "x19, x7, x5"),
        Q!("    eor             " "x14, x26, x10"),
        Q!("    mov             " "x7, v28.d[1]"),
        Q!("    adcs            " "x24, x9, x14"),
        Q!("    extr            " "x4, x19, x6, #55"),
        Q!("    umulh           " "x15, x17, x20"),
        Q!("    mov             " "x14, v18.d[1]"),
        Q!("    lsr             " "x9, x19, #55"),
        Q!("    adcs            " "x5, x16, x10"),
        Q!("    mov             " "x16, v18.d[0]"),
        Q!("    adcs            " "x19, x22, x10"),
        Q!("    str             " "x9, [sp, #64]"),
        Q!("    extr            " "x25, x6, x11, #55"),
        Q!("    adc             " "x21, x12, x10"),
        Q!("    subs            " "x26, x17, x13"),
        Q!("    stp             " "x25, x4, [sp, #48]"),
        Q!("    stp             " "x19, x21, [sp, #16]"),
        Q!("    csetm           " "x6, cc"),
        Q!("    cneg            " "x4, x26, cc"),
        Q!("    mul             " "x19, x13, x8"),
        Q!("    subs            " "x11, x8, x20"),
        Q!("    stp             " "x24, x5, [sp]"),
        Q!("    ldp             " "x21, x10, [x1, #32]"),
        Q!("    cinv            " "x12, x6, cc"),
        Q!("    cneg            " "x6, x11, cc"),
        Q!("    mov             " "x9, v28.d[0]"),
        Q!("    umulh           " "x25, x4, x6"),
        Q!("    adds            " "x22, x7, x16"),
        Q!("    ldp             " "x16, x5, [x2, #32]"),
        Q!("    adcs            " "x14, x23, x14"),
        Q!("    adcs            " "x11, x19, x15"),
        Q!("    adc             " "x24, x3, xzr"),
        Q!("    adds            " "x3, x22, x9"),
        Q!("    adcs            " "x15, x14, x22"),
        Q!("    mul             " "x22, x4, x6"),
        Q!("    adcs            " "x6, x11, x14"),
        Q!("    adcs            " "x4, x24, x11"),
        Q!("    eor             " "x14, x25, x12"),
        Q!("    adc             " "x26, xzr, x24"),
        Q!("    subs            " "x7, x21, x10"),
        Q!("    csetm           " "x23, cc"),
        Q!("    cneg            " "x19, x7, cc"),
        Q!("    subs            " "x24, x5, x16"),
        Q!("    cneg            " "x11, x24, cc"),
        Q!("    cinv            " "x7, x23, cc"),
        Q!("    adds            " "x25, x15, x9"),
        Q!("    eor             " "x23, x22, x12"),
        Q!("    adcs            " "x22, x6, x3"),
        Q!("    mul             " "x24, x19, x11"),
        Q!("    adcs            " "x15, x4, x15"),
        Q!("    adcs            " "x6, x26, x6"),
        Q!("    umulh           " "x19, x19, x11"),
        Q!("    adcs            " "x11, xzr, x4"),
        Q!("    adc             " "x26, xzr, x26"),
        Q!("    cmn             " "x12, #0x1"),
        Q!("    adcs            " "x4, x6, x23"),
        Q!("    eor             " "x6, x24, x7"),
        Q!("    adcs            " "x14, x11, x14"),
        Q!("    adc             " "x26, x26, x12"),
        Q!("    subs            " "x11, x10, x13"),
        Q!("    cneg            " "x12, x11, cc"),
        Q!("    csetm           " "x11, cc"),
        Q!("    eor             " "x19, x19, x7"),
        Q!("    subs            " "x24, x8, x5"),
        Q!("    cinv            " "x11, x11, cc"),
        Q!("    cneg            " "x24, x24, cc"),
        Q!("    cmn             " "x7, #0x1"),
        Q!("    adcs            " "x3, x3, x6"),
        Q!("    mul             " "x23, x12, x24"),
        Q!("    adcs            " "x25, x25, x19"),
        Q!("    adcs            " "x6, x22, x7"),
        Q!("    umulh           " "x19, x12, x24"),
        Q!("    adcs            " "x22, x15, x7"),
        Q!("    adcs            " "x12, x4, x7"),
        Q!("    eor             " "x24, x23, x11"),
        Q!("    adcs            " "x4, x14, x7"),
        Q!("    adc             " "x26, x26, x7"),
        Q!("    eor             " "x19, x19, x11"),
        Q!("    subs            " "x14, x21, x17"),
        Q!("    cneg            " "x7, x14, cc"),
        Q!("    csetm           " "x14, cc"),
        Q!("    subs            " "x23, x20, x16"),
        Q!("    cinv            " "x14, x14, cc"),
        Q!("    cneg            " "x23, x23, cc"),
        Q!("    cmn             " "x11, #0x1"),
        Q!("    adcs            " "x22, x22, x24"),
        Q!("    mul             " "x24, x7, x23"),
        Q!("    adcs            " "x15, x12, x19"),
        Q!("    adcs            " "x4, x4, x11"),
        Q!("    adc             " "x19, x26, x11"),
        Q!("    umulh           " "x26, x7, x23"),
        Q!("    subs            " "x7, x21, x13"),
        Q!("    eor             " "x11, x24, x14"),
        Q!("    cneg            " "x23, x7, cc"),
        Q!("    csetm           " "x12, cc"),
        Q!("    subs            " "x7, x8, x16"),
        Q!("    cneg            " "x7, x7, cc"),
        Q!("    cinv            " "x12, x12, cc"),
        Q!("    cmn             " "x14, #0x1"),
        Q!("    eor             " "x26, x26, x14"),
        Q!("    adcs            " "x11, x25, x11"),
        Q!("    mul             " "x25, x23, x7"),
        Q!("    adcs            " "x26, x6, x26"),
        Q!("    adcs            " "x6, x22, x14"),
        Q!("    adcs            " "x24, x15, x14"),
        Q!("    umulh           " "x23, x23, x7"),
        Q!("    adcs            " "x4, x4, x14"),
        Q!("    adc             " "x22, x19, x14"),
        Q!("    eor             " "x14, x25, x12"),
        Q!("    eor             " "x7, x23, x12"),
        Q!("    cmn             " "x12, #0x1"),
        Q!("    adcs            " "x14, x26, x14"),
        Q!("    ldp             " "x19, x25, [x2]"),
        Q!("    ldp             " "x15, x23, [x2, #16]"),
        Q!("    adcs            " "x26, x6, x7"),
        Q!("    adcs            " "x24, x24, x12"),
        Q!("    adcs            " "x7, x4, x12"),
        Q!("    adc             " "x4, x22, x12"),
        Q!("    subs            " "x19, x19, x16"),
        Q!("    ldp             " "x16, x22, [x1]"),
        Q!("    sbcs            " "x6, x25, x5"),
        Q!("    ldp             " "x12, x25, [x1, #16]"),
        Q!("    sbcs            " "x15, x15, x20"),
        Q!("    sbcs            " "x8, x23, x8"),
        Q!("    csetm           " "x23, cc"),
        Q!("    subs            " "x21, x21, x16"),
        Q!("    eor             " "x16, x19, x23"),
        Q!("    sbcs            " "x19, x10, x22"),
        Q!("    eor             " "x22, x6, x23"),
        Q!("    eor             " "x8, x8, x23"),
        Q!("    sbcs            " "x6, x17, x12"),
        Q!("    sbcs            " "x13, x13, x25"),
        Q!("    csetm           " "x12, cc"),
        Q!("    subs            " "x10, x10, x17"),
        Q!("    cneg            " "x17, x10, cc"),
        Q!("    csetm           " "x25, cc"),
        Q!("    subs            " "x5, x20, x5"),
        Q!("    eor             " "x10, x19, x12"),
        Q!("    cneg            " "x19, x5, cc"),
        Q!("    eor             " "x20, x15, x23"),
        Q!("    eor             " "x21, x21, x12"),
        Q!("    cinv            " "x15, x25, cc"),
        Q!("    mul             " "x25, x17, x19"),
        Q!("    subs            " "x16, x16, x23"),
        Q!("    sbcs            " "x5, x22, x23"),
        Q!("    eor             " "x6, x6, x12"),
        Q!("    sbcs            " "x20, x20, x23"),
        Q!("    eor             " "x22, x13, x12"),
        Q!("    sbc             " "x8, x8, x23"),
        Q!("    subs            " "x21, x21, x12"),
        Q!("    umulh           " "x19, x17, x19"),
        Q!("    sbcs            " "x10, x10, x12"),
        Q!("    sbcs            " "x17, x6, x12"),
        Q!("    eor             " "x6, x19, x15"),
        Q!("    eor             " "x19, x25, x15"),
        Q!("    umulh           " "x25, x17, x20"),
        Q!("    sbc             " "x13, x22, x12"),
        Q!("    cmn             " "x15, #0x1"),
        Q!("    adcs            " "x22, x14, x19"),
        Q!("    adcs            " "x19, x26, x6"),
        Q!("    ldp             " "x6, x26, [sp]"),
        Q!("    adcs            " "x14, x24, x15"),
        Q!("    umulh           " "x24, x21, x16"),
        Q!("    adcs            " "x7, x7, x15"),
        Q!("    adc             " "x15, x4, x15"),
        Q!("    adds            " "x4, x9, x6"),
        Q!("    eor             " "x9, x23, x12"),
        Q!("    adcs            " "x12, x3, x26"),
        Q!("    stp             " "x4, x12, [sp]"),
        Q!("    ldp             " "x4, x26, [sp, #16]"),
        Q!("    umulh           " "x12, x10, x5"),
        Q!("    ldp             " "x6, x23, [sp, #32]"),
        Q!("    adcs            " "x3, x11, x4"),
        Q!("    mul             " "x4, x13, x8"),
        Q!("    adcs            " "x26, x22, x26"),
        Q!("    ldp             " "x22, x11, [sp, #48]"),
        Q!("    adcs            " "x6, x19, x6"),
        Q!("    stp             " "x3, x26, [sp, #16]"),
        Q!("    mul             " "x26, x10, x5"),
        Q!("    adcs            " "x14, x14, x23"),
        Q!("    stp             " "x6, x14, [sp, #32]"),
        Q!("    ldr             " "x6, [sp, #64]"),
        Q!("    adcs            " "x22, x7, x22"),
        Q!("    adcs            " "x14, x15, x11"),
        Q!("    mul             " "x11, x17, x20"),
        Q!("    adc             " "x19, x6, xzr"),
        Q!("    stp             " "x22, x14, [sp, #48]"),
        Q!("    adds            " "x14, x26, x24"),
        Q!("    str             " "x19, [sp, #64]"),
        Q!("    umulh           " "x19, x13, x8"),
        Q!("    adcs            " "x7, x11, x12"),
        Q!("    adcs            " "x22, x4, x25"),
        Q!("    mul             " "x6, x21, x16"),
        Q!("    adc             " "x19, x19, xzr"),
        Q!("    subs            " "x11, x17, x13"),
        Q!("    cneg            " "x12, x11, cc"),
        Q!("    csetm           " "x11, cc"),
        Q!("    subs            " "x24, x8, x20"),
        Q!("    cinv            " "x11, x11, cc"),
        Q!("    cneg            " "x24, x24, cc"),
        Q!("    adds            " "x4, x14, x6"),
        Q!("    adcs            " "x14, x7, x14"),
        Q!("    mul             " "x3, x12, x24"),
        Q!("    adcs            " "x7, x22, x7"),
        Q!("    adcs            " "x22, x19, x22"),
        Q!("    umulh           " "x12, x12, x24"),
        Q!("    adc             " "x24, xzr, x19"),
        Q!("    adds            " "x19, x14, x6"),
        Q!("    eor             " "x3, x3, x11"),
        Q!("    adcs            " "x26, x7, x4"),
        Q!("    adcs            " "x14, x22, x14"),
        Q!("    adcs            " "x25, x24, x7"),
        Q!("    adcs            " "x23, xzr, x22"),
        Q!("    eor             " "x7, x12, x11"),
        Q!("    adc             " "x12, xzr, x24"),
        Q!("    subs            " "x22, x21, x10"),
        Q!("    cneg            " "x24, x22, cc"),
        Q!("    csetm           " "x22, cc"),
        Q!("    subs            " "x15, x5, x16"),
        Q!("    cinv            " "x22, x22, cc"),
        Q!("    cneg            " "x15, x15, cc"),
        Q!("    cmn             " "x11, #0x1"),
        Q!("    adcs            " "x3, x25, x3"),
        Q!("    mul             " "x25, x24, x15"),
        Q!("    adcs            " "x23, x23, x7"),
        Q!("    adc             " "x11, x12, x11"),
        Q!("    subs            " "x7, x10, x13"),
        Q!("    umulh           " "x15, x24, x15"),
        Q!("    cneg            " "x12, x7, cc"),
        Q!("    csetm           " "x7, cc"),
        Q!("    eor             " "x24, x25, x22"),
        Q!("    eor             " "x25, x15, x22"),
        Q!("    cmn             " "x22, #0x1"),
        Q!("    adcs            " "x24, x4, x24"),
        Q!("    adcs            " "x19, x19, x25"),
        Q!("    adcs            " "x15, x26, x22"),
        Q!("    adcs            " "x4, x14, x22"),
        Q!("    adcs            " "x26, x3, x22"),
        Q!("    adcs            " "x25, x23, x22"),
        Q!("    adc             " "x23, x11, x22"),
        Q!("    subs            " "x14, x21, x17"),
        Q!("    cneg            " "x3, x14, cc"),
        Q!("    csetm           " "x11, cc"),
        Q!("    subs            " "x14, x8, x5"),
        Q!("    cneg            " "x14, x14, cc"),
        Q!("    cinv            " "x7, x7, cc"),
        Q!("    subs            " "x13, x21, x13"),
        Q!("    cneg            " "x21, x13, cc"),
        Q!("    csetm           " "x13, cc"),
        Q!("    mul             " "x22, x12, x14"),
        Q!("    subs            " "x8, x8, x16"),
        Q!("    cinv            " "x13, x13, cc"),
        Q!("    umulh           " "x14, x12, x14"),
        Q!("    cneg            " "x12, x8, cc"),
        Q!("    subs            " "x8, x20, x16"),
        Q!("    cneg            " "x8, x8, cc"),
        Q!("    cinv            " "x16, x11, cc"),
        Q!("    eor             " "x22, x22, x7"),
        Q!("    cmn             " "x7, #0x1"),
        Q!("    eor             " "x14, x14, x7"),
        Q!("    adcs            " "x4, x4, x22"),
        Q!("    mul             " "x11, x3, x8"),
        Q!("    adcs            " "x22, x26, x14"),
        Q!("    adcs            " "x14, x25, x7"),
        Q!("    eor             " "x25, x24, x9"),
        Q!("    adc             " "x26, x23, x7"),
        Q!("    umulh           " "x7, x3, x8"),
        Q!("    subs            " "x17, x10, x17"),
        Q!("    cneg            " "x24, x17, cc"),
        Q!("    eor             " "x3, x11, x16"),
        Q!("    csetm           " "x11, cc"),
        Q!("    subs            " "x20, x20, x5"),
        Q!("    cneg            " "x5, x20, cc"),
        Q!("    cinv            " "x11, x11, cc"),
        Q!("    cmn             " "x16, #0x1"),
        Q!("    mul             " "x17, x21, x12"),
        Q!("    eor             " "x8, x7, x16"),
        Q!("    adcs            " "x10, x19, x3"),
        Q!("    and             " "x19, x9, #0x1ff"),
        Q!("    adcs            " "x20, x15, x8"),
        Q!("    umulh           " "x15, x21, x12"),
        Q!("    eor             " "x12, x10, x9"),
        Q!("    eor             " "x8, x6, x9"),
        Q!("    adcs            " "x6, x4, x16"),
        Q!("    adcs            " "x4, x22, x16"),
        Q!("    adcs            " "x21, x14, x16"),
        Q!("    adc             " "x7, x26, x16"),
        Q!("    mul             " "x10, x24, x5"),
        Q!("    cmn             " "x13, #0x1"),
        Q!("    ldp             " "x3, x14, [x1]"),
        Q!("    eor             " "x17, x17, x13"),
        Q!("    umulh           " "x5, x24, x5"),
        Q!("    adcs            " "x20, x20, x17"),
        Q!("    eor             " "x17, x15, x13"),
        Q!("    adcs            " "x16, x6, x17"),
        Q!("    eor             " "x22, x10, x11"),
        Q!("    adcs            " "x23, x4, x13"),
        Q!("    extr            " "x10, x14, x3, #52"),
        Q!("    and             " "x26, x3, #0xfffffffffffff"),
        Q!("    adcs            " "x24, x21, x13"),
        Q!("    and             " "x15, x10, #0xfffffffffffff"),
        Q!("    adc             " "x6, x7, x13"),
        Q!("    cmn             " "x11, #0x1"),
        Q!("    adcs            " "x17, x20, x22"),
        Q!("    eor             " "x4, x5, x11"),
        Q!("    ldp             " "x21, x10, [sp]"),
        Q!("    adcs            " "x7, x16, x4"),
        Q!("    eor             " "x16, x17, x9"),
        Q!("    eor             " "x13, x7, x9"),
        Q!("    ldp             " "x3, x17, [sp, #16]"),
        Q!("    adcs            " "x7, x23, x11"),
        Q!("    eor             " "x23, x7, x9"),
        Q!("    ldp             " "x5, x22, [sp, #32]"),
        Q!("    adcs            " "x7, x24, x11"),
        Q!("    adc             " "x24, x6, x11"),
        Q!("    ldr             " "x6, [x2, #64]"),
        Q!("    adds            " "x20, x8, x21"),
        Q!("    lsl             " "x11, x20, #9"),
        Q!("    eor             " "x4, x7, x9"),
        Q!("    orr             " "x7, x11, x19"),
        Q!("    eor             " "x8, x24, x9"),
        Q!("    adcs            " "x11, x25, x10"),
        Q!("    mul             " "x26, x6, x26"),
        Q!("    ldp             " "x19, x24, [sp, #48]"),
        Q!("    adcs            " "x12, x12, x3"),
        Q!("    adcs            " "x16, x16, x17"),
        Q!("    adcs            " "x9, x13, x5"),
        Q!("    ldr             " "x25, [sp, #64]"),
        Q!("    extr            " "x20, x11, x20, #55"),
        Q!("    adcs            " "x13, x23, x22"),
        Q!("    adcs            " "x4, x4, x19"),
        Q!("    extr            " "x23, x12, x11, #55"),
        Q!("    adcs            " "x8, x8, x24"),
        Q!("    adc             " "x11, x25, xzr"),
        Q!("    adds            " "x21, x9, x21"),
        Q!("    extr            " "x9, x16, x12, #55"),
        Q!("    lsr             " "x12, x16, #55"),
        Q!("    adcs            " "x10, x13, x10"),
        Q!("    mul             " "x15, x6, x15"),
        Q!("    adcs            " "x13, x4, x3"),
        Q!("    ldp             " "x16, x4, [x2]"),
        Q!("    ldr             " "x3, [x1, #64]"),
        Q!("    adcs            " "x17, x8, x17"),
        Q!("    adcs            " "x5, x5, x7"),
        Q!("    adcs            " "x20, x22, x20"),
        Q!("    adcs            " "x8, x19, x23"),
        Q!("    and             " "x22, x16, #0xfffffffffffff"),
        Q!("    ldp             " "x19, x7, [x1, #16]"),
        Q!("    adcs            " "x9, x24, x9"),
        Q!("    extr            " "x24, x4, x16, #52"),
        Q!("    adc             " "x16, x12, x25"),
        Q!("    mul             " "x22, x3, x22"),
        Q!("    and             " "x25, x24, #0xfffffffffffff"),
        Q!("    extr            " "x14, x19, x14, #40"),
        Q!("    and             " "x12, x14, #0xfffffffffffff"),
        Q!("    extr            " "x23, x7, x19, #28"),
        Q!("    ldp             " "x19, x24, [x2, #16]"),
        Q!("    mul             " "x14, x3, x25"),
        Q!("    and             " "x23, x23, #0xfffffffffffff"),
        Q!("    add             " "x22, x26, x22"),
        Q!("    lsl             " "x11, x11, #48"),
        Q!("    lsr             " "x26, x22, #52"),
        Q!("    lsl             " "x25, x22, #12"),
        Q!("    mul             " "x22, x6, x12"),
        Q!("    extr            " "x12, x19, x4, #40"),
        Q!("    add             " "x4, x15, x14"),
        Q!("    mul             " "x15, x6, x23"),
        Q!("    add             " "x4, x4, x26"),
        Q!("    extr            " "x23, x24, x19, #28"),
        Q!("    ldp             " "x14, x19, [x1, #32]"),
        Q!("    and             " "x26, x12, #0xfffffffffffff"),
        Q!("    extr            " "x12, x4, x25, #12"),
        Q!("    and             " "x25, x23, #0xfffffffffffff"),
        Q!("    adds            " "x21, x21, x12"),
        Q!("    mul             " "x12, x3, x26"),
        Q!("    extr            " "x23, x14, x7, #16"),
        Q!("    and             " "x23, x23, #0xfffffffffffff"),
        Q!("    mul             " "x7, x3, x25"),
        Q!("    ldp             " "x25, x26, [x2, #32]"),
        Q!("    add             " "x12, x22, x12"),
        Q!("    extr            " "x22, x19, x14, #56"),
        Q!("    mul             " "x23, x6, x23"),
        Q!("    lsr             " "x14, x14, #4"),
        Q!("    extr            " "x24, x25, x24, #16"),
        Q!("    add             " "x7, x15, x7"),
        Q!("    and             " "x15, x24, #0xfffffffffffff"),
        Q!("    and             " "x22, x22, #0xfffffffffffff"),
        Q!("    lsr             " "x24, x4, #52"),
        Q!("    mul             " "x15, x3, x15"),
        Q!("    and             " "x14, x14, #0xfffffffffffff"),
        Q!("    add             " "x12, x12, x24"),
        Q!("    lsl             " "x24, x4, #12"),
        Q!("    lsr             " "x4, x12, #52"),
        Q!("    extr            " "x24, x12, x24, #24"),
        Q!("    adcs            " "x10, x10, x24"),
        Q!("    lsl             " "x24, x12, #12"),
        Q!("    add             " "x12, x7, x4"),
        Q!("    mul             " "x22, x6, x22"),
        Q!("    add             " "x4, x23, x15"),
        Q!("    extr            " "x7, x12, x24, #36"),
        Q!("    adcs            " "x13, x13, x7"),
        Q!("    lsl             " "x15, x12, #12"),
        Q!("    add             " "x7, x4, x11"),
        Q!("    lsr             " "x24, x12, #52"),
        Q!("    ldp             " "x23, x11, [x2, #48]"),
        Q!("    add             " "x4, x7, x24"),
        Q!("    mul             " "x12, x6, x14"),
        Q!("    extr            " "x7, x26, x25, #56"),
        Q!("    extr            " "x14, x4, x15, #48"),
        Q!("    and             " "x2, x7, #0xfffffffffffff"),
        Q!("    extr            " "x24, x11, x23, #32"),
        Q!("    ldp             " "x15, x7, [x1, #48]"),
        Q!("    and             " "x1, x24, #0xfffffffffffff"),
        Q!("    lsr             " "x24, x4, #52"),
        Q!("    mul             " "x2, x3, x2"),
        Q!("    extr            " "x26, x23, x26, #44"),
        Q!("    lsr             " "x23, x25, #4"),
        Q!("    and             " "x23, x23, #0xfffffffffffff"),
        Q!("    and             " "x25, x26, #0xfffffffffffff"),
        Q!("    extr            " "x26, x7, x15, #32"),
        Q!("    extr            " "x19, x15, x19, #44"),
        Q!("    mul             " "x23, x3, x23"),
        Q!("    and             " "x15, x26, #0xfffffffffffff"),
        Q!("    lsl             " "x26, x4, #12"),
        Q!("    and             " "x4, x19, #0xfffffffffffff"),
        Q!("    lsr             " "x11, x11, #20"),
        Q!("    mul             " "x19, x6, x4"),
        Q!("    adcs            " "x17, x17, x14"),
        Q!("    add             " "x14, x22, x2"),
        Q!("    add             " "x22, x12, x23"),
        Q!("    lsr             " "x7, x7, #20"),
        Q!("    add             " "x22, x22, x24"),
        Q!("    extr            " "x2, x22, x26, #60"),
        Q!("    mul             " "x24, x3, x25"),
        Q!("    lsr             " "x22, x22, #52"),
        Q!("    add             " "x14, x14, x22"),
        Q!("    lsl             " "x22, x2, #8"),
        Q!("    extr            " "x22, x14, x22, #8"),
        Q!("    lsl             " "x2, x14, #12"),
        Q!("    mul             " "x1, x3, x1"),
        Q!("    adcs            " "x12, x5, x22"),
        Q!("    mul             " "x5, x6, x15"),
        Q!("    and             " "x26, x10, x13"),
        Q!("    and             " "x4, x26, x17"),
        Q!("    add             " "x23, x19, x24"),
        Q!("    lsr             " "x14, x14, #52"),
        Q!("    mul             " "x22, x3, x11"),
        Q!("    add             " "x11, x23, x14"),
        Q!("    extr            " "x25, x11, x2, #20"),
        Q!("    lsl             " "x19, x11, #12"),
        Q!("    adcs            " "x25, x20, x25"),
        Q!("    and             " "x14, x4, x12"),
        Q!("    add             " "x1, x5, x1"),
        Q!("    and             " "x14, x14, x25"),
        Q!("    mul             " "x15, x6, x7"),
        Q!("    add             " "x26, x15, x22"),
        Q!("    mul             " "x6, x6, x3"),
        Q!("    lsr             " "x22, x11, #52"),
        Q!("    add             " "x4, x1, x22"),
        Q!("    lsr             " "x1, x4, #52"),
        Q!("    extr            " "x3, x4, x19, #32"),
        Q!("    lsl             " "x15, x4, #12"),
        Q!("    add             " "x7, x26, x1"),
        Q!("    adcs            " "x23, x8, x3"),
        Q!("    extr            " "x20, x7, x15, #44"),
        Q!("    and             " "x3, x14, x23"),
        Q!("    lsr             " "x19, x7, #44"),
        Q!("    adcs            " "x7, x9, x20"),
        Q!("    add             " "x11, x6, x19"),
        Q!("    adc             " "x4, x16, x11"),
        Q!("    lsr             " "x14, x4, #9"),
        Q!("    cmp             " "xzr, xzr"),
        Q!("    and             " "x15, x3, x7"),
        Q!("    orr             " "x3, x4, #0xfffffffffffffe00"),
        Q!("    adcs            " "xzr, x21, x14"),
        Q!("    adcs            " "xzr, x15, xzr"),
        Q!("    adcs            " "xzr, x3, xzr"),
        Q!("    adcs            " "x11, x21, x14"),
        Q!("    and             " "x14, x11, #0x1ff"),
        Q!("    adcs            " "x1, x10, xzr"),
        Q!("    extr            " "x10, x1, x11, #9"),
        Q!("    str             " "x14, [x0, #64]"),
        Q!("    adcs            " "x14, x13, xzr"),
        Q!("    extr            " "x11, x14, x1, #9"),
        Q!("    adcs            " "x1, x17, xzr"),
        Q!("    extr            " "x4, x1, x14, #9"),
        Q!("    stp             " "x10, x11, [x0]"),
        Q!("    adcs            " "x11, x12, xzr"),
        Q!("    extr            " "x14, x11, x1, #9"),
        Q!("    adcs            " "x10, x25, xzr"),
        Q!("    extr            " "x11, x10, x11, #9"),
        Q!("    stp             " "x4, x14, [x0, #16]"),
        Q!("    adcs            " "x14, x23, xzr"),
        Q!("    extr            " "x10, x14, x10, #9"),
        Q!("    adcs            " "x1, x7, xzr"),
        Q!("    stp             " "x11, x10, [x0, #32]"),
        Q!("    extr            " "x14, x1, x14, #9"),
        Q!("    adc             " "x10, x3, xzr"),
        Q!("    extr            " "x26, x10, x1, #9"),
        Q!("    stp             " "x14, x26, [x0, #48]"),

        // Restore regs and return

        Q!("    add             " "sp, sp, # (80 + 0)"),
        Q!("    ldp             " "x25, x26, [sp], #16"),
        Q!("    ldp             " "x23, x24, [sp], #16"),
        Q!("    ldp             " "x21, x22, [sp], #16"),
        Q!("    ldp             " "x19, x20, [sp], #16"),
        inout("x0") z.as_mut_ptr() => _,
        inout("x1") x.as_ptr() => _,
        inout("x2") y.as_ptr() => _,
        // clobbers
        out("v1") _,
        out("v16") _,
        out("v17") _,
        out("v18") _,
        out("v2") _,
        out("v20") _,
        out("v21") _,
        out("v22") _,
        out("v25") _,
        out("v26") _,
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
        out("x20") _,
        out("x21") _,
        out("x22") _,
        out("x23") _,
        out("x24") _,
        out("x25") _,
        out("x26") _,
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
        bignum_mul_p521,
        &mut crate::low::abi::Aligned([0; 9]).0,
        &crate::low::abi::Aligned([0; 9]).0,
        &crate::low::abi::Aligned([0; 9]).0
    );
}
