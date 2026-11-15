// generated source. do not edit.
#![allow(non_upper_case_globals, unused_macros, unused_imports)]
use crate::low::macros::*;

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jadd_alt(uint64_t p3[static 27], const uint64_t p1[static 27],
//                              const uint64_t p2[static 27]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input points p1 and p2 are
// fully reduced mod p_521, that both z coordinates are nonzero and
// that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents
// the same affine point as".
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
// ----------------------------------------------------------------------------

// Size of individual field elements

macro_rules! NUMSIZE {
    () => {
        "72"
    };
}

// Stable homes for input arguments during main code sequence

macro_rules! input_z {
    () => {
        "x26"
    };
}
macro_rules! input_x {
    () => {
        "x27"
    };
}
macro_rules! input_y {
    () => {
        "x28"
    };
}

// Pointer-offset pairs for inputs and outputs

macro_rules! x_1 { () => { Q!(input_x!() ", #0") } }
macro_rules! y_1 { () => { Q!(input_x!() ", # " NUMSIZE!()) } }
macro_rules! z_1 { () => { Q!(input_x!() ", # (2 * " NUMSIZE!() ")") } }

macro_rules! x_2 { () => { Q!(input_y!() ", #0") } }
macro_rules! y_2 { () => { Q!(input_y!() ", # " NUMSIZE!()) } }
macro_rules! z_2 { () => { Q!(input_y!() ", # (2 * " NUMSIZE!() ")") } }

macro_rules! x_3 { () => { Q!(input_z!() ", #0") } }
macro_rules! y_3 { () => { Q!(input_z!() ", # " NUMSIZE!()) } }
macro_rules! z_3 { () => { Q!(input_z!() ", # (2 * " NUMSIZE!() ")") } }

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

macro_rules! z1sq { () => { Q!("sp, # (" NUMSIZE!() "* 0)") } }
macro_rules! ww { () => { Q!("sp, # (" NUMSIZE!() "* 0)") } }
macro_rules! resx { () => { Q!("sp, # (" NUMSIZE!() "* 0)") } }

macro_rules! yd { () => { Q!("sp, # (" NUMSIZE!() "* 1)") } }
macro_rules! y2a { () => { Q!("sp, # (" NUMSIZE!() "* 1)") } }

macro_rules! x2a { () => { Q!("sp, # (" NUMSIZE!() "* 2)") } }
macro_rules! zzx2 { () => { Q!("sp, # (" NUMSIZE!() "* 2)") } }

macro_rules! zz { () => { Q!("sp, # (" NUMSIZE!() "* 3)") } }
macro_rules! t1 { () => { Q!("sp, # (" NUMSIZE!() "* 3)") } }

macro_rules! t2 { () => { Q!("sp, # (" NUMSIZE!() "* 4)") } }
macro_rules! x1a { () => { Q!("sp, # (" NUMSIZE!() "* 4)") } }
macro_rules! zzx1 { () => { Q!("sp, # (" NUMSIZE!() "* 4)") } }
macro_rules! resy { () => { Q!("sp, # (" NUMSIZE!() "* 4)") } }

macro_rules! xd { () => { Q!("sp, # (" NUMSIZE!() "* 5)") } }
macro_rules! z2sq { () => { Q!("sp, # (" NUMSIZE!() "* 5)") } }
macro_rules! resz { () => { Q!("sp, # (" NUMSIZE!() "* 5)") } }

macro_rules! y1a { () => { Q!("sp, # (" NUMSIZE!() "* 6)") } }

// NUMSIZE*7 is not 16-aligned so we round it up

macro_rules! NSPACE {
    () => {
        "512"
    };
}

// Corresponds exactly to bignum_mul_p521_alt

macro_rules! mul_p521 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "ldp x3, x4, [" $P1 "];\n"
        "ldp x5, x6, [" $P2 "];\n"
        "mul x15, x3, x5;\n"
        "umulh x16, x3, x5;\n"
        "mul x14, x3, x6;\n"
        "umulh x17, x3, x6;\n"
        "adds x16, x16, x14;\n"
        "ldp x7, x8, [" $P2 "+ 16];\n"
        "mul x14, x3, x7;\n"
        "umulh x19, x3, x7;\n"
        "adcs x17, x17, x14;\n"
        "mul x14, x3, x8;\n"
        "umulh x20, x3, x8;\n"
        "adcs x19, x19, x14;\n"
        "ldp x9, x10, [" $P2 "+ 32];\n"
        "mul x14, x3, x9;\n"
        "umulh x21, x3, x9;\n"
        "adcs x20, x20, x14;\n"
        "mul x14, x3, x10;\n"
        "umulh x22, x3, x10;\n"
        "adcs x21, x21, x14;\n"
        "ldp x11, x12, [" $P2 "+ 48];\n"
        "mul x14, x3, x11;\n"
        "umulh x23, x3, x11;\n"
        "adcs x22, x22, x14;\n"
        "ldr x13, [" $P2 "+ 64];\n"
        "mul x14, x3, x12;\n"
        "umulh x24, x3, x12;\n"
        "adcs x23, x23, x14;\n"
        "mul x14, x3, x13;\n"
        "umulh x1, x3, x13;\n"
        "adcs x24, x24, x14;\n"
        "adc x1, x1, xzr;\n"
        "mul x14, x4, x5;\n"
        "adds x16, x16, x14;\n"
        "mul x14, x4, x6;\n"
        "adcs x17, x17, x14;\n"
        "mul x14, x4, x7;\n"
        "adcs x19, x19, x14;\n"
        "mul x14, x4, x8;\n"
        "adcs x20, x20, x14;\n"
        "mul x14, x4, x9;\n"
        "adcs x21, x21, x14;\n"
        "mul x14, x4, x10;\n"
        "adcs x22, x22, x14;\n"
        "mul x14, x4, x11;\n"
        "adcs x23, x23, x14;\n"
        "mul x14, x4, x12;\n"
        "adcs x24, x24, x14;\n"
        "mul x14, x4, x13;\n"
        "adcs x1, x1, x14;\n"
        "cset x0, hs;\n"
        "umulh x14, x4, x5;\n"
        "adds x17, x17, x14;\n"
        "umulh x14, x4, x6;\n"
        "adcs x19, x19, x14;\n"
        "umulh x14, x4, x7;\n"
        "adcs x20, x20, x14;\n"
        "umulh x14, x4, x8;\n"
        "adcs x21, x21, x14;\n"
        "umulh x14, x4, x9;\n"
        "adcs x22, x22, x14;\n"
        "umulh x14, x4, x10;\n"
        "adcs x23, x23, x14;\n"
        "umulh x14, x4, x11;\n"
        "adcs x24, x24, x14;\n"
        "umulh x14, x4, x12;\n"
        "adcs x1, x1, x14;\n"
        "umulh x14, x4, x13;\n"
        "adc x0, x0, x14;\n"
        "stp x15, x16, [" $P0 "];\n"
        "ldp x3, x4, [" $P1 "+ 16];\n"
        "mul x14, x3, x5;\n"
        "adds x17, x17, x14;\n"
        "mul x14, x3, x6;\n"
        "adcs x19, x19, x14;\n"
        "mul x14, x3, x7;\n"
        "adcs x20, x20, x14;\n"
        "mul x14, x3, x8;\n"
        "adcs x21, x21, x14;\n"
        "mul x14, x3, x9;\n"
        "adcs x22, x22, x14;\n"
        "mul x14, x3, x10;\n"
        "adcs x23, x23, x14;\n"
        "mul x14, x3, x11;\n"
        "adcs x24, x24, x14;\n"
        "mul x14, x3, x12;\n"
        "adcs x1, x1, x14;\n"
        "mul x14, x3, x13;\n"
        "adcs x0, x0, x14;\n"
        "cset x15, hs;\n"
        "umulh x14, x3, x5;\n"
        "adds x19, x19, x14;\n"
        "umulh x14, x3, x6;\n"
        "adcs x20, x20, x14;\n"
        "umulh x14, x3, x7;\n"
        "adcs x21, x21, x14;\n"
        "umulh x14, x3, x8;\n"
        "adcs x22, x22, x14;\n"
        "umulh x14, x3, x9;\n"
        "adcs x23, x23, x14;\n"
        "umulh x14, x3, x10;\n"
        "adcs x24, x24, x14;\n"
        "umulh x14, x3, x11;\n"
        "adcs x1, x1, x14;\n"
        "umulh x14, x3, x12;\n"
        "adcs x0, x0, x14;\n"
        "umulh x14, x3, x13;\n"
        "adc x15, x15, x14;\n"
        "mul x14, x4, x5;\n"
        "adds x19, x19, x14;\n"
        "mul x14, x4, x6;\n"
        "adcs x20, x20, x14;\n"
        "mul x14, x4, x7;\n"
        "adcs x21, x21, x14;\n"
        "mul x14, x4, x8;\n"
        "adcs x22, x22, x14;\n"
        "mul x14, x4, x9;\n"
        "adcs x23, x23, x14;\n"
        "mul x14, x4, x10;\n"
        "adcs x24, x24, x14;\n"
        "mul x14, x4, x11;\n"
        "adcs x1, x1, x14;\n"
        "mul x14, x4, x12;\n"
        "adcs x0, x0, x14;\n"
        "mul x14, x4, x13;\n"
        "adcs x15, x15, x14;\n"
        "cset x16, hs;\n"
        "umulh x14, x4, x5;\n"
        "adds x20, x20, x14;\n"
        "umulh x14, x4, x6;\n"
        "adcs x21, x21, x14;\n"
        "umulh x14, x4, x7;\n"
        "adcs x22, x22, x14;\n"
        "umulh x14, x4, x8;\n"
        "adcs x23, x23, x14;\n"
        "umulh x14, x4, x9;\n"
        "adcs x24, x24, x14;\n"
        "umulh x14, x4, x10;\n"
        "adcs x1, x1, x14;\n"
        "umulh x14, x4, x11;\n"
        "adcs x0, x0, x14;\n"
        "umulh x14, x4, x12;\n"
        "adcs x15, x15, x14;\n"
        "umulh x14, x4, x13;\n"
        "adc x16, x16, x14;\n"
        "stp x17, x19, [" $P0 "+ 16];\n"
        "ldp x3, x4, [" $P1 "+ 32];\n"
        "mul x14, x3, x5;\n"
        "adds x20, x20, x14;\n"
        "mul x14, x3, x6;\n"
        "adcs x21, x21, x14;\n"
        "mul x14, x3, x7;\n"
        "adcs x22, x22, x14;\n"
        "mul x14, x3, x8;\n"
        "adcs x23, x23, x14;\n"
        "mul x14, x3, x9;\n"
        "adcs x24, x24, x14;\n"
        "mul x14, x3, x10;\n"
        "adcs x1, x1, x14;\n"
        "mul x14, x3, x11;\n"
        "adcs x0, x0, x14;\n"
        "mul x14, x3, x12;\n"
        "adcs x15, x15, x14;\n"
        "mul x14, x3, x13;\n"
        "adcs x16, x16, x14;\n"
        "cset x17, hs;\n"
        "umulh x14, x3, x5;\n"
        "adds x21, x21, x14;\n"
        "umulh x14, x3, x6;\n"
        "adcs x22, x22, x14;\n"
        "umulh x14, x3, x7;\n"
        "adcs x23, x23, x14;\n"
        "umulh x14, x3, x8;\n"
        "adcs x24, x24, x14;\n"
        "umulh x14, x3, x9;\n"
        "adcs x1, x1, x14;\n"
        "umulh x14, x3, x10;\n"
        "adcs x0, x0, x14;\n"
        "umulh x14, x3, x11;\n"
        "adcs x15, x15, x14;\n"
        "umulh x14, x3, x12;\n"
        "adcs x16, x16, x14;\n"
        "umulh x14, x3, x13;\n"
        "adc x17, x17, x14;\n"
        "mul x14, x4, x5;\n"
        "adds x21, x21, x14;\n"
        "mul x14, x4, x6;\n"
        "adcs x22, x22, x14;\n"
        "mul x14, x4, x7;\n"
        "adcs x23, x23, x14;\n"
        "mul x14, x4, x8;\n"
        "adcs x24, x24, x14;\n"
        "mul x14, x4, x9;\n"
        "adcs x1, x1, x14;\n"
        "mul x14, x4, x10;\n"
        "adcs x0, x0, x14;\n"
        "mul x14, x4, x11;\n"
        "adcs x15, x15, x14;\n"
        "mul x14, x4, x12;\n"
        "adcs x16, x16, x14;\n"
        "mul x14, x4, x13;\n"
        "adcs x17, x17, x14;\n"
        "cset x19, hs;\n"
        "umulh x14, x4, x5;\n"
        "adds x22, x22, x14;\n"
        "umulh x14, x4, x6;\n"
        "adcs x23, x23, x14;\n"
        "umulh x14, x4, x7;\n"
        "adcs x24, x24, x14;\n"
        "umulh x14, x4, x8;\n"
        "adcs x1, x1, x14;\n"
        "umulh x14, x4, x9;\n"
        "adcs x0, x0, x14;\n"
        "umulh x14, x4, x10;\n"
        "adcs x15, x15, x14;\n"
        "umulh x14, x4, x11;\n"
        "adcs x16, x16, x14;\n"
        "umulh x14, x4, x12;\n"
        "adcs x17, x17, x14;\n"
        "umulh x14, x4, x13;\n"
        "adc x19, x19, x14;\n"
        "stp x20, x21, [" $P0 "+ 32];\n"
        "ldp x3, x4, [" $P1 "+ 48];\n"
        "mul x14, x3, x5;\n"
        "adds x22, x22, x14;\n"
        "mul x14, x3, x6;\n"
        "adcs x23, x23, x14;\n"
        "mul x14, x3, x7;\n"
        "adcs x24, x24, x14;\n"
        "mul x14, x3, x8;\n"
        "adcs x1, x1, x14;\n"
        "mul x14, x3, x9;\n"
        "adcs x0, x0, x14;\n"
        "mul x14, x3, x10;\n"
        "adcs x15, x15, x14;\n"
        "mul x14, x3, x11;\n"
        "adcs x16, x16, x14;\n"
        "mul x14, x3, x12;\n"
        "adcs x17, x17, x14;\n"
        "mul x14, x3, x13;\n"
        "adcs x19, x19, x14;\n"
        "cset x20, hs;\n"
        "umulh x14, x3, x5;\n"
        "adds x23, x23, x14;\n"
        "umulh x14, x3, x6;\n"
        "adcs x24, x24, x14;\n"
        "umulh x14, x3, x7;\n"
        "adcs x1, x1, x14;\n"
        "umulh x14, x3, x8;\n"
        "adcs x0, x0, x14;\n"
        "umulh x14, x3, x9;\n"
        "adcs x15, x15, x14;\n"
        "umulh x14, x3, x10;\n"
        "adcs x16, x16, x14;\n"
        "umulh x14, x3, x11;\n"
        "adcs x17, x17, x14;\n"
        "umulh x14, x3, x12;\n"
        "adcs x19, x19, x14;\n"
        "umulh x14, x3, x13;\n"
        "adc x20, x20, x14;\n"
        "mul x14, x4, x5;\n"
        "adds x23, x23, x14;\n"
        "mul x14, x4, x6;\n"
        "adcs x24, x24, x14;\n"
        "mul x14, x4, x7;\n"
        "adcs x1, x1, x14;\n"
        "mul x14, x4, x8;\n"
        "adcs x0, x0, x14;\n"
        "mul x14, x4, x9;\n"
        "adcs x15, x15, x14;\n"
        "mul x14, x4, x10;\n"
        "adcs x16, x16, x14;\n"
        "mul x14, x4, x11;\n"
        "adcs x17, x17, x14;\n"
        "mul x14, x4, x12;\n"
        "adcs x19, x19, x14;\n"
        "mul x14, x4, x13;\n"
        "adcs x20, x20, x14;\n"
        "cset x21, hs;\n"
        "umulh x14, x4, x5;\n"
        "adds x24, x24, x14;\n"
        "umulh x14, x4, x6;\n"
        "adcs x1, x1, x14;\n"
        "umulh x14, x4, x7;\n"
        "adcs x0, x0, x14;\n"
        "umulh x14, x4, x8;\n"
        "adcs x15, x15, x14;\n"
        "umulh x14, x4, x9;\n"
        "adcs x16, x16, x14;\n"
        "umulh x14, x4, x10;\n"
        "adcs x17, x17, x14;\n"
        "umulh x14, x4, x11;\n"
        "adcs x19, x19, x14;\n"
        "umulh x14, x4, x12;\n"
        "adcs x20, x20, x14;\n"
        "umulh x14, x4, x13;\n"
        "adc x21, x21, x14;\n"
        "stp x22, x23, [" $P0 "+ 48];\n"
        "ldr x3, [" $P1 "+ 64];\n"
        "mul x14, x3, x5;\n"
        "adds x24, x24, x14;\n"
        "mul x14, x3, x6;\n"
        "adcs x1, x1, x14;\n"
        "mul x14, x3, x7;\n"
        "adcs x0, x0, x14;\n"
        "mul x14, x3, x8;\n"
        "adcs x15, x15, x14;\n"
        "mul x14, x3, x9;\n"
        "adcs x16, x16, x14;\n"
        "mul x14, x3, x10;\n"
        "adcs x17, x17, x14;\n"
        "mul x14, x3, x11;\n"
        "adcs x19, x19, x14;\n"
        "mul x14, x3, x12;\n"
        "adcs x20, x20, x14;\n"
        "mul x14, x3, x13;\n"
        "adc x21, x21, x14;\n"
        "umulh x14, x3, x5;\n"
        "adds x1, x1, x14;\n"
        "umulh x14, x3, x6;\n"
        "adcs x0, x0, x14;\n"
        "umulh x14, x3, x7;\n"
        "adcs x15, x15, x14;\n"
        "umulh x14, x3, x8;\n"
        "adcs x16, x16, x14;\n"
        "umulh x14, x3, x9;\n"
        "adcs x17, x17, x14;\n"
        "umulh x14, x3, x10;\n"
        "adcs x19, x19, x14;\n"
        "umulh x14, x3, x11;\n"
        "adcs x20, x20, x14;\n"
        "umulh x14, x3, x12;\n"
        "adc x21, x21, x14;\n"
        "cmp xzr, xzr;\n"
        "ldp x5, x6, [" $P0 "];\n"
        "extr x14, x1, x24, #9;\n"
        "adcs x5, x5, x14;\n"
        "extr x14, x0, x1, #9;\n"
        "adcs x6, x6, x14;\n"
        "ldp x7, x8, [" $P0 "+ 16];\n"
        "extr x14, x15, x0, #9;\n"
        "adcs x7, x7, x14;\n"
        "extr x14, x16, x15, #9;\n"
        "adcs x8, x8, x14;\n"
        "ldp x9, x10, [" $P0 "+ 32];\n"
        "extr x14, x17, x16, #9;\n"
        "adcs x9, x9, x14;\n"
        "extr x14, x19, x17, #9;\n"
        "adcs x10, x10, x14;\n"
        "ldp x11, x12, [" $P0 "+ 48];\n"
        "extr x14, x20, x19, #9;\n"
        "adcs x11, x11, x14;\n"
        "extr x14, x21, x20, #9;\n"
        "adcs x12, x12, x14;\n"
        "orr x13, x24, #0xfffffffffffffe00;\n"
        "lsr x14, x21, #9;\n"
        "adcs x13, x13, x14;\n"
        "sbcs x5, x5, xzr;\n"
        "sbcs x6, x6, xzr;\n"
        "sbcs x7, x7, xzr;\n"
        "sbcs x8, x8, xzr;\n"
        "sbcs x9, x9, xzr;\n"
        "sbcs x10, x10, xzr;\n"
        "sbcs x11, x11, xzr;\n"
        "sbcs x12, x12, xzr;\n"
        "sbc x13, x13, xzr;\n"
        "and x13, x13, #0x1ff;\n"
        "stp x5, x6, [" $P0 "];\n"
        "stp x7, x8, [" $P0 "+ 16];\n"
        "stp x9, x10, [" $P0 "+ 32];\n"
        "stp x11, x12, [" $P0 "+ 48];\n"
        "str x13, [" $P0 "+ 64]"
    )}
}

// Corresponds exactly to bignum_sqr_p521_alt

macro_rules! sqr_p521 {
    ($P0:expr, $P1:expr) => { Q!(
        "ldp x2, x3, [" $P1 "];\n"
        "mul x11, x2, x3;\n"
        "umulh x12, x2, x3;\n"
        "ldp x4, x5, [" $P1 "+ 16];\n"
        "mul x10, x2, x4;\n"
        "umulh x13, x2, x4;\n"
        "adds x12, x12, x10;\n"
        "ldp x6, x7, [" $P1 "+ 32];\n"
        "mul x10, x2, x5;\n"
        "umulh x14, x2, x5;\n"
        "adcs x13, x13, x10;\n"
        "ldp x8, x9, [" $P1 "+ 48];\n"
        "mul x10, x2, x6;\n"
        "umulh x15, x2, x6;\n"
        "adcs x14, x14, x10;\n"
        "mul x10, x2, x7;\n"
        "umulh x16, x2, x7;\n"
        "adcs x15, x15, x10;\n"
        "mul x10, x2, x8;\n"
        "umulh x17, x2, x8;\n"
        "adcs x16, x16, x10;\n"
        "mul x10, x2, x9;\n"
        "umulh x19, x2, x9;\n"
        "adcs x17, x17, x10;\n"
        "adc x19, x19, xzr;\n"
        "mul x10, x3, x4;\n"
        "adds x13, x13, x10;\n"
        "mul x10, x3, x5;\n"
        "adcs x14, x14, x10;\n"
        "mul x10, x3, x6;\n"
        "adcs x15, x15, x10;\n"
        "mul x10, x3, x7;\n"
        "adcs x16, x16, x10;\n"
        "mul x10, x3, x8;\n"
        "adcs x17, x17, x10;\n"
        "mul x10, x3, x9;\n"
        "adcs x19, x19, x10;\n"
        "cset x20, hs;\n"
        "umulh x10, x3, x4;\n"
        "adds x14, x14, x10;\n"
        "umulh x10, x3, x5;\n"
        "adcs x15, x15, x10;\n"
        "umulh x10, x3, x6;\n"
        "adcs x16, x16, x10;\n"
        "umulh x10, x3, x7;\n"
        "adcs x17, x17, x10;\n"
        "umulh x10, x3, x8;\n"
        "adcs x19, x19, x10;\n"
        "umulh x10, x3, x9;\n"
        "adc x20, x20, x10;\n"
        "mul x10, x6, x7;\n"
        "umulh x21, x6, x7;\n"
        "adds x20, x20, x10;\n"
        "adc x21, x21, xzr;\n"
        "mul x10, x4, x5;\n"
        "adds x15, x15, x10;\n"
        "mul x10, x4, x6;\n"
        "adcs x16, x16, x10;\n"
        "mul x10, x4, x7;\n"
        "adcs x17, x17, x10;\n"
        "mul x10, x4, x8;\n"
        "adcs x19, x19, x10;\n"
        "mul x10, x4, x9;\n"
        "adcs x20, x20, x10;\n"
        "mul x10, x6, x8;\n"
        "adcs x21, x21, x10;\n"
        "cset x22, hs;\n"
        "umulh x10, x4, x5;\n"
        "adds x16, x16, x10;\n"
        "umulh x10, x4, x6;\n"
        "adcs x17, x17, x10;\n"
        "umulh x10, x4, x7;\n"
        "adcs x19, x19, x10;\n"
        "umulh x10, x4, x8;\n"
        "adcs x20, x20, x10;\n"
        "umulh x10, x4, x9;\n"
        "adcs x21, x21, x10;\n"
        "umulh x10, x6, x8;\n"
        "adc x22, x22, x10;\n"
        "mul x10, x7, x8;\n"
        "umulh x23, x7, x8;\n"
        "adds x22, x22, x10;\n"
        "adc x23, x23, xzr;\n"
        "mul x10, x5, x6;\n"
        "adds x17, x17, x10;\n"
        "mul x10, x5, x7;\n"
        "adcs x19, x19, x10;\n"
        "mul x10, x5, x8;\n"
        "adcs x20, x20, x10;\n"
        "mul x10, x5, x9;\n"
        "adcs x21, x21, x10;\n"
        "mul x10, x6, x9;\n"
        "adcs x22, x22, x10;\n"
        "mul x10, x7, x9;\n"
        "adcs x23, x23, x10;\n"
        "cset x24, hs;\n"
        "umulh x10, x5, x6;\n"
        "adds x19, x19, x10;\n"
        "umulh x10, x5, x7;\n"
        "adcs x20, x20, x10;\n"
        "umulh x10, x5, x8;\n"
        "adcs x21, x21, x10;\n"
        "umulh x10, x5, x9;\n"
        "adcs x22, x22, x10;\n"
        "umulh x10, x6, x9;\n"
        "adcs x23, x23, x10;\n"
        "umulh x10, x7, x9;\n"
        "adc x24, x24, x10;\n"
        "mul x10, x8, x9;\n"
        "umulh x25, x8, x9;\n"
        "adds x24, x24, x10;\n"
        "adc x25, x25, xzr;\n"
        "adds x11, x11, x11;\n"
        "adcs x12, x12, x12;\n"
        "adcs x13, x13, x13;\n"
        "adcs x14, x14, x14;\n"
        "adcs x15, x15, x15;\n"
        "adcs x16, x16, x16;\n"
        "adcs x17, x17, x17;\n"
        "adcs x19, x19, x19;\n"
        "adcs x20, x20, x20;\n"
        "adcs x21, x21, x21;\n"
        "adcs x22, x22, x22;\n"
        "adcs x23, x23, x23;\n"
        "adcs x24, x24, x24;\n"
        "adcs x25, x25, x25;\n"
        "cset x0, hs;\n"
        "umulh x10, x2, x2;\n"
        "adds x11, x11, x10;\n"
        "mul x10, x3, x3;\n"
        "adcs x12, x12, x10;\n"
        "umulh x10, x3, x3;\n"
        "adcs x13, x13, x10;\n"
        "mul x10, x4, x4;\n"
        "adcs x14, x14, x10;\n"
        "umulh x10, x4, x4;\n"
        "adcs x15, x15, x10;\n"
        "mul x10, x5, x5;\n"
        "adcs x16, x16, x10;\n"
        "umulh x10, x5, x5;\n"
        "adcs x17, x17, x10;\n"
        "mul x10, x6, x6;\n"
        "adcs x19, x19, x10;\n"
        "umulh x10, x6, x6;\n"
        "adcs x20, x20, x10;\n"
        "mul x10, x7, x7;\n"
        "adcs x21, x21, x10;\n"
        "umulh x10, x7, x7;\n"
        "adcs x22, x22, x10;\n"
        "mul x10, x8, x8;\n"
        "adcs x23, x23, x10;\n"
        "umulh x10, x8, x8;\n"
        "adcs x24, x24, x10;\n"
        "mul x10, x9, x9;\n"
        "adcs x25, x25, x10;\n"
        "umulh x10, x9, x9;\n"
        "adc x0, x0, x10;\n"
        "ldr x1, [" $P1 "+ 64];\n"
        "add x1, x1, x1;\n"
        "mul x10, x1, x2;\n"
        "adds x19, x19, x10;\n"
        "umulh x10, x1, x2;\n"
        "adcs x20, x20, x10;\n"
        "mul x10, x1, x4;\n"
        "adcs x21, x21, x10;\n"
        "umulh x10, x1, x4;\n"
        "adcs x22, x22, x10;\n"
        "mul x10, x1, x6;\n"
        "adcs x23, x23, x10;\n"
        "umulh x10, x1, x6;\n"
        "adcs x24, x24, x10;\n"
        "mul x10, x1, x8;\n"
        "adcs x25, x25, x10;\n"
        "umulh x10, x1, x8;\n"
        "adcs x0, x0, x10;\n"
        "lsr x4, x1, #1;\n"
        "mul x4, x4, x4;\n"
        "adc x4, x4, xzr;\n"
        "mul x10, x1, x3;\n"
        "adds x20, x20, x10;\n"
        "umulh x10, x1, x3;\n"
        "adcs x21, x21, x10;\n"
        "mul x10, x1, x5;\n"
        "adcs x22, x22, x10;\n"
        "umulh x10, x1, x5;\n"
        "adcs x23, x23, x10;\n"
        "mul x10, x1, x7;\n"
        "adcs x24, x24, x10;\n"
        "umulh x10, x1, x7;\n"
        "adcs x25, x25, x10;\n"
        "mul x10, x1, x9;\n"
        "adcs x0, x0, x10;\n"
        "umulh x10, x1, x9;\n"
        "adc x4, x4, x10;\n"
        "mul x2, x2, x2;\n"
        "cmp xzr, xzr;\n"
        "extr x10, x20, x19, #9;\n"
        "adcs x2, x2, x10;\n"
        "extr x10, x21, x20, #9;\n"
        "adcs x11, x11, x10;\n"
        "extr x10, x22, x21, #9;\n"
        "adcs x12, x12, x10;\n"
        "extr x10, x23, x22, #9;\n"
        "adcs x13, x13, x10;\n"
        "extr x10, x24, x23, #9;\n"
        "adcs x14, x14, x10;\n"
        "extr x10, x25, x24, #9;\n"
        "adcs x15, x15, x10;\n"
        "extr x10, x0, x25, #9;\n"
        "adcs x16, x16, x10;\n"
        "extr x10, x4, x0, #9;\n"
        "adcs x17, x17, x10;\n"
        "orr x19, x19, #0xfffffffffffffe00;\n"
        "lsr x10, x4, #9;\n"
        "adcs x19, x19, x10;\n"
        "sbcs x2, x2, xzr;\n"
        "sbcs x11, x11, xzr;\n"
        "sbcs x12, x12, xzr;\n"
        "sbcs x13, x13, xzr;\n"
        "sbcs x14, x14, xzr;\n"
        "sbcs x15, x15, xzr;\n"
        "sbcs x16, x16, xzr;\n"
        "sbcs x17, x17, xzr;\n"
        "sbc x19, x19, xzr;\n"
        "and x19, x19, #0x1ff;\n"
        "stp x2, x11, [" $P0 "];\n"
        "stp x12, x13, [" $P0 "+ 16];\n"
        "stp x14, x15, [" $P0 "+ 32];\n"
        "stp x16, x17, [" $P0 "+ 48];\n"
        "str x19, [" $P0 "+ 64]"
    )}
}

// Corresponds exactly to bignum_sub_p521

macro_rules! sub_p521 {
    ($P0:expr, $P1:expr, $P2:expr) => { Q!(
        "ldp x5, x6, [" $P1 "];\n"
        "ldp x4, x3, [" $P2 "];\n"
        "subs x5, x5, x4;\n"
        "sbcs x6, x6, x3;\n"
        "ldp x7, x8, [" $P1 "+ 16];\n"
        "ldp x4, x3, [" $P2 "+ 16];\n"
        "sbcs x7, x7, x4;\n"
        "sbcs x8, x8, x3;\n"
        "ldp x9, x10, [" $P1 "+ 32];\n"
        "ldp x4, x3, [" $P2 "+ 32];\n"
        "sbcs x9, x9, x4;\n"
        "sbcs x10, x10, x3;\n"
        "ldp x11, x12, [" $P1 "+ 48];\n"
        "ldp x4, x3, [" $P2 "+ 48];\n"
        "sbcs x11, x11, x4;\n"
        "sbcs x12, x12, x3;\n"
        "ldr x13, [" $P1 "+ 64];\n"
        "ldr x4, [" $P2 "+ 64];\n"
        "sbcs x13, x13, x4;\n"
        "sbcs x5, x5, xzr;\n"
        "sbcs x6, x6, xzr;\n"
        "sbcs x7, x7, xzr;\n"
        "sbcs x8, x8, xzr;\n"
        "sbcs x9, x9, xzr;\n"
        "sbcs x10, x10, xzr;\n"
        "sbcs x11, x11, xzr;\n"
        "sbcs x12, x12, xzr;\n"
        "sbcs x13, x13, xzr;\n"
        "and x13, x13, #0x1ff;\n"
        "stp x5, x6, [" $P0 "];\n"
        "stp x7, x8, [" $P0 "+ 16];\n"
        "stp x9, x10, [" $P0 "+ 32];\n"
        "stp x11, x12, [" $P0 "+ 48];\n"
        "str x13, [" $P0 "+ 64]"
    )}
}

// Transliterated from s2n-bignum's arm/p521/p521_jadd_alt.S.
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

        // Save regs and make room on stack for temporary variables

        Q!("    stp             " "x19, x20, [sp, #-16] !"),
        Q!("    stp             " "x21, x22, [sp, #-16] !"),
        Q!("    stp             " "x23, x24, [sp, #-16] !"),
        Q!("    stp             " "x25, x26, [sp, #-16] !"),
        Q!("    stp             " "x27, x28, [sp, #-16] !"),
        Q!("    sub             " "sp, sp, # (" NSPACE!() "+ 0)"),

        // Move the input arguments to stable places

        Q!("    mov             " input_z!() ", x0"),
        Q!("    mov             " input_x!() ", x1"),
        Q!("    mov             " input_y!() ", x2"),

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
        // So  "HI" <=> CF /\ ~ZF <=> P1 = 0 /\ ~(P2 = 0)
        // and "LO" <=> ~CF       <=> ~(P1 = 0) /\ P2 = 0
        // Multiplex the z outputs accordingly and re-store in resz

        Q!("    ldp             " "x0, x1, [" z_1!() "]"),
        Q!("    ldp             " "x2, x3, [" z_1!() "+ 16]"),
        Q!("    ldp             " "x4, x5, [" z_1!() "+ 32]"),
        Q!("    ldp             " "x6, x7, [" z_1!() "+ 48]"),
        Q!("    ldr             " "x8, [" z_1!() "+ 64]"),

        Q!("    orr             " "x20, x0, x1"),
        Q!("    orr             " "x21, x2, x3"),
        Q!("    orr             " "x22, x4, x5"),
        Q!("    orr             " "x23, x6, x7"),
        Q!("    orr             " "x20, x20, x21"),
        Q!("    orr             " "x22, x22, x23"),
        Q!("    orr             " "x20, x20, x8"),
        Q!("    orr             " "x20, x20, x22"),
        Q!("    cmp             " "x20, xzr"),
        Q!("    cset            " "x20, ne"),

        Q!("    ldp             " "x10, x11, [" z_2!() "]"),
        Q!("    ldp             " "x12, x13, [" z_2!() "+ 16]"),
        Q!("    ldp             " "x14, x15, [" z_2!() "+ 32]"),
        Q!("    ldp             " "x16, x17, [" z_2!() "+ 48]"),
        Q!("    ldr             " "x19, [" z_2!() "+ 64]"),

        Q!("    orr             " "x21, x10, x11"),
        Q!("    orr             " "x22, x12, x13"),
        Q!("    orr             " "x23, x14, x15"),
        Q!("    orr             " "x24, x16, x17"),
        Q!("    orr             " "x21, x21, x22"),
        Q!("    orr             " "x23, x23, x24"),
        Q!("    orr             " "x21, x21, x19"),
        Q!("    orr             " "x21, x21, x23"),

        Q!("    csel            " "x0, x0, x10, ne"),
        Q!("    csel            " "x1, x1, x11, ne"),
        Q!("    csel            " "x2, x2, x12, ne"),
        Q!("    csel            " "x3, x3, x13, ne"),
        Q!("    csel            " "x4, x4, x14, ne"),
        Q!("    csel            " "x5, x5, x15, ne"),
        Q!("    csel            " "x6, x6, x16, ne"),
        Q!("    csel            " "x7, x7, x17, ne"),
        Q!("    csel            " "x8, x8, x19, ne"),

        Q!("    cmp             " "x21, xzr"),
        Q!("    cset            " "x21, ne"),

        Q!("    cmp             " "x21, x20"),

        Q!("    ldp             " "x10, x11, [" resz!() "]"),
        Q!("    ldp             " "x12, x13, [" resz!() "+ 16]"),
        Q!("    ldp             " "x14, x15, [" resz!() "+ 32]"),
        Q!("    ldp             " "x16, x17, [" resz!() "+ 48]"),
        Q!("    ldr             " "x19, [" resz!() "+ 64]"),

        Q!("    csel            " "x0, x0, x10, ne"),
        Q!("    csel            " "x1, x1, x11, ne"),
        Q!("    csel            " "x2, x2, x12, ne"),
        Q!("    csel            " "x3, x3, x13, ne"),
        Q!("    csel            " "x4, x4, x14, ne"),
        Q!("    csel            " "x5, x5, x15, ne"),
        Q!("    csel            " "x6, x6, x16, ne"),
        Q!("    csel            " "x7, x7, x17, ne"),
        Q!("    csel            " "x8, x8, x19, ne"),

        Q!("    stp             " "x0, x1, [" resz!() "]"),
        Q!("    stp             " "x2, x3, [" resz!() "+ 16]"),
        Q!("    stp             " "x4, x5, [" resz!() "+ 32]"),
        Q!("    stp             " "x6, x7, [" resz!() "+ 48]"),
        Q!("    str             " "x8, [" resz!() "+ 64]"),

        // Multiplex the x and y outputs too, keeping the results in registers

        Q!("    ldp             " "x20, x21, [" x_1!() "]"),
        Q!("    ldp             " "x0, x1, [" resx!() "]"),
        Q!("    csel            " "x0, x20, x0, lo"),
        Q!("    csel            " "x1, x21, x1, lo"),
        Q!("    ldp             " "x20, x21, [" x_2!() "]"),
        Q!("    csel            " "x0, x20, x0, hi"),
        Q!("    csel            " "x1, x21, x1, hi"),

        Q!("    ldp             " "x20, x21, [" x_1!() "+ 16]"),
        Q!("    ldp             " "x2, x3, [" resx!() "+ 16]"),
        Q!("    csel            " "x2, x20, x2, lo"),
        Q!("    csel            " "x3, x21, x3, lo"),
        Q!("    ldp             " "x20, x21, [" x_2!() "+ 16]"),
        Q!("    csel            " "x2, x20, x2, hi"),
        Q!("    csel            " "x3, x21, x3, hi"),

        Q!("    ldp             " "x20, x21, [" x_1!() "+ 32]"),
        Q!("    ldp             " "x4, x5, [" resx!() "+ 32]"),
        Q!("    csel            " "x4, x20, x4, lo"),
        Q!("    csel            " "x5, x21, x5, lo"),
        Q!("    ldp             " "x20, x21, [" x_2!() "+ 32]"),
        Q!("    csel            " "x4, x20, x4, hi"),
        Q!("    csel            " "x5, x21, x5, hi"),

        Q!("    ldp             " "x20, x21, [" x_1!() "+ 48]"),
        Q!("    ldp             " "x6, x7, [" resx!() "+ 48]"),
        Q!("    csel            " "x6, x20, x6, lo"),
        Q!("    csel            " "x7, x21, x7, lo"),
        Q!("    ldp             " "x20, x21, [" x_2!() "+ 48]"),
        Q!("    csel            " "x6, x20, x6, hi"),
        Q!("    csel            " "x7, x21, x7, hi"),

        Q!("    ldr             " "x20, [" x_1!() "+ 64]"),
        Q!("    ldr             " "x8, [" resx!() "+ 64]"),
        Q!("    csel            " "x8, x20, x8, lo"),
        Q!("    ldr             " "x21, [" x_2!() "+ 64]"),
        Q!("    csel            " "x8, x21, x8, hi"),

        Q!("    ldp             " "x20, x21, [" y_1!() "]"),
        Q!("    ldp             " "x10, x11, [" resy!() "]"),
        Q!("    csel            " "x10, x20, x10, lo"),
        Q!("    csel            " "x11, x21, x11, lo"),
        Q!("    ldp             " "x20, x21, [" y_2!() "]"),
        Q!("    csel            " "x10, x20, x10, hi"),
        Q!("    csel            " "x11, x21, x11, hi"),

        Q!("    ldp             " "x20, x21, [" y_1!() "+ 16]"),
        Q!("    ldp             " "x12, x13, [" resy!() "+ 16]"),
        Q!("    csel            " "x12, x20, x12, lo"),
        Q!("    csel            " "x13, x21, x13, lo"),
        Q!("    ldp             " "x20, x21, [" y_2!() "+ 16]"),
        Q!("    csel            " "x12, x20, x12, hi"),
        Q!("    csel            " "x13, x21, x13, hi"),

        Q!("    ldp             " "x20, x21, [" y_1!() "+ 32]"),
        Q!("    ldp             " "x14, x15, [" resy!() "+ 32]"),
        Q!("    csel            " "x14, x20, x14, lo"),
        Q!("    csel            " "x15, x21, x15, lo"),
        Q!("    ldp             " "x20, x21, [" y_2!() "+ 32]"),
        Q!("    csel            " "x14, x20, x14, hi"),
        Q!("    csel            " "x15, x21, x15, hi"),

        Q!("    ldp             " "x20, x21, [" y_1!() "+ 48]"),
        Q!("    ldp             " "x16, x17, [" resy!() "+ 48]"),
        Q!("    csel            " "x16, x20, x16, lo"),
        Q!("    csel            " "x17, x21, x17, lo"),
        Q!("    ldp             " "x20, x21, [" y_2!() "+ 48]"),
        Q!("    csel            " "x16, x20, x16, hi"),
        Q!("    csel            " "x17, x21, x17, hi"),

        Q!("    ldr             " "x20, [" y_1!() "+ 64]"),
        Q!("    ldr             " "x19, [" resy!() "+ 64]"),
        Q!("    csel            " "x19, x20, x19, lo"),
        Q!("    ldr             " "x21, [" y_2!() "+ 64]"),
        Q!("    csel            " "x19, x21, x19, hi"),

        // Finally store back the multiplexed values

        Q!("    stp             " "x0, x1, [" x_3!() "]"),
        Q!("    stp             " "x2, x3, [" x_3!() "+ 16]"),
        Q!("    stp             " "x4, x5, [" x_3!() "+ 32]"),
        Q!("    stp             " "x6, x7, [" x_3!() "+ 48]"),
        Q!("    str             " "x8, [" x_3!() "+ 64]"),

        Q!("    ldp             " "x0, x1, [" resz!() "]"),
        Q!("    ldp             " "x2, x3, [" resz!() "+ 16]"),
        Q!("    ldp             " "x4, x5, [" resz!() "+ 32]"),
        Q!("    ldp             " "x6, x7, [" resz!() "+ 48]"),
        Q!("    ldr             " "x8, [" resz!() "+ 64]"),

        Q!("    stp             " "x10, x11, [" y_3!() "]"),
        Q!("    stp             " "x12, x13, [" y_3!() "+ 16]"),
        Q!("    stp             " "x14, x15, [" y_3!() "+ 32]"),
        Q!("    stp             " "x16, x17, [" y_3!() "+ 48]"),
        Q!("    str             " "x19, [" y_3!() "+ 64]"),

        Q!("    stp             " "x0, x1, [" z_3!() "]"),
        Q!("    stp             " "x2, x3, [" z_3!() "+ 16]"),
        Q!("    stp             " "x4, x5, [" z_3!() "+ 32]"),
        Q!("    stp             " "x6, x7, [" z_3!() "+ 48]"),
        Q!("    str             " "x8, [" z_3!() "+ 64]"),

        // Restore stack and registers

        Q!("    add             " "sp, sp, # (" NSPACE!() "+ 0)"),

        Q!("    ldp             " "x27, x28, [sp], #16"),
        Q!("    ldp             " "x25, x26, [sp], #16"),
        Q!("    ldp             " "x23, x24, [sp], #16"),
        Q!("    ldp             " "x21, x22, [sp], #16"),
        Q!("    ldp             " "x19, x20, [sp], #16"),

        inout("x0") p3.as_mut_ptr() => _,
        inout("x1") p1.as_ptr() => _,
        inout("x2") p2.as_ptr() => _,
        // clobbers
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
        out("x27") _,
        out("x28") _,
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
        p521_jadd,
        &mut crate::low::abi::Aligned([0; 27]).0,
        &crate::low::abi::Aligned([0; 27]).0,
        &crate::low::abi::Aligned([0; 27]).0
    );
}
