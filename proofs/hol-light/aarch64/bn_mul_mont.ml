(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication, aws-lc's aarch64 bn_mul_mont, as rind's build  *)
(* emits it, for widths that are not a multiple of four.                     *)
(* ========================================================================= *)

(* rind's naked function low::aarch64::mont::bn_mul_mont is aws-lc's
   bn_mul_mont (crypto/fipsmodule/bn/asm/armv8-mont.pl). It dispatches on the
   width k: a multiple of eight goes to __bn_sqr8x_mont when squaring and to
   __bn_mul4x_mont otherwise, as does any other multiple of four, and every
   other width runs the generic path at offset 0x10. The goal is s2n-bignum's
   bignum_montmul specification for all three. This file proves it for the
   generic path: BN_MUL_MONT_GENERIC_SUBROUTINE_CORRECT is that, for a width
   k that is not a multiple of four, called with the AAPCS64, it writes to z
   the Montgomery product x * y / 2^(64k) mod m of the k-word x, y and m,
   given the word at n0p is -m^-1 mod 2^64, and returns 1. As for the x86
   routines, the result is reduced only when x * y <= 2^(64k) * m, which
   x, y < m give. The proof is segment lemmas, each an `ensures` between two
   program points with a definitional invariant:

   - GEN_PRE, 0x24 to 0x70: the frame and the first pass's first words.
   - GEN_H1_BODY and GEN_LOOP1: the first pass's loop, multiplying x by y's
     first word and adding q0 times m, word by word (gen_h1_inv).
   - GEN_SKIP1: the first pass's tail, ending at the outer loop's head with
     its invariant for one word of y (gen_out_inv).
   - GEN_OUT_PRE, GEN_IN_BODY, GEN_IN_LOOP and GEN_OUT_TAIL: one outer
     iteration's prelude, inner loop (gen_in_inv) and tail, which GEN_OUTER
     joins.
   - GEN_SUB and GEN_COPY: the final subtraction of m, and the selection
     that copies the reduced result to z and wipes the accumulator.
   - GEN_BODY joins them from 0x24 to 0x224, and the subroutine theorem adds
     the dispatch, the frame saves and the epilogue.

   Carries the code drops are proven zero from product bounds: a 64x64-bit
   product's high word is at most 2^64 - 2, and when it is, the low word is
   at most 1 (PROD_BOUND), with linear arithmetic over the carry cases. *)

needs "arm/proofs/base.ml";;

(* admin/prove writes the function, as rind's release build emits it, to
   aarch64/bn_mul_mont.o. The definition fails unless its instructions are
   these. *)
let bn_mul_mont_mc =
  define_assert_from_elf "bn_mul_mont_mc" "aarch64/bn_mul_mont.o"
[
  0xf24008bf;       (* arm_TST X5 (rvalue (word 7)) *)
  0x540011e0;       (* arm_BEQ (word 572) *)
  0xf24004bf;       (* arm_TST X5 (rvalue (word 3)) *)
  0x540060a0;       (* arm_BEQ (word 3092) *)
  0xa9bc7bfd;       (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &64))) *)
  0x910003fd;       (* arm_ADD X29 SP (rvalue (word 0)) *)
  0xa90153f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  0xa9025bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&32))) *)
  0xa90363f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&48))) *)
  0xf8408449;       (* arm_LDR X9 X2 (Postimmediate_Offset (word 8)) *)
  0xcb256ff6;       (* arm_SUB X22 SP (Shiftedreg (Extendedreg X5 UXTX) LSL 3) *)
  0xa8c12027;       (* arm_LDP X7 X8 X1 (Postimmediate_Offset (iword (&16))) *)
  0xd37df0a5;       (* arm_LSL X5 X5 3 *)
  0xf9400084;       (* arm_LDR X4 X4 (Immediate_Offset (word 0)) *)
  0x927ceed6;       (* arm_AND X22 X22 (rvalue (word 18446744073709551600)) *)
  0xa8c1386d;       (* arm_LDP X13 X14 X3 (Postimmediate_Offset (iword (&16))) *)
  0x9b097ce6;       (* arm_MUL X6 X7 X9 *)
  0xd10040b5;       (* arm_SUB X21 X5 (rvalue (word 16)) *)
  0x9bc97ce7;       (* arm_UMULH X7 X7 X9 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d0b;       (* arm_UMULH X11 X8 X9 *)
  0x9b047ccf;       (* arm_MUL X15 X6 X4 *)
  0x910002df;       (* arm_ADD SP X22 (rvalue (word 0)) *)
  0x9bcf7dad;       (* arm_UMULH X13 X13 X15 *)
  0x9b0f7dd0;       (* arm_MUL X16 X14 X15 *)
  0xf10004df;       (* arm_CMP X6 (rvalue (word 1)) *)
  0x9bcf7dd1;       (* arm_UMULH X17 X14 X15 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xb4000215;       (* arm_CBZ X21 (word 64) *)
  0xf8408428;       (* arm_LDR X8 X1 (Postimmediate_Offset (word 8)) *)
  0xab070146;       (* arm_ADDS X6 X10 X7 *)
  0xd10022b5;       (* arm_SUB X21 X21 (rvalue (word 8)) *)
  0x9a1f0167;       (* arm_ADC X7 X11 XZR *)
  0xf840846e;       (* arm_LDR X14 X3 (Postimmediate_Offset (word 8)) *)
  0xab0d020c;       (* arm_ADDS X12 X16 X13 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9a1f022d;       (* arm_ADC X13 X17 XZR *)
  0x9bc97d0b;       (* arm_UMULH X11 X8 X9 *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0x9b0f7dd0;       (* arm_MUL X16 X14 X15 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0x9bcf7dd1;       (* arm_UMULH X17 X14 X15 *)
  0xf80086cc;       (* arm_STR X12 X22 (Postimmediate_Offset (word 8)) *)
  0xb5fffe55;       (* arm_CBNZ X21 (word 2097096) *)
  0xab070146;       (* arm_ADDS X6 X10 X7 *)
  0xcb050021;       (* arm_SUB X1 X1 X5 *)
  0x9a1f0167;       (* arm_ADC X7 X11 XZR *)
  0xab0d020c;       (* arm_ADDS X12 X16 X13 *)
  0xcb050063;       (* arm_SUB X3 X3 X5 *)
  0x9a1f022d;       (* arm_ADC X13 X17 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xd10020b4;       (* arm_SUB X20 X5 (rvalue (word 8)) *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0xa90036cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xf8408449;       (* arm_LDR X9 X2 (Postimmediate_Offset (word 8)) *)
  0xa8c12027;       (* arm_LDP X7 X8 X1 (Postimmediate_Offset (iword (&16))) *)
  0xf94003f7;       (* arm_LDR X23 SP (Immediate_Offset (word 0)) *)
  0x910023f6;       (* arm_ADD X22 SP (rvalue (word 8)) *)
  0x9b097ce6;       (* arm_MUL X6 X7 X9 *)
  0xd10040b5;       (* arm_SUB X21 X5 (rvalue (word 16)) *)
  0x9bc97ce7;       (* arm_UMULH X7 X7 X9 *)
  0xa8c1386d;       (* arm_LDP X13 X14 X3 (Postimmediate_Offset (iword (&16))) *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0xab1700c6;       (* arm_ADDS X6 X6 X23 *)
  0x9bc97d0b;       (* arm_UMULH X11 X8 X9 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0x9b047ccf;       (* arm_MUL X15 X6 X4 *)
  0xd1002294;       (* arm_SUB X20 X20 (rvalue (word 8)) *)
  0x9bcf7dad;       (* arm_UMULH X13 X13 X15 *)
  0x9b0f7dd0;       (* arm_MUL X16 X14 X15 *)
  0xf10004df;       (* arm_CMP X6 (rvalue (word 1)) *)
  0x9bcf7dd1;       (* arm_UMULH X17 X14 X15 *)
  0xb4000275;       (* arm_CBZ X21 (word 76) *)
  0xf8408428;       (* arm_LDR X8 X1 (Postimmediate_Offset (word 8)) *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xf84086d7;       (* arm_LDR X23 X22 (Postimmediate_Offset (word 8)) *)
  0xab070146;       (* arm_ADDS X6 X10 X7 *)
  0xd10022b5;       (* arm_SUB X21 X21 (rvalue (word 8)) *)
  0x9a1f0167;       (* arm_ADC X7 X11 XZR *)
  0xab0d020c;       (* arm_ADDS X12 X16 X13 *)
  0xf840846e;       (* arm_LDR X14 X3 (Postimmediate_Offset (word 8)) *)
  0x9a1f022d;       (* arm_ADC X13 X17 XZR *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0xab1700c6;       (* arm_ADDS X6 X6 X23 *)
  0x9bc97d0b;       (* arm_UMULH X11 X8 X9 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0x9b0f7dd0;       (* arm_MUL X16 X14 X15 *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0x9bcf7dd1;       (* arm_UMULH X17 X14 X15 *)
  0xf81f02cc;       (* arm_STR X12 X22 (Immediate_Offset (word 18446744073709551600)) *)
  0xb5fffdf5;       (* arm_CBNZ X21 (word 2097084) *)
  0xf84086d7;       (* arm_LDR X23 X22 (Postimmediate_Offset (word 8)) *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab070146;       (* arm_ADDS X6 X10 X7 *)
  0xcb050021;       (* arm_SUB X1 X1 X5 *)
  0x9a1f0167;       (* arm_ADC X7 X11 XZR *)
  0xab0d020c;       (* arm_ADDS X12 X16 X13 *)
  0xcb050063;       (* arm_SUB X3 X3 X5 *)
  0xba13022d;       (* arm_ADCS X13 X17 X19 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0xab1700c6;       (* arm_ADDS X6 X6 X23 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xa93f36cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (-- &16))) *)
  0xb5fff994;       (* arm_CBNZ X20 (word 2096944) *)
  0xf94003f7;       (* arm_LDR X23 SP (Immediate_Offset (word 0)) *)
  0x910023f6;       (* arm_ADD X22 SP (rvalue (word 8)) *)
  0xf840846e;       (* arm_LDR X14 X3 (Postimmediate_Offset (word 8)) *)
  0xf10020b5;       (* arm_SUBS X21 X5 (rvalue (word 8)) *)
  0xaa0003e1;       (* arm_MOV X1 X0 *)
  0xfa0e02e8;       (* arm_SBCS X8 X23 X14 *)
  0xf84086d7;       (* arm_LDR X23 X22 (Postimmediate_Offset (word 8)) *)
  0xd10022b5;       (* arm_SUB X21 X21 (rvalue (word 8)) *)
  0xf840846e;       (* arm_LDR X14 X3 (Postimmediate_Offset (word 8)) *)
  0xf8008428;       (* arm_STR X8 X1 (Postimmediate_Offset (word 8)) *)
  0xb5ffff75;       (* arm_CBNZ X21 (word 2097132) *)
  0xfa0e02e8;       (* arm_SBCS X8 X23 X14 *)
  0xfa1f0273;       (* arm_SBCS X19 X19 XZR *)
  0xf8008428;       (* arm_STR X8 X1 (Postimmediate_Offset (word 8)) *)
  0xf94003f7;       (* arm_LDR X23 SP (Immediate_Offset (word 0)) *)
  0x910023f6;       (* arm_ADD X22 SP (rvalue (word 8)) *)
  0xf8408408;       (* arm_LDR X8 X0 (Postimmediate_Offset (word 8)) *)
  0xd10020a5;       (* arm_SUB X5 X5 (rvalue (word 8)) *)
  0xd503201f;       (* arm_NOP *)
  0xd10020a5;       (* arm_SUB X5 X5 (rvalue (word 8)) *)
  0x9a8832ee;       (* arm_CSEL X14 X23 X8 Condition_CC *)
  0xf84086d7;       (* arm_LDR X23 X22 (Postimmediate_Offset (word 8)) *)
  0xf8408408;       (* arm_LDR X8 X0 (Postimmediate_Offset (word 8)) *)
  0xf81f02df;       (* arm_STR XZR X22 (Immediate_Offset (word 18446744073709551600)) *)
  0xf81f000e;       (* arm_STR X14 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0xb5ffff45;       (* arm_CBNZ X5 (word 2097128) *)
  0x9a8832ee;       (* arm_CSEL X14 X23 X8 Condition_CC *)
  0xf81f82df;       (* arm_STR XZR X22 (Immediate_Offset (word 18446744073709551608)) *)
  0xf81f800e;       (* arm_STR X14 X0 (Immediate_Offset (word 18446744073709551608)) *)
  0xa94153b3;       (* arm_LDP X19 X20 X29 (Immediate_Offset (iword (&16))) *)
  0x910003bf;       (* arm_ADD SP X29 (rvalue (word 0)) *)
  0xa9425bb5;       (* arm_LDP X21 X22 X29 (Immediate_Offset (iword (&32))) *)
  0xd2800020;       (* arm_MOV X0 (rvalue (word 1)) *)
  0xa94363b7;       (* arm_LDP X23 X24 X29 (Immediate_Offset (iword (&48))) *)
  0xf84407fd;       (* arm_LDR X29 SP (Postimmediate_Offset (word 64)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xeb02003f;       (* arm_CMP X1 X2 *)
  0x54004ee1;       (* arm_BNE (word 2524) *)
  0xa9b87bfd;       (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &128))) *)
  0x910003fd;       (* arm_ADD X29 SP (rvalue (word 0)) *)
  0xa90153f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  0xa9025bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&32))) *)
  0xa90363f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&48))) *)
  0xa9046bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&64))) *)
  0xa90573fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&80))) *)
  0xa9060fe0;       (* arm_STP X0 X3 SP (Immediate_Offset (iword (&96))) *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xa9422c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&32))) *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0xcb2573e2;       (* arm_SUB X2 SP (Shiftedreg (Extendedreg X5 UXTX) LSL 4) *)
  0xd37df0a5;       (* arm_LSL X5 X5 3 *)
  0xf9400084;       (* arm_LDR X4 X4 (Immediate_Offset (word 0)) *)
  0x9100005f;       (* arm_ADD SP X2 (rvalue (word 0)) *)
  0xd10100bb;       (* arm_SUB X27 X5 (rvalue (word 64)) *)
  0x14000006;       (* arm_B (word 24) *)
  0xd101037b;       (* arm_SUB X27 X27 (rvalue (word 64)) *)
  0xa9007c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&0))) *)
  0xa9017c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&16))) *)
  0xa9027c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&32))) *)
  0xa9037c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&48))) *)
  0xa9047c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&64))) *)
  0xa9057c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&80))) *)
  0xa9067c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&96))) *)
  0xa9077c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&112))) *)
  0x91020042;       (* arm_ADD X2 X2 (rvalue (word 128)) *)
  0xb5fffedb;       (* arm_CBNZ X27 (word 2097112) *)
  0x8b050023;       (* arm_ADD X3 X1 X5 *)
  0x91010021;       (* arm_ADD X1 X1 (rvalue (word 64)) *)
  0xaa1f03f3;       (* arm_MOV X19 XZR *)
  0xaa1f03f4;       (* arm_MOV X20 XZR *)
  0xaa1f03f5;       (* arm_MOV X21 XZR *)
  0xaa1f03f6;       (* arm_MOV X22 XZR *)
  0xaa1f03f7;       (* arm_MOV X23 XZR *)
  0xaa1f03f8;       (* arm_MOV X24 XZR *)
  0xaa1f03f9;       (* arm_MOV X25 XZR *)
  0xaa1f03fa;       (* arm_MOV X26 XZR *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0xf9003ba4;       (* arm_STR X4 X29 (Immediate_Offset (word 112)) *)
  0xd503201f;       (* arm_NOP *)
  0x9b067cee;       (* arm_MUL X14 X7 X6 *)
  0x9b067d0f;       (* arm_MUL X15 X8 X6 *)
  0x9b067d30;       (* arm_MUL X16 X9 X6 *)
  0x9b067d51;       (* arm_MUL X17 X10 X6 *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9b067d6e;       (* arm_MUL X14 X11 X6 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0x9b067d8f;       (* arm_MUL X15 X12 X6 *)
  0xba1002d6;       (* arm_ADCS X22 X22 X16 *)
  0x9b067db0;       (* arm_MUL X16 X13 X6 *)
  0xba1102f7;       (* arm_ADCS X23 X23 X17 *)
  0x9bc67cf1;       (* arm_UMULH X17 X7 X6 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bc67d0e;       (* arm_UMULH X14 X8 X6 *)
  0xba0f0339;       (* arm_ADCS X25 X25 X15 *)
  0x9bc67d2f;       (* arm_UMULH X15 X9 X6 *)
  0xba10035a;       (* arm_ADCS X26 X26 X16 *)
  0x9bc67d50;       (* arm_UMULH X16 X10 X6 *)
  0xa8815053;       (* arm_STP X19 X20 X2 (Postimmediate_Offset (iword (&16))) *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0xab1102b5;       (* arm_ADDS X21 X21 X17 *)
  0x9bc67d71;       (* arm_UMULH X17 X11 X6 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bc67d8e;       (* arm_UMULH X14 X12 X6 *)
  0xba0f02f7;       (* arm_ADCS X23 X23 X15 *)
  0x9bc67daf;       (* arm_UMULH X15 X13 X6 *)
  0xba100318;       (* arm_ADCS X24 X24 X16 *)
  0x9b077d10;       (* arm_MUL X16 X8 X7 *)
  0xba110339;       (* arm_ADCS X25 X25 X17 *)
  0x9b077d31;       (* arm_MUL X17 X9 X7 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b077d4e;       (* arm_MUL X14 X10 X7 *)
  0x9a0f0273;       (* arm_ADC X19 X19 X15 *)
  0x9b077d6f;       (* arm_MUL X15 X11 X7 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9b077d90;       (* arm_MUL X16 X12 X7 *)
  0xba1102f7;       (* arm_ADCS X23 X23 X17 *)
  0x9b077db1;       (* arm_MUL X17 X13 X7 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bc77d0e;       (* arm_UMULH X14 X8 X7 *)
  0xba0f0339;       (* arm_ADCS X25 X25 X15 *)
  0x9bc77d2f;       (* arm_UMULH X15 X9 X7 *)
  0xba10035a;       (* arm_ADCS X26 X26 X16 *)
  0x9bc77d50;       (* arm_UMULH X16 X10 X7 *)
  0xba110273;       (* arm_ADCS X19 X19 X17 *)
  0x9bc77d71;       (* arm_UMULH X17 X11 X7 *)
  0xa8815855;       (* arm_STP X21 X22 X2 (Postimmediate_Offset (iword (&16))) *)
  0x9a1f03f4;       (* arm_ADC X20 XZR XZR *)
  0xab0e02f7;       (* arm_ADDS X23 X23 X14 *)
  0x9bc77d8e;       (* arm_UMULH X14 X12 X7 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0x9bc77daf;       (* arm_UMULH X15 X13 X7 *)
  0xba100339;       (* arm_ADCS X25 X25 X16 *)
  0x9b087d30;       (* arm_MUL X16 X9 X8 *)
  0xba11035a;       (* arm_ADCS X26 X26 X17 *)
  0x9b087d51;       (* arm_MUL X17 X10 X8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b087d6e;       (* arm_MUL X14 X11 X8 *)
  0x9a0f0294;       (* arm_ADC X20 X20 X15 *)
  0x9b087d8f;       (* arm_MUL X15 X12 X8 *)
  0xab100318;       (* arm_ADDS X24 X24 X16 *)
  0x9b087db0;       (* arm_MUL X16 X13 X8 *)
  0xba110339;       (* arm_ADCS X25 X25 X17 *)
  0x9bc87d31;       (* arm_UMULH X17 X9 X8 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bc87d4e;       (* arm_UMULH X14 X10 X8 *)
  0xba0f0273;       (* arm_ADCS X19 X19 X15 *)
  0x9bc87d6f;       (* arm_UMULH X15 X11 X8 *)
  0xba100294;       (* arm_ADCS X20 X20 X16 *)
  0x9bc87d90;       (* arm_UMULH X16 X12 X8 *)
  0xa8816057;       (* arm_STP X23 X24 X2 (Postimmediate_Offset (iword (&16))) *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xab110339;       (* arm_ADDS X25 X25 X17 *)
  0x9bc87db1;       (* arm_UMULH X17 X13 X8 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b097d4e;       (* arm_MUL X14 X10 X9 *)
  0xba0f0273;       (* arm_ADCS X19 X19 X15 *)
  0x9b097d6f;       (* arm_MUL X15 X11 X9 *)
  0xba100294;       (* arm_ADCS X20 X20 X16 *)
  0x9b097d90;       (* arm_MUL X16 X12 X9 *)
  0x9a1102b5;       (* arm_ADC X21 X21 X17 *)
  0x9b097db1;       (* arm_MUL X17 X13 X9 *)
  0xab0e035a;       (* arm_ADDS X26 X26 X14 *)
  0x9bc97d4e;       (* arm_UMULH X14 X10 X9 *)
  0xba0f0273;       (* arm_ADCS X19 X19 X15 *)
  0x9bc97d6f;       (* arm_UMULH X15 X11 X9 *)
  0xba100294;       (* arm_ADCS X20 X20 X16 *)
  0x9bc97d90;       (* arm_UMULH X16 X12 X9 *)
  0xba1102b5;       (* arm_ADCS X21 X21 X17 *)
  0x9bc97db1;       (* arm_UMULH X17 X13 X9 *)
  0xa8816859;       (* arm_STP X25 X26 X2 (Postimmediate_Offset (iword (&16))) *)
  0x9a1f03f6;       (* arm_ADC X22 XZR XZR *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x9b0a7d6e;       (* arm_MUL X14 X11 X10 *)
  0xba0f0294;       (* arm_ADCS X20 X20 X15 *)
  0x9b0a7d8f;       (* arm_MUL X15 X12 X10 *)
  0xba1002b5;       (* arm_ADCS X21 X21 X16 *)
  0x9b0a7db0;       (* arm_MUL X16 X13 X10 *)
  0x9a1102d6;       (* arm_ADC X22 X22 X17 *)
  0x9bca7d71;       (* arm_UMULH X17 X11 X10 *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9bca7d8e;       (* arm_UMULH X14 X12 X10 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0x9bca7daf;       (* arm_UMULH X15 X13 X10 *)
  0xba1002d6;       (* arm_ADCS X22 X22 X16 *)
  0x9b0b7d90;       (* arm_MUL X16 X12 X11 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0xab1102b5;       (* arm_ADDS X21 X21 X17 *)
  0x9b0b7db1;       (* arm_MUL X17 X13 X11 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bcb7d8e;       (* arm_UMULH X14 X12 X11 *)
  0x9a0f02f7;       (* arm_ADC X23 X23 X15 *)
  0x9bcb7daf;       (* arm_UMULH X15 X13 X11 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9b0c7db0;       (* arm_MUL X16 X13 X12 *)
  0xba1102f7;       (* arm_ADCS X23 X23 X17 *)
  0x9bcc7db1;       (* arm_UMULH X17 X13 X12 *)
  0x9a1f03f8;       (* arm_ADC X24 XZR XZR *)
  0xab0e02f7;       (* arm_ADDS X23 X23 X14 *)
  0xcb01007b;       (* arm_SUB X27 X3 X1 *)
  0x9a0f0318;       (* arm_ADC X24 X24 X15 *)
  0xab100318;       (* arm_ADDS X24 X24 X16 *)
  0xcb05006e;       (* arm_SUB X14 X3 X5 *)
  0x9a1f03f9;       (* arm_ADC X25 XZR XZR *)
  0x8b110339;       (* arm_ADD X25 X25 X17 *)
  0xb4000cfb;       (* arm_CBZ X27 (word 412) *)
  0xaa0603e4;       (* arm_MOV X4 X6 *)
  0xa9401c46;       (* arm_LDP X6 X7 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&16))) *)
  0xa9422c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&32))) *)
  0xa943344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&48))) *)
  0xab060273;       (* arm_ADDS X19 X19 X6 *)
  0xba070294;       (* arm_ADCS X20 X20 X7 *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xba0802b5;       (* arm_ADCS X21 X21 X8 *)
  0xba0902d6;       (* arm_ADCS X22 X22 X9 *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0xba0b0318;       (* arm_ADCS X24 X24 X11 *)
  0xa9422c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&32))) *)
  0xba0c0339;       (* arm_ADCS X25 X25 X12 *)
  0xaa0103e0;       (* arm_MOV X0 X1 *)
  0xba0d03fa;       (* arm_ADCS X26 XZR X13 *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0x91010021;       (* arm_ADD X1 X1 (rvalue (word 64)) *)
  0x928007fb;       (* arm_MOVN X27 (word 63) 0 *)
  0x9b047cce;       (* arm_MUL X14 X6 X4 *)
  0x9a1f03fc;       (* arm_ADC X28 XZR XZR *)
  0x9b047cef;       (* arm_MUL X15 X7 X4 *)
  0x9100237b;       (* arm_ADD X27 X27 (rvalue (word 8)) *)
  0x9b047d10;       (* arm_MUL X16 X8 X4 *)
  0x9b047d31;       (* arm_MUL X17 X9 X4 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x9b047d4e;       (* arm_MUL X14 X10 X4 *)
  0xba0f0294;       (* arm_ADCS X20 X20 X15 *)
  0x9b047d6f;       (* arm_MUL X15 X11 X4 *)
  0xba1002b5;       (* arm_ADCS X21 X21 X16 *)
  0x9b047d90;       (* arm_MUL X16 X12 X4 *)
  0xba1102d6;       (* arm_ADCS X22 X22 X17 *)
  0x9b047db1;       (* arm_MUL X17 X13 X4 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bc47cce;       (* arm_UMULH X14 X6 X4 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0x9bc47cef;       (* arm_UMULH X15 X7 X4 *)
  0xba100339;       (* arm_ADCS X25 X25 X16 *)
  0x9bc47d10;       (* arm_UMULH X16 X8 X4 *)
  0xba11035a;       (* arm_ADCS X26 X26 X17 *)
  0x9bc47d31;       (* arm_UMULH X17 X9 X4 *)
  0x9a1f039c;       (* arm_ADC X28 X28 XZR *)
  0xf8008453;       (* arm_STR X19 X2 (Postimmediate_Offset (word 8)) *)
  0xab0e0293;       (* arm_ADDS X19 X20 X14 *)
  0x9bc47d4e;       (* arm_UMULH X14 X10 X4 *)
  0xba0f02b4;       (* arm_ADCS X20 X21 X15 *)
  0x9bc47d6f;       (* arm_UMULH X15 X11 X4 *)
  0xba1002d5;       (* arm_ADCS X21 X22 X16 *)
  0x9bc47d90;       (* arm_UMULH X16 X12 X4 *)
  0xba1102f6;       (* arm_ADCS X22 X23 X17 *)
  0x9bc47db1;       (* arm_UMULH X17 X13 X4 *)
  0xf87b6804;       (* arm_LDR X4 X0 (Register_Offset X27) *)
  0xba0e0317;       (* arm_ADCS X23 X24 X14 *)
  0xba0f0338;       (* arm_ADCS X24 X25 X15 *)
  0xba100359;       (* arm_ADCS X25 X26 X16 *)
  0xba11039a;       (* arm_ADCS X26 X28 X17 *)
  0xb5fffb7b;       (* arm_CBNZ X27 (word 2097004) *)
  0xeb03003f;       (* arm_CMP X1 X3 *)
  0x540002e0;       (* arm_BEQ (word 92) *)
  0xa9401c46;       (* arm_LDP X6 X7 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&16))) *)
  0xa9422c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&32))) *)
  0xa943344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&48))) *)
  0xab060273;       (* arm_ADDS X19 X19 X6 *)
  0xf85c0004;       (* arm_LDR X4 X0 (Immediate_Offset (word 18446744073709551552)) *)
  0xba070294;       (* arm_ADCS X20 X20 X7 *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xba0802b5;       (* arm_ADCS X21 X21 X8 *)
  0xba0902d6;       (* arm_ADCS X22 X22 X9 *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0xba0b0318;       (* arm_ADCS X24 X24 X11 *)
  0xa9422c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&32))) *)
  0xba0c0339;       (* arm_ADCS X25 X25 X12 *)
  0x928007fb;       (* arm_MOVN X27 (word 63) 0 *)
  0xba0d035a;       (* arm_ADCS X26 X26 X13 *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0x91010021;       (* arm_ADD X1 X1 (rvalue (word 64)) *)
  0x17ffffc5;       (* arm_B (word 268435220) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xa9401c06;       (* arm_LDP X6 X7 X0 (Immediate_Offset (iword (&0))) *)
  0x91010001;       (* arm_ADD X1 X0 (rvalue (word 64)) *)
  0xa9412408;       (* arm_LDP X8 X9 X0 (Immediate_Offset (iword (&16))) *)
  0xcb01006e;       (* arm_SUB X14 X3 X1 *)
  0xa9422c0a;       (* arm_LDP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xcb0e004f;       (* arm_SUB X15 X2 X14 *)
  0xa943340c;       (* arm_LDP X12 X13 X0 (Immediate_Offset (iword (&48))) *)
  0xb4ffe52e;       (* arm_CBZ X14 (word 2096292) *)
  0xa9005053;       (* arm_STP X19 X20 X2 (Immediate_Offset (iword (&0))) *)
  0xa94051f3;       (* arm_LDP X19 X20 X15 (Immediate_Offset (iword (&0))) *)
  0xa9015855;       (* arm_STP X21 X22 X2 (Immediate_Offset (iword (&16))) *)
  0xa94159f5;       (* arm_LDP X21 X22 X15 (Immediate_Offset (iword (&16))) *)
  0xa9026057;       (* arm_STP X23 X24 X2 (Immediate_Offset (iword (&32))) *)
  0xa94261f7;       (* arm_LDP X23 X24 X15 (Immediate_Offset (iword (&32))) *)
  0xa9036859;       (* arm_STP X25 X26 X2 (Immediate_Offset (iword (&48))) *)
  0xaa0f03e2;       (* arm_MOV X2 X15 *)
  0xa94369f9;       (* arm_LDP X25 X26 X15 (Immediate_Offset (iword (&48))) *)
  0x17ffff1f;       (* arm_B (word 268434556) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xa94025c7;       (* arm_LDP X7 X9 X14 (Immediate_Offset (iword (&0))) *)
  0xa940c3ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&8))) *)
  0xa94135cb;       (* arm_LDP X11 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x910081c1;       (* arm_ADD X1 X14 (rvalue (word 32)) *)
  0xa941bbf1;       (* arm_LDP X17 X14 SP (Immediate_Offset (iword (&24))) *)
  0xa9005053;       (* arm_STP X19 X20 X2 (Immediate_Offset (iword (&0))) *)
  0x9b077cf3;       (* arm_MUL X19 X7 X7 *)
  0xa9015855;       (* arm_STP X21 X22 X2 (Immediate_Offset (iword (&16))) *)
  0x9bc77ce7;       (* arm_UMULH X7 X7 X7 *)
  0xa9026057;       (* arm_STP X23 X24 X2 (Immediate_Offset (iword (&32))) *)
  0x9b097d28;       (* arm_MUL X8 X9 X9 *)
  0xa9036859;       (* arm_STP X25 X26 X2 (Immediate_Offset (iword (&48))) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x9bc97d29;       (* arm_UMULH X9 X9 X9 *)
  0xab0f04f4;       (* arm_ADDS X20 X7 (Shiftedreg X15 LSL 1) *)
  0x93cffe0f;       (* arm_EXTR X15 X16 X15 63 *)
  0xd10080bb;       (* arm_SUB X27 X5 (rvalue (word 32)) *)
  0xba0f0115;       (* arm_ADCS X21 X8 X15 *)
  0x93d0fe30;       (* arm_EXTR X16 X17 X16 63 *)
  0xd100837b;       (* arm_SUB X27 X27 (rvalue (word 32)) *)
  0xba100136;       (* arm_ADCS X22 X9 X16 *)
  0xa942c04f;       (* arm_LDP X15 X16 X2 (Immediate_Offset (iword (&40))) *)
  0x9b0b7d6a;       (* arm_MUL X10 X11 X11 *)
  0xa8c12427;       (* arm_LDP X7 X9 X1 (Postimmediate_Offset (iword (&16))) *)
  0x9bcb7d6b;       (* arm_UMULH X11 X11 X11 *)
  0x9b0d7dac;       (* arm_MUL X12 X13 X13 *)
  0x9bcd7dad;       (* arm_UMULH X13 X13 X13 *)
  0x93d1fdd1;       (* arm_EXTR X17 X14 X17 63 *)
  0xa9005053;       (* arm_STP X19 X20 X2 (Immediate_Offset (iword (&0))) *)
  0xba110157;       (* arm_ADCS X23 X10 X17 *)
  0x93cefdee;       (* arm_EXTR X14 X15 X14 63 *)
  0xa9015855;       (* arm_STP X21 X22 X2 (Immediate_Offset (iword (&16))) *)
  0xba0e0178;       (* arm_ADCS X24 X11 X14 *)
  0xa943b851;       (* arm_LDP X17 X14 X2 (Immediate_Offset (iword (&56))) *)
  0x93cffe0f;       (* arm_EXTR X15 X16 X15 63 *)
  0xba0f0199;       (* arm_ADCS X25 X12 X15 *)
  0x93d0fe30;       (* arm_EXTR X16 X17 X16 63 *)
  0xba1001ba;       (* arm_ADCS X26 X13 X16 *)
  0xa944c04f;       (* arm_LDP X15 X16 X2 (Immediate_Offset (iword (&72))) *)
  0x9b077ce6;       (* arm_MUL X6 X7 X7 *)
  0xa8c1342b;       (* arm_LDP X11 X13 X1 (Postimmediate_Offset (iword (&16))) *)
  0x9bc77ce7;       (* arm_UMULH X7 X7 X7 *)
  0x9b097d28;       (* arm_MUL X8 X9 X9 *)
  0x9bc97d29;       (* arm_UMULH X9 X9 X9 *)
  0xa9026057;       (* arm_STP X23 X24 X2 (Immediate_Offset (iword (&32))) *)
  0x93d1fdd1;       (* arm_EXTR X17 X14 X17 63 *)
  0xa9036859;       (* arm_STP X25 X26 X2 (Immediate_Offset (iword (&48))) *)
  0x91010042;       (* arm_ADD X2 X2 (rvalue (word 64)) *)
  0xba1100d3;       (* arm_ADCS X19 X6 X17 *)
  0x93cefdee;       (* arm_EXTR X14 X15 X14 63 *)
  0xba0e00f4;       (* arm_ADCS X20 X7 X14 *)
  0xa941b851;       (* arm_LDP X17 X14 X2 (Immediate_Offset (iword (&24))) *)
  0x93cffe0f;       (* arm_EXTR X15 X16 X15 63 *)
  0xb5fffb9b;       (* arm_CBNZ X27 (word 2097008) *)
  0xa94693a1;       (* arm_LDP X1 X4 X29 (Immediate_Offset (iword (&104))) *)
  0xba0f0115;       (* arm_ADCS X21 X8 X15 *)
  0x93d0fe30;       (* arm_EXTR X16 X17 X16 63 *)
  0xba100136;       (* arm_ADCS X22 X9 X16 *)
  0xa942c04f;       (* arm_LDP X15 X16 X2 (Immediate_Offset (iword (&40))) *)
  0x9b0b7d6a;       (* arm_MUL X10 X11 X11 *)
  0x9bcb7d6b;       (* arm_UMULH X11 X11 X11 *)
  0xa9005053;       (* arm_STP X19 X20 X2 (Immediate_Offset (iword (&0))) *)
  0x9b0d7dac;       (* arm_MUL X12 X13 X13 *)
  0x9bcd7dad;       (* arm_UMULH X13 X13 X13 *)
  0xa9015855;       (* arm_STP X21 X22 X2 (Immediate_Offset (iword (&16))) *)
  0x93d1fdd1;       (* arm_EXTR X17 X14 X17 63 *)
  0xba110157;       (* arm_ADCS X23 X10 X17 *)
  0x93cefdee;       (* arm_EXTR X14 X15 X14 63 *)
  0xa94053f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  0xba0e0178;       (* arm_ADCS X24 X11 X14 *)
  0x93cffe0f;       (* arm_EXTR X15 X16 X15 63 *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xba0f0199;       (* arm_ADCS X25 X12 X15 *)
  0x93d0fff0;       (* arm_EXTR X16 XZR X16 63 *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0x9a1001ba;       (* arm_ADC X26 X13 X16 *)
  0xa9422c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&32))) *)
  0x9b137c9c;       (* arm_MUL X28 X4 X19 *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0x8b050023;       (* arm_ADD X3 X1 X5 *)
  0xa9415bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa9026057;       (* arm_STP X23 X24 X2 (Immediate_Offset (iword (&32))) *)
  0xa94263f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  0xa9036859;       (* arm_STP X25 X26 X2 (Immediate_Offset (iword (&48))) *)
  0xa9436bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&48))) *)
  0x91010021;       (* arm_ADD X1 X1 (rvalue (word 64)) *)
  0xaa1f03fe;       (* arm_MOV X30 XZR *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0xd280011b;       (* arm_MOV X27 (rvalue (word 8)) *)
  0x9b1c7cef;       (* arm_MUL X15 X7 X28 *)
  0xd100077b;       (* arm_SUB X27 X27 (rvalue (word 1)) *)
  0x9b1c7d10;       (* arm_MUL X16 X8 X28 *)
  0xf800845c;       (* arm_STR X28 X2 (Postimmediate_Offset (word 8)) *)
  0x9b1c7d31;       (* arm_MUL X17 X9 X28 *)
  0xf100067f;       (* arm_CMP X19 (rvalue (word 1)) *)
  0x9b1c7d4e;       (* arm_MUL X14 X10 X28 *)
  0xba0f0293;       (* arm_ADCS X19 X20 X15 *)
  0x9b1c7d6f;       (* arm_MUL X15 X11 X28 *)
  0xba1002b4;       (* arm_ADCS X20 X21 X16 *)
  0x9b1c7d90;       (* arm_MUL X16 X12 X28 *)
  0xba1102d5;       (* arm_ADCS X21 X22 X17 *)
  0x9b1c7db1;       (* arm_MUL X17 X13 X28 *)
  0xba0e02f6;       (* arm_ADCS X22 X23 X14 *)
  0x9bdc7cce;       (* arm_UMULH X14 X6 X28 *)
  0xba0f0317;       (* arm_ADCS X23 X24 X15 *)
  0x9bdc7cef;       (* arm_UMULH X15 X7 X28 *)
  0xba100338;       (* arm_ADCS X24 X25 X16 *)
  0x9bdc7d10;       (* arm_UMULH X16 X8 X28 *)
  0xba110359;       (* arm_ADCS X25 X26 X17 *)
  0x9bdc7d31;       (* arm_UMULH X17 X9 X28 *)
  0x9a1f03fa;       (* arm_ADC X26 XZR XZR *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x9bdc7d4e;       (* arm_UMULH X14 X10 X28 *)
  0xba0f0294;       (* arm_ADCS X20 X20 X15 *)
  0x9bdc7d6f;       (* arm_UMULH X15 X11 X28 *)
  0xba1002b5;       (* arm_ADCS X21 X21 X16 *)
  0x9bdc7d90;       (* arm_UMULH X16 X12 X28 *)
  0xba1102d6;       (* arm_ADCS X22 X22 X17 *)
  0x9bdc7db1;       (* arm_UMULH X17 X13 X28 *)
  0x9b137c9c;       (* arm_MUL X28 X4 X19 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0xba100339;       (* arm_ADCS X25 X25 X16 *)
  0x9a11035a;       (* arm_ADC X26 X26 X17 *)
  0xb5fffbbb;       (* arm_CBNZ X27 (word 2097012) *)
  0xa9403c4e;       (* arm_LDP X14 X15 X2 (Immediate_Offset (iword (&0))) *)
  0xa9414450;       (* arm_LDP X16 X17 X2 (Immediate_Offset (iword (&16))) *)
  0xaa0203e0;       (* arm_MOV X0 X2 *)
  0xcb01007b;       (* arm_SUB X27 X3 X1 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0xba0f0294;       (* arm_ADCS X20 X20 X15 *)
  0xa9423c4e;       (* arm_LDP X14 X15 X2 (Immediate_Offset (iword (&32))) *)
  0xba1002b5;       (* arm_ADCS X21 X21 X16 *)
  0xba1102d6;       (* arm_ADCS X22 X22 X17 *)
  0xa9434450;       (* arm_LDP X16 X17 X2 (Immediate_Offset (iword (&48))) *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0xba100339;       (* arm_ADCS X25 X25 X16 *)
  0xba11035a;       (* arm_ADCS X26 X26 X17 *)
  0xb400163b;       (* arm_CBZ X27 (word 708) *)
  0xf85c0044;       (* arm_LDR X4 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xa9422c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&32))) *)
  0x928007fb;       (* arm_MOVN X27 (word 63) 0 *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0x91010021;       (* arm_ADD X1 X1 (rvalue (word 64)) *)
  0x9b047cce;       (* arm_MUL X14 X6 X4 *)
  0x9a1f03fc;       (* arm_ADC X28 XZR XZR *)
  0x9b047cef;       (* arm_MUL X15 X7 X4 *)
  0x9100237b;       (* arm_ADD X27 X27 (rvalue (word 8)) *)
  0x9b047d10;       (* arm_MUL X16 X8 X4 *)
  0x9b047d31;       (* arm_MUL X17 X9 X4 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x9b047d4e;       (* arm_MUL X14 X10 X4 *)
  0xba0f0294;       (* arm_ADCS X20 X20 X15 *)
  0x9b047d6f;       (* arm_MUL X15 X11 X4 *)
  0xba1002b5;       (* arm_ADCS X21 X21 X16 *)
  0x9b047d90;       (* arm_MUL X16 X12 X4 *)
  0xba1102d6;       (* arm_ADCS X22 X22 X17 *)
  0x9b047db1;       (* arm_MUL X17 X13 X4 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bc47cce;       (* arm_UMULH X14 X6 X4 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0x9bc47cef;       (* arm_UMULH X15 X7 X4 *)
  0xba100339;       (* arm_ADCS X25 X25 X16 *)
  0x9bc47d10;       (* arm_UMULH X16 X8 X4 *)
  0xba11035a;       (* arm_ADCS X26 X26 X17 *)
  0x9bc47d31;       (* arm_UMULH X17 X9 X4 *)
  0x9a1f039c;       (* arm_ADC X28 X28 XZR *)
  0xf8008453;       (* arm_STR X19 X2 (Postimmediate_Offset (word 8)) *)
  0xab0e0293;       (* arm_ADDS X19 X20 X14 *)
  0x9bc47d4e;       (* arm_UMULH X14 X10 X4 *)
  0xba0f02b4;       (* arm_ADCS X20 X21 X15 *)
  0x9bc47d6f;       (* arm_UMULH X15 X11 X4 *)
  0xba1002d5;       (* arm_ADCS X21 X22 X16 *)
  0x9bc47d90;       (* arm_UMULH X16 X12 X4 *)
  0xba1102f6;       (* arm_ADCS X22 X23 X17 *)
  0x9bc47db1;       (* arm_UMULH X17 X13 X4 *)
  0xf87b6804;       (* arm_LDR X4 X0 (Register_Offset X27) *)
  0xba0e0317;       (* arm_ADCS X23 X24 X14 *)
  0xba0f0338;       (* arm_ADCS X24 X25 X15 *)
  0xba100359;       (* arm_ADCS X25 X26 X16 *)
  0xba11039a;       (* arm_ADCS X26 X28 X17 *)
  0xb5fffb7b;       (* arm_CBNZ X27 (word 2097004) *)
  0xa9401c46;       (* arm_LDP X6 X7 X2 (Immediate_Offset (iword (&0))) *)
  0xcb01007b;       (* arm_SUB X27 X3 X1 *)
  0xcb050070;       (* arm_SUB X16 X3 X5 *)
  0xa9412448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&16))) *)
  0xa9422c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&32))) *)
  0xa943344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&48))) *)
  0xb400023b;       (* arm_CBZ X27 (word 68) *)
  0xf85c0004;       (* arm_LDR X4 X0 (Immediate_Offset (word 18446744073709551552)) *)
  0xab060273;       (* arm_ADDS X19 X19 X6 *)
  0xba070294;       (* arm_ADCS X20 X20 X7 *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xba0802b5;       (* arm_ADCS X21 X21 X8 *)
  0xba0902d6;       (* arm_ADCS X22 X22 X9 *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0xba0b0318;       (* arm_ADCS X24 X24 X11 *)
  0xa9422c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&32))) *)
  0xba0c0339;       (* arm_ADCS X25 X25 X12 *)
  0x928007fb;       (* arm_MOVN X27 (word 63) 0 *)
  0xba0d035a;       (* arm_ADCS X26 X26 X13 *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0x91010021;       (* arm_ADD X1 X1 (rvalue (word 64)) *)
  0x17ffffc4;       (* arm_B (word 268435216) *)
  0xf9403ba4;       (* arm_LDR X4 X29 (Immediate_Offset (word 112)) *)
  0x9101005b;       (* arm_ADD X27 X2 (rvalue (word 64)) *)
  0xf10007df;       (* arm_CMP X30 (rvalue (word 1)) *)
  0xba06026e;       (* arm_ADCS X14 X19 X6 *)
  0xba07028f;       (* arm_ADCS X15 X20 X7 *)
  0xa9405013;       (* arm_LDP X19 X20 X0 (Immediate_Offset (iword (&0))) *)
  0xba0802b5;       (* arm_ADCS X21 X21 X8 *)
  0xa9401e06;       (* arm_LDP X6 X7 X16 (Immediate_Offset (iword (&0))) *)
  0xba0902d6;       (* arm_ADCS X22 X22 X9 *)
  0xa9412608;       (* arm_LDP X8 X9 X16 (Immediate_Offset (iword (&16))) *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0xba0b0318;       (* arm_ADCS X24 X24 X11 *)
  0xa9422e0a;       (* arm_LDP X10 X11 X16 (Immediate_Offset (iword (&32))) *)
  0xba0c0339;       (* arm_ADCS X25 X25 X12 *)
  0xba0d035a;       (* arm_ADCS X26 X26 X13 *)
  0xa943360c;       (* arm_LDP X12 X13 X16 (Immediate_Offset (iword (&48))) *)
  0x91010201;       (* arm_ADD X1 X16 (rvalue (word 64)) *)
  0x9a1f03fe;       (* arm_ADC X30 XZR XZR *)
  0x9b137c9c;       (* arm_MUL X28 X4 X19 *)
  0xa9003c4e;       (* arm_STP X14 X15 X2 (Immediate_Offset (iword (&0))) *)
  0xa9015855;       (* arm_STP X21 X22 X2 (Immediate_Offset (iword (&16))) *)
  0xa9415815;       (* arm_LDP X21 X22 X0 (Immediate_Offset (iword (&16))) *)
  0xa9026057;       (* arm_STP X23 X24 X2 (Immediate_Offset (iword (&32))) *)
  0xa9426017;       (* arm_LDP X23 X24 X0 (Immediate_Offset (iword (&32))) *)
  0xeb1d037f;       (* arm_CMP X27 X29 *)
  0xa9036859;       (* arm_STP X25 X26 X2 (Immediate_Offset (iword (&48))) *)
  0xaa0003e2;       (* arm_MOV X2 X0 *)
  0xa9436819;       (* arm_LDP X25 X26 X0 (Immediate_Offset (iword (&48))) *)
  0xd280011b;       (* arm_MOV X27 (rvalue (word 8)) *)
  0x54ffed81;       (* arm_BNE (word 2096560) *)
  0xf94033a0;       (* arm_LDR X0 X29 (Immediate_Offset (word 96)) *)
  0x91010042;       (* arm_ADD X2 X2 (rvalue (word 64)) *)
  0xeb06026e;       (* arm_SUBS X14 X19 X6 *)
  0xfa07028f;       (* arm_SBCS X15 X20 X7 *)
  0xd10100bb;       (* arm_SUB X27 X5 (rvalue (word 64)) *)
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xfa0802b0;       (* arm_SBCS X16 X21 X8 *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xfa0902d1;       (* arm_SBCS X17 X22 X9 *)
  0xa9003c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&0))) *)
  0xfa0a02ee;       (* arm_SBCS X14 X23 X10 *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xfa0b030f;       (* arm_SBCS X15 X24 X11 *)
  0xa9014410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&16))) *)
  0xfa0c0330;       (* arm_SBCS X16 X25 X12 *)
  0xa9422c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&32))) *)
  0xfa0d0351;       (* arm_SBCS X17 X26 X13 *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0x91010021;       (* arm_ADD X1 X1 (rvalue (word 64)) *)
  0xa9405053;       (* arm_LDP X19 X20 X2 (Immediate_Offset (iword (&0))) *)
  0xd101037b;       (* arm_SUB X27 X27 (rvalue (word 64)) *)
  0xa9415855;       (* arm_LDP X21 X22 X2 (Immediate_Offset (iword (&16))) *)
  0xa9426057;       (* arm_LDP X23 X24 X2 (Immediate_Offset (iword (&32))) *)
  0xa9436859;       (* arm_LDP X25 X26 X2 (Immediate_Offset (iword (&48))) *)
  0x91010042;       (* arm_ADD X2 X2 (rvalue (word 64)) *)
  0xa9023c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&32))) *)
  0xfa06026e;       (* arm_SBCS X14 X19 X6 *)
  0xa9034410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&48))) *)
  0x91010000;       (* arm_ADD X0 X0 (rvalue (word 64)) *)
  0xfa07028f;       (* arm_SBCS X15 X20 X7 *)
  0xb5fffd1b;       (* arm_CBNZ X27 (word 2097056) *)
  0xfa0802b0;       (* arm_SBCS X16 X21 X8 *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x8b2563e1;       (* arm_ADD X1 SP (Extendedreg X5 UXTX) *)
  0xa9401c66;       (* arm_LDP X6 X7 X3 (Immediate_Offset (iword (&0))) *)
  0xfa0902d1;       (* arm_SBCS X17 X22 X9 *)
  0xa9003c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&0))) *)
  0xfa0a02ee;       (* arm_SBCS X14 X23 X10 *)
  0xa9412468;       (* arm_LDP X8 X9 X3 (Immediate_Offset (iword (&16))) *)
  0xfa0b030f;       (* arm_SBCS X15 X24 X11 *)
  0xa9014410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&16))) *)
  0xfa0c0330;       (* arm_SBCS X16 X25 X12 *)
  0xa9405033;       (* arm_LDP X19 X20 X1 (Immediate_Offset (iword (&0))) *)
  0xfa0d0351;       (* arm_SBCS X17 X26 X13 *)
  0xa9415835;       (* arm_LDP X21 X22 X1 (Immediate_Offset (iword (&16))) *)
  0xfa1f03df;       (* arm_SBCS XZR X30 XZR *)
  0xf94007be;       (* arm_LDR X30 X29 (Immediate_Offset (word 8)) *)
  0xa9023c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&32))) *)
  0xa9034410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&48))) *)
  0xd10080bb;       (* arm_SUB X27 X5 (rvalue (word 32)) *)
  0xd100837b;       (* arm_SUB X27 X27 (rvalue (word 32)) *)
  0x9a86326e;       (* arm_CSEL X14 X19 X6 Condition_CC *)
  0xa9007c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&0))) *)
  0x9a87328f;       (* arm_CSEL X15 X20 X7 Condition_CC *)
  0xa9421c66;       (* arm_LDP X6 X7 X3 (Immediate_Offset (iword (&32))) *)
  0xa9425033;       (* arm_LDP X19 X20 X1 (Immediate_Offset (iword (&32))) *)
  0x9a8832b0;       (* arm_CSEL X16 X21 X8 Condition_CC *)
  0xa9017c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&16))) *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0x9a8932d1;       (* arm_CSEL X17 X22 X9 Condition_CC *)
  0xa9432468;       (* arm_LDP X8 X9 X3 (Immediate_Offset (iword (&48))) *)
  0xa9435835;       (* arm_LDP X21 X22 X1 (Immediate_Offset (iword (&48))) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xa9003c6e;       (* arm_STP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0xa9014470;       (* arm_STP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0x91008063;       (* arm_ADD X3 X3 (rvalue (word 32)) *)
  0xa9007c3f;       (* arm_STP XZR XZR X1 (Immediate_Offset (iword (&0))) *)
  0xa9017c3f;       (* arm_STP XZR XZR X1 (Immediate_Offset (iword (&16))) *)
  0xb5fffddb;       (* arm_CBNZ X27 (word 2097080) *)
  0x9a86326e;       (* arm_CSEL X14 X19 X6 Condition_CC *)
  0xa9007c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&0))) *)
  0x9a87328f;       (* arm_CSEL X15 X20 X7 Condition_CC *)
  0xa9017c5f;       (* arm_STP XZR XZR X2 (Immediate_Offset (iword (&16))) *)
  0x9a8832b0;       (* arm_CSEL X16 X21 X8 Condition_CC *)
  0x9a8932d1;       (* arm_CSEL X17 X22 X9 Condition_CC *)
  0xa9003c6e;       (* arm_STP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0xa9014470;       (* arm_STP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0x14000021;       (* arm_B (word 132) *)
  0x9a1f03fc;       (* arm_ADC X28 XZR XZR *)
  0xf94007be;       (* arm_LDR X30 X29 (Immediate_Offset (word 8)) *)
  0xeb060266;       (* arm_SUBS X6 X19 X6 *)
  0xf94033a1;       (* arm_LDR X1 X29 (Immediate_Offset (word 96)) *)
  0xfa070287;       (* arm_SBCS X7 X20 X7 *)
  0xa9007fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&0))) *)
  0xfa0802a8;       (* arm_SBCS X8 X21 X8 *)
  0xa9017fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&16))) *)
  0xfa0902c9;       (* arm_SBCS X9 X22 X9 *)
  0xa9027fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&32))) *)
  0xfa0a02ea;       (* arm_SBCS X10 X23 X10 *)
  0xa9037fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&48))) *)
  0xfa0b030b;       (* arm_SBCS X11 X24 X11 *)
  0xa9047fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&64))) *)
  0xfa0c032c;       (* arm_SBCS X12 X25 X12 *)
  0xa9057fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&80))) *)
  0xfa0d034d;       (* arm_SBCS X13 X26 X13 *)
  0xa9067fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&96))) *)
  0xfa1f039c;       (* arm_SBCS X28 X28 XZR *)
  0xa9077fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&112))) *)
  0x9a863266;       (* arm_CSEL X6 X19 X6 Condition_CC *)
  0x9a873287;       (* arm_CSEL X7 X20 X7 Condition_CC *)
  0x9a8832a8;       (* arm_CSEL X8 X21 X8 Condition_CC *)
  0x9a8932c9;       (* arm_CSEL X9 X22 X9 Condition_CC *)
  0xa9001c26;       (* arm_STP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0x9a8a32ea;       (* arm_CSEL X10 X23 X10 Condition_CC *)
  0x9a8b330b;       (* arm_CSEL X11 X24 X11 Condition_CC *)
  0xa9012428;       (* arm_STP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0x9a8c332c;       (* arm_CSEL X12 X25 X12 Condition_CC *)
  0x9a8d334d;       (* arm_CSEL X13 X26 X13 Condition_CC *)
  0xa9022c2a;       (* arm_STP X10 X11 X1 (Immediate_Offset (iword (&32))) *)
  0xa903342c;       (* arm_STP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0xa94153b3;       (* arm_LDP X19 X20 X29 (Immediate_Offset (iword (&16))) *)
  0x910003bf;       (* arm_ADD SP X29 (rvalue (word 0)) *)
  0xa9425bb5;       (* arm_LDP X21 X22 X29 (Immediate_Offset (iword (&32))) *)
  0xd2800020;       (* arm_MOV X0 (rvalue (word 1)) *)
  0xa94363b7;       (* arm_LDP X23 X24 X29 (Immediate_Offset (iword (&48))) *)
  0xa9446bb9;       (* arm_LDP X25 X26 X29 (Immediate_Offset (iword (&64))) *)
  0xa94573bb;       (* arm_LDP X27 X28 X29 (Immediate_Offset (iword (&80))) *)
  0xf84807fd;       (* arm_LDR X29 SP (Postimmediate_Offset (word 128)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xa9b87bfd;       (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &128))) *)
  0x910003fd;       (* arm_ADD X29 SP (rvalue (word 0)) *)
  0xa90153f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  0xa9025bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&32))) *)
  0xa90363f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&48))) *)
  0xa9046bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&64))) *)
  0xa90573fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&80))) *)
  0xcb256ffa;       (* arm_SUB X26 SP (Shiftedreg (Extendedreg X5 UXTX) LSL 3) *)
  0xd37df0a5;       (* arm_LSL X5 X5 3 *)
  0xf9400084;       (* arm_LDR X4 X4 (Immediate_Offset (word 0)) *)
  0xd100835f;       (* arm_SUB SP X26 (rvalue (word 32)) *)
  0x8b05004a;       (* arm_ADD X10 X2 X5 *)
  0x8b05003b;       (* arm_ADD X27 X1 X5 *)
  0xa9062ba0;       (* arm_STP X0 X10 X29 (Immediate_Offset (iword (&96))) *)
  0xf9400058;       (* arm_LDR X24 X2 (Immediate_Offset (word 0)) *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xaa1f03f3;       (* arm_MOV X19 XZR *)
  0xaa1f03f4;       (* arm_MOV X20 XZR *)
  0xaa1f03f5;       (* arm_MOV X21 XZR *)
  0xaa1f03f6;       (* arm_MOV X22 XZR *)
  0xa9403c6e;       (* arm_LDP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0xa9414470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0xb1008063;       (* arm_ADDS X3 X3 (rvalue (word 32)) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xd280001c;       (* arm_MOV X28 (rvalue (word 0)) *)
  0x910003fa;       (* arm_ADD X26 SP (rvalue (word 0)) *)
  0x9b187cca;       (* arm_MUL X10 X6 X24 *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0x9b187ceb;       (* arm_MUL X11 X7 X24 *)
  0x9100239c;       (* arm_ADD X28 X28 (rvalue (word 8)) *)
  0x9b187d0c;       (* arm_MUL X12 X8 X24 *)
  0x9240139c;       (* arm_AND X28 X28 (rvalue (word 31)) *)
  0x9b187d2d;       (* arm_MUL X13 X9 X24 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bd87cca;       (* arm_UMULH X10 X6 X24 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b047e79;       (* arm_MUL X25 X19 X4 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0x9bd87ceb;       (* arm_UMULH X11 X7 X24 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bd87d0c;       (* arm_UMULH X12 X8 X24 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0x9bd87d2d;       (* arm_UMULH X13 X9 X24 *)
  0xf87c6858;       (* arm_LDR X24 X2 (Register_Offset X28) *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0xf8008759;       (* arm_STR X25 X26 (Postimmediate_Offset (word 8)) *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b197deb;       (* arm_MUL X11 X15 X25 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0x9b197e0c;       (* arm_MUL X12 X16 X25 *)
  0x9a0d02f7;       (* arm_ADC X23 X23 X13 *)
  0x9b197e2d;       (* arm_MUL X13 X17 X25 *)
  0xf100067f;       (* arm_CMP X19 (rvalue (word 1)) *)
  0x9bd97dca;       (* arm_UMULH X10 X14 X25 *)
  0xba0b0293;       (* arm_ADCS X19 X20 X11 *)
  0x9bd97deb;       (* arm_UMULH X11 X15 X25 *)
  0xba0c02b4;       (* arm_ADCS X20 X21 X12 *)
  0x9bd97e0c;       (* arm_UMULH X12 X16 X25 *)
  0xba0d02d5;       (* arm_ADCS X21 X22 X13 *)
  0x9bd97e2d;       (* arm_UMULH X13 X17 X25 *)
  0xba0002f6;       (* arm_ADCS X22 X23 X0 *)
  0x9a1f03e0;       (* arm_ADC X0 XZR XZR *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0xcb01036a;       (* arm_SUB X10 X27 X1 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xb5fffafc;       (* arm_CBNZ X28 (word 2096988) *)
  0xb40023ca;       (* arm_CBZ X10 (word 1144) *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xf94003f9;       (* arm_LDR X25 SP (Immediate_Offset (word 0)) *)
  0xa9403c6e;       (* arm_LDP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0xa9414470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0x91008063;       (* arm_ADD X3 X3 (rvalue (word 32)) *)
  0x9b187cca;       (* arm_MUL X10 X6 X24 *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0x9b187ceb;       (* arm_MUL X11 X7 X24 *)
  0x9100239c;       (* arm_ADD X28 X28 (rvalue (word 8)) *)
  0x9b187d0c;       (* arm_MUL X12 X8 X24 *)
  0x9240139c;       (* arm_AND X28 X28 (rvalue (word 31)) *)
  0x9b187d2d;       (* arm_MUL X13 X9 X24 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bd87cca;       (* arm_UMULH X10 X6 X24 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bd87ceb;       (* arm_UMULH X11 X7 X24 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0x9bd87d0c;       (* arm_UMULH X12 X8 X24 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bd87d2d;       (* arm_UMULH X13 X9 X24 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0xf87c6858;       (* arm_LDR X24 X2 (Register_Offset X28) *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9b197dca;       (* arm_MUL X10 X14 X25 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b197deb;       (* arm_MUL X11 X15 X25 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0x9b197e0c;       (* arm_MUL X12 X16 X25 *)
  0x9a0d02f7;       (* arm_ADC X23 X23 X13 *)
  0x9b197e2d;       (* arm_MUL X13 X17 X25 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bd97dca;       (* arm_UMULH X10 X14 X25 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bd97deb;       (* arm_UMULH X11 X15 X25 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0x9bd97e0c;       (* arm_UMULH X12 X16 X25 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0002f7;       (* arm_ADCS X23 X23 X0 *)
  0x9bd97e2d;       (* arm_UMULH X13 X17 X25 *)
  0x9a1f03e0;       (* arm_ADC X0 XZR XZR *)
  0xf87c6bf9;       (* arm_LDR X25 SP (Register_Offset X28) *)
  0xf8008753;       (* arm_STR X19 X26 (Postimmediate_Offset (word 8)) *)
  0xab0a0293;       (* arm_ADDS X19 X20 X10 *)
  0xcb01036a;       (* arm_SUB X10 X27 X1 *)
  0xba0b02b4;       (* arm_ADCS X20 X21 X11 *)
  0xba0c02d5;       (* arm_ADCS X21 X22 X12 *)
  0xba0d02f6;       (* arm_ADCS X22 X23 X13 *)
  0xb5fffadc;       (* arm_CBNZ X28 (word 2096984) *)
  0xcb05036b;       (* arm_SUB X11 X27 X5 *)
  0xb40001ca;       (* arm_CBZ X10 (word 56) *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xa9403c6e;       (* arm_LDP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0xa9414470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0x91008063;       (* arm_ADD X3 X3 (rvalue (word 32)) *)
  0x17ffffcd;       (* arm_B (word 268435252) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xf8420c58;       (* arm_LDR X24 X2 (Preimmediate_Offset (word 32)) *)
  0x9a1f001e;       (* arm_ADC X30 X0 XZR *)
  0xa9401d66;       (* arm_LDP X6 X7 X11 (Immediate_Offset (iword (&0))) *)
  0xcb050063;       (* arm_SUB X3 X3 X5 *)
  0xa9412568;       (* arm_LDP X8 X9 X11 (Immediate_Offset (iword (&16))) *)
  0x91008161;       (* arm_ADD X1 X11 (rvalue (word 32)) *)
  0xa9005353;       (* arm_STP X19 X20 X26 (Immediate_Offset (iword (&0))) *)
  0xa94253f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&32))) *)
  0xa9015b55;       (* arm_STP X21 X22 X26 (Immediate_Offset (iword (&16))) *)
  0xa9435bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&48))) *)
  0xa9403c6e;       (* arm_LDP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0x910003fa;       (* arm_ADD X26 SP (rvalue (word 0)) *)
  0xa9414470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0xb1008063;       (* arm_ADDS X3 X3 (rvalue (word 32)) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xd503201f;       (* arm_NOP *)
  0x9b187cca;       (* arm_MUL X10 X6 X24 *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0x9b187ceb;       (* arm_MUL X11 X7 X24 *)
  0x9100239c;       (* arm_ADD X28 X28 (rvalue (word 8)) *)
  0x9b187d0c;       (* arm_MUL X12 X8 X24 *)
  0x9240139c;       (* arm_AND X28 X28 (rvalue (word 31)) *)
  0x9b187d2d;       (* arm_MUL X13 X9 X24 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bd87cca;       (* arm_UMULH X10 X6 X24 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b047e79;       (* arm_MUL X25 X19 X4 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0x9bd87ceb;       (* arm_UMULH X11 X7 X24 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bd87d0c;       (* arm_UMULH X12 X8 X24 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0x9bd87d2d;       (* arm_UMULH X13 X9 X24 *)
  0xf87c6858;       (* arm_LDR X24 X2 (Register_Offset X28) *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0xf8008759;       (* arm_STR X25 X26 (Postimmediate_Offset (word 8)) *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b197deb;       (* arm_MUL X11 X15 X25 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0x9b197e0c;       (* arm_MUL X12 X16 X25 *)
  0x9a0d02f7;       (* arm_ADC X23 X23 X13 *)
  0x9b197e2d;       (* arm_MUL X13 X17 X25 *)
  0xf100067f;       (* arm_CMP X19 (rvalue (word 1)) *)
  0x9bd97dca;       (* arm_UMULH X10 X14 X25 *)
  0xba0b0293;       (* arm_ADCS X19 X20 X11 *)
  0x9bd97deb;       (* arm_UMULH X11 X15 X25 *)
  0xba0c02b4;       (* arm_ADCS X20 X21 X12 *)
  0x9bd97e0c;       (* arm_UMULH X12 X16 X25 *)
  0xba0d02d5;       (* arm_ADCS X21 X22 X13 *)
  0x9bd97e2d;       (* arm_UMULH X13 X17 X25 *)
  0xba0002f6;       (* arm_ADCS X22 X23 X0 *)
  0x9a1f03e0;       (* arm_ADC X0 XZR XZR *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xb5fffb1c;       (* arm_CBNZ X28 (word 2096992) *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0xa9422f4a;       (* arm_LDP X10 X11 X26 (Immediate_Offset (iword (&32))) *)
  0xa943374c;       (* arm_LDP X12 X13 X26 (Immediate_Offset (iword (&48))) *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xf94003f9;       (* arm_LDR X25 SP (Immediate_Offset (word 0)) *)
  0xa9403c6e;       (* arm_LDP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0xa9414470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0x91008063;       (* arm_ADD X3 X3 (rvalue (word 32)) *)
  0xd503201f;       (* arm_NOP *)
  0x9b187cca;       (* arm_MUL X10 X6 X24 *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0x9b187ceb;       (* arm_MUL X11 X7 X24 *)
  0x9100239c;       (* arm_ADD X28 X28 (rvalue (word 8)) *)
  0x9b187d0c;       (* arm_MUL X12 X8 X24 *)
  0x9240139c;       (* arm_AND X28 X28 (rvalue (word 31)) *)
  0x9b187d2d;       (* arm_MUL X13 X9 X24 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bd87cca;       (* arm_UMULH X10 X6 X24 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bd87ceb;       (* arm_UMULH X11 X7 X24 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0x9bd87d0c;       (* arm_UMULH X12 X8 X24 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bd87d2d;       (* arm_UMULH X13 X9 X24 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0xf87c6858;       (* arm_LDR X24 X2 (Register_Offset X28) *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9b197dca;       (* arm_MUL X10 X14 X25 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b197deb;       (* arm_MUL X11 X15 X25 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0x9b197e0c;       (* arm_MUL X12 X16 X25 *)
  0x9a0d02f7;       (* arm_ADC X23 X23 X13 *)
  0x9b197e2d;       (* arm_MUL X13 X17 X25 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bd97dca;       (* arm_UMULH X10 X14 X25 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bd97deb;       (* arm_UMULH X11 X15 X25 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0x9bd97e0c;       (* arm_UMULH X12 X16 X25 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bd97e2d;       (* arm_UMULH X13 X17 X25 *)
  0xba0002f7;       (* arm_ADCS X23 X23 X0 *)
  0xf87c6bf9;       (* arm_LDR X25 SP (Register_Offset X28) *)
  0x9a1f03e0;       (* arm_ADC X0 XZR XZR *)
  0xf8008753;       (* arm_STR X19 X26 (Postimmediate_Offset (word 8)) *)
  0xab0a0293;       (* arm_ADDS X19 X20 X10 *)
  0xcb01036a;       (* arm_SUB X10 X27 X1 *)
  0xba0b02b4;       (* arm_ADCS X20 X21 X11 *)
  0xba0c02d5;       (* arm_ADCS X21 X22 X12 *)
  0xba0d02f6;       (* arm_ADCS X22 X23 X13 *)
  0xb5fffadc;       (* arm_CBNZ X28 (word 2096984) *)
  0xcb05006b;       (* arm_SUB X11 X3 X5 *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0xb40001ea;       (* arm_CBZ X10 (word 60) *)
  0xa9422f4a;       (* arm_LDP X10 X11 X26 (Immediate_Offset (iword (&32))) *)
  0xa943374c;       (* arm_LDP X12 X13 X26 (Immediate_Offset (iword (&48))) *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xa9403c6e;       (* arm_LDP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0xa9414470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0x91008063;       (* arm_ADD X3 X3 (rvalue (word 32)) *)
  0x17ffffc6;       (* arm_B (word 268435224) *)
  0xd503201f;       (* arm_NOP *)
  0xa94637ac;       (* arm_LDP X12 X13 X29 (Immediate_Offset (iword (&96))) *)
  0xab1e0273;       (* arm_ADDS X19 X19 X30 *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0xcb050021;       (* arm_SUB X1 X1 X5 *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0xa9005353;       (* arm_STP X19 X20 X26 (Immediate_Offset (iword (&0))) *)
  0xba1f02d6;       (* arm_ADCS X22 X22 XZR *)
  0xa94253f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&32))) *)
  0x9a1f001e;       (* arm_ADC X30 X0 XZR *)
  0xa9015b55;       (* arm_STP X21 X22 X26 (Immediate_Offset (iword (&16))) *)
  0xeb0d005f;       (* arm_CMP X2 X13 *)
  0xa9435bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&48))) *)
  0xa9403d6e;       (* arm_LDP X14 X15 X11 (Immediate_Offset (iword (&0))) *)
  0xa9414570;       (* arm_LDP X16 X17 X11 (Immediate_Offset (iword (&16))) *)
  0x91008163;       (* arm_ADD X3 X11 (rvalue (word 32)) *)
  0x54000100;       (* arm_BEQ (word 32) *)
  0xf9400058;       (* arm_LDR X24 X2 (Immediate_Offset (word 0)) *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xb1008021;       (* arm_ADDS X1 X1 (rvalue (word 32)) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0x910003fa;       (* arm_ADD X26 SP (rvalue (word 0)) *)
  0x17ffff75;       (* arm_B (word 268434900) *)
  0xaa0c03e0;       (* arm_MOV X0 X12 *)
  0xaa0c03fb;       (* arm_MOV X27 X12 *)
  0xeb0e026a;       (* arm_SUBS X10 X19 X14 *)
  0x910103fa;       (* arm_ADD X26 SP (rvalue (word 64)) *)
  0xfa0f028b;       (* arm_SBCS X11 X20 X15 *)
  0xd10080bc;       (* arm_SUB X28 X5 (rvalue (word 32)) *)
  0xfa1002ac;       (* arm_SBCS X12 X21 X16 *)
  0xa9403c6e;       (* arm_LDP X14 X15 X3 (Immediate_Offset (iword (&0))) *)
  0xd100839c;       (* arm_SUB X28 X28 (rvalue (word 32)) *)
  0xa9405353;       (* arm_LDP X19 X20 X26 (Immediate_Offset (iword (&0))) *)
  0xfa1102cd;       (* arm_SBCS X13 X22 X17 *)
  0xa9414470;       (* arm_LDP X16 X17 X3 (Immediate_Offset (iword (&16))) *)
  0x91008063;       (* arm_ADD X3 X3 (rvalue (word 32)) *)
  0xa9415b55;       (* arm_LDP X21 X22 X26 (Immediate_Offset (iword (&16))) *)
  0x9100835a;       (* arm_ADD X26 X26 (rvalue (word 32)) *)
  0xa9002c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xfa0e026a;       (* arm_SBCS X10 X19 X14 *)
  0xa901340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&16))) *)
  0x91008000;       (* arm_ADD X0 X0 (rvalue (word 32)) *)
  0xfa0f028b;       (* arm_SBCS X11 X20 X15 *)
  0xb5fffe5c;       (* arm_CBNZ X28 (word 2097096) *)
  0xfa1002ac;       (* arm_SBCS X12 X21 X16 *)
  0x910003fa;       (* arm_ADD X26 SP (rvalue (word 0)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0xa9401f66;       (* arm_LDP X6 X7 X27 (Immediate_Offset (iword (&0))) *)
  0xfa1102cd;       (* arm_SBCS X13 X22 X17 *)
  0xa9002c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xa9412768;       (* arm_LDP X8 X9 X27 (Immediate_Offset (iword (&16))) *)
  0xa901340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&16))) *)
  0xa9405033;       (* arm_LDP X19 X20 X1 (Immediate_Offset (iword (&0))) *)
  0xa9415835;       (* arm_LDP X21 X22 X1 (Immediate_Offset (iword (&16))) *)
  0xfa1f03df;       (* arm_SBCS XZR X30 XZR *)
  0xf94007be;       (* arm_LDR X30 X29 (Immediate_Offset (word 8)) *)
  0xd10080bc;       (* arm_SUB X28 X5 (rvalue (word 32)) *)
  0xd100839c;       (* arm_SUB X28 X28 (rvalue (word 32)) *)
  0x9a86326a;       (* arm_CSEL X10 X19 X6 Condition_CC *)
  0xa9007f5f;       (* arm_STP XZR XZR X26 (Immediate_Offset (iword (&0))) *)
  0x9a87328b;       (* arm_CSEL X11 X20 X7 Condition_CC *)
  0xa9421f66;       (* arm_LDP X6 X7 X27 (Immediate_Offset (iword (&32))) *)
  0xa9425033;       (* arm_LDP X19 X20 X1 (Immediate_Offset (iword (&32))) *)
  0x9a8832ac;       (* arm_CSEL X12 X21 X8 Condition_CC *)
  0xa9017f5f;       (* arm_STP XZR XZR X26 (Immediate_Offset (iword (&16))) *)
  0x9100835a;       (* arm_ADD X26 X26 (rvalue (word 32)) *)
  0x9a8932cd;       (* arm_CSEL X13 X22 X9 Condition_CC *)
  0xa9432768;       (* arm_LDP X8 X9 X27 (Immediate_Offset (iword (&48))) *)
  0xa9435835;       (* arm_LDP X21 X22 X1 (Immediate_Offset (iword (&48))) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xa9002f6a;       (* arm_STP X10 X11 X27 (Immediate_Offset (iword (&0))) *)
  0xa901376c;       (* arm_STP X12 X13 X27 (Immediate_Offset (iword (&16))) *)
  0x9100837b;       (* arm_ADD X27 X27 (rvalue (word 32)) *)
  0xb5fffe1c;       (* arm_CBNZ X28 (word 2097088) *)
  0x9a86326a;       (* arm_CSEL X10 X19 X6 Condition_CC *)
  0xa9007f5f;       (* arm_STP XZR XZR X26 (Immediate_Offset (iword (&0))) *)
  0x9a87328b;       (* arm_CSEL X11 X20 X7 Condition_CC *)
  0xa9017f5f;       (* arm_STP XZR XZR X26 (Immediate_Offset (iword (&16))) *)
  0x9a8832ac;       (* arm_CSEL X12 X21 X8 Condition_CC *)
  0xa901ff5f;       (* arm_STP XZR XZR X26 (Immediate_Offset (iword (&24))) *)
  0x9a8932cd;       (* arm_CSEL X13 X22 X9 Condition_CC *)
  0xa9027f5f;       (* arm_STP XZR XZR X26 (Immediate_Offset (iword (&32))) *)
  0xa9002f6a;       (* arm_STP X10 X11 X27 (Immediate_Offset (iword (&0))) *)
  0xa901376c;       (* arm_STP X12 X13 X27 (Immediate_Offset (iword (&16))) *)
  0x14000015;       (* arm_B (word 84) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0xf94033a1;       (* arm_LDR X1 X29 (Immediate_Offset (word 96)) *)
  0xeb0e0266;       (* arm_SUBS X6 X19 X14 *)
  0xf94007be;       (* arm_LDR X30 X29 (Immediate_Offset (word 8)) *)
  0xfa0f0287;       (* arm_SBCS X7 X20 X15 *)
  0xa9007fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&0))) *)
  0xfa1002a8;       (* arm_SBCS X8 X21 X16 *)
  0xa9017fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&16))) *)
  0xfa1102c9;       (* arm_SBCS X9 X22 X17 *)
  0xa9027fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&32))) *)
  0xfa1f001f;       (* arm_SBCS XZR X0 XZR *)
  0xa9037fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&48))) *)
  0x9a863266;       (* arm_CSEL X6 X19 X6 Condition_CC *)
  0x9a873287;       (* arm_CSEL X7 X20 X7 Condition_CC *)
  0x9a8832a8;       (* arm_CSEL X8 X21 X8 Condition_CC *)
  0x9a8932c9;       (* arm_CSEL X9 X22 X9 Condition_CC *)
  0xa9001c26;       (* arm_STP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9012428;       (* arm_STP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xa94153b3;       (* arm_LDP X19 X20 X29 (Immediate_Offset (iword (&16))) *)
  0x910003bf;       (* arm_ADD SP X29 (rvalue (word 0)) *)
  0xa9425bb5;       (* arm_LDP X21 X22 X29 (Immediate_Offset (iword (&32))) *)
  0xd2800020;       (* arm_MOV X0 (rvalue (word 1)) *)
  0xa94363b7;       (* arm_LDP X23 X24 X29 (Immediate_Offset (iword (&48))) *)
  0xa9446bb9;       (* arm_LDP X25 X26 X29 (Immediate_Offset (iword (&64))) *)
  0xa94573bb;       (* arm_LDP X27 X28 X29 (Immediate_Offset (iword (&80))) *)
  0xf84807fd;       (* arm_LDR X29 SP (Postimmediate_Offset (word 128)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BN_MUL_MONT_EXEC = ARM_MK_EXEC_RULE bn_mul_mont_mc;;

let LENGTH_BN = REWRITE_CONV[bn_mul_mont_mc] `LENGTH bn_mul_mont_mc` |> CONV_RULE(RAND_CONV LENGTH_CONV);;

let BN_DIGIT_READ = prove
 (`!base k s v i. bignum_from_memory(base,k) s = v /\ i < k
    ==> read (memory :> bytes64(word_add base (word(8*i)))) s = word(bigdigit v i)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY; WORD_VAL]);;

let ALIGN16_AND = prove
 (`!tp:int64 d. aligned 16 tp /\ d < 16
   ==> word_and (word_add tp (word d)) (word 18446744073709551600) = tp`,
  REWRITE_TAC[aligned] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_and (x:int64) (word 18446744073709551600) =
                          word_sub x (word_and x (word 15))`] THEN
  SUBGOAL_THEN `word_and (word_add tp (word d)) (word 15):int64 = word d`
   SUBST1_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `word 15:int64 = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `d < 16 ==> d < 2 EXP 64`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 4 * 2 EXP 60`; MOD_MULT_MOD] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[divides]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let NUM_ARITH_ASM_TAC : tactic =
  fun (asl,w) ->
    let ok th =
      let c = concl th in
      let rec good t =
        if is_conj t then good(lhand t) && good(rand t) else
        (is_eq t && type_of(lhs t) = `:num`) ||
        (is_comb t && is_comb(rator t) &&
         (let f = rator(rator t) in
          f = `(<):num->num->bool` || f = `(<=):num->num->bool`)) ||
        (is_neg t && good(rand t)) in
      good c in
    let ths = filter ok (map snd asl) in
    (MAP_EVERY MP_TAC ths THEN ARITH_TAC) (asl,w);;

let BN_DIGIT_READ_BYTES = prove
 (`!base k s v i. read (memory :> bytes(base,8 * k)) s = v /\ i < k
    ==> read (memory :> bytes64(word_add base (word(8*i)))) s = word(bigdigit v i)`,
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN MESON_TAC[BN_DIGIT_READ]);;

(* From read(memory :> bytes(base,8 * k)) s = v (or the bignum_from_memory
   form), adds read(memory :> bytes64(base + 8*i)) s = word(bigdigit v i). *)

let READ_DIGIT_TAC (base:term) (i:term) : tactic =
  fun (asl,w) ->
    let pat1 = vsubst [base,`base:int64`] `read (memory :> bytes(base,8 * kk)) ss`
    and pat2 = vsubst [base,`base:int64`] `bignum_from_memory(base,kk) ss` in
    let lcs = frees base in
    let th = snd(find (fun (_,th) ->
      let c = concl th in is_eq c &&
      (can (term_match lcs pat1) (lhs c) || can (term_match lcs pat2) (lhs c)))
      asl) in
    let th = if can (term_match lcs pat2) (lhs(concl th)) then th
             else REWRITE_RULE[GSYM BIGNUM_FROM_MEMORY_BYTES] th in
    let l = lhs(concl th) in
    let kt = rand(rand(rator l)) and st = rand l and v = rhs(concl th) in
    let tm = vsubst [base,`base:int64`; st,`s:armstate`; v,`v:num`; i,`i:num`]
      `read (memory :> bytes64(word_add base (word(8*i)))) s = word(bigdigit v i)` in
    (SUBGOAL_THEN tm MP_TAC THENL
      [MATCH_MP_TAC BN_DIGIT_READ THEN EXISTS_TAC kt THEN
       CONJ_TAC THENL [ACCEPT_TAC th; NUM_ARITH_ASM_TAC];
       CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
       REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC]) (asl,w);;

let MONT_Q_CONG = prove
 (`!n w:int64 t:int64.
     (n * val w + 1 == 0) (mod (2 EXP 64))
     ==> (bigdigit n 0 * val(word(val t * val w):int64) + val t == 0)
         (mod (2 EXP 64))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bigdigit; MULT_CLAUSES; EXP; DIV_1; VAL_WORD; DIMINDEX_64] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
  UNDISCH_TAC `(n * val(w:int64) + 1 == 0) (mod (2 EXP 64))` THEN
  SPEC_TAC(`2 EXP 64`,`e:num`) THEN CONV_TAC NUMBER_RULE);;

let LOWWORD_CARRY = prove
 (`!n0 q t:int64 lo:int64.
     (n0 * q + val t == 0) (mod (2 EXP 64)) /\ word(n0 * q) = lo
     ==> val lo + val t = 2 EXP 64 * bitval(1 <= val t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; CONG; MOD_0] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64] THEN
  MP_TAC(ISPEC `t:int64` VAL_BOUND_64) THEN
  MP_TAC(SPECL [`n0 * q:num`; `2 EXP 64`] MOD_LT_EQ) THEN
  ABBREV_TAC `l = (n0 * q) MOD 2 EXP 64` THEN ABBREV_TAC `u = val(t:int64)` THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l + u:num`; `2 EXP 64`] DIVISION) THEN
  ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ; ADD_CLAUSES] THEN
  SUBGOAL_THEN `(l + u) DIV 2 EXP 64 < 2` MP_TAC THENL
   [REWRITE_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    SPEC_TAC(`(l + u) DIV 2 EXP 64`,`c:num`)] THEN
  REWRITE_TAC[ARITH_RULE `c < 2 <=> c = 0 \/ c = 1`] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let WORD_SHL3 = prove
 (`!k. word_shl (word k:int64) 3 = word(8 * k)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM] THEN CONV_TAC NUM_REDUCE_CONV);;

let CMP_ONE_CARRY = prove
 (`!c s:int64 x:int64.
     --(&2 pow 64) * &(bitval c) + &(val s):real = &(val x) - &1
     ==> (c <=> val x = 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `--(e:real) * c + s = x - &1 <=> x + e * c = s + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  MP_TAC(ISPEC `s:int64` VAL_BOUND_64) THEN
  BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let VAL_WORD_BIGDIGIT = prove
 (`!n i. val(word(bigdigit n i):int64) = bigdigit n i`,
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND]);;

let MONT_LOWWORD = prove
 (`!n w:int64 t:int64 q:int64 lo:int64.
     (n * val w + 1 == 0) (mod (2 EXP 64)) /\
     word(val t * val w) = q /\ word(bigdigit n 0 * val q) = lo
     ==> val lo + val t = 2 EXP 64 * bitval(1 <= val t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOWWORD_CARRY THEN
  EXISTS_TAC `bigdigit n 0` THEN EXISTS_TAC `val(q:int64)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `word(val(t:int64) * val(w:int64)):int64 = q` (SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[MONT_Q_CONG]);;

let LOWWORD_TAC t q lo : tactic =
  MP_TAC(SPECL [`n:num`; `w:int64`; t; q; lo] MONT_LOWWORD) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BIGDIGIT]) THEN ASM_REWRITE_TAC[];
    DISCH_TAC];;

let REAL_VAL_BOUND = prove
 (`!x:int64. &0 <= &(val x):real /\ &(val x):real <= &18446744073709551615`,
  GEN_TAC THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND_64) THEN ARITH_TAC);;

let REAL_BITVAL_BOUND = prove
 (`!c. &0 <= &(bitval c):real /\ &(bitval c):real <= &1`,
  GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  REAL_ARITH_TAC);;

let real_atoms_of tm =
  let vs = find_terms (fun t -> match t with
     Comb(Const("real_of_num",_),Comb(Const("val",_),x)) -> type_of x = `:int64`
   | _ -> false) tm
  and bs = find_terms (fun t -> match t with
     Comb(Const("real_of_num",_),Comb(Const("bitval",_),_)) -> true
   | _ -> false) tm in
  setify vs, setify bs;;

(* Linear arithmetic over the real equations and inequalities in the
   assumptions, with word and bit bounds for every atom. *)

let PROD_BOUND = prove
 (`!h:int64 l:int64 x y.
     2 EXP 64 * val h + val l = x * y /\ x < 2 EXP 64 /\ y < 2 EXP 64
     ==> &2 pow 64 * &(val h) + &(val l):real <=
         &340282366920938463426481119284349108225`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC LE_TRANS `(2 EXP 64 - 1) * (2 EXP 64 - 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]);;

(* Adds the real bound of every assumption 2^64 * hi + lo = x * y. *)

let BOUND_LT_TAC : tactic =
  REWRITE_TAC[BIGDIGIT_BOUND; VAL_BOUND_64];;

let PROD_BOUND_RULE th =
  let th1 = MATCH_MP (REWRITE_RULE[IMP_CONJ] PROD_BOUND) th in
  let a1 = fst(dest_imp(concl th1)) in
  let th2 = MP th1 (prove(a1,BOUND_LT_TAC)) in
  let a2 = fst(dest_imp(concl th2)) in
  MP th2 (prove(a2,BOUND_LT_TAC));;

let ADDS_WORD = prove
 (`!c s:int64 x:int64 y.
     &2 pow 64 * &(bitval c) + &(val s):real = &(val x) + &y ==> s = word_add x (word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64]);;

let REAL_PROD_BOUND = prove
 (`!h:int64 l:int64 x:int64 y:int64.
     &2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y)
     ==> &2 pow 64 * &(val h) + &(val l):real <=
         &340282366920938463426481119284349108225`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  TRANS_TAC LE_TRANS `(2 EXP 64 - 1) * (2 EXP 64 - 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[ARITH_RULE `x <= 2 EXP 64 - 1 <=> x < 2 EXP 64`] THEN
    REWRITE_TAC[VAL_BOUND_64]; CONV_TAC NUM_REDUCE_CONV]);;

let ADD_PROD_BOUNDS_TAC : tactic =
  ASSUM_LIST(fun ths ->
    MAP_EVERY (fun th ->
      try ASSUME_TAC(PROD_BOUND_RULE th) with Failure _ ->
      try ASSUME_TAC(MATCH_MP REAL_PROD_BOUND th) with Failure _ -> ALL_TAC) ths);;

let REAL_LINEAR_SPLIT_TAC (cs:term list) : tactic =
  fun (asl,w) ->
    let isreal t =
      (is_eq t && type_of(lhs t) = `:real`) ||
      (is_comb t && is_comb(rator t) &&
       (let f = rator(rator t) in
        f = `(<=):real->real->bool` || f = `(<):real->real->bool`)) in
    let ths = filter (isreal o concl) (map snd asl) in
    let tm = list_mk_conj(w :: map concl ths) in
    let vs,_ = real_atoms_of tm in
    let vths = map (fun t -> SPEC (rand(rand t)) REAL_VAL_BOUND) vs in
    (MAP_EVERY MP_TAC (ths @ vths) THEN
     MAP_EVERY BOOL_CASES_TAC cs THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
     CONV_TAC REAL_ARITH) (asl,w);;

let CARRY_ZERO_TAC (c:term) (cs:term list) : tactic =
  SUBGOAL_THEN (mk_neg c) ASSUME_TAC THENL
   [DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ASSUME c; BITVAL_CLAUSES]) THEN
    REWRITE_TAC[] THEN REAL_LINEAR_SPLIT_TAC cs;
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (mk_neg c); BITVAL_CLAUSES])];;

let LOWDIGITS_TOP = prove
 (`!x p. x < 2 EXP (64 * (p + 1)) ==> x = 2 EXP (64 * p) * bigdigit x p + lowdigits x p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LOWDIGITS_CLAUSES] THEN
  ASM_SIMP_TAC[LOWDIGITS_SELF]);;

let BYTES_STEP = prove
 (`!tp p s. read (memory :> bytes(tp,8 * (p + 1))) s =
            read (memory :> bytes(tp,8 * p)) s +
            2 EXP (64 * p) * val(read (memory :> bytes64(word_add tp (word(8 * p)))) s)`,
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_STEP]);;

let gen_h1_inv = new_definition `gen_h1_inv (k:num) (z:int64) (x:int64) (y:int64)
    (m:int64) (w:int64) (a:num) (b:num) (n:num) (tp:int64) (q0:int64) (j:num) s <=>
   read X0 s = z /\ read X2 s = word_add y (word 8) /\ read X4 s = w /\
   read X5 s = word(8 * k) /\ read SP s = tp /\
   read X1 s = word_add x (word(8 * j)) /\ read X3 s = word_add m (word(8 * j)) /\
   read X9 s = word(bigdigit b 0) /\ read X15 s = q0 /\
   read X21 s = word(8 * (k - j)) /\ read X22 s = word_add tp (word(8 * (j - 2))) /\
   bignum_from_memory(x,k) s = a /\ bignum_from_memory(y,k) s = b /\
   bignum_from_memory(m,k) s = n /\
   2 EXP 64 * val(read X11 s) + val(read X10 s) = bigdigit a (j - 1) * bigdigit b 0 /\
   2 EXP 64 * val(read X17 s) + val(read X16 s) = bigdigit n (j - 1) * val q0 /\
   2 EXP 64 * bignum_from_memory(tp,j - 2) s +
   2 EXP (64 * (j - 1)) * (val(read X7 s) + val(read X13 s)) =
   lowdigits a (j - 1) * bigdigit b 0 + lowdigits n (j - 1) * val q0`;;

let VAL_8K_EQ0 = prove
 (`!k j. k < 2 EXP 58 ==> (val(word(8 * (k - j)):int64) = 0 <=> k <= j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `8 * (k - j) < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN
  ASM_ARITH_TAC);;

let GEN_H1_BODY = prove
 (`!k z x y m a b n w tp q0 j pc.
   2 <= j /\ j < k /\ k < 2 EXP 58 /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x74) /\ gen_h1_inv k z x y m w a b n tp q0 j s)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0xac) /\ gen_h1_inv k z x y m w a b n tp q0 (j + 1) s)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[gen_h1_inv] THEN
  SUBGOAL_THEN `?p. j = p + 2` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `j - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(p + 2) - 2 = p /\ (p + 2) - 1 = p + 1 /\ ((p + 2) + 1) - 2 = p + 1 /\ ((p + 2) + 1) - 1 = p + 2`] THEN
  GHOST_INTRO_TAC `h7:int64` `read X7` THEN GHOST_INTRO_TAC `h13:int64` `read X13` THEN
  GHOST_INTRO_TAC `h11:int64` `read X11` THEN GHOST_INTRO_TAC `l10:int64` `read X10` THEN
  GHOST_INTRO_TAC `h17:int64` `read X17` THEN GHOST_INTRO_TAC `l16:int64` `read X16` THEN
  GHOST_INTRO_TAC `nlo:num` `bignum_from_memory(tp,p)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  READ_DIGIT_TAC `x:int64` `p + 2` THEN READ_DIGIT_TAC `m:int64` `p + 2` THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [2;4;6;7;8;10;11;12] (1--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ADD_PROD_BOUNDS_TAC THEN
  CARRY_ZERO_TAC `carry_s4:bool` [] THEN
  CARRY_ZERO_TAC `carry_s8:bool` [] THEN
  CARRY_ZERO_TAC `carry_s12:bool` [`carry_s6:bool`; `carry_s10:bool`] THEN
  SUBGOAL_THEN `&(val(sum_s10:int64)) + &2 pow 64 * (&(val(sum_s4:int64)) + &(val(sum_s12:int64))):real =
   &(val(h7:int64)) + &(val(h13:int64)) + &(val(l10:int64)) + &(val(l16:int64)) +
   &2 pow 64 * (&(val(h11:int64)) + &(val(h17:int64)))` ASSUME_TAC THENL
  [REAL_LINEAR_SPLIT_TAC []; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BIGDIGIT]) THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `p + 2 < k ==> 8 <= 8 * (k - (p + 2))`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    CONV_TAC WORD_RULE;
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_LINEAR_SPLIT_TAC [];
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_LINEAR_SPLIT_TAC [];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. lowdigits x (p + 2) = 2 EXP (64 * (p + 1)) * bigdigit x (p + 1) + lowdigits x (p + 1)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ARITH_RULE `p + 2 = SUC(p + 1)`] THEN
    GEN_TAC THEN REWRITE_TAC[ADD1; LOWDIGITS_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real` &&
     free_in `sum_s10:int64` (concl th) && free_in `h7:int64` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `nlo:num` (concl th) && free_in `h7:int64` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `l16:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:num`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `l10:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:num`)) THEN
  REWRITE_TAC[ARITH_RULE `64 * (p + 2) = 64 * p + 128 /\ 64 * (p + 1) = 64 * p + 64`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP (64 * p)`,`e:num`) THEN GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING);;

let gen_out_inv = new_definition `gen_out_inv (k:num) (z:int64) (x:int64) (y:int64)
    (m:int64) (w:int64) (a:num) (b:num) (n:num) (tp:int64) (i:num) s <=>
   read X0 s = z /\ read X1 s = x /\ read X2 s = word_add y (word(8 * i)) /\
   read X3 s = m /\ read X4 s = w /\ read X5 s = word(8 * k) /\
   read SP s = tp /\ read X20 s = word(8 * (k - i)) /\
   bignum_from_memory(x,k) s = a /\ bignum_from_memory(y,k) s = b /\
   bignum_from_memory(m,k) s = n /\
   ?q. q < 2 EXP (64 * i) /\
       2 EXP (64 * i) * (2 EXP (64 * k) * val(read X19 s) + bignum_from_memory(tp,k) s) =
       lowdigits b i * a + q * n`;;

let GEN_SKIP1 = prove
 (`!k z x y m a b n w tp q0 pc.
   2 <= k /\ k < 2 EXP 58 /\ a < 2 EXP (64 * k) /\ n < 2 EXP (64 * k) /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0xb0) /\ gen_h1_inv k z x y m w a b n tp q0 k s)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0xdc) /\ gen_out_inv k z x y m w a b n tp 1 s)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[gen_h1_inv; gen_out_inv] THEN
  SUBGOAL_THEN `?p. k = p + 2` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `k - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(p + 2) - 2 = p /\ (p + 2) - 1 = p + 1`] THEN
  GHOST_INTRO_TAC `h7:int64` `read X7` THEN GHOST_INTRO_TAC `h13:int64` `read X13` THEN
  GHOST_INTRO_TAC `h11:int64` `read X11` THEN GHOST_INTRO_TAC `l10:int64` `read X10` THEN
  GHOST_INTRO_TAC `h17:int64` `read X17` THEN GHOST_INTRO_TAC `l16:int64` `read X16` THEN
  GHOST_INTRO_TAC `nlo:num` `bignum_from_memory(tp,p)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [1;3;4;6;7;9] (1--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ADD_PROD_BOUNDS_TAC THEN
  CARRY_ZERO_TAC `carry_s3:bool` [] THEN CARRY_ZERO_TAC `carry_s6:bool` [] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE; CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC; CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  EXISTS_TAC `val(q0:int64)` THEN REWRITE_TAC[VAL_BOUND_64; MULT_CLAUSES; LOWDIGITS_1] THEN
  REWRITE_TAC[ARITH_RULE `p + 2 = (p + 1) + 1`; BYTES_STEP] THEN
  REWRITE_TAC[ARITH_RULE `8 * (p + 1) = 8 * p + 8`] THEN ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN
  MP_TAC(SPECL [`a:num`; `p + 1`] LOWDIGITS_TOP) THEN MP_TAC(SPECL [`n:num`; `p + 1`] LOWDIGITS_TOP) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(p + 1) + 1 = p + 2`] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `&(val(sum_s7:int64)) + &2 pow 64 * (&(val(sum_s9:int64)) + &2 pow 64 * &(bitval carry_s9)):real =
   &(val(h7:int64)) + &(val(h13:int64)) + &(val(l10:int64)) + &(val(l16:int64)) +
   &2 pow 64 * (&(val(h11:int64)) + &(val(h17:int64)))` MP_TAC THENL
  [REAL_LINEAR_SPLIT_TAC []; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `nlo:num` (concl th) && free_in `h7:int64` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `l16:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:num`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `l10:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:num`)) THEN
  REWRITE_TAC[ARITH_RULE `64 * (p + 2) = 64 * p + 128 /\ 64 * (p + 1) = 64 * p + 64`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP (64 * p)`,`e:num`) THEN GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING);;

let BR_TAC exec inv : tactic =
  REWRITE_TAC[inv; BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC exec [1] THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[VAL_8K_EQ0; SUB_REFL] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let GEN_LOOP1 = prove
 (`!k z x y m a b n w tp q0 pc.
   2 <= k /\ k < 2 EXP 58 /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x70) /\ gen_h1_inv k z x y m w a b n tp q0 2 s)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0xb0) /\ gen_h1_inv k z x y m w a b n tp q0 k s)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `k = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[gen_h1_inv; BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD_0] THEN REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ENSURES_WHILE_AUP_TAC `2` `k:num` `pc + 0x74` `pc + 0xac`
   `\j s. gen_h1_inv k z x y m w a b n tp q0 j s` THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    BR_TAC BN_MUL_MONT_EXEC gen_h1_inv;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                  `w:int64`; `tp:int64`; `q0:int64`; `j:num`; `pc:num`] GEN_H1_BODY) THEN
    ASM_REWRITE_TAC[SOME_FLAGS];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BR_TAC BN_MUL_MONT_EXEC gen_h1_inv;
    BR_TAC BN_MUL_MONT_EXEC gen_h1_inv]);;

let gen_in_inv = new_definition `gen_in_inv (k:num) (z:int64) (x:int64) (y:int64)
    (m:int64) (w:int64) (a:num) (b:num) (n:num) (tp:int64) (i:num) (t:num)
    (c19:int64) (qi:int64) (j:num) s <=>
   read X0 s = z /\ read X2 s = word_add y (word(8 * (i + 1))) /\ read X4 s = w /\
   read X5 s = word(8 * k) /\ read SP s = tp /\ read X20 s = word(8 * (k - (i + 1))) /\
   read X19 s = c19 /\ read X9 s = word(bigdigit b i) /\ read X15 s = qi /\
   read X1 s = word_add x (word(8 * j)) /\ read X3 s = word_add m (word(8 * j)) /\
   read X21 s = word(8 * (k - j)) /\ read X22 s = word_add tp (word(8 * (j - 1))) /\
   bignum_from_memory(x,k) s = a /\ bignum_from_memory(y,k) s = b /\
   bignum_from_memory(m,k) s = n /\
   bignum_from_memory(word_add tp (word(8 * (j - 1))),k - (j - 1)) s = highdigits t (j - 1) /\
   2 EXP 64 * val(read X11 s) + val(read X10 s) = bigdigit a (j - 1) * bigdigit b i /\
   2 EXP 64 * val(read X17 s) + val(read X16 s) = bigdigit n (j - 1) * val qi /\
   val(read X13 s) + bitval(read CF s) < 2 EXP 64 /\
   2 EXP 64 * bignum_from_memory(tp,j - 2) s +
   2 EXP (64 * (j - 1)) * (val(read X7 s) + val(read X13 s) + bitval(read CF s)) =
   lowdigits t (j - 1) + lowdigits a (j - 1) * bigdigit b i + lowdigits n (j - 1) * val qi`;;

let GEN_IN_BODY = prove
 (`!k z x y m a b n w tp i t c19 qi j pc.
   2 <= j /\ j < k /\ k < 2 EXP 58 /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x128) /\ gen_in_inv k z x y m w a b n tp i t c19 qi j s)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x16c) /\ gen_in_inv k z x y m w a b n tp i t c19 qi (j + 1) s)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[gen_in_inv] THEN
  SUBGOAL_THEN `?p. j = p + 2` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `j - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(p + 2) - 2 = p /\ (p + 2) - 1 = p + 1 /\ ((p + 2) + 1) - 2 = p + 1 /\ ((p + 2) + 1) - 1 = p + 2`] THEN
  MP_TAC(ISPECL [`tp:int64`; `k - (p + 1)`; `t:num`; `p + 1`; `p + 1`] BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - (p + 1) = 0 <=> ~(p + 2 <= k)`; ARITH_RULE `k - (p + 1) - 1 = k - (p + 2)`;
                  ARITH_RULE `(p + 1) + 1 = p + 2`] THEN
  ASM_SIMP_TAC[ARITH_RULE `p + 2 < k ==> p + 2 <= k`] THEN
  GHOST_INTRO_TAC `h7:int64` `read X7` THEN GHOST_INTRO_TAC `h13:int64` `read X13` THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `h11:int64` `read X11` THEN GHOST_INTRO_TAC `l10:int64` `read X10` THEN
  GHOST_INTRO_TAC `h17:int64` `read X17` THEN GHOST_INTRO_TAC `l16:int64` `read X16` THEN
  GHOST_INTRO_TAC `nlo:num` `bignum_from_memory(tp,p)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  READ_DIGIT_TAC `x:int64` `p + 2` THEN READ_DIGIT_TAC `m:int64` `p + 2` THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [2;4;6;7;9;10;11;13;14;15] (1--16) THEN
  SUBGOAL_THEN `read X22 s16 = word_add (word_add tp (word (8 * p))) (word 16)` MP_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> try rator(lhs(concl th)) = `read X22` with _ -> false)) THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC [17] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ADD_PROD_BOUNDS_TAC THEN
  CARRY_ZERO_TAC `carry_s6:bool` [] THEN
  CARRY_ZERO_TAC `carry_s9:bool` [] THEN
  CARRY_ZERO_TAC `carry_s13:bool` [`carry_s4:bool`; `carry_s11:bool`] THEN
  SUBGOAL_THEN `val(sum_s9:int64) + bitval carry_s15 < 18446744073709551616` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_LT] THEN
   REAL_LINEAR_SPLIT_TAC [`carry_s7:bool`; `carry_s15:bool`]; ALL_TAC] THEN
  SUBGOAL_THEN `~carry_s2` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; BITVAL_CLAUSES])) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BIGDIGIT]) THEN
  SUBGOAL_THEN `&(val(sum_s15:int64)) + &2 pow 64 * (&(val(sum_s13:int64)) + &(val(sum_s9:int64)) + &(bitval carry_s15)):real =
   &(val(h7:int64)) + &(val(h13:int64)) + &(bitval cf) + &(bigdigit t (p + 1)) + &(val(l10:int64)) + &(val(l16:int64)) +
   &2 pow 64 * (&(val(h11:int64)) + &(val(h17:int64)))` ASSUME_TAC THENL
  [REAL_LINEAR_SPLIT_TAC []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `p + 2 < k ==> 8 <= 8 * (k - (p + 2))`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    CONV_TAC WORD_RULE;
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_LINEAR_SPLIT_TAC [];
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_LINEAR_SPLIT_TAC [];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. lowdigits x (p + 2) = 2 EXP (64 * (p + 1)) * bigdigit x (p + 1) + lowdigits x (p + 1)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ARITH_RULE `p + 2 = SUC(p + 1)`] THEN
    GEN_TAC THEN REWRITE_TAC[ADD1; LOWDIGITS_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real` &&
     free_in `sum_s15:int64` (concl th) && free_in `h7:int64` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `nlo:num` (concl th) && free_in `h7:int64` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `l16:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:num`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `l10:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:num`)) THEN
  REWRITE_TAC[ARITH_RULE `64 * (p + 2) = 64 * p + 128 /\ 64 * (p + 1) = 64 * p + 64`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP (64 * p)`,`e:num`) THEN GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING);;

let UMULH_SPLIT = prove
 (`!x y. x < 2 EXP 64 /\ y < 2 EXP 64
         ==> 2 EXP 64 * val(word((x * y) DIV 2 EXP 64):int64) + val(word(x * y):int64) = x * y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(x * y) DIV 2 EXP 64 < 2 EXP 64` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[];
    SPEC_TAC(`x * y:num`,`p:num`) THEN GEN_TAC THEN
    MP_TAC(SPECL [`p:num`; `2 EXP 64`] DIVISION) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

(* The outer loop's prelude, 0xdc to 0x124: y[i], x[0..1] and m[0..1] are
   loaded, t[0] is added to x[0] * y[i], and q = that sum times w. The low
   word of m[0] * q is never computed: it cancels the sum's, so its carry is
   whether the sum is nonzero, which CMP leaves in CF. *)

let GEN_OUT_PRE = prove
 (`!k z x y m a b n w tp i t c19 pc.
   1 <= i /\ i < k /\ 2 <= k /\ k < 2 EXP 58 /\ aligned 16 tp /\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0xdc) /\
          read X0 s = z /\ read X1 s = x /\ read X2 s = word_add y (word(8 * i)) /\
          read X3 s = m /\ read X4 s = w /\ read X5 s = word(8 * k) /\
          read SP s = tp /\ read X20 s = word(8 * (k - i)) /\ read X19 s = c19 /\
          bignum_from_memory(x,k) s = a /\ bignum_from_memory(y,k) s = b /\
          bignum_from_memory(m,k) s = n /\ bignum_from_memory(tp,k) s = t)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x124) /\
          gen_in_inv k z x y m w a b n tp i t c19 (read X15 s) 2 s)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[gen_in_inv] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  READ_DIGIT_TAC `x:int64` `0` THEN READ_DIGIT_TAC `x:int64` `1` THEN
  READ_DIGIT_TAC `m:int64` `0` THEN READ_DIGIT_TAC `m:int64` `1` THEN
  READ_DIGIT_TAC `y:int64` `i:num` THEN READ_DIGIT_TAC `tp:int64` `0` THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [5;9;10;12;16;17] (1--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ADD_PROD_BOUNDS_TAC THEN
  CARRY_ZERO_TAC `carry_s12:bool` [] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BIGDIGIT]) THEN
  ABBREV_TAC `q:int64 = word(val(sum_s10:int64) * val(w:int64))` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BIGDIGIT] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CMP_ONE_CARRY o check (fun th -> let c = concl th in
     is_eq c && type_of(lhs c) = `:real` && free_in `carry_s17:bool` c)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`bigdigit n 0`; `val(q:int64)`] UMULH_SPLIT) THEN
  REWRITE_TAC[BIGDIGIT_BOUND; VAL_BOUND_64] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o PROD_BOUND_RULE o check (fun th -> free_in `val(q:int64)` (concl th) && is_eq(concl th))) THEN
  LOWWORD_TAC `sum_s10:int64` `q:int64` `word(bigdigit n 0 * val(q:int64)):int64` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `i < k ==> 8 <= 8 * (k - i)`] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `2 <= k ==> 16 <= 8 * k`] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    UNDISCH_THEN `read (memory :> bytes (tp,8 * k)) s18 = t` (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_LINEAR_SPLIT_TAC [];
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_LINEAR_SPLIT_TAC [];
    ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; LOWDIGITS_1; MULT_CLAUSES; ADD_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `1 <= x <=> ~(x = 0)`]) THEN
  ABBREV_TAC `cz <=> ~(val(sum_s10:int64) = 0)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REAL_LINEAR_SPLIT_TAC [`cz:bool`]);;
let GEN_IN_LOOP = prove
 (`!k z x y m a b n w tp i t c19 qi pc.
   2 <= k /\ k < 2 EXP 58 /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x124) /\ gen_in_inv k z x y m w a b n tp i t c19 qi 2 s)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x170) /\ gen_in_inv k z x y m w a b n tp i t c19 qi k s)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `k = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[gen_in_inv; BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD_0] THEN REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ENSURES_WHILE_AUP_TAC `2` `k:num` `pc + 0x128` `pc + 0x16c`
   `\j s. gen_in_inv k z x y m w a b n tp i t c19 qi j s` THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    BR_TAC BN_MUL_MONT_EXEC gen_in_inv;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                  `w:int64`; `tp:int64`; `i:num`; `t:num`; `c19:int64`; `qi:int64`; `j:num`; `pc:num`]
                 GEN_IN_BODY) THEN
    ASM_REWRITE_TAC[SOME_FLAGS];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BR_TAC BN_MUL_MONT_EXEC gen_in_inv;
    BR_TAC BN_MUL_MONT_EXEC gen_in_inv]);;
(* Linear arithmetic over the real equations in the assumptions alone, for a
   goal that follows from them without bounds. *)
let REAL_EQS_TAC : tactic =
  fun (asl,w) ->
    let ths = filter (fun th -> let c = concl th in is_eq c && type_of(lhs c) = `:real`)
                (map snd asl) in
    (MAP_EVERY MP_TAC ths THEN CONV_TAC REAL_ARITH) (asl,w);;

(* The outer loop's tail, 0x170 to 0x1ac: the inner loop's last product
   words, t's top word and the old carry word c19 are added in, and the
   accumulator's top two words and its new carry word X19 stored. *)

let GEN_OUT_TAIL = prove
 (`!k z x y m a b n w tp i t c19 qi pc.
   i < k /\ 2 <= k /\ k < 2 EXP 58 /\ a < 2 EXP (64 * k) /\ n < 2 EXP (64 * k) /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x170) /\ gen_in_inv k z x y m w a b n tp i t c19 qi k s)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x1ac) /\
          read X0 s = z /\ read X1 s = x /\ read X2 s = word_add y (word(8 * (i + 1))) /\
          read X3 s = m /\ read X4 s = w /\ read X5 s = word(8 * k) /\
          read SP s = tp /\ read X20 s = word(8 * (k - (i + 1))) /\
          bignum_from_memory(x,k) s = a /\ bignum_from_memory(y,k) s = b /\
          bignum_from_memory(m,k) s = n /\
          2 EXP 64 * (2 EXP (64 * k) * val(read X19 s) + bignum_from_memory(tp,k) s) =
          t + 2 EXP (64 * k) * val c19 + a * bigdigit b i + n * val qi)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[gen_in_inv] THEN
  SUBGOAL_THEN `?p. k = p + 2` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `k - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(p + 2) - 2 = p /\ (p + 2) - 1 = p + 1 /\ (p + 2) - (p + 1) = 1 /\ (p + 2) - (p + 2) = 0`] THEN
  MP_TAC(ISPECL [`tp:int64`; `1`; `t:num`; `p + 1`; `p + 1`] BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `~(1 = 0) /\ 1 - 1 = 0 /\ (p + 1) + 1 = p + 2`; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  REWRITE_TAC[ARITH_RULE `0 = x <=> x = 0`; HIGHDIGITS_EQ_0] THEN
  GHOST_INTRO_TAC `h7:int64` `read X7` THEN GHOST_INTRO_TAC `h13:int64` `read X13` THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `h11:int64` `read X11` THEN GHOST_INTRO_TAC `l10:int64` `read X10` THEN
  GHOST_INTRO_TAC `h17:int64` `read X17` THEN GHOST_INTRO_TAC `l16:int64` `read X16` THEN
  GHOST_INTRO_TAC `nlo:num` `bignum_from_memory(tp,p)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [2;3;5;6;8;10;11;12;13;14] (1--14) THEN
  SUBGOAL_THEN `read X22 s14 = word_add (word_add tp (word (8 * p))) (word 16)` MP_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> try rator(lhs(concl th)) = `read X22` with _ -> false)) THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC [15] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ADD_PROD_BOUNDS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  CARRY_ZERO_TAC `carry_s5:bool` [`carry_s3:bool`] THEN
  CARRY_ZERO_TAC `carry_s11:bool` [`carry_s3:bool`; `carry_s10:bool`] THEN
  CARRY_ZERO_TAC `carry_s14:bool` [`carry_s8:bool`; `carry_s13:bool`] THEN
  REPEAT CONJ_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `&(val(sum_s12:int64)) + &2 pow 64 * &(val(sum_s13:int64)) + &2 pow 128 * &(val(sum_s14:int64)):real =
   &(val(h7:int64)) + &(val(h13:int64)) + &(bitval cf) + &(val(word(bigdigit t (p + 1)):int64)) +
   &(val(l10:int64)) + &(val(l16:int64)) +
   &2 pow 64 * (&(val(h11:int64)) + &(val(h17:int64)) + &(val(c19:int64)))` MP_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~carry_s2`; BITVAL_CLAUSES]) THEN REAL_EQS_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
  REWRITE_TAC[ARITH_RULE `p + 2 = (p + 1) + 1`; BYTES_STEP] THEN
  REWRITE_TAC[ARITH_RULE `8 * (p + 1) = 8 * p + 8`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a:num`; `p + 1`] LOWDIGITS_TOP) THEN MP_TAC(SPECL [`n:num`; `p + 1`] LOWDIGITS_TOP) THEN
  MP_TAC(SPECL [`t:num`; `p + 1`] LOWDIGITS_TOP) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(p + 1) + 1 = p + 2`] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `nlo:num` (concl th) && free_in `h7:int64` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `l16:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:num`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `l10:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:num`)) THEN
  REWRITE_TAC[ARITH_RULE `64 * (p + 2) = 64 * p + 128 /\ 64 * ((p + 1) + 1) = 64 * p + 128 /\ 64 * (p + 1) = 64 * p + 64`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP (64 * p)`,`e:num`) THEN GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING);;
(* Reduces an ensures goal to the theorem th, whose frame it must subsume,
   leaving the implications between their pre- and postconditions. *)
let USE_ENSURES_TAC th : tactic =
  let p,q,c = match snd(strip_comb(concl th)) with
      [_;p;q;c] -> p,q,c | _ -> failwith "USE_ENSURES_TAC" in
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c THEN CONJ_TAC THENL
   [SUBSUMED_MAYCHANGE_TAC;
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    MAP_EVERY EXISTS_TAC [p; q] THEN REWRITE_TAC[th]];;

(* One outer iteration, 0xdc to 0x1ac: with t the accumulator and c19 its
   carry word, it adds x * y[i] + q * m and shifts down a word. *)

let GEN_OUTER = prove
 (`!k z x y m a b n w tp i pc.
   1 <= i /\ i < k /\ 2 <= k /\ k < 2 EXP 58 /\ aligned 16 tp /\
   a < 2 EXP (64 * k) /\ n < 2 EXP (64 * k) /\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0xdc) /\ gen_out_inv k z x y m w a b n tp i s)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x1ac) /\ gen_out_inv k z x y m w a b n tp (i + 1) s)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[gen_out_inv; SOME_FLAGS] THEN
  GHOST_INTRO_TAC `t:num` `bignum_from_memory(tp,k)` THEN
  GHOST_INTRO_TAC `c19:int64` `read X19` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  ENSURES_SEQUENCE_TAC `pc + 0x124`
   `\s. gen_in_inv k z x y m w a b n tp i t c19 (read X15 s) 2 s` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                  `w:int64`; `tp:int64`; `i:num`; `t:num`; `c19:int64`; `pc:num`] GEN_OUT_PRE) THEN
    ASM_REWRITE_TAC[SOME_FLAGS] THEN DISCH_THEN USE_ENSURES_TAC THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GHOST_INTRO_TAC `qi:int64` `read X15` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x170` `\s. gen_in_inv k z x y m w a b n tp i t c19 qi k s` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                  `w:int64`; `tp:int64`; `i:num`; `t:num`; `c19:int64`; `qi:int64`; `pc:num`] GEN_IN_LOOP) THEN
    ASM_REWRITE_TAC[SOME_FLAGS] THEN DISCH_THEN USE_ENSURES_TAC THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                  `w:int64`; `tp:int64`; `i:num`; `t:num`; `c19:int64`; `qi:int64`; `pc:num`] GEN_OUT_TAIL) THEN
    ASM_REWRITE_TAC[SOME_FLAGS] THEN DISCH_THEN USE_ENSURES_TAC THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `q + 2 EXP (64 * i) * val(qi:int64)` THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      MATCH_MP_TAC(ARITH_RULE `q < e /\ e * (q' + 1) <= e * 2 EXP 64 ==> q + e * q' < e * 2 EXP 64`) THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN MP_TAC(ISPEC `qi:int64` VAL_BOUND_64) THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && free_in `qi:int64` (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && free_in `c19:int64` (concl th))) THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      SPEC_TAC(`2 EXP (64 * i)`,`e:num`) THEN GEN_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING]]);;

let SBC_BORROW = prove
 (`!c s:int64 x:int64 b.
     --(&2 pow 64) * &(bitval c) + &(val s):real = &(val x) - &0 - &(bitval b)
     ==> (c <=> val x < bitval b)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `s:int64` VAL_BOUND_64) THEN MP_TAC(ISPEC `x:int64` VAL_BOUND_64) THEN
  BOOL_CASES_TAC `c:bool` THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC);;

(* The final subtraction, 0x1b0 to 0x1e8: z = t - m word by word, then the
   carry word c minus the borrow, which leaves CF clear exactly when the
   accumulator 2^(64k) * c + t is below m. *)

let GEN_SUB = prove
 (`!k z m n tp t c pc.
   2 <= k /\ k < 2 EXP 58 /\ aligned 16 tp /\
   nonoverlapping (z,8 * k) (tp,8 * k) /\
   ALL (nonoverlapping (tp,8 * k)) [(word pc,LENGTH bn_mul_mont_mc); (m,8 * k)] /\
   ALL (nonoverlapping (z,8 * k)) [(word pc,LENGTH bn_mul_mont_mc); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x1b0) /\
          read X0 s = z /\ read X3 s = m /\ read X5 s = word(8 * k) /\
          read SP s = tp /\ read X19 s = c /\
          bignum_from_memory(m,k) s = n /\ bignum_from_memory(tp,k) s = t)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x1e8) /\
          read X0 s = z /\ read X5 s = word(8 * k) /\ read SP s = tp /\
          bignum_from_memory(tp,k) s = t /\
          &(bignum_from_memory(z,k) s):real =
          &2 pow (64 * k) * &(bitval(t < n)) + &t - &n /\
          (read CF s <=> ~(val c < bitval(t < n))))
     (MAYCHANGE [PC; X1; X3; X8; X14; X19; X21; X22; X23] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k)])`,
  let inv = `\i s. read X0 s = z /\ read X5 s = word(8 * k) /\ read SP s = tp /\ read X19 s = c /\
  bignum_from_memory(m,k) s = n /\ bignum_from_memory(tp,k) s = t /\
  read X1 s = word_add z (word(8 * i)) /\ read X3 s = word_add m (word(8 * (i + 1))) /\
  read X22 s = word_add tp (word(8 * (i + 1))) /\ read X21 s = word(8 * (k - (i + 1))) /\
  read X23 s = word(bigdigit t i) /\ read X14 s = word(bigdigit n i) /\
  &(bignum_from_memory(z,i) s):real =
  &2 pow (64 * i) * &(bitval(~read CF s)) + &(lowdigits t i) - &(lowdigits n i)` in
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `t:num` THEN BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  ENSURES_WHILE_UP_TAC `k - 1` `pc + 0x1c4` `pc + 0x1d8` inv THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    (* entry *)
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      READ_DIGIT_TAC `tp:int64` `0` THEN READ_DIGIT_TAC `m:int64` `0` THEN
      ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--5) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `2 <= k ==> 8 <= 8 * k`] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; LOWDIGITS_0] THEN
        VAL_INT64_TAC `8 * k` THEN ASM_SIMP_TAC[ARITH_RULE `2 <= k ==> 8 <= 8 * k`] THEN
        REWRITE_TAC[BITVAL_CLAUSES] THEN REAL_ARITH_TAC];
    (* one word *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      READ_DIGIT_TAC `tp:int64` `i + 1` THEN READ_DIGIT_TAC `m:int64` `i + 1` THEN
      ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [1] (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE; CONV_TAC WORD_RULE;
        ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `i < k - 1 ==> 8 <= 8 * (k - (i + 1))`] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && type_of(lhs c) = `:real` &&
         free_in `sum_s1:int64` c)) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && type_of(lhs c) = `:real` &&
         free_in `cin:bool` c)) THEN
      REWRITE_TAC[VAL_WORD_BIGDIGIT; REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      SPEC_TAC(`(&2 pow (64 * i)):real`,`e:real`) THEN GEN_TAC THEN CONV_TAC REAL_RING;
    (* back edge *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BR_TAC BN_MUL_MONT_EXEC BIGNUM_FROM_MEMORY_BYTES;
    (* exit *)
    SUBGOAL_THEN `?p. k = p + 1` (CHOOSE_THEN SUBST_ALL_TAC) THENL
       [EXISTS_TAC `k - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(p + 1) - 1 = p /\ (p + 1) - (p + 1) = 0`; MULT_CLAUSES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [2;3] (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP SBC_BORROW o check (fun th -> free_in `carry_s3:bool` (concl th) &&
         is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
      SUBGOAL_THEN `&(read (memory :> bytes (z,8 * p)) s4 + 2 EXP (64 * p) * val(sum_s2:int64)):real =
                    &2 pow (64 * (p + 1)) * &(bitval carry_s2) + &t - &n` ASSUME_TAC THENL
       [MP_TAC(SPECL [`t:num`; `p:num`] LOWDIGITS_TOP) THEN MP_TAC(SPECL [`n:num`; `p:num`] LOWDIGITS_TOP) THEN
        ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && type_of(lhs c) = `:real` &&
           free_in `sum_s2:int64` c)) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && type_of(lhs c) = `:real` &&
           free_in `cin:bool` c)) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && lhs c = `t:num`)) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && lhs c = `n:num`)) THEN
        REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (p + 1) = 64 * p + 64`] THEN
        SPEC_TAC(`(&2 pow (64 * p)):real`,`e:real`) THEN GEN_TAC THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN `read (memory :> bytes (z,8 * p)) s4 + 2 EXP (64 * p) * val(sum_s2:int64) < 2 EXP (64 * (p + 1))`
      ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * (p + 1) = 64 * p + 64`; EXP_ADD] THEN
        MATCH_MP_TAC(ARITH_RULE `a < e /\ e * (s + 1) <= e * f ==> a + e * s < e * f`) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND; LE_MULT_LCANCEL] THEN
        MP_TAC(ISPEC `sum_s2:int64` VAL_BOUND_64) THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `carry_s2 <=> t < n` (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_OF_NUM_POW] THEN
      SPEC_TAC(`read (memory :> bytes (z,8 * p)) s4 + 2 EXP (64 * p) * val(sum_s2:int64)`,`d:num`) THEN
      SPEC_TAC(`2 EXP (64 * (p + 1))`,`e:num`) THEN REPEAT GEN_TAC THEN
      BOOL_CASES_TAC `carry_s2:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC]);;

(* The selection, 0x1e8 to 0x224: each word of z becomes t's where CF is
   clear and stays where it is set, and t's word is wiped. *)

let GEN_COPY = prove
 (`!k z tp t d cf pc.
   2 <= k /\ k < 2 EXP 58 /\ aligned 16 tp /\
   nonoverlapping (z,8 * k) (tp,8 * k) /\
   nonoverlapping (tp,8 * k) (word pc,LENGTH bn_mul_mont_mc) /\
   nonoverlapping (z,8 * k) (word pc,LENGTH bn_mul_mont_mc)
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x1e8) /\
          read X0 s = z /\ read X5 s = word(8 * k) /\ read SP s = tp /\
          bignum_from_memory(tp,k) s = t /\ bignum_from_memory(z,k) s = d /\ read CF s = cf)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x224) /\ read SP s = tp /\
          bignum_from_memory(z,k) s = (if cf then d else t))
     (MAYCHANGE [PC; X0; X5; X8; X14; X22; X23] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  let inv = `\i s. read SP s = tp /\ read CF s = cf /\
  read X0 s = word_add z (word(8 * (i + 1))) /\ read X22 s = word_add tp (word(8 * (i + 1))) /\
  read X5 s = word(8 * (k - (i + 1))) /\
  read X23 s = word(bigdigit t i) /\ read X8 s = word(bigdigit d i) /\
  bignum_from_memory(word_add z (word(8 * (i + 1))),k - (i + 1)) s = highdigits d (i + 1) /\
  bignum_from_memory(word_add tp (word(8 * (i + 1))),k - (i + 1)) s = highdigits t (i + 1) /\
  bignum_from_memory(z,i) s = lowdigits (if cf then d else t) i` in
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN] THEN STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `t:num` THEN BIGNUM_TERMRANGE_TAC `k:num` `d:num` THEN
  ENSURES_WHILE_UP_TAC `k - 1` `pc + 0x1fc` `pc + 0x214` inv THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    (* entry *)
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ENSURES_INIT_TAC "s0" THEN
      READ_DIGIT_TAC `tp:int64` `0` THEN READ_DIGIT_TAC `z:int64` `0` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN
      ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--5) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `2 <= k ==> 8 <= 8 * k`] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        UNDISCH_THEN `read (memory :> bytes (z,8 * k)) s5 = d` (SUBST1_TAC o SYM);
        UNDISCH_THEN `read (memory :> bytes (tp,8 * k)) s5 = t` (SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN CONV_TAC NUM_REDUCE_CONV;
    (* one word *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV) [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> ~(k - (i + 1) = 0)`; ARITH_RULE `k - (i + 1) - 1 = k - ((i + 1) + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--4) THEN
      SUBGOAL_THEN `read X22 s4 = word_add (word_add tp (word (8 * i))) (word 16) /\
                    read X0 s4 = word_add (word_add z (word (8 * i))) (word 16)` MP_TAC THENL
      [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> try rator(lhs(concl th)) = `read X22` with _ -> false)) THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> try rator(lhs(concl th)) = `read X0` with _ -> false)) THEN
      STRIP_TAC THEN
      ARM_STEPS_TAC BN_MUL_MONT_EXEC (5--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE;
        ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `i < k - 1 ==> 8 <= 8 * (k - (i + 1))`] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[LOWDIGITS_CLAUSES] THEN BOOL_CASES_TAC `cf:bool` THEN
        REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN ARITH_TAC];
    (* back edge *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BR_TAC BN_MUL_MONT_EXEC BIGNUM_FROM_MEMORY_BYTES;
    (* exit *)
    SUBGOAL_THEN `?p. k = p + 1` (CHOOSE_THEN SUBST_ALL_TAC) THENL
       [EXISTS_TAC `k - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(p + 1) - 1 = p`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `read X22 s0 = word_add (word_add tp (word (8 * p))) (word 8) /\
                    read X0 s0 = word_add (word_add z (word (8 * p))) (word 8)` MP_TAC THENL
      [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> try rator(lhs(concl th)) = `read X22` with _ -> false)) THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> try rator(lhs(concl th)) = `read X0` with _ -> false)) THEN
      STRIP_TAC THEN
      ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      BOOL_CASES_TAC `cf:bool` THEN REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
      CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC LOWDIGITS_TOP THEN ASM_REWRITE_TAC[]]);;
let GEN_FINAL_ARITH = prove
 (`!n t d e cv.
     n < e /\ t < e /\ &d:real = &e * &(bitval(t < n)) + &t - &n /\ e * cv + t < 2 * n
     ==> (if ~(cv < bitval(t < n)) then d else t) = (e * cv + t) MOD n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cv = 0 \/ cv = 1 /\ t < n` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `cv = 0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e * 1 <= e * cv` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `e * cv < e * 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LT_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_CASES_TAC `t < n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; ARITH] THENL
     [ASM_SIMP_TAC[MOD_LT];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `d:num` (concl th))) THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_MUL_RZERO; REAL_ADD_LID] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT; REAL_OF_NUM_EQ] THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; LT_REFL] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
    UNDISCH_TAC `t < n` THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; BITVAL_CLAUSES]) THEN ASSUME_TAC th) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th))))) THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC]);;
let ALIGN16_MASK = prove
 (`!x:int64. aligned 16 (word_and x (word 18446744073709551600))`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIVIDES_MOD] THEN
  MP_TAC(ISPECL [`word_and (x:int64) (word 18446744073709551600)`; `4`] VAL_WORD_AND_MASK_WORD) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_BLAST `word_and (word_and (x:int64) (word 18446744073709551600)) (word 15) = word 0`;
              VAL_WORD_0]);;

let MONT_REDUCE_CONG = prove
 (`!n r t q c. coprime(n,r) /\ r * t = q * n + c
               ==> t MOD n = (inverse_mod n r * c) MOD n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CONG] THEN
  MP_TAC(SPECL [`n:num`; `r:num`] INVERSE_MOD_LMUL) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `r * t = q * n + c` THEN
  SPEC_TAC(`inverse_mod n r`,`i:num`) THEN NUMBER_TAC);;

let NEGMODINV_ODD = prove
 (`!n w. (n * w + 1 == 0) (mod (2 EXP 64)) ==> ODD n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONG_0_DIVIDES] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 divides n * w + 1` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `2 EXP 64` THEN
    ASM_REWRITE_TAC[DIVIDES_2; EVEN_EXP] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[DIVIDES_2; EVEN_ADD; EVEN_MULT; ARITH; GSYM NOT_EVEN] THEN CONV_TAC TAUT);;

(* The first pass's prelude, 0x24 to 0x70: the frame of k words is
   allocated below the saved registers, aligned down to 16 bytes, and
   x[0..1] * y[0] + q0 * m[0..1] begun, as in GEN_OUT_PRE with t = 0. *)

let GEN_PRE = prove
 (`!k z x y m a b n w n0p fp tp pc.
   2 <= k /\ k < 2 EXP 58 /\
   tp = word_and (word_sub fp (word(8 * k))) (word 18446744073709551600) /\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x24) /\ read SP s = fp /\
          read X0 s = z /\ read X1 s = x /\ read X2 s = y /\ read X3 s = m /\
          read X4 s = n0p /\ read X5 s = word k /\
          read (memory :> bytes64 n0p) s = w /\
          bignum_from_memory(x,k) s = a /\ bignum_from_memory(y,k) s = b /\
          bignum_from_memory(m,k) s = n)
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x70) /\
          gen_h1_inv k z x y m w a b n tp (read X15 s) 2 s)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[gen_h1_inv] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  READ_DIGIT_TAC `x:int64` `0` THEN READ_DIGIT_TAC `x:int64` `1` THEN
  READ_DIGIT_TAC `m:int64` `0` THEN READ_DIGIT_TAC `m:int64` `1` THEN
  READ_DIGIT_TAC `y:int64` `0` THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [8;11;16;17;19] (1--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ADD_PROD_BOUNDS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BIGDIGIT]) THEN
  ABBREV_TAC `q:int64 = word(val(mullo_s8:int64) * val(w:int64))` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BIGDIGIT; WORD_SHL3] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CMP_ONE_CARRY o check (fun th -> let c = concl th in
     is_eq c && type_of(lhs c) = `:real` && free_in `carry_s17:bool` c)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`bigdigit n 0`; `val(q:int64)`] UMULH_SPLIT) THEN
  REWRITE_TAC[BIGDIGIT_BOUND; VAL_BOUND_64] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o PROD_BOUND_RULE o check (fun th -> free_in `val(q:int64)` (concl th) && is_eq(concl th))) THEN
  LOWWORD_TAC `mullo_s8:int64` `q:int64` `word(bigdigit n 0 * val(q:int64)):int64` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `1 <= x <=> ~(x = 0)`]) THEN
  ABBREV_TAC `cz <=> ~(val(mullo_s8:int64) = 0)` THEN
  CARRY_ZERO_TAC `carry_s19:bool` [`cz:bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `2 <= k ==> 16 <= 8 * k`] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_LINEAR_SPLIT_TAC [];
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_LINEAR_SPLIT_TAC [];
    ALL_TAC] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; LOWDIGITS_1; MULT_CLAUSES; ADD_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REAL_LINEAR_SPLIT_TAC [`cz:bool`]);;
(* ------------------------------------------------------------------------- *)
(* The generic path from after the frame saves to before the epilogue.        *)
(* ------------------------------------------------------------------------- *)

let GEN_USE_TAC th = MP_TAC th THEN ASM_REWRITE_TAC[ALL; SOME_FLAGS] THEN DISCH_THEN USE_ENSURES_TAC THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];;

let GEN_OUT_BR_TAC : tactic =
  REWRITE_TAC[gen_out_inv] THEN
  GHOST_INTRO_TAC `t:num` `bignum_from_memory(tp,k)` THEN
  GHOST_INTRO_TAC `c19:int64` `read X19` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[VAL_8K_EQ0; SUB_REFL] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY ASM_ARITH_TAC);;

let GEN_BODY = prove
 (`!k z x y m a b n w n0p fp tp pc.
   2 <= k /\ k < 2 EXP 58 /\
   tp = word_and (word_sub fp (word(8 * k))) (word 18446744073709551600) /\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
   nonoverlapping (z,8 * k) (tp,8 * k) /\
   ALL (nonoverlapping (tp,8 * k))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k)] /\
   ALL (nonoverlapping (z,8 * k)) [(word pc,LENGTH bn_mul_mont_mc); (m,8 * k)]
   ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
          read PC s = word(pc + 0x24) /\ read SP s = fp /\
          read X0 s = z /\ read X1 s = x /\ read X2 s = y /\ read X3 s = m /\
          read X4 s = n0p /\ read X5 s = word k /\
          read (memory :> bytes64 n0p) s = w /\
          bignum_from_memory(x,k) s = a /\ bignum_from_memory(y,k) s = b /\
          bignum_from_memory(m,k) s = n)
     (\s. read PC s = word(pc + 0x224) /\ read SP s = tp /\
          (a * b <= 2 EXP (64 * k) * n
           ==> bignum_from_memory(z,k) s = (inverse_mod n (2 EXP (64 * k)) * a * b) MOD n))
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                 X12; X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k)])`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN
  SUBGOAL_THEN `aligned 16 (tp:int64)` ASSUME_TAC THENL [ASM_REWRITE_TAC[ALIGN16_MASK]; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> try lhs(concl th) = `tp:int64` with _ -> false)) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x70` `\s. gen_h1_inv k z x y m w a b n tp (read X15 s) 2 s` THEN CONJ_TAC THENL
   [GEN_USE_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                   `w:int64`; `n0p:int64`; `fp:int64`; `tp:int64`; `pc:num`] GEN_PRE);
    ALL_TAC] THEN
  GHOST_INTRO_TAC `q0:int64` `read X15` THEN
  ENSURES_SEQUENCE_TAC `pc + 0xb0` `\s. gen_h1_inv k z x y m w a b n tp q0 k s` THEN CONJ_TAC THENL
   [GEN_USE_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                   `w:int64`; `tp:int64`; `q0:int64`; `pc:num`] GEN_LOOP1);
    ALL_TAC]) THEN
  (ENSURES_SEQUENCE_TAC `pc + 0x1b0` `\s. gen_out_inv k z x y m w a b n tp k s` THEN CONJ_TAC THENL
   [ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0xdc` `pc + 0x1ac`
     `\i s. gen_out_inv k z x y m w a b n tp i s` THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      GEN_USE_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                     `w:int64`; `tp:int64`; `q0:int64`; `pc:num`] GEN_SKIP1);
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      GEN_USE_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                     `w:int64`; `tp:int64`; `i:num`; `pc:num`] GEN_OUTER);
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN GEN_OUT_BR_TAC;
      GEN_OUT_BR_TAC];
    ALL_TAC]) THEN
  (REWRITE_TAC[gen_out_inv] THEN
  GHOST_INTRO_TAC `t:num` `bignum_from_memory(tp,k)` THEN
  GHOST_INTRO_TAC `c19:int64` `read X19` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `t:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  ENSURES_SEQUENCE_TAC `pc + 0x1e8`
   `\s. read X0 s = z /\ read X5 s = word(8 * k) /\ read SP s = tp /\
        bignum_from_memory(tp,k) s = t /\
        &(bignum_from_memory(z,k) s):real = &2 pow (64 * k) * &(bitval(t < n)) + &t - &n /\
        (read CF s <=> ~(val(c19:int64) < bitval(t < n)))` THEN CONJ_TAC THENL
   [GEN_USE_TAC(SPECL [`k:num`; `z:int64`; `m:int64`; `n:num`; `tp:int64`; `t:num`; `c19:int64`; `pc:num`] GEN_SUB);
    ALL_TAC] THEN
  GHOST_INTRO_TAC `d:num` `bignum_from_memory(z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  MP_TAC(SPECL [`k:num`; `z:int64`; `tp:int64`; `t:num`; `d:num`;
                `~(val(c19:int64) < bitval(t < n))`; `pc:num`] GEN_COPY) THEN
  ASM_REWRITE_TAC[ALL; SOME_FLAGS] THEN DISCH_THEN USE_ENSURES_TAC THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `lowdigits b k = b` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_SIMP_TAC[LOWDIGITS_SELF]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NEGMODINV_ODD) THEN
  SUBGOAL_THEN `2 EXP (64 * k) * val(c19:int64) + t < 2 * n` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP (64 * k) * (2 EXP (64 * k) * val(c19:int64) + t) < 2 EXP (64 * k) * (2 * n)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `q * n < r * n /\ x <= r * n ==> x + q * n < r * (2 * n)`) THEN
      REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `ODD n` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH];
        UNDISCH_TAC `a * b <= 2 EXP (64 * k) * n` THEN ARITH_TAC];
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `t:num`; `d:num`; `2 EXP (64 * k)`; `val(c19:int64)`] GEN_FINAL_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MONT_REDUCE_CONG THEN EXISTS_TAC `q:num` THEN CONJ_TAC THENL
   [REWRITE_TAC[COPRIME_REXP] THEN DISJ1_TAC THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_REWRITE_TAC[COPRIME_2];
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The generic path as a subroutine.                                         *)
(* ------------------------------------------------------------------------- *)

(* The routine saves x29, x30 and x19 to x24 in 64 bytes below the caller's
   16-aligned stack pointer sp, then puts its k-word accumulator tp at
   (sp - 64 - 8k) aligned down to 16: sp - 8k - 64, or 8 bytes lower when k
   is odd. All of it lies in the 8k + 72 bytes below sp. *)

let FRAME_TP = prove
 (`!sp:int64 k.
     aligned 16 sp
     ==> word_and (word_sub (word_sub sp (word 64)) (word(8 * k))) (word 18446744073709551600) =
         word_sub sp (word(8 * k + 64 + 8 * (k MOD 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word_sub sp (word 64)) (word(8 * k)):int64 =
                word_add (word_sub sp (word(8 * k + 64 + 8 * (k MOD 2)))) (word(8 * (k MOD 2)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  MATCH_MP_TAC ALIGN16_AND THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_SUB_EQ; ALIGNED_WORD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONJ_TAC THENL [REWRITE_TAC[DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    MP_TAC(SPECL [`k:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    SPEC_TAC(`k DIV 2`,`q:num`) THEN SPEC_TAC(`k MOD 2`,`r:num`) THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `8 * (q * 2 + r) + 64 + 8 * r = 16 * (q + r + 4)`] THEN
    CONV_TAC NUMBER_RULE;
    MP_TAC(SPECL [`k:num`; `2`] MOD_LT_EQ) THEN ARITH_TAC]);;

(* A width that is not a multiple of four takes neither branch of the
   dispatch at 0x0 to 0xc. *)

let GEN_DISPATCH = prove
 (`!k. k < 2 EXP 64 /\ ~(k MOD 4 = 0)
       ==> ~(val(word_and (word k:int64) (word 7)) = 0) /\
           ~(val(word_and (word k:int64) (word 3)) = 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word 7:int64 = word(2 EXP 3 - 1) /\ word 3:int64 = word(2 EXP 2 - 1)`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `~(k MOD 4 = 0)` THEN
  MP_TAC(SPECL [`k:num`; `4`; `2`] MOD_MOD) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Regions of the stack frame, as offsets below the stack pointer. *)

let SUBFRAME_CONTAINED = prove
 (`!(sp:int64) nn c l.
     l <= c /\ c <= nn /\ nn < 2 EXP 64
     ==> contained_modulo (2 EXP 64) (val(word_sub sp (word c)),l)
                                     (val(word_sub sp (word nn)),nn)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub sp (word c):int64 = word_add (word_sub sp (word nn)) (word(nn - c))`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SPEC_TAC(`word_sub sp (word nn):int64`,`a:int64`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV MOD_DOWN_CONV)) THEN
  GEN_REWRITE_TAC I [CONTAINED_MODULO_MOD2] THEN
  MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN ASM_ARITH_TAC);;

let SUBFRAME = prove
 (`!(sp:int64) nn c l r len.
     l <= c /\ c <= nn /\ nn < 2 EXP 64 /\
     nonoverlapping (word_sub sp (word nn),nn) (r,len)
     ==> nonoverlapping (word_sub sp (word c),l) (r,len) /\
         nonoverlapping (r,len) (word_sub sp (word c),l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  GEN_REWRITE_TAC (RAND_CONV) [NONOVERLAPPING_MODULO_SYM] THEN
  MATCH_MP_TAC(TAUT `p ==> p /\ p`) THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`val(word_sub sp (word nn):int64)`; `nn:num`; `val(r:int64)`; `len:num`] THEN
  ASM_SIMP_TAC[SUBFRAME_CONTAINED; CONTAINED_MODULO_REFL; LE_REFL]);;

let SUBFRAME_DISJ = prove
 (`!(sp:int64) c1 l1 c2 l2.
     l1 <= c1 /\ c1 + l2 <= c2 /\ c2 < 2 EXP 64
     ==> nonoverlapping (word_sub sp (word c1),l1) (word_sub sp (word c2),l2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub sp (word c1):int64 = word_add (word_sub sp (word c2)) (word(c2 - c1)) /\
                word_sub sp (word c2):int64 = word_add (word_sub sp (word c2)) (word 0)`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[WORD_ADD_0] THEN
    SUBGOAL_THEN `c1 <= c2` (fun th -> SIMP_TAC[th; WORD_SUB]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  MP_TAC(ISPECL [`word_sub sp (word c2):int64`; `c2 - c1`; `l1:num`; `0`; `l2:num`]
    NONOVERLAPPING_MODULO_OFFSET_BOTH) THEN
  REWRITE_TAC[DIMINDEX_64] THEN DISCH_THEN MATCH_MP_TAC THEN DISJ2_TAC THEN ASM_ARITH_TAC);;

let SUBFRAME2 = prove
 (`!(sp:int64) nn r len.
     nonoverlapping (word_sub sp (word nn),nn) (r,len)
     ==> !c l. l <= c /\ c <= nn /\ nn < 2 EXP 64
               ==> nonoverlapping (word_sub sp (word c),l) (r,len) /\
                   nonoverlapping (r,len) (word_sub sp (word c),l)`,
  MESON_TAC[SUBFRAME]);;
(* From each assumption that the frame misses a region, that the region at
   c below the stack pointer, of l bytes, misses it too. *)

let FRAME_SPLIT_TAC c l : tactic =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
    TRY(fun g -> (MP_TAC(SPECL [c; l] (MATCH_MP SUBFRAME2 th)) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `k < 2 EXP 58` THEN MP_TAC(SPECL [`k:num`; `2`] MOD_LT_EQ) THEN ARITH_TAC;
          STRIP_TAC]) g)) ths);;

(* The generic path from entry to return. It simulates the dispatch and the
   frame saves, runs GEN_BODY as one step, and simulates the epilogue. The
   flag facts the dispatch leaves are dropped before GEN_BODY, since the
   nonoverlapping prover stalls on them, and the code length is a numeral
   throughout, as the simulator's own checks state it. *)

let BN_MUL_MONT_GENERIC_SUBROUTINE_CORRECT = prove
 (`!z x y m n0p a b n w k pc stackpointer returnaddress.
     2 <= k /\ k < 2 EXP 58 /\ ~(k MOD 4 = 0) /\
     (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [(z,8 * k); (word_sub stackpointer (word(8 * k + 72)),8 * k + 72)]
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k); (n0p,8)] /\
     nonoverlapping (z,8 * k) (word_sub stackpointer (word(8 * k + 72)),8 * k + 72)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [z; x; y; m; n0p; word k] s /\
               read (memory :> bytes64 n0p) s = w /\
               bignum_from_memory (x,k) s = a /\
               bignum_from_memory (y,k) s = b /\
               bignum_from_memory (m,k) s = n)
          (\s. read PC s = returnaddress /\
               read X0 s = word 1 /\
               (a * b <= 2 EXP (64 * k) * n
                ==> bignum_from_memory (z,k) s =
                    (inverse_mod n (2 EXP (64 * k)) * a * b) MOD n))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * k);
                      memory :> bytes(word_sub stackpointer (word(8 * k + 72)),8 * k + 72)])`,
  (MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`;
                       `a:num`; `b:num`; `n:num`; `w:int64`; `k:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] o
    check (fun th -> try fst(dest_pair(lhand(concl th))) = `z:int64` &&
                         fst(dest_pair(rand(concl th))) <> `word pc:int64` &&
                         snd(dest_pair(rand(concl th))) = `8 * k + 72` with _ -> false)) THEN
  FRAME_SPLIT_TAC `64` `64` THEN
  FRAME_SPLIT_TAC `8 * k + 64 + 8 * (k MOD 2)` `8 * k` THEN
  MP_TAC(SPECL [`word_add stackpointer (word 64):int64`; `64`; `64`; `8 * k + 64 + 8 * (k MOD 2)`; `8 * k`] SUBFRAME_DISJ) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `k < 2 EXP 58` THEN MP_TAC(SPECL [`k:num`; `2`] MOD_LT_EQ) THEN ARITH_TAC;
    DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_sub (word_add (sp:int64) (word 64)) (word 64) = sp`]) THEN
  ABBREV_TAC `tp = word_sub (word_add stackpointer (word 64)) (word(8 * k + 64 + 8 * (k MOD 2))):int64` THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(fun th' ->
    if concl th' = concl th then th' else REWRITE_RULE[th] th')) THEN
  FIRST_X_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[GSYM IN_SING] o SYM o
    check (fun th -> try rhs(concl th) = `tp:int64` with _ -> false))) THEN
  (REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> free_in `8 * k + 72` (concl th)))) THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MP_TAC(SPEC `k:num` GEN_DISPATCH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst BN_MUL_MONT_EXEC]) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(word_and (word k:int64) (word 7)) = 0)`]) THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (3--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(word_and (word k:int64) (word 3)) = 0)`]) THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (5--9) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> free_in `word_and (word k:int64)` (concl th))))) THEN
  (MP_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `a:num`; `b:num`; `n:num`;
                `w:int64`; `n0p:int64`; `stackpointer:int64`;
                `tp:int64`;
                `pc:num`] GEN_BODY) THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst BN_MUL_MONT_EXEC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o REWRITE_RULE[IN_SING] o
      check (fun th -> try rator(concl th) = `(IN) (tp:int64)` with _ -> false)) THEN
    MP_TAC(SPECL [`word_add stackpointer (word 64):int64`; `k:num`] FRAME_TP) THEN
    ASM_REWRITE_TAC[WORD_RULE `word_sub (word_add (sp:int64) (word 64)) (word 64) = sp`] THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s10") THEN
  (ARM_STEPS_TAC BN_MUL_MONT_EXEC (11--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
  (FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_SING] o
    check (fun th -> try rator(concl th) = `(IN) (tp:int64)` with _ -> false)) THEN
  ABBREV_TAC `fr = word_sub (word_add stackpointer (word 64)) (word(8 * k + 72)):int64` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `stackpointer:int64 = word_add fr (word(8 * k + 8)) /\
                tp:int64 = word_add fr (word(8 - 8 * (k MOD 2)))`
   (CONJUNCTS_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "fr" THEN
    SUBGOAL_THEN `word(8 - 8 * (k MOD 2)):int64 = word_sub (word 8) (word(8 * (k MOD 2)))`
     SUBST1_TAC THENL
     [REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`k:num`; `2`] MOD_LT_EQ) THEN ASM_ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])) THEN
  (FIRST_X_ASSUM(MP_TAC o check (maychange_term o concl)) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC));;
