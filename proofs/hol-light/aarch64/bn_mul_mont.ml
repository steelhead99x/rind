(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication, aws-lc's aarch64 bn_mul_mont, as rind's build  *)
(* emits it, for every width from two words.                                 *)
(* ========================================================================= *)

(* rind's naked function low::aarch64::mont::bn_mul_mont is aws-lc's
   bn_mul_mont (crypto/fipsmodule/bn/asm/armv8-mont.pl). It dispatches on the
   width k: a multiple of eight goes to __bn_sqr8x_mont when squaring and to
   __bn_mul4x_mont otherwise, as does any other multiple of four, and every
   other width runs the generic path at offset 0x10. The goal is s2n-bignum's
   bignum_montmul specification for all three, and the file's last theorem,
   BN_MUL_MONT_SUBROUTINE_CORRECT, is that for every width from two words.
   BN_MUL_MONT_GENERIC_SUBROUTINE_CORRECT is that, for a width k that is not
   a multiple of four, called with the AAPCS64, it writes to z the Montgomery
   product x * y / 2^(64k) mod m of the k-word x, y and m, given the word at
   n0p is -m^-1 mod 2^64, and returns 1. BN_MUL_MONT_MUL4X_SUBROUTINE_CORRECT
   is the same for a multiple of four, except a multiple of eight with
   x = y, through __bn_mul4x_mont; its section, after the generic path's,
   states its argument. BN_MUL_MONT_SQR8X_SUBROUTINE_CORRECT is the same for
   that last case, through __bn_sqr8x_mont, in the section after. Each
   routine has its own stack frame, and the combined theorem takes the
   largest, the squaring's 16k + 128 bytes, with the 4x path's hypothesis
   that x + 32 and m + 32 do not wrap. As for the x86 routines, the result
   is reduced only when x * y <= 2^(64k) * m, which x, y < m give. The
   generic path's proof is segment lemmas, each an `ensures` between two
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

(* ========================================================================= *)
(* The 4x path: __bn_mul4x_mont, for widths that are a multiple of four.     *)
(* ========================================================================= *)

(* __bn_mul4x_mont runs at offset 0xc20 for a width k = 4K, unless k is a
   multiple of eight and x = y, which goes to __bn_sqr8x_mont. It keeps an
   accumulator t of k words at tp + 32, where tp is the stack pointer after
   it reserves 8k + 32 bytes below its 128-byte save area, and it computes
   the product four words of y at a time. Row j takes y's words 4j to 4j + 3
   (bb) and runs in two halves:

   - The first chunk, four steps i (m4_c0_inv): each multiplies x's low four
     words by bb's word i, adds t's low words, takes the Montgomery quotient
     word q_i = n0 * (low word) mod 2^64, adds q_i times m's low four words,
     which clears the low word, and shifts the window x19 to x22 (plus x0 and
     CF, m4_win) down a word, storing q_i at tp + 8i. Its invariant is the
     exact equation 2^(64i) * window = t's low four words + bb's low i words
     * x's low four + the stored quotients * m's low four.
   - The other chunks l = 1 .. K - 1 (m4_cl_inv): each step i multiplies x's
     and m's chunk l by bb's and the quotients' (mm's) word i, adding the
     accumulator's word, and stores the window's low word back to t. The
     invariant is the same equation, over the 4(l + 1) words processed, with
     the parts of bb and mm not yet applied to chunk l written separately.

   The row's end adds the top carry word (x30) and leaves the relation
   2^(256(j+1)) * (2^(64k) * x30 + t) = b's low 4(j+1) words * a + q * n with
   q < 2^(256(j+1)) (m4_row), which after the last row is the classical
   Montgomery relation 2^(64k) * (2^(64k) * x30 + t) = b * a + q * n with
   q < 2^(64k) (m4_fin). Each word of the window is a sum of products of
   64-bit words with their carries, and the carries the code drops are
   proven zero from the window's bound, as for the generic path. The final
   subtraction writes d = t - n to z four words at a time (m4_sub_inv, an
   exact equation with the borrow), and the selection copies t or d to z by
   the borrow and x30, wiping t (m4_sel_inv). M4_FINAL_ARITH shows the
   selected value is (a * b / 2^(64k)) mod n when a * b <= 2^(64k) * n.

   The code needs x + 32 and m + 32 not to wrap: a row's first ADC reads
   the carry of an ADDS adding 32 to m's pointer (the first two rows, at
   0xc80 and 0xe74) or to x's (the rows after, at 0x10a0). Width four has
   no other chunks or later rows, so its only row ends at 0xd34 and goes
   straight to the final subtraction (M4_FINAL4). *)

let m4_win = new_definition
 `m4_win s = val(read X19 s) + 2 EXP 64 * val(read X20 s) + 2 EXP 128 * val(read X21 s) +
             2 EXP 192 * val(read X22 s) + 2 EXP 256 * (val(read X0 s) + bitval(read CF s))`;;

(* Facts that hold from the prelude to the final subtraction: the width,
   pointers and n0, the saved return address and the two words the prelude
   stores in the frame, and the inputs. *)
let m4_frame = new_definition `m4_frame (k:num) (z:int64) (x:int64) (y:int64) (m:int64)
    (w:int64) (a:num) (b:num) (n:num) (tp:int64) (fr:int64) (ra:int64) s <=>
   read X4 s = w /\ read X5 s = word(8 * k) /\ read X27 s = word_add x (word(8 * k)) /\
   read SP s = tp /\ read X29 s = fr /\
   read (memory :> bytes64(word_add fr (word 8))) s = ra /\
   read (memory :> bytes64(word_add fr (word 96))) s = z /\
   read (memory :> bytes64(word_add fr (word 104))) s = word_add y (word(8 * k)) /\
   bignum_from_memory(x,k) s = a /\ bignum_from_memory(y,k) s = b /\
   bignum_from_memory(m,k) s = n`;;

let m4_c0_inv = new_definition `m4_c0_inv (f:bool) (k:num) (z:int64) (x:int64) (y:int64) (m:int64)
    (w:int64) (a:num) (b:num) (n:num) (tp:int64) (fr:int64) (ra:int64) (c30:int64) (t:num)
    (j:num) (bb:num) (i:num) s <=>
   m4_frame k z x y m w a b n tp fr ra s /\ read X30 s = c30 /\
   read X1 s = word_add x (word 32) /\ read X3 s = word_add m (word 32) /\
   read X2 s = word_add y (word(32 * j)) /\
   read X26 s = word_add tp (word(8 * i)) /\ read X28 s = word(8 * (i MOD 4)) /\
   read X24 s = word(bigdigit bb (i MOD 4)) /\
   read X6 s = word(bigdigit a 0) /\ read X7 s = word(bigdigit a 1) /\
   read X8 s = word(bigdigit a 2) /\ read X9 s = word(bigdigit a 3) /\
   read X14 s = word(bigdigit n 0) /\ read X15 s = word(bigdigit n 1) /\
   read X16 s = word(bigdigit n 2) /\ read X17 s = word(bigdigit n 3) /\
   (f /\ 0 < i ==> read X10 s = word(8 * k - 32)) /\
   val(read X0 s) <= 1 /\
   (f \/ bignum_from_memory(word_add tp (word 32),k) s = t) /\
   2 EXP (64 * i) * m4_win s =
   lowdigits t 4 + lowdigits bb i * lowdigits a 4 + bignum_from_memory(tp,i) s * lowdigits n 4`;;

let m4_cl_inv = new_definition `m4_cl_inv (f:bool) (k:num) (z:int64) (x:int64) (y:int64) (m:int64)
    (w:int64) (a:num) (b:num) (n:num) (tp:int64) (fr:int64) (ra:int64) (c30:int64) (t:num)
    (j:num) (bb:num) (mm:num) (l:num) (i:num) s <=>
   m4_frame k z x y m w a b n tp fr ra s /\ read X30 s = c30 /\
   read X1 s = word_add x (word(32 * (l + 1))) /\ read X3 s = word_add m (word(32 * (l + 1))) /\
   read X2 s = word_add y (word(32 * j)) /\
   read X26 s = word_add tp (word(32 * l + 8 * i)) /\ read X28 s = word(8 * (i MOD 4)) /\
   read X24 s = word(bigdigit bb (i MOD 4)) /\ read X25 s = word(bigdigit mm (i MOD 4)) /\
   read X6 s = word(bigdigit a (4 * l)) /\ read X7 s = word(bigdigit a (4 * l + 1)) /\
   read X8 s = word(bigdigit a (4 * l + 2)) /\ read X9 s = word(bigdigit a (4 * l + 3)) /\
   read X14 s = word(bigdigit n (4 * l)) /\ read X15 s = word(bigdigit n (4 * l + 1)) /\
   read X16 s = word(bigdigit n (4 * l + 2)) /\ read X17 s = word(bigdigit n (4 * l + 3)) /\
   (0 < i ==> read X10 s = word(8 * k - 32 * (l + 1))) /\
   val(read X0 s) <= (if i = 0 then 2 else 1) /\
   bignum_from_memory(tp,4) s = mm /\
   (f \/ bignum_from_memory(word_add tp (word(32 * l + 64)),k - 4 * (l + 1)) s =
         highdigits t (4 * (l + 1))) /\
   2 EXP 256 * bignum_from_memory(word_add tp (word 32),4 * (l - 1) + i) s +
   2 EXP (64 * (4 * l + i)) * m4_win s =
   lowdigits t (4 * l + 4) +
   lowdigits bb i * lowdigits a (4 * l + 4) + 2 EXP (64 * i) * highdigits bb i * lowdigits a (4 * l) +
   lowdigits mm i * lowdigits n (4 * l + 4) + 2 EXP (64 * i) * highdigits mm i * lowdigits n (4 * l)`;;

let WORD_AND31_STEP = prove
 (`!i. i < 4 ==> word_and (word_add (word(8 * i)) (word 8)) (word 31):int64 = word(8 * ((i + 1) MOD 4))`,
  REWRITE_TAC[ARITH_RULE `i < 4 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let M4_CHUNK_DIGIT = prove
 (`!base k s v j r vv.
     read (memory :> bytes(base,8 * k)) s = v /\ 4 * (j + 1) <= k /\ r < 4 /\
     vv = lowdigits (highdigits v (4 * j)) 4
     ==> read (memory :> bytes64(word_add base (word(32 * j + 8 * r)))) s =
         word(bigdigit vv r)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[BIGDIGIT_LOWDIGITS; BIGDIGIT_HIGHDIGITS] THEN
  REWRITE_TAC[ARITH_RULE `32 * j + 8 * r = 8 * (4 * j + r)`] THEN
  MATCH_MP_TAC BN_DIGIT_READ_BYTES THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LOWDIGITS_4 = prove
 (`!a. lowdigits a 4 = bigdigit a 0 + 2 EXP 64 * bigdigit a 1 + 2 EXP 128 * bigdigit a 2 + 2 EXP 192 * bigdigit a 3`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `4 = (((0 + 1) + 1) + 1) + 1`; LOWDIGITS_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let REAL_BOUNDED_TAC (ths:thm list) : tactic =
  fun (asl,w) ->
    let tm = list_mk_conj(w :: map concl ths) in
    let vs,bs = real_atoms_of tm in
    let atoms = vs @ bs in
    let isle t = is_comb t && is_comb(rator t) &&
      (let f = rator(rator t) in f = `(<=):real->real->bool` || f = `(<):real->real->bool`) in
    let bnds = filter (fun th -> let c = concl th in isle c &&
      (let vs',bs' = real_atoms_of c in vs' @ bs' <> [] && forall (fun a -> mem a atoms) (vs' @ bs')))
      (map snd asl) in
    let vths = map (fun t -> SPEC (rand(rand t)) REAL_VAL_BOUND) vs
    and bths = map (fun t -> SPEC (rand(rand t)) REAL_BITVAL_BOUND) bs in
    (MAP_EVERY MP_TAC (ths @ bnds @ vths @ bths) THEN CONV_TAC REAL_ARITH) (asl,w);;

let sum_var n = mk_var("sum_s" ^ string_of_int n,`:int64`);;
let carry_var n = mk_var("carry_s" ^ string_of_int n,`:bool`);;

(* Linear arithmetic over the accumulated equations defining the sums of the
   given steps, and the given extra theorems. *)
let SUMS_EQS_TAC (ns:int list) (extra:thm list) : tactic =
  fun (asl,w) ->
    let vs = map sum_var ns in
    let ths = filter (fun th -> let c = concl th in
      is_eq c && type_of(lhs c) = `:real` && exists (fun v -> free_in v (lhs c)) vs) (map snd asl) in
    (MAP_EVERY MP_TAC (ths @ extra) THEN CONV_TAC REAL_ARITH) (asl,w);;

let REAL_EQS_THEN_TAC (extra:thm list) : tactic =
  fun (asl,w) ->
    let ths = filter (fun th -> let c = concl th in is_eq c && type_of(lhs c) = `:real`)
                (map snd asl) in
    (MAP_EVERY MP_TAC (ths @ extra) THEN CONV_TAC REAL_ARITH) (asl,w);;

(* Proves ~c from the theorem th, which states it times a large power, and
   the bounds of th's atoms. *)
let NOCARRY_TAC (c:term) (th:thm) : tactic =
  SUBGOAL_THEN (mk_neg c) ASSUME_TAC THENL
   [DISCH_TAC THEN REAL_BOUNDED_TAC [REWRITE_RULE[ASSUME c; BITVAL_CLAUSES] th]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (mk_neg c); BITVAL_CLAUSES]);;

let sums_eqs (ns:int list) asl =
  let vs = map sum_var ns in
  filter (fun th -> let c = concl th in
      is_eq c && type_of(lhs c) = `:real` && exists (fun v -> free_in v (lhs c)) vs) (map snd asl);;

(* ~c, from the equations defining the sums of steps ns with c set, and the
   bounds of their atoms. *)
let NOCARRY_SUMS_TAC (c:term) (ns:int list) : tactic =
  fun (asl,w) ->
    let ths = sums_eqs ns asl in
    (SUBGOAL_THEN (mk_neg c) ASSUME_TAC THENL
      [DISCH_TAC THEN REAL_BOUNDED_TAC (map (REWRITE_RULE[ASSUME c; BITVAL_CLAUSES]) ths); ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (mk_neg c); BITVAL_CLAUSES])) (asl,w);;

let m4_maychange = "MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
                 X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X30; SP] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * k + 32);
                 memory :> bytes(word_add fr (word 96),16)]";;

let m4_nonover = "ALL (nonoverlapping (tp,8 * k + 32))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k);
        (word_add fr (word 8),8); (word_add fr (word 96),16)]";;

let m4_c0_step_tm f base len = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 t j bb i pc.
   i < 4 /\\ 4 * (j + 1) <= k /\\ k < 2 EXP 58 /\\ bb = lowdigits (highdigits b (4 * j)) 4 /\\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_c0_inv %s k z x y m w a b n tp fr ra c30 t j bb i s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_c0_inv %s k z x y m w a b n tp fr ra c30 t j bb (i + 1) s)
     (%s)" m4_nonover base f (base + 4 * len) f m4_maychange);;

let M4_STEP_COMBINE = prove
 (`!e w0 w1 t l bi a4 ql q n4.
     2 EXP 64 * w1 = w0 + a4 * bi + n4 * q /\ e * w0 = t + l * a4 + ql * n4
     ==> (e * 2 EXP 64) * w1 = t + (e * bi + l) * a4 + (ql + e * q) * n4`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MULT_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN CONV_TAC NUM_RING);;

let M4_C0_STEP_TAC (row0:bool) (acc2:int list) (n:int) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> try lhs(concl th) = `bb:num` with _ -> false)) THEN
  REWRITE_TAC[m4_c0_inv; m4_frame; m4_win] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `0 < i + 1`] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w19:int64` `read X19` THEN GHOST_INTRO_TAC `w20:int64` `read X20` THEN
  GHOST_INTRO_TAC `w21:int64` `read X21` THEN GHOST_INTRO_TAC `w22:int64` `read X22` THEN
  GHOST_INTRO_TAC `w0:int64` `read X0` THEN
  GHOST_INTRO_TAC `qlo:num` `bignum_from_memory(tp,i)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [1;2;3;5;7;8;10;12;14] (1--17) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try rator(lhs(concl th)) = `read X28` with _ -> false)) THEN
  ASM_SIMP_TAC[WORD_AND31_STEP] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`y:int64`; `k:num`; `s17:armstate`; `b:num`; `j:num`; `(i + 1) MOD 4`; `bb:num`] M4_CHUNK_DIGIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; DISCH_TAC] THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC acc2 (18--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `32 <= 8 * k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   ([CONV_TAC WORD_RULE] @
    (if row0 then
      [REWRITE_TAC[WORD_RULE `word_sub (word_add x a) (word_add x b):int64 = word_sub a b`] THEN
       ASM_SIMP_TAC[WORD_SUB2]] else []) @
    [REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN MP_TAC(SPEC `carry_s35:bool` BITVAL_BOUND) THEN ARITH_TAC;
     ALL_TAC]) THEN
  REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD; LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[BYTES_STEP] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC M4_STEP_COMBINE THEN
  EXISTS_TAC `val(w19:int64) + 2 EXP 64 * val(w20:int64) + 2 EXP 128 * val(w21:int64) +
              2 EXP 192 * val(w22:int64) + 2 EXP 256 * (val(w0:int64) + bitval cf)` THEN
  ASM_REWRITE_TAC[] THEN
  ADD_PROD_BOUNDS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BIGDIGIT; VAL_WORD_BITVAL]) THEN
  REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL; LOWDIGITS_4] THEN
  SUBGOAL_THEN `&(val(w0:int64)):real <= &2` ASSUME_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  NOCARRY_SUMS_TAC `carry_s2:bool` [2] THEN
  SUBGOAL_THEN `&(val(sum_s8:int64)) + &2 pow 64 * &(val(sum_s19:int64)) + &2 pow 128 * &(val(sum_s21:int64)) +
     &2 pow 192 * &(val(sum_s23:int64)) + &2 pow 256 * (&(val(sum_s25:int64)) + &2 pow 64 * &(bitval carry_s25)):real =
     &(val(w19:int64)) + &2 pow 64 * &(val(w20:int64)) + &2 pow 128 * &(val(w21:int64)) + &2 pow 192 * &(val(w22:int64)) +
     (&2 pow 64 * &(val(mulhi_s1:int64)) + &(val(mullo_s1:int64))) +
     &2 pow 64 * (&2 pow 64 * &(val(mulhi_s3:int64)) + &(val(mullo_s3:int64))) +
     &2 pow 128 * (&2 pow 64 * &(val(mulhi_s5:int64)) + &(val(mullo_s5:int64))) +
     &2 pow 192 * (&2 pow 64 * &(val(mulhi_s7:int64)) + &(val(mullo_s7:int64)))` ASSUME_TAC THENL
   [SUMS_EQS_TAC [8;10;12;14;19;21;23;25] []; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if free_in `carry_s25:bool` (concl th) && free_in `w19:int64` (concl th)
                        then NOCARRY_TAC `carry_s25:bool` th else NO_TAC) THEN
  ABBREV_TAC `q:int64 = word(val(sum_s8:int64) * val(w:int64))` THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CMP_ONE_CARRY o check (fun th -> let c = concl th in
     is_eq c && type_of(lhs c) = `:real` && free_in `carry_s27:bool` c)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  LOWWORD_TAC `sum_s8:int64` `q:int64` `mullo_s36:int64` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `1 <= x <=> ~(x = 0)`]) THEN
  ABBREV_TAC `cz <=> ~(val(sum_s8:int64) = 0)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
  REAL_EQS_TAC;;

let M4_C0_STEP_0 = prove(m4_c0_step_tm "T" 0xc90 41,
  M4_C0_STEP_TAC true [19;21;22;23;24;25;26;27;29;31;33;35;36;37;39;40;41] 41);;
let M4_C0_STEP_R = prove(m4_c0_step_tm "F" 0xe80 40,
  M4_C0_STEP_TAC false [19;21;22;23;24;25;26;27;29;31;33;35;36;37;38;39;40] 40);;

(* An ensures whose pre- and postcondition agree holds in no steps. *)
let ENSURES_REFL_TAC : tactic =
  ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let VAL_WORD_8I = prove
 (`!i. 0 < i /\ i < 4 ==> ~(val(word(8 * i):int64) = 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `8 * i < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN ASM_ARITH_TAC);;

let m4_c0_loop_tm f base len = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 t j bb pc.
   4 * (j + 1) <= k /\\ k < 2 EXP 58 /\\ bb = lowdigits (highdigits b (4 * j)) 4 /\\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_c0_inv %s k z x y m w a b n tp fr ra c30 t j bb 0 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_c0_inv %s k z x y m w a b n tp fr ra c30 t j bb 4 s)
     (%s)" m4_nonover base f (base + 4 * len) f m4_maychange);;

let M4_C0_LOOP_TAC (f:string) (step:thm) (base:int) (len:int) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_WHILE_UP_TAC `4` (mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),mk_small_numeral base))
    (mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),mk_small_numeral(base + 4 * len)))
    (parse_term ("\\i s. m4_c0_inv " ^ f ^ " k z x y m w a b n tp fr ra c30 t j bb i s")) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_REFL_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] step) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[m4_c0_inv; m4_frame; m4_win; BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[VAL_WORD_8I];
    ENSURES_REFL_TAC];;

let M4_C0_LOOP_0 = prove(m4_c0_loop_tm "T" 0xc90 41, M4_C0_LOOP_TAC "T" M4_C0_STEP_0 0xc90 41);;
let M4_C0_LOOP_R = prove(m4_c0_loop_tm "F" 0xe80 40, M4_C0_LOOP_TAC "F" M4_C0_STEP_R 0xe80 40);;

let m4_cl_step_tm base len = parse_term (Printf.sprintf
 "!f k z x y m w a b n tp fr ra c30 t j bb mm l i pc.
   1 <= l /\\ 4 * (l + 1) <= k /\\ i < 4 /\\ aligned 16 tp /\\ 4 * (j + 1) <= k /\\ k < 2 EXP 58 /\\
   bb = lowdigits (highdigits b (4 * j)) 4 /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_cl_inv f k z x y m w a b n tp fr ra c30 t j bb mm l i s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_cl_inv f k z x y m w a b n tp fr ra c30 t j bb mm l (i + 1) s)
     (%s)" m4_nonover base (base + 4 * len) m4_maychange);;

let LOWDIGITS_ADD4 = prove
 (`!a p. lowdigits a (p + 4) = lowdigits a p + 2 EXP (64 * p) *
     (bigdigit a p + 2 EXP 64 * bigdigit a (p + 1) + 2 EXP 128 * bigdigit a (p + 2) + 2 EXP 192 * bigdigit a (p + 3))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `p + 4 = (((p + 1) + 1) + 1) + 1`; LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `64 * (p + 1) = 64 * p + 64 /\ 64 * ((p + 1) + 1) = 64 * p + 128 /\
                          64 * (((p + 1) + 1) + 1) = 64 * p + 192 /\ ((p + 1) + 1) + 1 = p + 3 /\ (p + 1) + 1 = p + 2`; EXP_ADD] THEN
  ARITH_TAC);;

let mulhi_var n = mk_var("mulhi_s" ^ string_of_int n,`:int64`);;

(* Linear arithmetic over the equations defining the sums of steps ns and the
   products of steps ps, and the real equations satisfying p. *)
let STEP_EQS_TAC (ns:int list) (ps:int list) (p:term->bool) : tactic =
  fun (asl,w) ->
    let vs = map sum_var ns @ map mulhi_var ps in
    let ths = filter (fun th -> let c = concl th in
      is_eq c && type_of(lhs c) = `:real` && (exists (fun v -> free_in v (lhs c)) vs || p c)) (map snd asl) in
    (MAP_EVERY MP_TAC ths THEN CONV_TAC REAL_ARITH) (asl,w);;

let M4_CL_STEP_TAC (acc2:int list) (xc:int) : tactic =
  let c_xc = carry_var xc in
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> try lhs(concl th) = `bb:num` with _ -> false)) THEN
  REWRITE_TAC[m4_cl_inv; m4_frame; m4_win] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `0 < i + 1`; ARITH_RULE `~(i + 1 = 0)`] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w19:int64` `read X19` THEN GHOST_INTRO_TAC `w20:int64` `read X20` THEN
  GHOST_INTRO_TAC `w21:int64` `read X21` THEN GHOST_INTRO_TAC `w22:int64` `read X22` THEN
  GHOST_INTRO_TAC `w0:int64` `read X0` THEN
  GHOST_INTRO_TAC `elo:num` `bignum_from_memory(word_add tp (word 32),4 * (l - 1) + i)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [1;2;3;5;7;8;10;12;14] (1--16) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try rator(lhs(concl th)) = `read X28` with _ -> false)) THEN
  ASM_SIMP_TAC[WORD_AND31_STEP] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`y:int64`; `k:num`; `s16:armstate`; `b:num`; `j:num`; `(i + 1) MOD 4`; `bb:num`] M4_CHUNK_DIGIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tp:int64`; `4`; `s16:armstate`; `mm:num`; `(i + 1) MOD 4`] BN_DIGIT_READ_BYTES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; DISCH_TAC] THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC acc2 (17--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `32 * (l + 1) <= 8 * k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    REWRITE_TAC[WORD_RULE `word_sub (word_add x a) (word_add x b):int64 = word_sub a b`] THEN
    ASM_SIMP_TAC[WORD_SUB2];
    REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN MP_TAC(SPEC c_xc BITVAL_BOUND) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 * (l - 1) + i + 1 = (4 * (l - 1) + i) + 1`; BYTES_STEP] THEN
  SUBGOAL_THEN `word_add (word_add tp (word 32)) (word (8 * (4 * (l - 1) + i))):int64 = word_add tp (word (32 * l + 8 * i))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (subst [c_xc,`cx:bool`] `val(sum_s26:int64) + 2 EXP 64 * (val(sum_s38:int64) + 2 EXP 64 * val(sum_s40:int64) + 2 EXP 128 * val(sum_s41:int64) +
     2 EXP 192 * val(sum_s42:int64) + 2 EXP 256 * (bitval cx + bitval carry_s42)) =
   (val(w19:int64) + 2 EXP 64 * val(w20:int64) + 2 EXP 128 * val(w21:int64) + 2 EXP 192 * val(w22:int64) +
    2 EXP 256 * (val(w0:int64) + bitval cf)) +
   (bigdigit a (4 * l) + 2 EXP 64 * bigdigit a (4 * l + 1) + 2 EXP 128 * bigdigit a (4 * l + 2) + 2 EXP 192 * bigdigit a (4 * l + 3)) * bigdigit bb i +
   (bigdigit n (4 * l) + 2 EXP 64 * bigdigit n (4 * l + 1) + 2 EXP 128 * bigdigit n (4 * l + 2) + 2 EXP 192 * bigdigit n (4 * l + 3)) * bigdigit mm i`)
  ASSUME_TAC THENL
  [ADD_PROD_BOUNDS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BIGDIGIT; VAL_WORD_BITVAL]) THEN
   SUBGOAL_THEN `&(val(w0:int64)):real <= &2` ASSUME_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_LE] THEN
     FIRST_ASSUM(MP_TAC o check (fun th -> try lhand(concl th) = `val(w0:int64)` && is_cond(rand(concl th)) with _ -> false)) THEN
     COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
   NOCARRY_SUMS_TAC `carry_s2:bool` [2] THEN
   SUBGOAL_THEN `&(val(sum_s8:int64)) + &2 pow 64 * &(val(sum_s18:int64)) + &2 pow 128 * &(val(sum_s20:int64)) +
     &2 pow 192 * &(val(sum_s22:int64)) + &2 pow 256 * (&(val(sum_s24:int64)) + &2 pow 64 * &(bitval carry_s24)):real =
     &(val(w19:int64)) + &2 pow 64 * &(val(w20:int64)) + &2 pow 128 * &(val(w21:int64)) + &2 pow 192 * &(val(w22:int64)) +
     (&2 pow 64 * &(val(mulhi_s1:int64)) + &(val(mullo_s1:int64))) +
     &2 pow 64 * (&2 pow 64 * &(val(mulhi_s3:int64)) + &(val(mullo_s3:int64))) +
     &2 pow 128 * (&2 pow 64 * &(val(mulhi_s5:int64)) + &(val(mullo_s5:int64))) +
     &2 pow 192 * (&2 pow 64 * &(val(mulhi_s7:int64)) + &(val(mullo_s7:int64)))` ASSUME_TAC THENL
    [SUMS_EQS_TAC [8;10;12;14;18;20;22;24] []; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> if free_in `carry_s24:bool` (concl th) && free_in `w19:int64` (concl th)
                         then NOCARRY_TAC `carry_s24:bool` th else NO_TAC) THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
   STEP_EQS_TAC [2;26;28;30;32;xc;38;40;41;42] [1;3;5;7;19;21;23;25]
     (fun c -> free_in `carry_s24:bool` c || free_in `sum_s24:int64` c);
   ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && free_in `sum_s26:int64` (lhs c) && type_of(lhs c) = `:num`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && free_in `elo:num` c && free_in `w19:int64` c)) THEN
  MP_TAC(SPECL [`a:num`; `4 * l`] LOWDIGITS_ADD4) THEN MP_TAC(SPECL [`n:num`; `4 * l`] LOWDIGITS_ADD4) THEN
  MP_TAC(SPECL [`bb:num`; `i:num`] (CONJUNCT2 LOWDIGITS_CLAUSES)) THEN MP_TAC(SPECL [`mm:num`; `i:num`] (CONJUNCT2 LOWDIGITS_CLAUSES)) THEN
  MP_TAC(SPECL [`bb:num`; `i:num`] HIGHDIGITS_STEP) THEN MP_TAC(SPECL [`mm:num`; `i:num`] HIGHDIGITS_STEP) THEN
  SUBGOAL_THEN `2 EXP 256 * 2 EXP (64 * (4 * (l - 1) + i)) = 2 EXP (64 * (4 * l)) * 2 EXP (64 * i)` MP_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `64 * (4 * l + i + 1) = 64 * (4 * l) + 64 * i + 64 /\ 64 * (4 * l + i) = 64 * (4 * l) + 64 * i /\
                          64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP (64 * (4 * (l - 1) + i))`,`kk:num`) THEN
  SPEC_TAC(`2 EXP (64 * (4 * l))`,`gg:num`) THEN SPEC_TAC(`2 EXP (64 * i)`,`ff:num`) THEN
  SPEC_TAC(`lowdigits a (4 * l + 4)`,`al4:num`) THEN SPEC_TAC(`lowdigits n (4 * l + 4)`,`nl4:num`) THEN
  REPEAT GEN_TAC THEN CONV_TAC NUM_RING;;

let M4_CL_STEP_0 = prove(m4_cl_step_tm 0xd58 42,
  M4_CL_STEP_TAC [18;19;20;21;22;23;24;25;26;28;30;32;33;35;38;40;41;42] 33);;
let M4_CL_STEP_R = prove(m4_cl_step_tm 0xf60 42,
  M4_CL_STEP_TAC [18;19;20;21;22;23;24;25;26;28;30;32;34;36;38;40;41;42] 34);;

let m4_cl_loop_tm base len = parse_term (Printf.sprintf
 "!f k z x y m w a b n tp fr ra c30 t j bb mm l pc.
   1 <= l /\\ 4 * (l + 1) <= k /\\ aligned 16 tp /\\ 4 * (j + 1) <= k /\\ k < 2 EXP 58 /\\
   bb = lowdigits (highdigits b (4 * j)) 4 /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_cl_inv f k z x y m w a b n tp fr ra c30 t j bb mm l 0 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_cl_inv f k z x y m w a b n tp fr ra c30 t j bb mm l 4 s)
     (%s)" m4_nonover base (base + 4 * len) m4_maychange);;

let M4_CL_LOOP_TAC (step:thm) (base:int) (len:int) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_WHILE_UP_TAC `4` (mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),mk_small_numeral base))
    (mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),mk_small_numeral(base + 4 * len)))
    `\i s. m4_cl_inv f k z x y m w a b n tp fr ra c30 t j bb mm l i s` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_REFL_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] step) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[m4_cl_inv; m4_frame; m4_win; BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[VAL_WORD_8I];
    ENSURES_REFL_TAC];;

let M4_CL_LOOP_0 = prove(m4_cl_loop_tm 0xd58 42, M4_CL_LOOP_TAC M4_CL_STEP_0 0xd58 42);;
let M4_CL_LOOP_R = prove(m4_cl_loop_tm 0xf60 42, M4_CL_LOOP_TAC M4_CL_STEP_R 0xf60 42);;

let VAL_WORD_8K_SUB = prove
 (`!k c. c < 8 * k /\ k < 2 EXP 58 ==> ~(val(word(8 * k - c):int64) = 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `8 * k - c < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN ASM_ARITH_TAC);;

(* The four words at base and the rest, from base holding t's digits from p. *)
let M4_HIGH4 = prove
 (`!base nn t p s.
     bignum_from_memory(base,nn) s = highdigits t p /\ 4 <= nn
     ==> bignum_from_memory(word_add base (word 32),nn - 4) s = highdigits t (p + 4) /\
         read(memory :> bytes64 base) s = word(bigdigit t p) /\
         read(memory :> bytes64(word_add base (word 8))) s = word(bigdigit t (p + 1)) /\
         read(memory :> bytes64(word_add base (word 16))) s = word(bigdigit t (p + 2)) /\
         read(memory :> bytes64(word_add base (word 24))) s = word(bigdigit t (p + 3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r < 4 ==> read(memory :> bytes64(word_add base (word(8 * r)))) s =
                              word(bigdigit t (p + r))` MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM BIGDIGIT_HIGHDIGITS] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC BN_DIGIT_READ THEN EXISTS_TAC `nn:num` THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun r -> MP_TAC(SPEC r th)) [`0`; `1`; `2`; `3`]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM HIGHDIGITS_HIGHDIGITS] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try is_comb(lhs(concl th)) && fst(strip_comb(rhs(concl th))) = `highdigits` with _ -> false)) THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Chains steps from iv i to iv (i + 1), for i from a below a + d. *)
let ENSURES_ITER = prove
 (`!step (iv:num->A->bool) C a d.
     C ,, C = C /\ ensures step (iv a) (iv a) C /\
     (!i. a <= i /\ i < a + d ==> ensures step (iv i) (iv (i + 1)) C)
     ==> ensures step (iv a) (iv (a + d)) C`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[ADD_CLAUSES; ADD1] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC `(iv:num->A->bool) (a + d)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* At the start of row j >= 1: the accumulator is 2^(64k) * x30 + t, with t
   at tp + 32, and the rows so far have added b's low 4j digits times a and
   some q times n, divided by 2^(256j). *)
let m4_row = new_definition `m4_row (k:num) (z:int64) (x:int64) (y:int64) (m:int64)
    (w:int64) (a:num) (b:num) (n:num) (tp:int64) (fr:int64) (ra:int64) (j:num) s <=>
   m4_c0_inv F k z x y m w a b n tp fr ra (read X30 s)
     (bignum_from_memory(word_add tp (word 32),k) s) j (lowdigits (highdigits b (4 * j)) 4) 0 s /\
   ?q. q < 2 EXP (256 * j) /\
       2 EXP (256 * j) * (2 EXP (64 * k) * val(read X30 s) + bignum_from_memory(word_add tp (word 32),k) s) =
       lowdigits b (4 * j) * a + q * n`;;

(* After the last row, at the final subtraction. *)
let m4_fin = new_definition `m4_fin (k:num) (z:int64) (x:int64) (y:int64) (m:int64)
    (w:int64) (a:num) (b:num) (n:num) (tp:int64) (fr:int64) (ra:int64) s <=>
   m4_frame k z x y m w a b n tp fr ra s /\
   read X12 s = z /\ read X3 s = word_add m (word 32) /\
   read X14 s = word(bigdigit n 0) /\ read X15 s = word(bigdigit n 1) /\
   read X16 s = word(bigdigit n 2) /\ read X17 s = word(bigdigit n 3) /\
   read X19 s = word(bigdigit (bignum_from_memory(word_add tp (word 32),k) s) 0) /\
   read X20 s = word(bigdigit (bignum_from_memory(word_add tp (word 32),k) s) 1) /\
   read X21 s = word(bigdigit (bignum_from_memory(word_add tp (word 32),k) s) 2) /\
   read X22 s = word(bigdigit (bignum_from_memory(word_add tp (word 32),k) s) 3) /\
   ?q. q < 2 EXP (64 * k) /\
       2 EXP (64 * k) * (2 EXP (64 * k) * val(read X30 s) + bignum_from_memory(word_add tp (word 32),k) s) =
       b * a + q * n`;;

let m4_t1_0_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 bb mm pc.
   8 <= k /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\ bb < 2 EXP 256 /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xd34) /\\
          m4_c0_inv T k z x y m w a b n tp fr ra c30 0 0 bb 4 s /\\ bignum_from_memory(tp,4) s = mm)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xd58) /\\
          m4_cl_inv T k z x y m w a b n tp fr ra c30 0 0 bb mm 1 0 s)
     (%s)" m4_nonover m4_maychange);;

let M4_T1_0 = prove(m4_t1_0_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lowdigits bb 4 = bb` ASSUME_TAC THENL
   [MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[ARITH_RULE `64 * 4 = 256`]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `32`] VAL_WORD_8K_SUB) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[m4_c0_inv; m4_cl_inv; m4_frame; m4_win] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL; LOWDIGITS_0; HIGHDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun i -> READ_DIGIT_TAC `x:int64` i THEN READ_DIGIT_TAC `m:int64` i) [`4`; `5`; `6`; `7`] THEN
  READ_DIGIT_TAC `tp:int64` `0` THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--9) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[ARITH_RULE `32 = 8 * 4`]]);;

let m4_t1_r_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 t j bb mm pc.
   8 <= k /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\ bb < 2 EXP 256 /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xf20) /\\
          m4_c0_inv F k z x y m w a b n tp fr ra c30 t j bb 4 s /\\ bignum_from_memory(tp,4) s = mm)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xf60) /\\
          m4_cl_inv F k z x y m w a b n tp fr ra c30 t j bb mm 1 0 s)
     (%s)" m4_nonover m4_maychange);;

let M4_T1_R = prove(m4_t1_r_tm,
  (REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lowdigits bb 4 = bb` ASSUME_TAC THENL
   [MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[ARITH_RULE `64 * 4 = 256`]; ALL_TAC] THEN
  REWRITE_TAC[m4_c0_inv; m4_cl_inv; m4_frame; m4_win] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL; LOWDIGITS_0; HIGHDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w19:int64` `read X19` THEN GHOST_INTRO_TAC `w20:int64` `read X20` THEN
  GHOST_INTRO_TAC `w21:int64` `read X21` THEN GHOST_INTRO_TAC `w22:int64` `read X22` THEN
  GHOST_INTRO_TAC `w0:int64` `read X0` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0") THEN
  (MAP_EVERY (fun i -> READ_DIGIT_TAC `x:int64` i THEN READ_DIGIT_TAC `m:int64` i) [`4`; `5`; `6`; `7`] THEN
  READ_DIGIT_TAC `tp:int64` `0`) THEN
  (MP_TAC(SPECL [`word_add tp (word 32):int64`; `k:num`; `t:num`; `0`; `s0:armstate`] M4_HIGH4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`word_add (word_add tp (word 32)) (word 32):int64`; `k - 4`; `t:num`; `0 + 4`; `s0:armstate`] M4_HIGH4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH_RULE `k - 4 - 4 = k - 8`; BIGNUM_FROM_MEMORY_BYTES]) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV)) THEN
  (ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [2;8;9;10;11] (1--16) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `&(val(w0:int64)):real <= &1` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  NOCARRY_SUMS_TAC `carry_s2:bool` [2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    FIRST_ASSUM(fun th -> if free_in `sum_s2:int64` (concl th) && is_eq(concl th) then REAL_BOUNDED_TAC [th] else NO_TAC);
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:num`; `4`] LOWDIGITS_ADD4) THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `w19:int64` (concl th) && free_in `lowdigits t 4` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BIGDIGIT]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
  STEP_EQS_TAC [2;8;9;10;11] [] (fun c -> free_in `lowdigits t 4` c)));;

let m4_trans_tm f t base1 base2 = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 t j bb mm l pc.
   1 <= l /\\ 4 * (l + 2) <= k /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\ bb < 2 EXP 256 /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_cl_inv %s k z x y m w a b n tp fr ra c30 %s j bb mm l 4 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_cl_inv %s k z x y m w a b n tp fr ra c30 %s j bb mm (l + 1) 0 s)
     (%s)" m4_nonover base1 f t base2 f t m4_maychange);;

(* Reads digit 4j + r of v, for r < 4, from the k-word v at base. *)
let CHUNK_DIGITS_TAC (base:term) (v:term) (j:term) (s:term) : tactic =
  MAP_EVERY (fun r ->
    MP_TAC(SPECL [base; `k:num`; s; v; j; r;
                  mk_comb(mk_comb(`lowdigits`,mk_comb(mk_comb(`highdigits`,v),mk_binop `( * ):num->num->num` `4` j)),`4`)]
             M4_CHUNK_DIGIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGDIGIT_LOWDIGITS; BIGDIGIT_HIGHDIGITS] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC)
  [`0`; `1`; `2`; `3`];;
let M4_WORD_OFFSET_TAC : tactic =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;;
let M4_MM_BOUND_TAC : tactic =
  SUBGOAL_THEN `mm < 2 EXP (64 * 4)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if (try rhs(concl th) = `mm:num` with _ -> false) then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[ARITH_RULE `32 = 8 * 4`; GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `bb < 2 EXP (64 * 4)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> try lhand(concl th) = `bb:num` && is_binary "<" (concl th) with _ -> false)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC];;

let M4_WINDOW_ADD_TAC (c0:int) (cs:int list) (base:term) : tactic =
  let sv n = mk_var("sum_s" ^ string_of_int n,`:int64`) in
  let s0 = sv c0 in
  let a,b,c,d = match map sv cs with [a;b;c;d] -> a,b,c,d | _ -> failwith "M4_WINDOW_ADD_TAC" in
  let cv = mk_var("carry_s" ^ string_of_int (List.nth cs 3),`:bool`) in
  let dig r = mk_comb(mk_comb(`bigdigit`,`t:num`), if r = 0 then base else mk_binop `(+):num->num->num` base (mk_small_numeral r)) in
  let tm = subst [s0,`s0:int64`; a,`sa:int64`; b,`sb:int64`; c,`sc:int64`; d,`sd:int64`; cv,`cv:bool`;
                  dig 0,`d0:num`; dig 1,`d1:num`; dig 2,`d2:num`; dig 3,`d3:num`]
    `val(sa:int64) + 2 EXP 64 * val(sb:int64) + 2 EXP 128 * val(sc:int64) + 2 EXP 192 * val(sd:int64) +
     2 EXP 256 * (val(s0:int64) + bitval cv) =
     (val(w19:int64) + 2 EXP 64 * val(w20:int64) + 2 EXP 128 * val(w21:int64) + 2 EXP 192 * val(w22:int64) +
      2 EXP 256 * (val(w0:int64) + bitval cf)) +
     (d0 + 2 EXP 64 * d1 + 2 EXP 128 * d2 + 2 EXP 192 * d3)` in
  SUBGOAL_THEN `&(val(w0:int64)):real <= &1` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  NOCARRY_SUMS_TAC (mk_var("carry_s" ^ string_of_int c0,`:bool`)) [c0] THEN
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BIGDIGIT]) THEN
    STEP_EQS_TAC (c0::cs) [] (K false);
    ALL_TAC];;

let M4_TRANS_0 = prove(m4_trans_tm "T" "0" 0xe00 0xd58,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `32 * (l + 1)`] VAL_WORD_8K_SUB) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[m4_cl_inv; m4_frame; m4_win] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[LOWDIGITS_TRIVIAL; LOWDIGITS_0; HIGHDIGITS_0; MULT_CLAUSES; ADD_CLAUSES; EXP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  CHUNK_DIGITS_TAC `x:int64` `a:num` `l + 1` `s0:armstate` THEN
  CHUNK_DIGITS_TAC `m:int64` `n:num` `l + 1` `s0:armstate` THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--10) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [M4_WORD_OFFSET_TAC; M4_WORD_OFFSET_TAC; M4_WORD_OFFSET_TAC; ASM_ARITH_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `32 = 8 * 4`]; ALL_TAC] THEN
  M4_MM_BOUND_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `highdigits bb 4` (concl th))) THEN
  ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; MULT_CLAUSES; ADD_CLAUSES] THEN
  SUBGOAL_THEN `4 * (l - 1) + 4 = 4 * ((l + 1) - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 * l + 4 = 4 * (l + 1)`]);;

let M4_TRANS_R = prove(m4_trans_tm "F" "t" 0x1008 0xf60,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `32 * (l + 1)`] VAL_WORD_8K_SUB) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[m4_cl_inv; m4_frame; m4_win] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; MULT_CLAUSES; ADD_CLAUSES; EXP] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w19:int64` `read X19` THEN GHOST_INTRO_TAC `w20:int64` `read X20` THEN
  GHOST_INTRO_TAC `w21:int64` `read X21` THEN GHOST_INTRO_TAC `w22:int64` `read X22` THEN
  GHOST_INTRO_TAC `w0:int64` `read X0` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  CHUNK_DIGITS_TAC `x:int64` `a:num` `l + 1` `s0:armstate` THEN
  CHUNK_DIGITS_TAC `m:int64` `n:num` `l + 1` `s0:armstate` THEN
  MP_TAC(SPECL [`word_add tp (word(32 * l + 64)):int64`; `k - 4 * (l + 1)`; `t:num`; `4 * (l + 1)`; `s0:armstate`] M4_HIGH4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC; BIGNUM_FROM_MEMORY_BYTES]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  (* The simulator states the loads' addresses as X26's offset plus the
     immediate. *)
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `32 * l + 64 = (32 * l + 32) + 32 /\ 32 * l + 72 = (32 * l + 32) + 40 /\
                                         32 * l + 80 = (32 * l + 32) + 48 /\ 32 * l + 88 = (32 * l + 32) + 56`]) THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [3;10;11;12;13] (1--17) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [M4_WORD_OFFSET_TAC; M4_WORD_OFFSET_TAC; M4_WORD_OFFSET_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  M4_WINDOW_ADD_TAC 3 [10;11;12;13] `4 * (l + 1)` THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    FIRST_ASSUM(fun th -> if free_in `sum_s3:int64` (concl th) && is_eq(concl th) && type_of(lhs(concl th)) = `:real`
                          then REAL_BOUNDED_TAC [th] else NO_TAC);
    SUBGOAL_THEN `32 * (l + 1) + 64 = 32 * l + 96 /\ k - 4 * ((l + 1) + 1) = k - 4 * (l + 1) - 4 /\
                  4 * ((l + 1) + 1) = 4 * (l + 1) + 4` (fun th -> ASM_REWRITE_TAC[th]) THEN ARITH_TAC;
    ALL_TAC] THEN
  M4_MM_BOUND_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `highdigits bb 4` (concl th))) THEN
  ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; MULT_CLAUSES; ADD_CLAUSES] THEN
  SUBGOAL_THEN `4 * (l - 1) + 4 = 4 * ((l + 1) - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 * l + 4 = 4 * (l + 1)`] THEN
  MP_TAC(SPECL [`t:num`; `4 * (l + 1)`] LOWDIGITS_ADD4) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `w19:int64` (concl th) && free_in `sum_s10:int64` (concl th))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `4 * ((l + 1) + 1) = 4 * (l + 1) + 4`] THEN
  SPEC_TAC(`2 EXP (64 * 4 * (l + 1))`,`gg:num`) THEN SPEC_TAC(`lowdigits t (4 * (l + 1))`,`ll:num`) THEN
  REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

(* Applies the ensures lemma th to the goal, leaving its hypotheses to the
   assumptions and arithmetic. *)
let M4_APPLY_TAC (th:thm) : tactic =
  MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

(* Chains iv a to iv (a + d), as ENSURES_ITER, with iv a lambda. *)
let M4_ITER_TAC (iv:term) (a:term) (d:term) : tactic =
  W(fun (asl,w) ->
    let c = rand w in
    MATCH_MP_TAC(BETA_RULE(ISPECL [`arm`; iv; c; a; d] ENSURES_ITER)) THEN
    REPEAT CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ENSURES_REFL_TAC; ALL_TAC]);;

let m4_chunks_tm f t base len = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 t j bb mm kk pc.
   k = 4 * kk /\\ 2 <= kk /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\ bb < 2 EXP 256 /\\
   4 * (j + 1) <= k /\\ lowdigits (highdigits b (4 * j)) 4 = bb /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_cl_inv %s k z x y m w a b n tp fr ra c30 %s j bb mm 1 0 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          m4_cl_inv %s k z x y m w a b n tp fr ra c30 %s j bb mm (kk - 1) 4 s)
     (%s)" m4_nonover base f t (base + 4 * len) f t m4_maychange);;

let M4_CHUNKS_TAC (f:string) (t:string) (base:int) (len:int) (loop:thm) (trans:thm) : tactic =
  let pcb = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral base)
  and pce = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral(base + 4 * len)) in
  let inv l i = parse_term (Printf.sprintf
    "\\s. m4_cl_inv %s k z x y m w a b n tp fr ra c30 %s j bb mm %s %s s" f t l i) in
  let iv = parse_term (Printf.sprintf
    "\\l s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
            m4_cl_inv %s k z x y m w a b n tp fr ra c30 %s j bb mm l 0 s" base f t) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC pcb (inv "(kk - 1)" "0") THEN CONJ_TAC THENL
   [SUBGOAL_THEN `kk - 1 = 1 + (kk - 2)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    M4_ITER_TAC iv `1` `kk - 2` THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    ENSURES_SEQUENCE_TAC pce (inv "l" "4") THEN CONJ_TAC THEN
    FIRST [M4_APPLY_TAC loop; M4_APPLY_TAC trans];
    M4_APPLY_TAC loop];;

let M4_CHUNKS_0 = prove(m4_chunks_tm "T" "0" 0xd58 42,
  M4_CHUNKS_TAC "T" "0" 0xd58 42 M4_CL_LOOP_0 M4_TRANS_0);;
let M4_CHUNKS_R = prove(m4_chunks_tm "F" "t" 0xf60 42,
  M4_CHUNKS_TAC "F" "t" 0xf60 42 M4_CL_LOOP_R M4_TRANS_R);;

let m4_end0_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 bb mm kk pc.
   4 * kk = k /\\ 2 <= kk /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\ lowdigits b 4 = bb /\\
   val m + 32 < 2 EXP 64 /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xe00) /\\
          m4_cl_inv T k z x y m w a b n tp fr ra c30 0 0 bb mm (kk - 1) 4 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xe80) /\\
          m4_row k z x y m w a b n tp fr ra 1 s)
     (%s)" m4_nonover m4_maychange);;

let LOWDIGITS_ADD_HIGH = prove
 (`!e x p q. p <= q ==> lowdigits (e + 2 EXP (64 * q) * x) p = lowdigits e p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lowdigits] THEN
  SUBGOAL_THEN `2 EXP (64 * q) = 2 EXP (64 * p) * 2 EXP (64 * (q - p))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM CONG] THEN NUMBER_TAC);;

let BIGDIGIT_ADD_HIGH = prove
 (`!e x q r. 4 <= q /\ r < 4 ==> bigdigit (e + 2 EXP (64 * q) * x) r = bigdigit e r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e + 2 EXP (64 * q) * x`; `4`; `r:num`] BIGDIGIT_LOWDIGITS) THEN
  MP_TAC(SPECL [`e:num`; `4`; `r:num`] BIGDIGIT_LOWDIGITS) THEN
  ASM_SIMP_TAC[LOWDIGITS_ADD_HIGH] THEN MESON_TAC[]);;

let M4_ADC_TOP = prove
 (`!w0:int64 cf. val w0 <= 1 ==> val(word_add w0 (word(bitval cf)):int64) = val w0 + bitval cf`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_BITVAL; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN MP_TAC(SPEC `cf:bool` BITVAL_BOUND) THEN ASM_ARITH_TAC);;

let M4_EXP_SPLIT = prove
 (`!k. 4 <= k ==> 2 EXP (64 * k) = 2 EXP 256 * 2 EXP (64 * (k - 4))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* The accumulator t at tp + 32, from its low k - 4 words e and the four
   words at tp + 8k. *)
let M4_SPLIT_TOP = prove
 (`!tp k s e d0 d1 d2 d3:int64. 4 <= k /\ k < 2 EXP 58 /\
     bignum_from_memory(word_add tp (word 32),k - 4) s = e /\
     read(memory :> bytes64(word_add tp (word(8 * k)))) s = d0 /\
     read(memory :> bytes64(word_add tp (word(8 * k + 8)))) s = d1 /\
     read(memory :> bytes64(word_add tp (word(8 * k + 16)))) s = d2 /\
     read(memory :> bytes64(word_add tp (word(8 * k + 24)))) s = d3
     ==> bignum_from_memory(word_add tp (word 32),k) s =
         e + 2 EXP (64 * (k - 4)) * (val d0 + 2 EXP 64 * val d1 + 2 EXP 128 * val d2 + 2 EXP 192 * val d3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`word_add tp (word 32):int64`; `k - 4`; `4`; `s:armstate`] BIGNUM_FROM_MEMORY_SPLIT) THEN
  ASM_SIMP_TAC[SUB_ADD] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `word_add (word_add tp (word 32)) (word(8 * (k - 4))):int64 = word_add tp (word(8 * k))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* v < 2^(64k), from an assumption read(memory :> bytes(base,8 * k)) s = v. *)
let BYTES_BOUND_TAC (base:term) (v:term) : tactic =
  let pat = vsubst [base,`base:int64`; v,`v:num`] `read (memory :> bytes(base,8 * k)) ss = v` in
  SUBGOAL_THEN (vsubst [v,`v:num`] `v < 2 EXP (64 * k)`) ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match (`k:num` :: frees base @ frees v) pat) (concl th)
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC];;

let M4_MM_BOUND4_TAC : tactic =
  SUBGOAL_THEN `mm < 2 EXP (64 * 4)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if (try rhs(concl th) = `mm:num` with _ -> false) then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[ARITH_RULE `32 = 8 * 4`; GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC];;

let M4_END_0 = prove(m4_end0_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[m4_cl_inv; m4_row; m4_c0_inv; m4_frame; m4_win] THEN
  SUBGOAL_THEN `8 * k - 32 * ((kk - 1) + 1) = 0 /\ 32 * (kk - 1) + 8 * 4 = 8 * k /\ 4 * ((kk - 1) - 1) + 4 = k - 4 /\
                4 * (kk - 1) + 4 = k /\ 32 * ((kk - 1) + 1) = 8 * k` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[LOWDIGITS_TRIVIAL; LOWDIGITS_0; HIGHDIGITS_0; MULT_CLAUSES; ADD_CLAUSES; EXP] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w19:int64` `read X19` THEN GHOST_INTRO_TAC `w20:int64` `read X20` THEN
  GHOST_INTRO_TAC `w21:int64` `read X21` THEN GHOST_INTRO_TAC `w22:int64` `read X22` THEN
  GHOST_INTRO_TAC `w0:int64` `read X0` THEN
  GHOST_INTRO_TAC `e:num` `bignum_from_memory (word_add tp (word 32),k - 4)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun i -> READ_DIGIT_TAC `x:int64` i THEN READ_DIGIT_TAC `m:int64` i) [`0`; `1`; `2`; `3`] THEN
  MAP_EVERY (fun i -> READ_DIGIT_TAC `word_add tp (word 32):int64` i) [`0`; `1`; `2`; `3`] THEN
  RULE_ASSUM_TAC(fun th -> if free_in `e:num` (concl th) && not(is_forall(concl th))
    then CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) (REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th) else th) THEN
  MP_TAC(SPECL [`y:int64`; `k:num`; `s0:armstate`; `b:num`; `1`; `0`; `lowdigits(highdigits b 4) 4`] M4_CHUNK_DIGIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC] THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--19) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add x (c:int64)) c = x`; VAL_WORD_0; VAL_WORD_BIGDIGIT;
              READ_MEMORY_BYTES_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `m + 32 < 2 EXP 64 ==> ~(2 EXP 64 <= m + 32)`; BITVAL_CLAUSES] THEN
  MP_TAC(SPECL [`tp:int64`; `k:num`; `s19:armstate`; `e:num`; `w19:int64`; `w20:int64`; `w21:int64`; `w22:int64`] M4_SPLIT_TOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_ARITH_TAC;
                  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LOWDIGITS_4] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  SUBGOAL_THEN `4 <= k - 4` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[BIGDIGIT_ADD_HIGH; ARITH]; EXISTS_TAC `mm:num`] THEN
  M4_MM_BOUND4_TAC THEN BYTES_BOUND_TAC `x:int64` `a:num` THEN BYTES_BOUND_TAC `m:int64` `n:num` THEN
  SUBGOAL_THEN `bb < 2 EXP (64 * 4)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs(concl th) = `bb:num` with _ -> false)) THEN
    REWRITE_TAC[LOWDIGITS_BOUND]; ALL_TAC] THEN
  CONJ_TAC THENL [UNDISCH_TAC `mm < 2 EXP (64 * 4)` THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `highdigits bb 4` (concl th))) THEN
  ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; MULT_CLAUSES; ADD_CLAUSES; M4_ADC_TOP] THEN
  SUBGOAL_THEN `4 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[M4_EXP_SPLIT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`2 EXP (64 * (k - 4))`,`gg:num`) THEN GEN_TAC THEN CONV_TAC NUM_RING);;

let M4_LOWDIGITS_CHUNK = prove
 (`!b j. lowdigits b (4 * (j + 1)) = lowdigits b (4 * j) + 2 EXP (256 * j) * lowdigits (highdigits b (4 * j)) 4`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4 * (j + 1) = 4 * j + 4`; LOWDIGITS_ADD4; LOWDIGITS_4; BIGDIGIT_HIGHDIGITS; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `64 * 4 * j = 256 * j`]);;

let m4_endr_tm last post = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 t q j bb mm kk pc.
   4 * kk = k /\\ 1 <= j /\\ %s /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\
   lowdigits (highdigits b (4 * j)) 4 = bb /\\ val x + 32 < 2 EXP 64 /\\ t < 2 EXP (64 * k) /\\
   q < 2 EXP (256 * j) /\\
   2 EXP (256 * j) * (2 EXP (64 * k) * val(c30:int64) + t) = lowdigits b (4 * j) * a + q * n /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1008) /\\
          m4_cl_inv F k z x y m w a b n tp fr ra c30 t j bb mm (kk - 1) 4 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ %s)
     (%s)" (if last then "j + 1 = kk" else "j + 1 < kk") m4_nonover post m4_maychange);;
let m4_endr_tm_mid = m4_endr_tm false "read PC s = word(pc + 0xe80) /\\ m4_row k z x y m w a b n tp fr ra (j + 1) s";;
let m4_endr_tm_last = m4_endr_tm true "read PC s = word(pc + 0x10b0) /\\ m4_fin k z x y m w a b n tp fr ra s";;

(* The row end's compare of y's pointer with y + 8k. *)
let M4_ROW_CMP = prove
 (`!y:int64 j k kk. 4 * kk = k /\ k < 2 EXP 58 /\ j + 1 <= kk
     ==> (val(word_sub (word_add (word_add y (word (32 * j))) (word 32)) (word_add y (word (8 * k)))) = 0 <=>
          j + 1 = kk)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (word_add y a) b) (word_add y c):int64 = word_sub (word_add a b) c`] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM WORD_ADD; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `32 * j + 32 < 2 EXP 64 /\ 8 * k < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let M4_ENDR_CLOSE_TAC (last:bool) (st:term) : tactic =
  REWRITE_TAC[WORD_RULE `word_sub (word_add x (c:int64)) c = x`; VAL_WORD_0; VAL_WORD_BIGDIGIT;
              READ_MEMORY_BYTES_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `x + 32 < 2 EXP 64 ==> ~(2 EXP 64 <= x + 32)`; BITVAL_CLAUSES] THEN
  MP_TAC(SPECL [`tp:int64`; `k:num`; st; `e:num`; `sum_s6:int64`; `sum_s8:int64`; `sum_s10:int64`; `sum_s12:int64`] M4_SPLIT_TOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_ARITH_TAC;
                  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LOWDIGITS_4] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  SUBGOAL_THEN `4 <= k - 4` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (if last then ASM_SIMP_TAC[BIGDIGIT_ADD_HIGH; ARITH]
   else CONJ_TAC THENL [ASM_SIMP_TAC[BIGDIGIT_ADD_HIGH; ARITH]; ALL_TAC]) THEN
  EXISTS_TAC `q + 2 EXP (256 * j) * mm` THEN
  M4_MM_BOUND4_TAC THEN BYTES_BOUND_TAC `x:int64` `a:num` THEN BYTES_BOUND_TAC `m:int64` `n:num` THEN
  SUBGOAL_THEN `bb < 2 EXP (64 * 4)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs(concl th) = `bb:num` with _ -> false)) THEN
    REWRITE_TAC[LOWDIGITS_BOUND]; ALL_TAC] THEN
  CONJ_TAC THENL
   [(if last then SUBGOAL_THEN `64 * k = 256 * (j + 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] else ALL_TAC) THEN
    REWRITE_TAC[ARITH_RULE `256 * (j + 1) = 256 * j + 256`; EXP_ADD] THEN
    MATCH_MP_TAC(ARITH_RULE `q < e /\ e * (q' + 1) <= e * f ==> q + e * q' < e * f`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `mm < 2 EXP (64 * 4)` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(val(w0:int64)):real <= &1` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  NOCARRY_SUMS_TAC `carry_s3:bool` [3] THEN
  NOCARRY_SUMS_TAC `carry_s14:bool` [3;14] THEN
  SUBGOAL_THEN `val(sum_s6:int64) + 2 EXP 64 * val(sum_s8:int64) + 2 EXP 128 * val(sum_s10:int64) +
                2 EXP 192 * val(sum_s12:int64) + 2 EXP 256 * val(sum_s14:int64) =
                (val(w19:int64) + 2 EXP 64 * val(w20:int64) + 2 EXP 128 * val(w21:int64) + 2 EXP 192 * val(w22:int64) +
                 2 EXP 256 * (val(w0:int64) + bitval cf)) + val(c30:int64)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN STEP_EQS_TAC [3;6;8;10;12;14] [] (K false); ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `highdigits bb 4` (concl th))) THEN
  ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `sum_s14:int64` (concl th) && free_in `w19:int64` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `e:num` (concl th) && free_in `w19:int64` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `c30:int64` (concl th) && free_in `q:num` (concl th))) THEN
  MP_TAC(SPECL [`b:num`; `j:num`] M4_LOWDIGITS_CHUNK) THEN
  FIRST_ASSUM(fun th -> if (try rhs(concl th) = `bb:num` with _ -> false) then REWRITE_TAC[th] else NO_TAC) THEN
  (if last then
     SUBGOAL_THEN `lowdigits b (4 * (j + 1)) = b` SUBST1_TAC THENL
      [MATCH_MP_TAC LOWDIGITS_SELF THEN SUBGOAL_THEN `4 * (j + 1) = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
       BYTES_BOUND_TAC `y:int64` `b:num` THEN ASM_REWRITE_TAC[]; ALL_TAC]
   else ALL_TAC) THEN
  SUBGOAL_THEN `4 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `k:num` M4_EXP_SPLIT) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (if last then
     SUBGOAL_THEN `2 EXP (64 * k) = 2 EXP (256 * j) * 2 EXP 256` MP_TAC THENL
      [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC]
   else ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `256 * (j + 1) = 256 * j + 256`; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`2 EXP (64 * k)`,`kx:num`) THEN SPEC_TAC(`2 EXP (64 * (k - 4))`,`gg:num`) THEN
  SPEC_TAC(`2 EXP (256 * j)`,`ee:num`) THEN
  REPEAT GEN_TAC THEN CONV_TAC NUM_RING;;

let M4_ENDR_TAC (last:bool) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[m4_cl_inv; m4_row; m4_fin; m4_c0_inv; m4_frame; m4_win] THEN
  SUBGOAL_THEN `8 * k - 32 * ((kk - 1) + 1) = 0 /\ 32 * (kk - 1) + 8 * 4 = 8 * k /\ 4 * ((kk - 1) - 1) + 4 = k - 4 /\
                4 * (kk - 1) + 4 = k /\ 32 * ((kk - 1) + 1) = 8 * k /\ 32 * (kk - 1) + 64 = 8 * k + 32 /\
                k - 4 * ((kk - 1) + 1) = 0` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; MULT_CLAUSES; ADD_CLAUSES; EXP] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w19:int64` `read X19` THEN GHOST_INTRO_TAC `w20:int64` `read X20` THEN
  GHOST_INTRO_TAC `w21:int64` `read X21` THEN GHOST_INTRO_TAC `w22:int64` `read X22` THEN
  GHOST_INTRO_TAC `w0:int64` `read X0` THEN
  GHOST_INTRO_TAC `e:num` `bignum_from_memory (word_add tp (word 32),k - 4)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun i -> READ_DIGIT_TAC `x:int64` i THEN READ_DIGIT_TAC `m:int64` i) [`0`; `1`; `2`; `3`] THEN
  MAP_EVERY (fun i -> READ_DIGIT_TAC `word_add tp (word 32):int64` i) [`0`; `1`; `2`; `3`] THEN
  RULE_ASSUM_TAC(fun th -> if free_in `e:num` (concl th) && not(is_forall(concl th))
    then CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) (REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th) else th) THEN
  (if last then ALL_TAC else
   MP_TAC(SPECL [`y:int64`; `k:num`; `s0:armstate`; `b:num`; `j + 1`; `0`; `lowdigits(highdigits b (4 * (j + 1))) 4`] M4_CHUNK_DIGIT) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
                   CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC]) THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [3;6;8;10;12;14] (1--20) THEN
  MP_TAC(SPECL [`y:int64`; `j:num`; `k:num`; `kk:num`] M4_ROW_CMP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  (if last then
     FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[ASSUME `j + 1 = kk`] o
       check (fun th -> is_iff(concl th) && free_in `kk:num` (concl th))) THEN
     ARM_STEPS_TAC BN_MUL_MONT_EXEC [21] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     M4_ENDR_CLOSE_TAC true `s21:armstate`
   else
     SUBGOAL_THEN `~(j + 1 = kk)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(j + 1 = kk)`]) THEN
     SUBGOAL_THEN `word_add (word_add y (word (32 * j))) (word 32):int64 = word_add y (word (32 * (j + 1)))`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [M4_WORD_OFFSET_TAC; ALL_TAC] THEN
     ARM_STEPS_TAC BN_MUL_MONT_EXEC (21--28) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     M4_ENDR_CLOSE_TAC false `s28:armstate`);;

let M4_END_R = prove(m4_endr_tm_mid, M4_ENDR_TAC false);;
let M4_END_R_LAST = prove(m4_endr_tm_last, M4_ENDR_TAC true);;

let M4_USE_TAC (th:thm) : tactic =
  MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS; m4_row] th) THEN
  TRY(EXISTS_TAC `q:num`) THEN ASM_REWRITE_TAC[MULT_CLAUSES; HIGHDIGITS_0] THEN ASM_ARITH_TAC;;

let m4_row_tm last = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra j kk pc.
   4 * kk = k /\\ 1 <= j /\\ %s /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\ val x + 32 < 2 EXP 64 /\\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xe80) /\\
          m4_row k z x y m w a b n tp fr ra j s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ %s)
     (%s)" (if last then "j + 1 = kk" else "j + 1 < kk") m4_nonover
     (if last then "read PC s = word(pc + 0x10b0) /\\ m4_fin k z x y m w a b n tp fr ra s"
      else "read PC s = word(pc + 0xe80) /\\ m4_row k z x y m w a b n tp fr ra (j + 1) s")
     m4_maychange);;

let M4_ROW_TAC (last:bool) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[m4_row] THEN
  GHOST_INTRO_TAC `c30:int64` `read X30` THEN
  GHOST_INTRO_TAC `t:num` `bignum_from_memory (word_add tp (word 32),k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `t:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `lowdigits (highdigits b (4 * j)) 4 < 2 EXP 256` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 = 64 * 4`; LOWDIGITS_BOUND]; ALL_TAC] THEN
  ABBREV_TAC `bb = lowdigits (highdigits b (4 * j)) 4` THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC `\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\ read PC s = word(pc + 0xe80) /\
                  m4_c0_inv F k z x y m w a b n tp fr ra c30 t j bb 0 s` THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xf20` `\s. m4_c0_inv F k z x y m w a b n tp fr ra c30 t j bb 4 s` THEN
  CONJ_TAC THENL [M4_USE_TAC M4_C0_LOOP_R; ALL_TAC] THEN
  GHOST_INTRO_TAC `mm:num` `bignum_from_memory(tp,4)` THEN
  ENSURES_SEQUENCE_TAC `pc + 0xf60` `\s. m4_cl_inv F k z x y m w a b n tp fr ra c30 t j bb mm 1 0 s` THEN
  CONJ_TAC THENL [M4_USE_TAC M4_T1_R; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x1008` `\s. m4_cl_inv F k z x y m w a b n tp fr ra c30 t j bb mm (kk - 1) 4 s` THEN
  CONJ_TAC THENL [M4_USE_TAC M4_CHUNKS_R; ALL_TAC] THEN
  M4_USE_TAC (if last then M4_END_R_LAST else M4_END_R);;

let M4_ROW_R = prove(m4_row_tm false, M4_ROW_TAC false);;
let M4_ROW_R_LAST = prove(m4_row_tm true, M4_ROW_TAC true);;

let m4_rows_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra kk pc.
   4 * kk = k /\\ 2 <= kk /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\ val x + 32 < 2 EXP 64 /\\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xe80) /\\
          m4_row k z x y m w a b n tp fr ra 1 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x10b0) /\\
          m4_fin k z x y m w a b n tp fr ra s)
     (%s)" m4_nonover m4_maychange);;

let M4_ROWS = prove(m4_rows_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xe80` `\s. m4_row k z x y m w a b n tp fr ra (kk - 1) s` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `kk - 1 = 1 + (kk - 2)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    M4_ITER_TAC `\j s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\ read PC s = word(pc + 0xe80) /\
                       m4_row k z x y m w a b n tp fr ra j s` `1` `kk - 2` THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] M4_ROW_R) THEN EXISTS_TAC `kk:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] M4_ROW_R_LAST) THEN EXISTS_TAC `kk:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let m4_row0_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 kk pc.
   4 * kk = k /\\ 2 <= kk /\\ k < 2 EXP 58 /\\ aligned 16 tp /\\ val m + 32 < 2 EXP 64 /\\
   (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xc90) /\\
          m4_c0_inv T k z x y m w a b n tp fr ra c30 0 0 (lowdigits b 4) 0 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xe80) /\\
          m4_row k z x y m w a b n tp fr ra 1 s)
     (%s)" m4_nonover m4_maychange);;

let M4_ROW_0 = prove(m4_row0_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lowdigits b 4 < 2 EXP 256` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 = 64 * 4`; LOWDIGITS_BOUND]; ALL_TAC] THEN
  ABBREV_TAC `bb = lowdigits b 4` THEN REWRITE_TAC[SOME_FLAGS; m4_row] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xd34` `\s. m4_c0_inv T k z x y m w a b n tp fr ra c30 0 0 bb 4 s` THEN
  CONJ_TAC THENL [M4_USE_TAC M4_C0_LOOP_0; ALL_TAC] THEN
  GHOST_INTRO_TAC `mm:num` `bignum_from_memory(tp,4)` THEN
  ENSURES_SEQUENCE_TAC `pc + 0xd58` `\s. m4_cl_inv T k z x y m w a b n tp fr ra c30 0 0 bb mm 1 0 s` THEN
  CONJ_TAC THENL [M4_USE_TAC M4_T1_0; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xe00` `\s. m4_cl_inv T k z x y m w a b n tp fr ra c30 0 0 bb mm (kk - 1) 4 s` THEN
  CONJ_TAC THENL [M4_USE_TAC M4_CHUNKS_0; ALL_TAC] THEN
  M4_USE_TAC M4_END_0);;

(* The final subtraction's loop, at its head, with chunk c pending: z holds
   t - n's low 4c words, x10 and x11 the next two with CF their borrow, and
   x21, x22, x16, x17 the two words of t and n after them. *)
let m4_sub_inv = new_definition `m4_sub_inv (k:num) (z:int64) (m:int64) (n:num) (tp:int64) (t:num)
    (cw:int64) (fr:int64) (ra:int64) (c:num) s <=>
   read X0 s = word_add z (word(32 * c)) /\ read X27 s = z /\
   read X3 s = word_add m (word(32 * (c + 1))) /\ read X26 s = word_add tp (word(32 * c + 64)) /\
   read X28 s = word(8 * k - 32 * (c + 1)) /\ read X5 s = word(8 * k) /\ read SP s = tp /\
   read X30 s = cw /\ read X29 s = fr /\ read (memory :> bytes64(word_add fr (word 8))) s = ra /\
   read X21 s = word(bigdigit t (4 * c + 2)) /\ read X22 s = word(bigdigit t (4 * c + 3)) /\
   read X16 s = word(bigdigit n (4 * c + 2)) /\ read X17 s = word(bigdigit n (4 * c + 3)) /\
   bignum_from_memory(m,k) s = n /\ bignum_from_memory(word_add tp (word 32),k) s = t /\
   &(bignum_from_memory(z,4 * c) s) +
   &2 pow (64 * 4 * c) * (&(val(read X10 s)) + &2 pow 64 * &(val(read X11 s))):real =
   &2 pow (64 * (4 * c + 2)) * &(bitval(~read CF s)) +
   &(lowdigits t (4 * c + 2)) - &(lowdigits n (4 * c + 2))`;;

let m4_sub_nonover = "nonoverlapping (z,8 * k) (tp,8 * k + 32) /\\
   ALL (nonoverlapping (z,8 * k)) [(word pc,LENGTH bn_mul_mont_mc); (m,8 * k); (word_add fr (word 8),8)]";;

let m4_sub_body_tm = parse_term (Printf.sprintf
 "!k z m n tp t cw fr ra c pc.
   4 * (c + 2) <= k /\\ k < 2 EXP 58 /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x10c8) /\\
          m4_sub_inv k z m n tp t cw fr ra c s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1100) /\\
          m4_sub_inv k z m n tp t cw fr ra (c + 1) s)
     (%s)" m4_sub_nonover m4_maychange);;

let M4_ADDR_TAC (eqs:term list) : tactic =
  MAP_EVERY (fun e -> SUBGOAL_THEN e (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [M4_WORD_OFFSET_TAC; ALL_TAC]) eqs;;

(* The 4 words at z + 32c on top of the 4c below them. *)
let M4_BYTES_ADD4 = prove
 (`!z c s. read(memory :> bytes(z,8 * 4 * (c + 1))) s =
           read(memory :> bytes(z,8 * 4 * c)) s + 2 EXP (64 * 4 * c) *
           (val(read(memory :> bytes64(word_add z (word(32 * c)))) s) +
            2 EXP 64 * val(read(memory :> bytes64(word_add z (word(32 * c + 8)))) s) +
            2 EXP 128 * val(read(memory :> bytes64(word_add z (word(32 * c + 16)))) s) +
            2 EXP 192 * val(read(memory :> bytes64(word_add z (word(32 * c + 24)))) s))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * 4 * (c + 1) = 8 * ((((4 * c + 1) + 1) + 1) + 1)`; BYTES_STEP] THEN
  REWRITE_TAC[ARITH_RULE `8 * (4 * c) = 32 * c /\ 8 * (4 * c + 1) = 32 * c + 8 /\
                          8 * ((4 * c + 1) + 1) = 32 * c + 16 /\ 8 * (((4 * c + 1) + 1) + 1) = 32 * c + 24 /\
                          64 * (4 * c + 1) = 64 * 4 * c + 64 /\ 64 * ((4 * c + 1) + 1) = 64 * 4 * c + 128 /\
                          64 * (((4 * c + 1) + 1) + 1) = 64 * 4 * c + 192`; EXP_ADD] THEN
  ARITH_TAC);;

let m4_sub_eqs (asl:(string*thm) list) =
  filter (fun th -> let c = concl th in is_eq c && type_of(lhs c) = `:real`) (map snd asl);;

let M4_SUB_BODY = prove(m4_sub_body_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[m4_sub_inv] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w10:int64` `read X10` THEN GHOST_INTRO_TAC `w11:int64` `read X11` THEN
  GHOST_INTRO_TAC `zl:num` `bignum_from_memory(z,4 * c)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  CHUNK_DIGITS_TAC `m:int64` `n:num` `c + 1` `s0:armstate` THEN
  CHUNK_DIGITS_TAC `word_add tp (word 32):int64` `t:num` `c + 1` `s0:armstate` THEN
  M4_ADDR_TAC [`word_add (word_add tp (word 32)) (word(32 * (c + 1))):int64 = word_add tp (word(32 * c + 64))`;
               `word_add (word_add tp (word 32)) (word(32 * (c + 1) + 8)):int64 = word_add tp (word((32 * c + 64) + 8))`;
               `word_add (word_add tp (word 32)) (word(32 * (c + 1) + 16)):int64 = word_add tp (word((32 * c + 64) + 16))`;
               `word_add (word_add tp (word 32)) (word(32 * (c + 1) + 24)):int64 = word_add tp (word((32 * c + 64) + 24))`] THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [1;5;11;14] (1--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY M4_WORD_OFFSET_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `4 * (c + 2) <= k ==> 32 <= 8 * k - 32 * (c + 1)`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[M4_BYTES_ADD4] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`t:num`; `4 * c + 2`] LOWDIGITS_ADD4) THEN
  MP_TAC(SPECL [`n:num`; `4 * c + 2`] LOWDIGITS_ADD4) THEN
  REWRITE_TAC[ARITH_RULE `(4 * c + 2) + 4 = 4 * (c + 1) + 2 /\ (4 * c + 2) + 1 = 4 * c + 3 /\
                          (4 * c + 2) + 2 = 4 * (c + 1) /\ (4 * c + 2) + 3 = 4 * (c + 1) + 1`] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BIGDIGIT]) THEN
  W(fun (asl,w) -> MAP_EVERY MP_TAC (m4_sub_eqs asl)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; VAL_WORD_BIGDIGIT] THEN
  REWRITE_TAC[ARITH_RULE `64 * (4 * c + 2) = 64 * 4 * c + 128 /\ 64 * 4 * (c + 1) = 64 * 4 * c + 256 /\
                          64 * (4 * (c + 1) + 2) = 64 * 4 * c + 384`; REAL_POW_ADD] THEN
  SPEC_TAC(`(&2 pow (64 * 4 * c)):real`,`e:real`) THEN GEN_TAC THEN
  REWRITE_TAC[BITVAL_NOT] THEN CONV_TAC REAL_RING);;

let m4_sub_exit_tm = parse_term (Printf.sprintf
 "!k z m n tp t cw fr ra p pc.
   4 * (p + 1) = k /\\ 1 <= p /\\ k < 2 EXP 58 /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1100) /\\
          m4_sub_inv k z m n tp t cw fr ra p s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1130) /\\
          read X27 s = z /\\ read X26 s = tp /\\ read X1 s = word_add tp (word 32) /\\
          read X5 s = word(8 * k) /\\ read SP s = tp /\\ read X29 s = fr /\\
          read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
          bignum_from_memory(word_add tp (word 32),k) s = t /\\
          read X6 s = word(bigdigit (bignum_from_memory(z,k) s) 0) /\\
          read X7 s = word(bigdigit (bignum_from_memory(z,k) s) 1) /\\
          read X8 s = word(bigdigit (bignum_from_memory(z,k) s) 2) /\\
          read X9 s = word(bigdigit (bignum_from_memory(z,k) s) 3) /\\
          read X19 s = word(bigdigit t 0) /\\ read X20 s = word(bigdigit t 1) /\\
          read X21 s = word(bigdigit t 2) /\\ read X22 s = word(bigdigit t 3) /\\
          &(bignum_from_memory(z,k) s):real = &2 pow (64 * k) * &(bitval(t < n)) + &t - &n /\\
          (read CF s <=> ~(val cw < bitval(t < n))))
     (%s)" m4_sub_nonover m4_maychange);;

let M4_SUB_EXIT = prove(m4_sub_exit_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[m4_sub_inv] THEN
  SUBGOAL_THEN `8 * k - 32 * (p + 1) = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w10:int64` `read X10` THEN GHOST_INTRO_TAC `w11:int64` `read X11` THEN
  GHOST_INTRO_TAC `zl:num` `bignum_from_memory(z,4 * p)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `t:num` THEN BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun r -> MP_TAC(SPECL [`z:int64`; `4 * p`; `s0:armstate`; `zl:num`; r] BN_DIGIT_READ_BYTES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC]) [`0`;`1`;`2`;`3`] THEN
  CHUNK_DIGITS_TAC `word_add tp (word 32):int64` `t:num` `0` `s0:armstate` THEN
  RULE_ASSUM_TAC(fun th -> if free_in `zl:num` (concl th) || free_in `bigdigit t` (concl th)
    then REWRITE_RULE[WORD_ADD_0] (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) th) else th) THEN
  M4_ADDR_TAC [`word_add (word_add tp (word 32)) (word 8):int64 = word_add tp (word 40)`;
               `word_add (word_add tp (word 32)) (word 16):int64 = word_add tp (word 48)`;
               `word_add (word_add tp (word 32)) (word 24):int64 = word_add tp (word 56)`] THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [2;6;12] (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `k:num` with _ -> false)) THEN
  MP_TAC(SPECL [`4 * (p + 1)`; `z:int64`; `s12:armstate`] BIGNUM_FROM_MEMORY_BOUND) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; M4_BYTES_ADD4] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIGDIGIT_ADD_HIGH; ARITH_RULE `1 <= p ==> 4 <= 4 * p`; ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  ABBREV_TAC `d = zl + 2 EXP (64 * 4 * p) * (val(w10:int64) + 2 EXP 64 * val(w11:int64) +
                  2 EXP 128 * val(sum_s2:int64) + 2 EXP 192 * val(sum_s6:int64))` THEN
  SUBGOAL_THEN `&d:real = &2 pow (64 * 4 * (p + 1)) * &(bitval carry_s6) + &t - &n` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t:num`; `4 * (p + 1)`] LOWDIGITS_SELF) THEN MP_TAC(SPECL [`n:num`; `4 * (p + 1)`] LOWDIGITS_SELF) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun v -> MAP_EVERY (fun i -> MP_TAC(SPECL [v; i] (CONJUNCT2 LOWDIGITS_CLAUSES))) [`4 * p + 2`; `4 * p + 3`])
      [`t:num`; `n:num`] THEN
    REWRITE_TAC[ARITH_RULE `(4 * p + 3) + 1 = 4 * (p + 1) /\ (4 * p + 2) + 1 = 4 * p + 3`] THEN
    REPEAT DISCH_TAC THEN
    W(fun (asl,w) -> MAP_EVERY MP_TAC (m4_sub_eqs asl)) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c && type_of(lhs c) = `:num` &&
       (free_in `lowdigits` c)))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; VAL_WORD_BIGDIGIT] THEN
    REWRITE_TAC[ARITH_RULE `64 * (4 * p + 2) = 64 * 4 * p + 128 /\ 64 * (4 * p + 3) = 64 * 4 * p + 192 /\
                            64 * 4 * (p + 1) = 64 * 4 * p + 256`; REAL_POW_ADD] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `64 * 4 * (p + 1) = 64 * 4 * p + 256`; REAL_POW_ADD] THEN
    SPEC_TAC(`(&2 pow (64 * 4 * p)):real`,`e:real`) THEN GEN_TAC THEN
    REWRITE_TAC[BITVAL_NOT] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SBC_BORROW o check (fun th -> free_in `carry_s12:bool` (concl th) &&
     is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
  SUBGOAL_THEN `carry_s6 <=> t < n` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `d:num` (concl th) && is_eq(concl th) &&
       type_of(lhs(concl th)) = `:real`)) THEN
    MAP_EVERY UNDISCH_TAC [`d < 2 EXP (64 * 4 * (p + 1))`; `t < 2 EXP (64 * 4 * (p + 1))`;
                           `n < 2 EXP (64 * 4 * (p + 1))`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW] THEN
    SPEC_TAC(`2 EXP (64 * 4 * (p + 1))`,`ee:num`) THEN GEN_TAC THEN
    BOOL_CASES_TAC `carry_s6:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[NOT_LT]]);;

let LOWDIGITS_2 = prove
 (`!a. lowdigits a 2 = bigdigit a 0 + 2 EXP 64 * bigdigit a 1`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 = (0 + 1) + 1`; LOWDIGITS_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let m4_sub_tm = parse_term (Printf.sprintf
 "!k z m n tp t cw fr ra kk pc.
   4 * kk = k /\\ 2 <= kk /\\ k < 2 EXP 58 /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x10b0) /\\
          read X12 s = z /\\ read X3 s = word_add m (word 32) /\\ read X5 s = word(8 * k) /\\
          read SP s = tp /\\ read X30 s = cw /\\ read X29 s = fr /\\
          read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
          read X14 s = word(bigdigit n 0) /\\ read X15 s = word(bigdigit n 1) /\\
          read X16 s = word(bigdigit n 2) /\\ read X17 s = word(bigdigit n 3) /\\
          read X19 s = word(bigdigit t 0) /\\ read X20 s = word(bigdigit t 1) /\\
          read X21 s = word(bigdigit t 2) /\\ read X22 s = word(bigdigit t 3) /\\
          bignum_from_memory(m,k) s = n /\\ bignum_from_memory(word_add tp (word 32),k) s = t)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1130) /\\
          read X27 s = z /\\ read X26 s = tp /\\ read X1 s = word_add tp (word 32) /\\
          read X5 s = word(8 * k) /\\ read SP s = tp /\\ read X29 s = fr /\\
          read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
          bignum_from_memory(word_add tp (word 32),k) s = t /\\
          read X6 s = word(bigdigit (bignum_from_memory(z,k) s) 0) /\\
          read X7 s = word(bigdigit (bignum_from_memory(z,k) s) 1) /\\
          read X8 s = word(bigdigit (bignum_from_memory(z,k) s) 2) /\\
          read X9 s = word(bigdigit (bignum_from_memory(z,k) s) 3) /\\
          read X19 s = word(bigdigit t 0) /\\ read X20 s = word(bigdigit t 1) /\\
          read X21 s = word(bigdigit t 2) /\\ read X22 s = word(bigdigit t 3) /\\
          &(bignum_from_memory(z,k) s):real = &2 pow (64 * k) * &(bitval(t < n)) + &t - &n /\\
          (read CF s <=> ~(val cw < bitval(t < n))))
     (%s)" m4_sub_nonover m4_maychange);;

let M4_SUB = prove(m4_sub_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_WHILE_UP_TAC `kk - 1` `pc + 0x10c8` `pc + 0x1100`
    `\c s. m4_sub_inv k z m n tp t cw fr ra c s` THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    (* entry *)
    RULE_ASSUM_TAC(REWRITE_RULE[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    REWRITE_TAC[m4_sub_inv] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; LOWDIGITS_2; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    SUBGOAL_THEN `32 <= 8 * k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [3;5] (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[WORD_SUB2];
      REWRITE_TAC[BITVAL_NOT] THEN
      W(fun (asl,w) -> MAP_EVERY MP_TAC (m4_sub_eqs asl)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; VAL_WORD_BIGDIGIT] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REAL_ARITH_TAC];
    (* one chunk *)
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] M4_SUB_BODY) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    (* back edge *)
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `32 * (c + 1)`] VAL_WORD_8K_SUB) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    REWRITE_TAC[m4_sub_inv; BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* exit *)
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] M4_SUB_EXIT) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* The selection's loop, at its head, with chunk c of t and of d = t - n in
   x19 to x22 and x6 to x9: z's low 4c words are selected, and z and t above
   chunk c are untouched. *)
let m4_sel_inv = new_definition `m4_sel_inv (k:num) (z:int64) (tp:int64) (t:num) (d:num)
    (cf:bool) (fr:int64) (ra:int64) (c:num) s <=>
   read X27 s = word_add z (word(32 * c)) /\ read X26 s = word_add tp (word(32 * c)) /\
   read X1 s = word_add tp (word(32 * c + 32)) /\
   read X28 s = word(8 * k - 32 * (c + 1)) /\ read X5 s = word(8 * k) /\ read SP s = tp /\
   read X29 s = fr /\ read X30 s = ra /\ read CF s = cf /\
   read X6 s = word(bigdigit d (4 * c)) /\ read X7 s = word(bigdigit d (4 * c + 1)) /\
   read X8 s = word(bigdigit d (4 * c + 2)) /\ read X9 s = word(bigdigit d (4 * c + 3)) /\
   read X19 s = word(bigdigit t (4 * c)) /\ read X20 s = word(bigdigit t (4 * c + 1)) /\
   read X21 s = word(bigdigit t (4 * c + 2)) /\ read X22 s = word(bigdigit t (4 * c + 3)) /\
   bignum_from_memory(word_add z (word(32 * c + 32)),k - 4 * (c + 1)) s = highdigits d (4 * (c + 1)) /\
   bignum_from_memory(word_add tp (word(32 * c + 64)),k - 4 * (c + 1)) s = highdigits t (4 * (c + 1)) /\
   bignum_from_memory(z,4 * c) s = lowdigits (if cf then d else t) (4 * c)`;;

let m4_sel_nonover = "nonoverlapping (z,8 * k) (tp,8 * k + 32) /\\
   ALL (nonoverlapping (z,8 * k)) [(word pc,LENGTH bn_mul_mont_mc); (word_add fr (word 8),8)] /\\
   nonoverlapping (tp,8 * k + 32) (word pc,LENGTH bn_mul_mont_mc)";;

let m4_sel_body_tm = parse_term (Printf.sprintf
 "!k z tp t d cf fr ra c pc.
   4 * (c + 2) <= k /\\ k < 2 EXP 58 /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1138) /\\
          m4_sel_inv k z tp t d cf fr ra c s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1178) /\\
          m4_sel_inv k z tp t d cf fr ra (c + 1) s)
     (%s)" m4_sel_nonover m4_maychange);;

let M4_SEL_BODY = prove(m4_sel_body_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[m4_sel_inv; BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`word_add z (word(32 * c + 32)):int64`; `k - 4 * (c + 1)`; `d:num`; `4 * (c + 1)`; `s0:armstate`] M4_HIGH4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`word_add tp (word(32 * c + 64)):int64`; `k - 4 * (c + 1)`; `t:num`; `4 * (c + 1)`; `s0:armstate`] M4_HIGH4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `k - 4 * (c + 1) - 4 = k - 4 * ((c + 1) + 1)`]) THEN
  M4_ADDR_TAC [`word_add (word_add z (word(32 * c + 32))) (word 8):int64 = word_add z (word(32 * c + 40))`;
               `word_add (word_add z (word(32 * c + 32))) (word 16):int64 = word_add z (word(32 * c + 48))`;
               `word_add (word_add z (word(32 * c + 32))) (word 24):int64 = word_add z (word(32 * c + 56))`;
               `word_add (word_add z (word(32 * c + 32))) (word 32):int64 = word_add z (word(32 * (c + 1) + 32))`;
               `word_add (word_add tp (word(32 * c + 64))) (word 8):int64 = word_add tp (word((32 * c + 32) + 40))`;
               `word_add (word_add tp (word(32 * c + 64))) (word 16):int64 = word_add tp (word((32 * c + 32) + 48))`;
               `word_add (word_add tp (word(32 * c + 64))) (word 24):int64 = word_add tp (word((32 * c + 32) + 56))`;
               `word_add (word_add tp (word(32 * c + 64))) (word 32):int64 = word_add tp (word(32 * (c + 1) + 64))`;
               `word_add tp (word(32 * c + 64)):int64 = word_add tp (word((32 * c + 32) + 32))`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY M4_WORD_OFFSET_TAC THEN TRY(AP_TERM_TAC THEN ARITH_TAC) THENL
   [ASM_SIMP_TAC[WORD_SUB2; ARITH_RULE `4 * (c + 2) <= k ==> 32 <= 8 * k - 32 * (c + 1)`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[M4_BYTES_ADD4] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `4 * (c + 1) = 4 * c + 4`; LOWDIGITS_ADD4] THEN
  BOOL_CASES_TAC `cf:bool` THEN REWRITE_TAC[VAL_WORD_BIGDIGIT]);;

let m4_sel_exit_tm = parse_term (Printf.sprintf
 "!k z tp t d cf fr ra p pc.
   4 * (p + 1) = k /\\ k < 2 EXP 58 /\\ t < 2 EXP (64 * k) /\\ d < 2 EXP (64 * k) /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1178) /\\
          m4_sel_inv k z tp t d cf fr ra p s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x11f8) /\\
          read X29 s = fr /\\ read X30 s = ra /\\ read SP s = tp /\\
          bignum_from_memory(z,k) s = (if cf then d else t))
     (%s)" m4_sel_nonover m4_maychange);;

let M4_SEL_EXIT = prove(m4_sel_exit_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[m4_sel_inv] THEN
  SUBGOAL_THEN `8 * k - 32 * (p + 1) = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `k:num` with _ -> false)) THEN
  REWRITE_TAC[M4_BYTES_ADD4] THEN ASM_REWRITE_TAC[] THEN
  BOOL_CASES_TAC `cf:bool` THEN REWRITE_TAC[] THEN
  W(fun (asl,w) -> let v = rand w in
    MP_TAC(SPECL [v; `4 * (p + 1)`] LOWDIGITS_SELF) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th])) THEN
  REWRITE_TAC[ARITH_RULE `4 * (p + 1) = 4 * p + 4`; LOWDIGITS_ADD4; VAL_WORD_BIGDIGIT]);;

let m4_sel_tm = parse_term (Printf.sprintf
 "!k z tp t d cf fr ra kk pc.
   4 * kk = k /\\ 2 <= kk /\\ k < 2 EXP 58 /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x1130) /\\
          read X27 s = z /\\ read X26 s = tp /\\ read X1 s = word_add tp (word 32) /\\
          read X5 s = word(8 * k) /\\ read SP s = tp /\\ read X29 s = fr /\\
          read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
          bignum_from_memory(word_add tp (word 32),k) s = t /\\ bignum_from_memory(z,k) s = d /\\
          read X6 s = word(bigdigit d 0) /\\ read X7 s = word(bigdigit d 1) /\\
          read X8 s = word(bigdigit d 2) /\\ read X9 s = word(bigdigit d 3) /\\
          read X19 s = word(bigdigit t 0) /\\ read X20 s = word(bigdigit t 1) /\\
          read X21 s = word(bigdigit t 2) /\\ read X22 s = word(bigdigit t 3) /\\
          read CF s = cf)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x11f8) /\\
          read X29 s = fr /\\ read X30 s = ra /\\ read SP s = tp /\\
          bignum_from_memory(z,k) s = (if cf then d else t))
     (%s)" m4_sel_nonover m4_maychange);;

let M4_HIGH_TAC (v:term) : tactic =
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs(concl th) = v &&
     can (term_match [] `read (memory :> bytes (a,l)) s:num`) (lhs(concl th)) with _ -> false)) THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_BIGNUM_FROM_MEMORY; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];;

let M4_SEL = prove(m4_sel_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `t:num` THEN BIGNUM_TERMRANGE_TAC `k:num` `d:num` THEN
  ENSURES_WHILE_UP_TAC `kk - 1` `pc + 0x1138` `pc + 0x1178`
    `\c s. m4_sel_inv k z tp t d cf fr ra c s` THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    (* entry *)
    RULE_ASSUM_TAC(REWRITE_RULE[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    REWRITE_TAC[m4_sel_inv] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; LOWDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    SUBGOAL_THEN `32 <= 8 * k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FIRST [ASM_SIMP_TAC[WORD_SUB2] THEN NO_TAC; M4_HIGH_TAC `d:num` THEN NO_TAC; M4_HIGH_TAC `t:num` THEN NO_TAC];
    (* one chunk *)
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] M4_SEL_BODY) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    (* back edge *)
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `32 * (c + 1)`] VAL_WORD_8K_SUB) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    REWRITE_TAC[m4_sel_inv; BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* exit *)
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] M4_SEL_EXIT) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let m4_pre_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n n0p fr ra tp pc.
   4 <= k /\\ k < 2 EXP 58 /\\ val m + 32 < 2 EXP 64 /\\
   tp = word_sub fr (word(8 * k + 32)) /\\
   %s /\\
   ALL (nonoverlapping (word_add fr (word 96),16))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k); (word_add fr (word 8),8)]
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xc3c) /\\
          read SP s = fr /\\ read X29 s = fr /\\ read X30 s = ra /\\
          read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
          read X0 s = z /\\ read X1 s = x /\\ read X2 s = y /\\ read X3 s = m /\\
          read X4 s = n0p /\\ read X5 s = word k /\\ read (memory :> bytes64 n0p) s = w /\\
          bignum_from_memory(x,k) s = a /\\ bignum_from_memory(y,k) s = b /\\
          bignum_from_memory(m,k) s = n)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xc90) /\\
          m4_c0_inv T k z x y m w a b n tp fr ra ra 0 0 (lowdigits b 4) 0 s)
     (%s)" m4_nonover m4_maychange);;

let M4_PRE = prove(m4_pre_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(2 EXP 64 <= val(m:int64) + 32)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[m4_c0_inv; m4_frame; m4_win] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun r -> READ_DIGIT_TAC `x:int64` r THEN READ_DIGIT_TAC `m:int64` r) [`0`;`1`;`2`;`3`] THEN
  READ_DIGIT_TAC `y:int64` `0` THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--21) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_SHL3; BIGDIGIT_LOWDIGITS; ARITH; VAL_WORD_0; LOWDIGITS_0; BITVAL_CLAUSES;
                  READ_MEMORY_BYTES_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[lowdigits; MOD_0; WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* The selected value is the Montgomery product, from the accumulator's
   relation 2^(64k) * (2^(64k) * cv + t) = b * a + q * n with q < 2^(64k). *)
let M4_FINAL_ARITH = prove
 (`!k n a b q t cv d.
     ODD n /\ n < 2 EXP (64 * k) /\ t < 2 EXP (64 * k) /\ q < 2 EXP (64 * k) /\
     2 EXP (64 * k) * (2 EXP (64 * k) * cv + t) = b * a + q * n /\
     &d:real = &2 pow (64 * k) * &(bitval(t < n)) + &t - &n /\ a * b <= 2 EXP (64 * k) * n
     ==> (if ~(cv < bitval(t < n)) then d else t) = (inverse_mod n (2 EXP (64 * k)) * a * b) MOD n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (64 * k) * cv + t < 2 * n` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP (64 * k) * (2 EXP (64 * k) * cv + t) < 2 EXP (64 * k) * (2 * n)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `q * n < r * n /\ x <= r * n ==> x + q * n < r * (2 * n)`) THEN
      REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `ODD n` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH];
        UNDISCH_TAC `a * b <= 2 EXP (64 * k) * n` THEN ARITH_TAC];
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `t:num`; `d:num`; `2 EXP (64 * k)`; `cv:num`] GEN_FINAL_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MONT_REDUCE_CONG THEN EXISTS_TAC `q:num` THEN CONJ_TAC THENL
   [REWRITE_TAC[COPRIME_REXP] THEN DISJ1_TAC THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_REWRITE_TAC[COPRIME_2];
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let m4_final_post = "read X29 s = fr /\\ read X30 s = ra /\\ read SP s = tp /\\
          (a * b <= 2 EXP (64 * k) * n
           ==> bignum_from_memory(z,k) s = (inverse_mod n (2 EXP (64 * k)) * a * b) MOD n)";;

let m4_final4_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra c30 kk pc.
   4 * kk = k /\\ 4 <= k /\\ k < 8 /\\ aligned 16 tp /\\ (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\ %s /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xd34) /\\
          m4_c0_inv T k z x y m w a b n tp fr ra c30 0 0 (lowdigits b 4) 4 s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x11f8) /\\ %s)
     (%s)" m4_nonover m4_sel_nonover m4_final_post m4_maychange);;

let BYTES4 = prove
 (`!z s. read(memory :> bytes(z,8 * 4)) s =
         val(read(memory :> bytes64 z) s) + 2 EXP 64 * val(read(memory :> bytes64(word_add z (word 8))) s) +
         2 EXP 128 * val(read(memory :> bytes64(word_add z (word 16))) s) +
         2 EXP 192 * val(read(memory :> bytes64(word_add z (word 24))) s)`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`z:int64`; `0`; `s:armstate`] M4_BYTES_ADD4) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL; ADD_CLAUSES; MULT_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[]);;

let M4_FINAL4 = prove(m4_final4_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `kk = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k = 4` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[m4_c0_inv; m4_frame; m4_win] THEN
  REWRITE_TAC[ARITH_RULE `8 * 4 - 32 = 0 /\ 0 < 4 /\ 4 MOD 4 = 0`; MULT_CLAUSES] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w19:int64` `read X19` THEN GHOST_INTRO_TAC `w20:int64` `read X20` THEN
  GHOST_INTRO_TAC `w21:int64` `read X21` THEN GHOST_INTRO_TAC `w22:int64` `read X22` THEN
  GHOST_INTRO_TAC `w0:int64` `read X0` THEN GHOST_INTRO_TAC `mm:num` `bignum_from_memory(tp,4)` THEN
  BIGNUM_TERMRANGE_TAC `4` `a:num` THEN BIGNUM_TERMRANGE_TAC `4` `b:num` THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN BIGNUM_TERMRANGE_TAC `4` `mm:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BN_MUL_MONT_EXEC [3;5;7;9;11;13] (1--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BYTES4] THEN
  SUBGOAL_THEN `val (if carry_s13 then w19 else sum_s5:int64) + 2 EXP 64 * val (if carry_s13 then w20 else sum_s7:int64) +
     2 EXP 128 * val (if carry_s13 then w21 else sum_s9:int64) + 2 EXP 192 * val (if carry_s13 then w22 else sum_s11:int64) =
     (if carry_s13 then val(w19:int64) + 2 EXP 64 * val(w20:int64) + 2 EXP 128 * val(w21:int64) + 2 EXP 192 * val(w22:int64)
      else val(sum_s5:int64) + 2 EXP 64 * val(sum_s7:int64) + 2 EXP 128 * val(sum_s9:int64) + 2 EXP 192 * val(sum_s11:int64))`
   SUBST1_TAC THENL [BOOL_CASES_TAC `carry_s13:bool` THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `tl = val(w19:int64) + 2 EXP 64 * val(w20:int64) + 2 EXP 128 * val(w21:int64) + 2 EXP 192 * val(w22:int64)` THEN
  ABBREV_TAC `d = val(sum_s5:int64) + 2 EXP 64 * val(sum_s7:int64) + 2 EXP 128 * val(sum_s9:int64) + 2 EXP 192 * val(sum_s11:int64)` THEN
  SUBGOAL_THEN `&(val(w0:int64)):real <= &1` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  NOCARRY_SUMS_TAC `carry_s3:bool` [3] THEN
  SUBGOAL_THEN `val(sum_s3:int64) = val(w0:int64) + bitval cf` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN SUMS_EQS_TAC [3] []; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SBC_BORROW o check (fun th -> free_in `carry_s13:bool` (concl th) &&
     is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
  SUBGOAL_THEN `&d:real = &2 pow 256 * &(bitval carry_s11) + &tl - &n` ASSUME_TAC THENL
   [SUBGOAL_THEN `n = bigdigit n 0 + 2 EXP 64 * bigdigit n 1 + 2 EXP 128 * bigdigit n 2 + 2 EXP 192 * bigdigit n 3`
     MP_TAC THENL
     [REWRITE_TAC[GSYM LOWDIGITS_4] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["d"; "tl"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BIGDIGIT]) THEN
    SUMS_EQS_TAC [5;7;9;11] [];
    ALL_TAC] THEN
  SUBGOAL_THEN `tl < 2 EXP 256 /\ d < 2 EXP 256` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d"; "tl"] THEN
    MAP_EVERY (fun v -> MP_TAC(ISPEC v VAL_BOUND_64))
      [`w19:int64`;`w20:int64`;`w21:int64`;`w22:int64`;`sum_s5:int64`;`sum_s7:int64`;`sum_s9:int64`;`sum_s11:int64`] THEN
    ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if free_in `n:num` (concl th) || free_in `a:num` (concl th) || free_in `b:num` (concl th) ||
     free_in `mm:num` (concl th) then REWRITE_RULE[ARITH_RULE `64 * 4 = 256`] th else th) THEN
  REWRITE_TAC[ARITH_RULE `64 * 4 = 256`] THEN
  SUBGOAL_THEN `carry_s11 <=> tl < n` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> free_in `d:num` (concl th) && is_eq(concl th) &&
       type_of(lhs(concl th)) = `:real`)) THEN
    MAP_EVERY UNDISCH_TAC [`d < 2 EXP 256`; `tl < 2 EXP 256`; `n < 2 EXP 256`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW] THEN
    SPEC_TAC(`2 EXP 256`,`ee:num`) THEN GEN_TAC THEN
    BOOL_CASES_TAC `carry_s11:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NEGMODINV_ODD) THEN
  SUBGOAL_THEN `2 EXP 256 * (2 EXP 256 * (val(w0:int64) + bitval cf) + tl) = b * a + mm * n` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> free_in `lowdigits a 4` (concl th))) THEN
    SUBGOAL_THEN `lowdigits 0 4 = 0` SUBST1_TAC THENL [REWRITE_TAC[lowdigits; MOD_0]; ALL_TAC] THEN
    SUBGOAL_THEN `!v. v < 2 EXP 256 ==> lowdigits v 4 = v` (fun th -> SIMP_TAC[th; ASSUME `a < 2 EXP 256`; ASSUME `b < 2 EXP 256`; ASSUME `n < 2 EXP 256`]) THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[ARITH_RULE `64 * 4 = 256`];
      ALL_TAC] THEN
    EXPAND_TAC "tl" THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`4`; `n:num`; `a:num`; `b:num`; `mm:num`; `tl:num`; `val(w0:int64) + bitval cf`; `d:num`] M4_FINAL_ARITH) THEN
  REWRITE_TAC[ARITH_RULE `64 * 4 = 256`] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[COND_SWAP]);;

let m4_final8_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n tp fr ra kk pc.
   4 * kk = k /\\ 2 <= kk /\\ k < 2 EXP 58 /\\ (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   %s /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x10b0) /\\
          m4_fin k z x y m w a b n tp fr ra s)
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x11f8) /\\ %s)
     (%s)" m4_sub_nonover m4_sel_nonover m4_final_post m4_maychange);;

let M4_USE_TAC2 th : tactic =
  MP_TAC th THEN ASM_REWRITE_TAC[SOME_FLAGS] THEN DISCH_THEN USE_ENSURES_TAC THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];;

let M4_FINAL8 = prove(m4_final8_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[m4_fin; m4_frame] THEN
  GHOST_INTRO_TAC `t:num` `bignum_from_memory(word_add tp (word 32),k)` THEN
  GHOST_INTRO_TAC `cw:int64` `read X30` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `t:num` THEN BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x1130`
   `\s. read X27 s = z /\ read X26 s = tp /\ read X1 s = word_add tp (word 32) /\
        read X5 s = word(8 * k) /\ read SP s = tp /\ read X29 s = fr /\
        read (memory :> bytes64(word_add fr (word 8))) s = ra /\
        bignum_from_memory(word_add tp (word 32),k) s = t /\
        read X6 s = word(bigdigit (bignum_from_memory(z,k) s) 0) /\
        read X7 s = word(bigdigit (bignum_from_memory(z,k) s) 1) /\
        read X8 s = word(bigdigit (bignum_from_memory(z,k) s) 2) /\
        read X9 s = word(bigdigit (bignum_from_memory(z,k) s) 3) /\
        read X19 s = word(bigdigit t 0) /\ read X20 s = word(bigdigit t 1) /\
        read X21 s = word(bigdigit t 2) /\ read X22 s = word(bigdigit t 3) /\
        &(bignum_from_memory(z,k) s):real = &2 pow (64 * k) * &(bitval(t < n)) + &t - &n /\
        (read CF s <=> ~(val(cw:int64) < bitval(t < n)))` THEN CONJ_TAC THENL
   [M4_USE_TAC2(SPECL [`k:num`; `z:int64`; `m:int64`; `n:num`; `tp:int64`; `t:num`; `cw:int64`;
                       `fr:int64`; `ra:int64`; `kk:num`; `pc:num`] M4_SUB);
    ALL_TAC] THEN
  GHOST_INTRO_TAC `d:num` `bignum_from_memory(z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  M4_USE_TAC2(SPECL [`k:num`; `z:int64`; `tp:int64`; `t:num`; `d:num`; `~(val(cw:int64) < bitval(t < n))`;
                     `fr:int64`; `ra:int64`; `kk:num`; `pc:num`] M4_SEL) THEN
  DISCH_TAC THEN MATCH_MP_TAC M4_FINAL_ARITH THEN EXISTS_TAC `q:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NEGMODINV_ODD]);;

let m4_body_tm = parse_term (Printf.sprintf
 "!k z x y m w a b n n0p fr ra tp pc.
   k MOD 4 = 0 /\\ 4 <= k /\\ k < 2 EXP 58 /\\ (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   val x + 32 < 2 EXP 64 /\\ val m + 32 < 2 EXP 64 /\\ aligned 16 fr /\\
   word_sub fr (word(8 * k + 32)) = tp /\\
   %s /\\
   ALL (nonoverlapping (word_add fr (word 96),16))
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k); (word_add fr (word 8),8)] /\\
   %s /\\ %s
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xc3c) /\\
          read SP s = fr /\\ read X29 s = fr /\\ read X30 s = ra /\\
          read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
          read X0 s = z /\\ read X1 s = x /\\ read X2 s = y /\\ read X3 s = m /\\
          read X4 s = n0p /\\ read X5 s = word k /\\ read (memory :> bytes64 n0p) s = w /\\
          bignum_from_memory(x,k) s = a /\\ bignum_from_memory(y,k) s = b /\\
          bignum_from_memory(m,k) s = n)
     (\\s. read PC s = word(pc + 0x11f8) /\\ %s)
     (%s)" m4_nonover m4_sub_nonover m4_sel_nonover m4_final_post m4_maychange);;

(* Discharges a segment lemma's hypotheses from the assumptions. *)
let M4_DISCH_TAC : tactic =
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN
  TRY(REWRITE_TAC[MULT_CLAUSES; HIGHDIGITS_0] THEN NO_TAC) THEN ASM_ARITH_TAC;;

let M4_USE_TAC3 th : tactic =
  MP_TAC th THEN ANTS_TAC THENL
   [M4_DISCH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN DISCH_THEN USE_ENSURES_TAC THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];;

let M4_BODY = prove(m4_body_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?kk. 4 * kk = k` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `k DIV 4` THEN MP_TAC(SPECL [`k:num`; `4`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (tp:int64)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs(concl th) = `tp:int64` with _ -> false)) THEN
    ASM_SIMP_TAC[ALIGNED_WORD_SUB_EQ; ALIGNED_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
     [REWRITE_TAC[DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[divides] THEN EXISTS_TAC `2 * kk + 2` THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xc90`
   `\s. m4_c0_inv T k z x y m w a b n tp fr ra ra 0 0 (lowdigits b 4) 0 s` THEN CONJ_TAC THENL
   [M4_USE_TAC3(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `w:int64`; `a:num`; `b:num`;
                       `n:num`; `n0p:int64`; `fr:int64`; `ra:int64`; `tp:int64`; `pc:num`] M4_PRE);
    ALL_TAC] THEN
  ASM_CASES_TAC `k < 8` THENL
   [ENSURES_SEQUENCE_TAC `pc + 0xd34`
     `\s. m4_c0_inv T k z x y m w a b n tp fr ra ra 0 0 (lowdigits b 4) 4 s` THEN CONJ_TAC THENL
     [M4_USE_TAC3(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `w:int64`; `a:num`; `b:num`;
                         `n:num`; `tp:int64`; `fr:int64`; `ra:int64`; `ra:int64`; `0`; `0`; `lowdigits b 4`;
                         `pc:num`] M4_C0_LOOP_0);
      M4_USE_TAC3(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `w:int64`; `a:num`; `b:num`;
                         `n:num`; `tp:int64`; `fr:int64`; `ra:int64`; `ra:int64`; `kk:num`; `pc:num`] M4_FINAL4)];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= kk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xe80` `\s. m4_row k z x y m w a b n tp fr ra 1 s` THEN CONJ_TAC THENL
   [M4_USE_TAC3(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `w:int64`; `a:num`; `b:num`;
                       `n:num`; `tp:int64`; `fr:int64`; `ra:int64`; `ra:int64`; `kk:num`; `pc:num`] M4_ROW_0);
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x10b0` `\s. m4_fin k z x y m w a b n tp fr ra s` THEN CONJ_TAC THENL
   [M4_USE_TAC3(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `w:int64`; `a:num`; `b:num`;
                       `n:num`; `tp:int64`; `fr:int64`; `ra:int64`; `kk:num`; `pc:num`] M4_ROWS);
    M4_USE_TAC3(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `w:int64`; `a:num`; `b:num`;
                       `n:num`; `tp:int64`; `fr:int64`; `ra:int64`; `kk:num`; `pc:num`] M4_FINAL8)]);;

let m4_subroutine_tm =
 `!z x y m n0p a b n w k pc stackpointer returnaddress.
     4 <= k /\ k < 2 EXP 58 /\ k MOD 4 = 0 /\ ~(k MOD 8 = 0 /\ x = y) /\
     val x + 32 < 2 EXP 64 /\ val m + 32 < 2 EXP 64 /\
     (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [(z,8 * k); (word_sub stackpointer (word(8 * k + 160)),8 * k + 160)]
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k); (n0p,8)] /\
     nonoverlapping (z,8 * k) (word_sub stackpointer (word(8 * k + 160)),8 * k + 160)
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
                      memory :> bytes(word_sub stackpointer (word(8 * k + 160)),8 * k + 160)])`;;

(* The dispatch at 0x0 to 0xc and 0x240 to 0x244 reaches the 4x routine for
   a width that is a multiple of four, unless it is a multiple of eight and
   x = y, the squaring that sqr8x takes. *)
let M4_DISPATCH = prove
 (`!k. k < 2 EXP 64 /\ k MOD 4 = 0
       ==> val(word_and (word k:int64) (word 3)) = 0 /\
           (val(word_and (word k:int64) (word 7)) = 0 <=> k MOD 8 = 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word 7:int64 = word(2 EXP 3 - 1) /\ word 3:int64 = word(2 EXP 2 - 1)`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let BN_MUL_MONT_MUL4X_SUBROUTINE_CORRECT = prove(m4_subroutine_tm,
  (MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`;
                       `a:num`; `b:num`; `n:num`; `w:int64`; `k:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 128 THEN
  MAP_EVERY X_GEN_TAC [`fr:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  STRIP_TAC) THEN
  (FIRST_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] o
    check (fun th -> try fst(dest_pair(lhand(concl th))) = `z:int64` &&
                         fst(dest_pair(rand(concl th))) <> `word pc:int64` &&
                         snd(dest_pair(rand(concl th))) = `8 * k + 160` with _ -> false)) THEN
  FRAME_SPLIT_TAC `128` `128` THEN
  FRAME_SPLIT_TAC `8 * k + 160` `8 * k + 32` THEN
  FRAME_SPLIT_TAC `120` `8` THEN
  FRAME_SPLIT_TAC `32` `16` THEN
  MAP_EVERY (fun (c1,l1,c2,l2) ->
    MP_TAC(SPECL [`word_add fr (word 128):int64`; c1; l1; c2; l2] SUBFRAME_DISJ) THEN
    ANTS_TAC THENL [UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC;
      DISCH_THEN(fun th -> ASSUME_TAC th THEN ASSUME_TAC(ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th))])
   [`120`,`8`,`8 * k + 160`,`8 * k + 32`; `32`,`16`,`8 * k + 160`,`8 * k + 32`;
    `32`,`16`,`120`,`8`; `128`,`128`,`8 * k + 160`,`8 * k + 32`] THEN
  SUBGOAL_THEN `aligned 16 (fr:int64)` ASSUME_TAC THENL
   [SUBGOAL_THEN `aligned 16 (word 128:int64)` ASSUME_TAC THENL
     [REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64; DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    ASM_MESON_TAC[ALIGNED_WORD_ADD_EQ];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_sub (word_add (fr:int64) (word 128)) (word 128) = fr`;
    WORD_RULE `word_sub (word_add (fr:int64) (word 128)) (word 120) = word_add fr (word 8)`;
    WORD_RULE `word_sub (word_add (fr:int64) (word 128)) (word 32) = word_add fr (word 96)`;
    REWRITE_RULE[ARITH_RULE `(8 * k + 32) + 128 = 8 * k + 160`]
     (SPECL [`fr:int64`; `8 * k + 32`] (WORD_RULE `!fr:int64 c. word_sub (word_add fr (word 128)) (word(c + 128)) = word_sub fr (word c)`))])) THEN
  (ABBREV_TAC `tp = word_sub fr (word(8 * k + 32)):int64` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> free_in `8 * k + 160` (concl th)))) THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MP_TAC(SPEC `k:num` M4_DISPATCH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst BN_MUL_MONT_EXEC]) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `k MOD 8 = 0` THENL
   [SUBGOAL_THEN `~(val(word_sub x y:int64) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `k MOD 8 = 0`]) THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_and (word k:int64) (word 7)) = 0`]) THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC (3--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(word_sub x y:int64) = 0)`]);
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(k MOD 8 = 0)`]) THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(word_and (word k:int64) (word 7)) = 0)`]) THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC (3--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_and (word k:int64) (word 3)) = 0`])] THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (5--11) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> free_in `word_and (word k:int64)` (concl th) ||
                                                    free_in `word_sub x y:int64` (concl th))))) THEN
  (MP_TAC(SPECL [`k:num`; `z:int64`; `x:int64`; `y:int64`; `m:int64`; `w:int64`; `a:num`; `b:num`; `n:num`;
                `n0p:int64`; `fr:int64`; `returnaddress:int64`; `tp:int64`; `pc:num`] M4_BODY) THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst BN_MUL_MONT_EXEC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s12" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (13--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
  (ABBREV_TAC `bs = word_sub (word_add fr (word 128)) (word(8 * k + 160)):int64` THEN
  SUBGOAL_THEN `fr:int64 = word_add bs (word(8 * k + 32)) /\ tp:int64 = bs` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tp"; "bs"] THEN
    REWRITE_TAC[ARITH_RULE `8 * k + 160 = (8 * k + 32) + 128`; WORD_ADD] THEN CONJ_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (maychange_term o concl)) THEN
  REWRITE_TAC[ASSUME `fr:int64 = word_add bs (word(8 * k + 32))`; ASSUME `tp:int64 = bs`] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC));;

(* ========================================================================= *)
(* The squaring routine, __bn_sqr8x_mont at 0x248 to 0xc10, which the        *)
(* dispatch reaches for a width that is a multiple of eight when x = y.      *)
(*                                                                           *)
(* It works in a frame of 2k words below the saved registers. It first sums  *)
(* the products a[i] * a[j] with i < j into the frame, eight words of a at   *)
(* a time; doubles that and adds the squares a[i]^2, which gives a^2; then   *)
(* reduces it eight words at a time, and ends with the conditional           *)
(* subtraction of n.                                                         *)
(* ========================================================================= *)

(* With kk = k / 8 blocks of eight words, a the number squared and tp the
   frame's base, the proof is segment lemmas:

   - S8_PRE, 0x268 to 0x2f0: the frame, zeroed from its ninth word on.
   - S8_ROWS, 0x2f0 to 0x680, from S8_TRI (a block's products among its own
     words) and S8_MUL8_SQR (eight words by eight) joined by a row's
     relation, S8_ROW_REL: after i rows the frame holds s8_off a i, the
     products of each of the first i blocks among its own words and with
     every word above it. S8_OFF_SQUARE is that twice all the rows plus the
     squares of the words, s8_dsq, make a^2.
   - S8_SA, 0x680 to 0x7e4: the doubling and the squares, four words of the
     frame a pass, leaving a^2 in the frame's 2k words.
   - S8_REDUCE, 0x7e4 to 0xa38, for kk >= 2: a round (S8_ROUND) is eight
     reduction steps (S8_RED8), each clearing the window's low word with a
     multiple q of n's low block, then q times n's other blocks
     (S8_MUL8_TAIL). After g rounds, 2^(512g) times what is left is a^2 plus
     n times the g blocks of q.
   - S8_FIN, 0xa38 to 0xbf0: the subtraction of n (S8_SUB) and the selection
     (S8_SEL), which also zeroes most of the frame: its stores through x2
     clear the lower k words, but those through x1 start 32 bytes past
     sp + 8k, so the four words there keep their values (S8_ONE's path, below,
     clears its whole scratch area); S8_FINAL_ARITH is the 4x path's
     M4_FINAL_ARITH on their result.
   - S8_ONE, 0x7e4 to 0xbf0, for kk = 1, where the code reduces, subtracts
     and selects in registers.
   - S8_BODY joins them from 0x268 to 0xbf0, and the subroutine theorem adds
     the dispatch, the register saves and the epilogue.

   Carries the code drops are proven zero from bounds on the sums they would
   carry out of (S8_DECARRY_TAC, S8_PASS_NOCARRY, S8_REDPASS_NOCARRY). *)

let s8_words (p:string) (lo:int) (hi:int) (sep:string) : string =
  String.concat sep (map (fun i -> p ^ string_of_int i) (lo--hi));;

(* "read X6 s = a0 /\ ... /\ read X13 s = a7", for eight registers from
   X<reg> and eight variables <v><lo>... *)
let s8_reads (reg:int) (v:string) (lo:int) : string =
  String.concat " /\\ " (map (fun i -> Printf.sprintf "read X%d s = %s%d" (reg + i) v (lo + i)) (0--7));;

(* The window X19..X26 read in the state s, as a word list. *)
let s8_win = "[read X19 s; read X20 s; read X21 s; read X22 s; read X23 s; read X24 s; read X25 s; read X26 s]";;

(* The sum of a[i] * a[j] * 2^(64 * (i + j)) over i < j < 8. *)
let s8_tri = new_definition (parse_term (
  "s8_tri (a0:int64) (a1:int64) (a2:int64) (a3:int64) (a4:int64) (a5:int64) (a6:int64) (a7:int64) = " ^
  String.concat " + " (List.concat (map (fun i -> map (fun j ->
    Printf.sprintf "2 EXP %d * (val a%d * val a%d)" (64 * (i + j)) j i) ((i+1)--7)) (0--6)))));;

(* Sets to zero the carries the code drops, where the decarry rule's interval
   bounds show them zero. *)
let S8_DECARRY_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  ACCUMULATOR_ASSUM_LIST(fun ths ->
    let zs = filter (fun th -> can (term_match [] `&(bitval c):real = &0`) (concl th)) (DECARRY_RULE ths) in
    let ncs = map (REWRITE_RULE[REAL_OF_NUM_EQ; BITVAL_EQ_0]) zs in
    RULE_ASSUM_TAC(REWRITE_RULE(BITVAL_CLAUSES :: ncs)));;

(* Proves an equation between sums of the accumulated words from the
   equations defining them. *)
let S8_DESUM_TAC : tactic =
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;;

(* The products of eight words of a among themselves, 0x2f0 to 0x4e4: they
   are added to the window, whose low eight words go to dst. The window's
   top word X26 is left stale. *)
let S8_TRI = prove(parse_term (Printf.sprintf
 "!dst a0 a1 a2 a3 a4 a5 a6 a7 w19 w20 w21 w22 w23 w24 w25 w26 x1 x3 x5 pc.
   nonoverlapping (dst:int64,64) (word pc,LENGTH bn_mul_mont_mc)
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x2f0) /\\
          read X2 s = dst /\\ read X1 s = x1 /\\ read X3 s = x3 /\\ read X5 s = x5 /\\ %s /\\ %s)
     (\\s. read PC s = word(pc + 0x4e4) /\\ read X2 s = word_add dst (word 64) /\\
          read X27 s = word_sub x3 x1 /\\ read X14 s = word_sub x3 x5 /\\
          bignum_from_memory(dst,8) s +
          2 EXP 512 * bignum_of_wordlist [read X19 s; read X20 s; read X21 s; read X22 s;
                                          read X23 s; read X24 s; read X25 s] =
          bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] +
          s8_tri a0 a1 a2 a3 a4 a5 a6 a7)
     (MAYCHANGE [PC; X2; X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(dst,64)])"
   (s8_reads 6 "a" 0) (s8_reads 19 "w" 19)),
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X2`;`X27`]
   [1;2;3;4;5;6;7;8;9;10;11;13;15;17;21;23;25;27;28;29;30;31;32;33;34;35;36;37;38;39;41;43;45;49;
    51;53;54;55;56;57;58;59;60;61;62;63;65;67;69;73;75;76;77;78;79;80;81;82;83;85;87;89;93;94;95;
    96;97;98;99;101;103;105;106;108;109;110;112;114;115;116;119;121;122;125] (1--125) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[s8_tri] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  S8_DECARRY_TAC THEN S8_DESUM_TAC);;

(* Eight words b times the eight words X6..X13, added to the window with its
   carry: the loops at 0x538 and at 0x8cc, which are the same code. b[0] is
   in X4 and the rest are read from qp; the low eight words go to dst and
   the window and the carry flag keep the rest. *)
let s8_mul8_tm (base:int) = parse_term (Printf.sprintf
 "!dst qp b0 b1 b2 b3 b4 b5 b6 b7 x6 x7 x8 x9 x10 x11 x12 x13 w19 w20 w21 w22 w23 w24 w25 w26 cf pc.
   nonoverlapping (dst:int64,64) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (dst,64) (qp:int64,64)
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\
          read X2 s = dst /\\ read X0 s = word_add qp (word 64) /\\
          read X27 s = word 18446744073709551552 /\\ read X4 s = b0 /\\
          %s /\\ %s /\\ %s /\\ read CF s = cf)
     (\\s. read PC s = word(pc + %d) /\\ read X2 s = word_add dst (word 64) /\\
          bignum_from_memory(dst,8) s +
          2 EXP 512 * (bignum_of_wordlist %s + 2 EXP 512 * bitval(read CF s)) =
          (bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] + 2 EXP 512 * bitval cf) +
          bignum_of_wordlist [b0; b1; b2; b3; b4; b5; b6; b7] *
          bignum_of_wordlist [x6; x7; x8; x9; x10; x11; x12; x13])
     (MAYCHANGE [PC; X2; X4; X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(dst,64)])"
   base
   (String.concat " /\\ " (map (fun i -> Printf.sprintf
      "read (memory :> bytes64(word_add qp (word %d))) s = b%d" (8 * i) i) (1--7)))
   (s8_reads 6 "x" 6) (s8_reads 19 "w" 19) (base + 0x98) s8_win);;

let S8_MUL8_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X2`;`X27`]
   (let one = [1;3;5;6;7;8;9;10;11;12;13;14;15;17;19;21;23;25;27;29;31;34;35;36;37] in
    List.concat (map (fun t -> map (fun i -> 38 * t + i) one) (0--7))) (1--304) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  S8_DECARRY_TAC THEN S8_DESUM_TAC;;

let S8_MUL8_SQR = prove(s8_mul8_tm 0x538, S8_MUL8_TAC);;
let S8_MUL8_TAIL = prove(s8_mul8_tm 0x8cc, S8_MUL8_TAC);;

(* The reduction's low word: with q = w * t, the low word of n[0] * q and t
   sum to 2^64 unless t is zero. The code never computes that low word and
   takes its carry from comparing t with 1. *)
let S8_LOWWORD = prove
 (`!(n0:int64) (w:int64) (t:int64).
     (val n0 * val w + 1 == 0) (mod (2 EXP 64))
     ==> val(word(val n0 * val(word(val w * val t):int64)):int64) + val t =
         2 EXP 64 * bitval(~(val t = 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`val(n0:int64)`; `w:int64`; `t:int64`; `word(val(t:int64) * val(w:int64)):int64`;
                `word(bigdigit (val(n0:int64)) 0 * val(word(val(t:int64) * val(w:int64)):int64)):int64`]
               MONT_LOWWORD) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
  SUBGOAL_THEN `bigdigit (val(n0:int64)) 0 = val n0` SUBST1_TAC THENL
   [REWRITE_TAC[bigdigit; MULT_CLAUSES; EXP; DIV_1] THEN MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND_64];
    REWRITE_TAC[MULT_SYM]]);;

let S8_RED_NOCARRY = prove
 (`!c x ww q nn. 2 EXP 64 * (x + 2 EXP 512 * bitval c) = ww + q * nn /\
                 ww < 2 EXP 512 /\ q < 2 EXP 64 /\ nn < 2 EXP 512 ==> ~c`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `2 EXP 64 - 1`; `nn:num`; `2 EXP 512 - 1`] LE_MULT2) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  UNDISCH_TAC `ww < 2 EXP 512` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let S8_WL8_BOUND = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7:int64. bignum_of_wordlist [a0; a1; a2; a3; a4; a5; a6; a7] < 2 EXP 512`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `[a0; a1; a2; a3; a4; a5; a6; a7]:int64 list` BIGNUM_OF_WORDLIST_BOUND) THEN
  DISCH_THEN(MP_TAC o SPEC `8`) THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* One reduction step, 0x7e4 to 0x870: with q = w * t[0] in X28, the window
   plus q times n's low eight words is shifted down a word, q is stored at
   dst, and X28 gets the next q. *)
let S8_RED1 = prove(parse_term (Printf.sprintf
 "!dst n0 n1 n2 n3 n4 n5 n6 n7 (w:int64) w19 w20 w21 w22 w23 w24 w25 w26 x27 pc.
   nonoverlapping (dst:int64,8) (word pc,LENGTH bn_mul_mont_mc) /\\
   (val(n0:int64) * val w + 1 == 0) (mod (2 EXP 64))
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x7e4) /\\
          read X2 s = dst /\\ read X27 s = x27 /\\ read X4 s = w /\\
          read X28 s = word(val w * val(w19:int64)) /\\ %s /\\ %s)
     (\\s. read PC s = word(pc + 0x870) /\\ read X2 s = word_add dst (word 8) /\\
          read X27 s = word_sub x27 (word 1) /\\
          read X28 s = word(val w * val(read X19 s)) /\\
          read (memory :> bytes64 dst) s = word(val w * val w19) /\\
          2 EXP 64 * bignum_of_wordlist %s =
          bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] +
          val(word(val w * val w19):int64) * bignum_of_wordlist [n0; n1; n2; n3; n4; n5; n6; n7])
     (MAYCHANGE [PC; X2; X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(dst,8)])"
   (s8_reads 6 "n" 0) (s8_reads 19 "w" 19) s8_win),
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n0:int64`; `w:int64`; `w19:int64`] S8_LOWWORD) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q:int64 = word(val(w:int64) * val(w19:int64))` THEN DISCH_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X2`;`X27`]
   [1;3;5;6;7;8;9;10;11;12;13;14;15;16;18;20;23;25;27;29;32;33;34;35] (1--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CMP_ONE_CARRY o check (fun th -> let c = concl th in
     is_eq c && type_of(lhs c) = `:real` && free_in `carry_s6:bool` c)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  ABBREV_TAC `cz <=> ~(val(w19:int64) = 0)` THEN
  SUBGOAL_THEN `2 EXP 64 * (bignum_of_wordlist [sum_s23; sum_s25; sum_s27; sum_s29; sum_s32; sum_s33; sum_s34; sum_s35] +
                            2 EXP 512 * bitval carry_s35) =
                bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] +
                val(q:int64) * bignum_of_wordlist [n0; n1; n2; n3; n4; n5; n6; n7]` ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN REAL_EQS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~carry_s35` ASSUME_TAC THENL
   [MATCH_MP_TAC S8_RED_NOCARRY THEN
    MAP_EVERY EXISTS_TAC [`bignum_of_wordlist [sum_s23; sum_s25; sum_s27; sum_s29; sum_s32; sum_s33; sum_s34; sum_s35]`;
      `bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26]`; `val(q:int64)`;
      `bignum_of_wordlist [n0; n1; n2; n3; n4; n5; n6; n7]`] THEN
    ASM_REWRITE_TAC[VAL_BOUND_64; S8_WL8_BOUND];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `2 EXP 512` (concl th))) THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES]]);;

let S8_RED_COMBINE = prove
 (`!e w0 w1 w2 ql q nn.
     e * w1 = w0 + ql * nn /\ 2 EXP 64 * w2 = w1 + q * nn
     ==> (e * 2 EXP 64) * w2 = w0 + (ql + e * q) * nn`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MULT_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let S8_GHOST_WIN : tactic =
  MAP_EVERY (fun (v,r) -> GHOST_INTRO_TAC (mk_var(v,`:int64`))
     (mk_comb(`read:(armstate,int64)component->armstate->int64`,r)))
   ["v19",`X19`; "v20",`X20`; "v21",`X21`; "v22",`X22`; "v23",`X23`; "v24",`X24`; "v25",`X25`; "v26",`X26`];;

(* The eight reduction steps, 0x7e4 to 0x874: 2^512 times the new window is
   the old one plus n's low eight words times the eight words of q, which
   are left at dst. *)
let S8_RED8 = prove(parse_term (Printf.sprintf
 "!dst n0 n1 n2 n3 n4 n5 n6 n7 (w:int64) w19 w20 w21 w22 w23 w24 w25 w26 pc.
   nonoverlapping (dst:int64,64) (word pc,LENGTH bn_mul_mont_mc) /\\
   (val(n0:int64) * val w + 1 == 0) (mod (2 EXP 64))
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x7e4) /\\
          read X2 s = dst /\\ read X27 s = word 8 /\\ read X4 s = w /\\
          read X28 s = word(val w * val(w19:int64)) /\\ %s /\\ %s)
     (\\s. read PC s = word(pc + 0x874) /\\ read X2 s = word_add dst (word 64) /\\
          read X28 s = word(val w * val(read X19 s)) /\\
          2 EXP 512 * bignum_of_wordlist %s =
          bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] +
          bignum_from_memory(dst,8) s * bignum_of_wordlist [n0; n1; n2; n3; n4; n5; n6; n7])
     (MAYCHANGE [PC; X2; X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(dst,64)])"
   (s8_reads 6 "n" 0) (s8_reads 19 "w" 19) s8_win),
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `8` `pc + 0x7e4` `pc + 0x870`
   (parse_term (Printf.sprintf
    "\\i s. read X2 s = word_add dst (word(8 * i)) /\\ read X27 s = word(8 - i) /\\ read X4 s = w /\\
          read X28 s = word(val w * val(read X19 s)) /\\ %s /\\
          2 EXP (64 * i) * bignum_of_wordlist %s =
          bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] +
          bignum_from_memory(dst,i) s * bignum_of_wordlist [n0; n1; n2; n3; n4; n5; n6; n7]"
    (s8_reads 6 "n" 0) s8_win)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; EXP; READ_MEMORY_BYTES_TRIVIAL; ADD_CLAUSES];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN S8_GHOST_WIN THEN
    GHOST_INTRO_TAC `ql:num` `bignum_from_memory(dst,i)` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`word_add dst (word(8 * i)):int64`; `n0:int64`; `n1:int64`; `n2:int64`; `n3:int64`;
                  `n4:int64`; `n5:int64`; `n6:int64`; `n7:int64`; `w:int64`;
                  `v19:int64`; `v20:int64`; `v21:int64`; `v22:int64`; `v23:int64`; `v24:int64`;
                  `v25:int64`; `v26:int64`; `word(8 - i):int64`; `pc:num`] S8_RED1) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
    ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
    ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      SUBGOAL_THEN `8 - i = (8 - (i + 1)) + 1` SUBST1_TAC THENL [ASM_ARITH_TAC; CONV_TAC WORD_RULE];
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8 /\ 64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE `8 * i + 8 = 8 * (i + 1)`; BIGNUM_FROM_MEMORY_STEP] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      MATCH_MP_TAC S8_RED_COMBINE THEN
      EXISTS_TAC `bignum_of_wordlist [v19; v20; v21; v22; v23; v24; v25; v26]` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(val(word(8 - i):int64) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `8 - i < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The numbers the squaring computes.                                        *)
(* ------------------------------------------------------------------------- *)

(* The sum of a[p]^2 * 2^(128 * p) over p < n. *)
let s8_dsq = define
 `s8_dsq a 0 = 0 /\
  s8_dsq a (SUC n) = s8_dsq a n + 2 EXP (128 * n) * bigdigit a n * bigdigit a n`;;

let S8_DSQ_STEP = prove
 (`!a n. s8_dsq a (n + 1) = s8_dsq a n + 2 EXP (128 * n) * bigdigit a n * bigdigit a n`,
  REWRITE_TAC[GSYM ADD1; s8_dsq]);;

(* "d0 * d0 + 2 EXP 128 * d1 * d1 + ...", the squares of c digits. *)
let s8_squares (c:int) (dig:int -> string) : string =
  String.concat " + " (map (fun p ->
    (if p = 0 then "" else Printf.sprintf "2 EXP %d * " (128 * p)) ^ dig p ^ " * " ^ dig p) (0--(c-1)));;

let s8_dsq_add (c:int) = prove(parse_term (Printf.sprintf
  "!a n. s8_dsq a (n + %d) = s8_dsq a n + 2 EXP (128 * n) * (%s)" c
  (s8_squares c (fun p -> if p = 0 then "bigdigit a n" else Printf.sprintf "bigdigit a (n + %d)" p))),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 8 = (((((((n + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 /\
                          n + 4 = (((n + 1) + 1) + 1) + 1`; S8_DSQ_STEP] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ARITH_TAC);;

let S8_DSQ_ADD8 = s8_dsq_add 8;;
let S8_DSQ_ADD4 = s8_dsq_add 4;;

let s8_digits (v:string) : string =
  "[" ^ String.concat "; " (map (fun p -> Printf.sprintf "word(bigdigit %s %d):int64" v p) (0--7)) ^ "]";;

(* The low eight digits as a word list. *)
let S8_BLOCK = prove(parse_term (Printf.sprintf
  "!v. bignum_of_wordlist %s = lowdigits v 8" (s8_digits "v")),
  GEN_TAC THEN
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BIGDIGIT;
              ARITH_RULE `8 = (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1`; LOWDIGITS_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* The products among the low eight digits of v. *)
let s8_trin = new_definition (parse_term (
  "s8_trin v = s8_tri " ^ String.concat " " (map (fun p -> Printf.sprintf "(word(bigdigit v %d))" p) (0--7))));;

let S8_TRIN_SQUARE = prove(parse_term (Printf.sprintf
  "!v. lowdigits v 8 * lowdigits v 8 = 2 * s8_trin v + (%s)"
  (s8_squares 8 (fun p -> Printf.sprintf "bigdigit v %d" p))),
  GEN_TAC THEN
  REWRITE_TAC[GSYM S8_BLOCK; s8_trin; s8_tri; bignum_of_wordlist; VAL_WORD_BIGDIGIT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let S8_TRIN_LE = prove
 (`!v. s8_trin v <= lowdigits v 8 * lowdigits v 8`,
  GEN_TAC THEN REWRITE_TAC[S8_TRIN_SQUARE] THEN ARITH_TAC);;

let S8_TRIN_DIVIDES = prove
 (`!v. 2 EXP 64 divides s8_trin v`,
  GEN_TAC THEN REWRITE_TAC[s8_trin; s8_tri] THEN
  REWRITE_TAC(map (fun m -> ARITH_RULE(parse_term (Printf.sprintf
    "2 EXP %d = 2 EXP 64 * 2 EXP %d" (64 * m) (64 * (m - 1))))) (2--13)) THEN
  SPEC_TAC(`2 EXP 64`,`e:num`) THEN GEN_TAC THEN CONV_TAC NUMBER_RULE);;

(* What the first i rows of the first phase have added: row j adds the
   products among block j's digits, and block j times all the digits above
   it. *)
let s8_off = define
 `s8_off a 0 = 0 /\
  s8_off a (SUC i) = s8_off a i + 2 EXP (1024 * i) *
     (s8_trin (highdigits a (8 * i)) +
      2 EXP 512 * lowdigits (highdigits a (8 * i)) 8 * highdigits a (8 * i + 8))`;;

let S8_OFF_STEP = prove
 (`!a i. s8_off a (i + 1) = s8_off a i + 2 EXP (1024 * i) *
     (s8_trin (highdigits a (8 * i)) +
      2 EXP 512 * lowdigits (highdigits a (8 * i)) 8 * highdigits a (8 * i + 8))`,
  REWRITE_TAC[GSYM ADD1; s8_off]);;

let S8_HIGH_BLOCK = prove
 (`!a i. highdigits a (8 * i) = lowdigits (highdigits a (8 * i)) 8 + 2 EXP 512 * highdigits a (8 * i + 8)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`highdigits a (8 * i)`; `8`] (CONJUNCT1(CONJUNCT2 HIGH_LOW_DIGITS))) THEN
  REWRITE_TAC[HIGHDIGITS_HIGHDIGITS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN REWRITE_TAC[]);;

(* Twice the rows, the squares of the digits below them, and the square of
   what is above make a^2. *)
let S8_OFF_SQUARE = prove
 (`!a i. 2 * s8_off a i + s8_dsq a (8 * i) +
         2 EXP (1024 * i) * highdigits a (8 * i) * highdigits a (8 * i) = a * a`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[s8_off; s8_dsq; MULT_CLAUSES; EXP; HIGHDIGITS_0; ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ADD1; S8_OFF_STEP; ARITH_RULE `8 * (i + 1) = 8 * i + 8`; S8_DSQ_ADD8] THEN
  REWRITE_TAC[ARITH_RULE `128 * 8 * i = 1024 * i /\ 1024 * (i + 1) = 1024 * i + 1024`; EXP_ADD] THEN
  MP_TAC(SPEC `highdigits a (8 * i)` S8_TRIN_SQUARE) THEN
  REWRITE_TAC[BIGDIGIT_HIGHDIGITS; ADD_CLAUSES] THEN
  MP_TAC(SPECL [`a:num`; `i:num`] S8_HIGH_BLOCK) THEN
  ABBREV_TAC `bl = lowdigits (highdigits a (8 * i)) 8` THEN
  SPEC_TAC(`highdigits a (8 * i)`,`h:num`) THEN GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  SPEC_TAC(`s8_trin (bl + 2 EXP 512 * highdigits a (8 * i + 8))`,`tr:num`) THEN
  SPEC_TAC(`highdigits a (8 * i + 8)`,`h':num`) THEN
  SPEC_TAC(`2 EXP (1024 * i)`,`e:num`) THEN
  REPEAT GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUM_RING);;

(* The rows so far are below 2^(512 * (kk + i)). *)
let S8_OFF_BOUND = prove
 (`!a kk i. a < 2 EXP (512 * kk) ==> s8_off a i < 2 EXP (512 * (kk + i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `i:num`] S8_OFF_SQUARE) THEN
  MP_TAC(SPECL [`a:num`; `8 * i`] (CONJUNCT1(CONJUNCT2 HIGH_LOW_DIGITS))) THEN
  MP_TAC(SPECL [`a:num`; `8 * i`] LOWDIGITS_BOUND) THEN
  REWRITE_TAC[ARITH_RULE `64 * 8 * i = 512 * i /\ 1024 * i = 512 * i + 512 * i /\ 512 * (kk + i) = 512 * kk + 512 * i`; EXP_ADD] THEN
  ABBREV_TAC `l = lowdigits a (8 * i)` THEN ABBREV_TAC `h = highdigits a (8 * i)` THEN
  ABBREV_TAC `e = 2 EXP (512 * i)` THEN ABBREV_TAC `s = s8_off a i` THEN
  ABBREV_TAC `d = s8_dsq a (8 * i)` THEN
  DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 * s + d = l * l + 2 * l * e * h` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `d:num` (concl th))) THEN CONV_TAC NUM_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s <= l * (l + e * h)` ASSUME_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `d:num` (concl th))) THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `l * (l + e * h)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[]);;

let S8_OFF_DIVIDES = prove
 (`!a i. 2 EXP 64 divides s8_off a i`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[s8_off; DIVIDES_0] THEN
  MATCH_MP_TAC DIVIDES_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVIDES_LMUL THEN
  MATCH_MP_TAC DIVIDES_ADD THEN REWRITE_TAC[S8_TRIN_DIVIDES] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 512 = 2 EXP 64 * 2 EXP 448`] THEN
  SPEC_TAC(`2 EXP 64`,`e:num`) THEN GEN_TAC THEN CONV_TAC NUMBER_RULE);;

(* All the rows, doubled, and the squares of the digits make a^2. *)
let S8_OFF_FINAL = prove
 (`!a kk. a < 2 EXP (512 * kk) ==> 2 * s8_off a kk + s8_dsq a (8 * kk) = a * a`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:num`; `kk:num`] S8_OFF_SQUARE) THEN
  SUBGOAL_THEN `highdigits a (8 * kk) = 0` SUBST1_TAC THENL
   [REWRITE_TAC[HIGHDIGITS_EQ_0] THEN ASM_REWRITE_TAC[ARITH_RULE `64 * 8 * kk = 512 * kk`];
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]]);;

(* Linear arithmetic from the assumptions that are plain: (in)equalities
   over variables and numerals. The others would only slow it down. *)
let S8_ARITH_TAC : tactic =
  fun (asl,w) ->
    let okc = ["+"; "*"; "-"; "<"; "<="; "="; "~"; "NUMERAL"; "BIT0"; "BIT1"; "_0"; ">"; ">="; "EXP"] in
    let rec ok t =
      if is_var t then type_of t = `:num` else
      if is_const t then mem (fst(dest_const t)) okc else
      if is_comb t then ok (rator t) && ok (rand t) else false in
    let ths = filter (ok o concl) (map snd asl) in
    (MAP_EVERY MP_TAC ths THEN ARITH_TAC) (asl,w);;

(* The eight words at base and the rest, from base holding t's digits from p. *)
let S8_HIGH8 = prove(parse_term (Printf.sprintf
 "!base nn t p s.
     bignum_from_memory(base,nn) s = highdigits t p /\\ 8 <= nn
     ==> bignum_from_memory(word_add base (word 64),nn - 8) s = highdigits t (p + 8) /\\
         read(memory :> bytes64 base) s = word(bigdigit t p) /\\ %s"
   (String.concat " /\\ " (map (fun r -> Printf.sprintf
      "read(memory :> bytes64(word_add base (word %d))) s = word(bigdigit t (p + %d))" (8 * r) r) (1--7)))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r < 8 ==> read(memory :> bytes64(word_add base (word(8 * r)))) s =
                              word(bigdigit t (p + r))` MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM BIGDIGIT_HIGHDIGITS] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC BN_DIGIT_READ THEN EXISTS_TAC `nn:num` THEN REWRITE_TAC[] THEN S8_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun r -> MP_TAC(SPEC r th)) [`0`; `1`; `2`; `3`; `4`; `5`; `6`; `7`]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM HIGHDIGITS_HIGHDIGITS] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try is_comb(lhs(concl th)) && fst(strip_comb(rhs(concl th))) = `highdigits` with _ -> false)) THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Two pointers into the same array are equal when their offsets are. *)
let S8_PTR_EQ = prove
 (`!(xb:int64) p q. p < 2 EXP 64 /\ q < 2 EXP 64
     ==> (val(word_sub (word_add xb (word p)) (word_add xb (word q))) = 0 <=> p = q)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (x:int64) a) (word_add x b) = word_sub a b`] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]);;

(* The read of the digit at addr, from the array at b that holds v. *)
let S8_DIGIT = prove
 (`!base len v s i (a:int64).
     read (memory :> bytes(base,8 * len)) s = v /\ i < len /\ a = word_add base (word(8 * i))
     ==> read (memory :> bytes64 a) s = word(bigdigit v i)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BN_DIGIT_READ_BYTES THEN
  EXISTS_TAC `len:num` THEN ASM_REWRITE_TAC[]);;

let S8_READ_TAC (st:term) (b:term) (len:term) (i:term) (addr:term) : tactic =
  fun (asl,w) ->
    let pat = vsubst [b,`b:int64`; len,`len:num`; st,`s:armstate`]
      `read (memory :> bytes((b:int64),8 * len)) (s:armstate)` in
    let th = snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = pat) asl) in
    let v = rhs(concl th) in
    let tm = subst [addr,`a:int64`; st,`s:armstate`; v,`v:num`; i,`i:num`]
      `read (memory :> bytes64 (a:int64)) s = word(bigdigit v i)` in
    (SUBGOAL_THEN tm MP_TAC THENL
      [MATCH_MP_TAC S8_DIGIT THEN MAP_EVERY EXISTS_TAC [b; len] THEN
       CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC] THEN CONJ_TAC THENL
        [S8_ARITH_TAC;
         FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
                REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]];
       REWRITE_TAC[BIGDIGIT_HIGHDIGITS] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
       REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC]) (asl,w);;

(* Reads of the eight digits from index i at address b' + off, off a
   numeral or a term. *)
let S8_READ8_TAC (st:term) (b:term) (len:term) (i:term) (b':term) (off:term) : tactic =
  MAP_EVERY (fun p ->
    let it = if p = 0 then i else mk_binop `(+):num->num->num` i (mk_small_numeral p) in
    let ot = if p = 0 then off else mk_binop `(+):num->num->num` off (mk_small_numeral(8 * p)) in
    let ot = if is_numeral off then rhs(concl(NUM_REDUCE_CONV ot)) else ot in
    let addr = if ot = `0` then b' else mk_comb(mk_comb(`word_add:int64->int64->int64`,b'),mk_comb(`word:num->int64`,ot)) in
    S8_READ_TAC st b len it addr) (0--7);;

(* Names the values read t in the state s after a big step. *)
let S8_NAME_TAC (s:string) (l:(string*term) list) : tactic =
  let st = mk_var(s,`:armstate`) in
  MAP_EVERY (fun (n,c) ->
    let r = mk_icomb(mk_icomb(`read:(armstate,A)component->armstate->A`,c),st) in
    ABBREV_TAC(mk_eq(mk_var(n,type_of r),r))) l;;

let s8_win_regs = [`X19`;`X20`;`X21`;`X22`;`X23`;`X24`;`X25`;`X26`];;
let S8_NAME_WIN_TAC (s:string) (p:string) : tactic =
  S8_NAME_TAC s (map2 (fun i r -> (p ^ string_of_int i, r)) (19--26) s8_win_regs);;

(* Proves read(memory :> bytes(a',8 * l')) s = highdigits v n from the
   assumption that gives v as the array at some a. *)
let S8_HIGH_TAC (v:term) : tactic =
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM BIGNUM_FROM_MEMORY_BYTES]) THEN
  FIRST_X_ASSUM(fun th ->
    if (try rhs(concl th) = v && can (term_match [] `bignum_from_memory (a,l) s`) (lhs(concl th)) with _ -> false)
    then GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th] else NO_TAC) THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
           REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN S8_ARITH_TAC];
    S8_ARITH_TAC];;

(* Closes an equation between numbers from the real equations among the
   assumptions, the accumulated ones included. *)
let S8_REAL_TAC : tactic =
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BIGDIGIT; GSYM REAL_OF_NUM_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bignum_of_wordlist; VAL_WORD_BIGDIGIT; ADD_CLAUSES; VAL_WORD_BITVAL;
                              GSYM REAL_OF_NUM_CLAUSES]) THEN
  REAL_EQS_TAC;;
(* A pass's carry out is zero: what the pass has built is below the place
   of that carry. *)
let S8_PASS_NOCARRY = prove
 (`!e x tt c ww lu tri aa ll.
     x + (e * 2 EXP 512) * (tt + 2 EXP 512 * bitval c) =
     (ww + 2 EXP 512 * lu) + tri + 2 EXP 512 * aa * ll /\
     ww < 2 EXP 512 /\ lu < e /\ tri <= aa * aa /\ aa < 2 EXP 512 /\ ll < e
     ==> ~c`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aa * (ll + 1) <= aa * e` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `aa * aa <= 2 EXP 512 * aa` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `aa * e <= (2 EXP 512 - 1) * e` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  MAP_EVERY UNDISCH_TAC [`ww < 2 EXP 512`; `lu < e`; `tri <= aa * aa`] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES; GSYM MULT_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`aa * ll`,`p1:num`) THEN SPEC_TAC(`aa * aa`,`p2:num`) THEN SPEC_TAC(`aa * e`,`p3:num`) THEN
  SPEC_TAC(`e * tt`,`p4:num`) THEN REPEAT GEN_TAC THEN ARITH_TAC);;

let S8_PASS_COMBINE = prove
 (`!ee lo m8 vv cfv tt w2 lu tri aa lh hb ub ww.
     lo + (ee * 2 EXP 512) * (vv + 2 EXP 512 * cfv) =
     (ww + 2 EXP 512 * lu) + tri + 2 EXP 512 * aa * lh /\
     m8 + 2 EXP 512 * tt = (vv + 2 EXP 512 * cfv) + aa * hb /\
     w2 = tt + ub
     ==> (lo + (ee * 2 EXP 512) * m8) + ((ee * 2 EXP 512) * 2 EXP 512) * w2 =
         (ww + 2 EXP 512 * (lu + (ee * 2 EXP 512) * ub)) + tri + 2 EXP 512 * aa * (lh + ee * hb)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN MP_TAC) THEN
  SPEC_TAC(`2 EXP 512`,`d:num`) THEN GEN_TAC THEN CONV_TAC NUM_RING);;
let s8_digits_from (v:string) (i:string) : string =
  "[" ^ String.concat "; " (map (fun p ->
     if p = 0 then Printf.sprintf "word(bigdigit %s (%s)):int64" v i
     else Printf.sprintf "word(bigdigit %s (%s + %d)):int64" v i p) (0--7)) ^ "]";;

(* Eight more low digits. *)
let S8_LOWDIGITS_BLOCK = prove(parse_term (Printf.sprintf
  "!v l. lowdigits v (8 * (l + 1)) = lowdigits v (8 * l) + 2 EXP (512 * l) * bignum_of_wordlist %s"
  (s8_digits_from "v" "8 * l")),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * (l + 1) = (((((((8 * l + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1`;
              LOWDIGITS_CLAUSES; bignum_of_wordlist; VAL_WORD_BIGDIGIT] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; EXP_ADD] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* Eight more words of an array. *)
let S8_BYTES_APPEND = prove
 (`!base c s. read(memory :> bytes(base,8 * 8 * (c + 1))) s =
              read(memory :> bytes(base,8 * 8 * c)) s +
              2 EXP (512 * c) * read(memory :> bytes(word_add base (word(64 * c)),8 * 8)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `8 * (c + 1) = 8 * c + 8`; BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `64 * 8 * c = 512 * c /\ 8 * 8 * c = 64 * c`] THEN ARITH_TAC);;

(* Writes constant powers of two as numerals, in the goal and assumptions,
   as the simulator does. *)
let S8_NUMS_TAC : tactic =
  CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_EXP_CONV));;
let S8_NUMS (th:thm) : thm = CONV_RULE(DEPTH_CONV NUM_EXP_CONV) th;;
let S8_OFFSET_TAC : tactic =
  FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
         REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN S8_ARITH_TAC];;

let S8_ADDR_TAC (eqs:term list) : tactic =
  MAP_EVERY (fun e -> SUBGOAL_THEN e (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [S8_OFFSET_TAC; ALL_TAC]) eqs;;

(* Closes an equation between numbers from the accumulated equations alone. *)
let S8_ACC_TAC : tactic =
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BIGDIGIT; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MAP_EVERY (MP_TAC o REWRITE_RULE[VAL_WORD_BIGDIGIT; ADD_CLAUSES; VAL_WORD_BITVAL])) THEN
  CONV_TAC REAL_ARITH;;

let s8_awl = "bignum_of_wordlist [a0; a1; a2; a3; a4; a5; a6; a7]";;
let s8_wwl = "bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26]";;

let S8_TRI_LE = prove(parse_term (Printf.sprintf
  "!a0 a1 a2 a3 a4 a5 a6 a7. s8_tri a0 a1 a2 a3 a4 a5 a6 a7 <= %s * %s" s8_awl s8_awl),
  REPEAT GEN_TAC THEN REWRITE_TAC[s8_tri; bignum_of_wordlist] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
(* Eight words of memory as a word list. *)
let S8_BYTES8 = prove(parse_term (Printf.sprintf
 "!(a:int64) s. read(memory :> bytes(a,8 * 8)) s =
     bignum_of_wordlist [read(memory :> bytes64 a) s; %s]"
   (String.concat "; " (map (fun p -> Printf.sprintf "read(memory :> bytes64(word_add a (word %d))) s" (8 * p)) (1--7)))),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN REWRITE_TAC[]);;

(* Proves read(memory :> bytes(a,8 * 8)) s = bignum_of_wordlist [...] from
   the assumptions about the eight words. *)
let S8_BYTES8_TAC : tactic =
  REWRITE_TAC[S8_BYTES8] THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];;

(* Sixteen words, eight more, and the rest make the whole array. *)
let S8_SPLIT3 = prove
 (`!base l s.
     read(memory :> bytes(base,128)) s +
     2 EXP 1024 * (read(memory :> bytes(word_add base (word 128),8 * 8)) s +
                   2 EXP 512 * read(memory :> bytes(word_add base (word 192),8 * 8 * l)) s) =
     read(memory :> bytes(base,8 * 8 * (l + 3))) s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word 128:int64 = word(8 * 16) /\ word 192:int64 = word(8 * 16 + 8 * 8) /\
                (base:int64,128) = (base,8 * 16)`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `8 * (l + 3) = 16 + (8 + 8 * l)`; BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One row of the first phase, 0x2f0 back to 0x2f0, for a block of a at xb   *)
(* with r - 1 >= 1 blocks above it: the products among the block's words     *)
(* and the block times the words above it are added in at base.              *)
(* ------------------------------------------------------------------------- *)

let s8_rowrel_maychange = "MAYCHANGE [PC; X0; X1; X2; X4; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
                 X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(base,64 * (r + 1))]";;
let s8_xb_words = "read (memory :> bytes64 xb) s = a0 /\\ " ^
  String.concat " /\\ " (map (fun p -> Printf.sprintf "read (memory :> bytes64(word_add xb (word %d))) s = a%d" (8 * p) p) (1--7));;

(* At 0x538, before the pass that multiplies by block l of hh, the words
   above the block at xb: the window and carry flag hold what is above the
   8 * (l + 1) words done so far. *)
let s8_pass_inv = Printf.sprintf
   "read X2 s = word_add base (word(64 * (l + 1))) /\\ read X0 s = word_add xb (word 64) /\\
    read X1 s = word_add xb (word(64 * (l + 2))) /\\ read X3 s = word_add xb (word(64 * r)) /\\
    read X27 s = word 18446744073709551552 /\\ read X4 s = a0 /\\ %s /\\ %s /\\
    bignum_from_memory(word_add xb (word 64),8 * (r - 1)) s = hh /\\
    bignum_from_memory(word_add base (word(64 * (l + 2))),8 * (r - 2 - l)) s = highdigits uh (8 * (l + 1)) /\\
    bignum_from_memory(base,8 * (l + 1)) s +
    2 EXP (512 * (l + 1)) * (bignum_of_wordlist %s + 2 EXP 512 * bitval(read CF s)) =
    (%s + 2 EXP 512 * lowdigits uh (8 * (l + 1))) + s8_tri a0 a1 a2 a3 a4 a5 a6 a7 +
    2 EXP 512 * %s * lowdigits hh (8 * l)"
   (String.concat " /\\ " (map (fun p -> Printf.sprintf "read X%d s = word(bigdigit hh (8 * l + %d))" (6 + p) p) (0--7)))
   s8_xb_words s8_win s8_wwl s8_awl;;
let s8_pass_inv_tm = parse_term ("\\(l:num) (s:armstate). " ^ s8_pass_inv);;
let s8_pass_at (t:term) = rand(concl(BETA_CONV(mk_comb(s8_pass_inv_tm,t))));;
let s8_pass_iv = parse_term
  ("\\(l:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x538) /\\ " ^ s8_pass_inv);;

let s8_rowrel_tm = parse_term (Printf.sprintf
 "!base xb r a0 a1 a2 a3 a4 a5 a6 a7 w19 w20 w21 w22 w23 w24 w25 w26 uh hh x5 pc.
   2 <= r /\\ r < 2 EXP 56 /\\
   nonoverlapping (base:int64,64 * (r + 1)) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (base,64 * (r + 1)) (xb:int64,64 * r)
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x2f0) /\\
          read X2 s = base /\\ read X1 s = word_add xb (word 64) /\\ read X3 s = word_add xb (word(64 * r)) /\\
          read X5 s = x5 /\\ %s /\\ %s /\\ %s /\\
          bignum_from_memory(word_add xb (word 64),8 * (r - 1)) s = hh /\\
          bignum_from_memory(word_add base (word 64),8 * (r - 1)) s = uh)
     (\\s. read PC s = word(pc + 0x2f0) /\\ read X2 s = word_add base (word 128) /\\
          read X1 s = word_add xb (word 128) /\\ %s /\\
          bignum_from_memory(base,16) s +
          2 EXP 1024 * (bignum_of_wordlist %s +
                        2 EXP 512 * bignum_from_memory(word_add base (word 192),8 * (r - 2)) s) =
          (%s + 2 EXP 512 * uh) + s8_tri a0 a1 a2 a3 a4 a5 a6 a7 + 2 EXP 512 * %s * hh)
     (%s)"
   (s8_reads 6 "a" 0) (s8_reads 19 "w" 19) s8_xb_words
   (String.concat " /\\ " (map (fun p -> Printf.sprintf "read X%d s = word(bigdigit hh %d)" (6 + p) p) (0--7)))
   s8_win s8_wwl s8_awl s8_rowrel_maychange);;

let s8_hb = parse_term ("bignum_of_wordlist " ^ s8_digits_from "hh" "8 * l");;
let s8_tl = `bignum_of_wordlist [t19; t20; t21; t22; t23; t24; t25; t26]`;;
let s8_vl = `bignum_of_wordlist [v19; v20; v21; v22; v23; v24; v25; v26]`;;
let s8_wl = `bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26]`;;
let s8_al = `bignum_of_wordlist [a0; a1; a2; a3; a4; a5; a6; a7]`;;
let s8_tr = `s8_tri a0 a1 a2 a3 a4 a5 a6 a7`;;

(* The pass at 0x538, from the invariant with its window ghosted as v19..
   and its array as lo: runs the multiplication and names its results m8,
   t19.., whose carry out is zero. Leaves the equation for the 8 * (l + 2)
   words now done. *)
let S8_PASS_MUL_TAC : tactic =
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL ([`word_add base (word(64 * (l + 1))):int64`; `xb:int64`] @
     map (fun i -> mk_var("a" ^ string_of_int i,`:int64`)) (0--7) @
     map (fun p -> mk_comb(`word:num->int64`,mk_comb(mk_comb(`bigdigit`,`hh:num`),
                     if p = 0 then `8 * l` else mk_binop `(+):num->num->num` `8 * l` (mk_small_numeral p)))) (0--7) @
     map (fun i -> mk_var("v" ^ string_of_int i,`:int64`)) (19--26) @ [`cf:bool`; `pc:num`]) S8_MUL8_SQR) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
  ANTS_TAC THENL [CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
  S8_NAME_TAC "s1" (["m8",`memory :> bytes(word_add base (word(64 * (l + 1))):int64,8 * 8)`; "cf'",`CF`]) THEN
  S8_NAME_WIN_TAC "s1" "t" THEN
  S8_ADDR_TAC [`word_add (word_add base (word (64 * (l + 1)))) (word 64):int64 = word_add base (word(64 * (l + 2)))`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; ARITH_RULE `512 * (l + 1) = 512 * l + 512`; EXP_ADD]) THEN
  SUBGOAL_THEN `lowdigits uh (8 * (l + 1)) < 2 EXP (512 * l) * 2 EXP 512 /\
                lowdigits hh (8 * (l + 1)) < 2 EXP (512 * l) * 2 EXP 512` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `512 * l + 512 = 64 * 8 * (l + 1)`; LOWDIGITS_BOUND]; ALL_TAC] THEN
  MP_TAC(SPECL [`2 EXP (512 * l)`; `lo:num`; `m8:num`; s8_vl; `bitval cf`;
                mk_binop `(+):num->num->num` s8_tl `2 EXP 512 * bitval cf'`;
                mk_binop `(+):num->num->num` s8_tl `2 EXP 512 * bitval cf'`;
                `lowdigits uh (8 * (l + 1))`; s8_tr; s8_al; `lowdigits hh (8 * l)`; s8_hb; `0`; s8_wl]
               S8_PASS_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; GSYM S8_LOWDIGITS_BLOCK] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `~cf'` ASSUME_TAC THENL
   [MATCH_MP_TAC S8_PASS_NOCARRY THEN
    MAP_EVERY EXISTS_TAC [`2 EXP (512 * l) * 2 EXP 512`; `lo + (2 EXP (512 * l) * 2 EXP 512) * m8`;
      s8_tl; s8_wl; `lowdigits uh (8 * (l + 1))`; s8_tr; s8_al; `lowdigits hh (8 * (l + 1))`] THEN
    ASM_REWRITE_TAC[S8_WL8_BOUND; S8_TRI_LE];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~cf'`; BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES]);;

let S8_ROW_REL = prove(s8_rowrel_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `8 * (r - 1)` `hh:num` THEN BIGNUM_TERMRANGE_TAC `8 * (r - 1)` `uh:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x538` (s8_pass_at `0`) THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`xb:int64`; `64 * r`; `64`] S8_PTR_EQ) THEN
    ANTS_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= r ==> ~(64 * r = 64)`] THEN DISCH_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    S8_READ8_TAC `s0:armstate` `word_add base (word 64):int64` `8 * (r - 1)` `0` `base:int64` `64` THEN
    S8_READ8_TAC `s0:armstate` `word_add xb (word 64):int64` `8 * (r - 1)` `0` `xb:int64` `64` THEN
    MP_TAC(SPECL [`base:int64`; `a0:int64`; `a1:int64`; `a2:int64`; `a3:int64`; `a4:int64`; `a5:int64`;
                  `a6:int64`; `a7:int64`; `w19:int64`; `w20:int64`; `w21:int64`; `w22:int64`; `w23:int64`;
                  `w24:int64`; `w25:int64`; `w26:int64`; `word_add xb (word 64):int64`;
                  `word_add xb (word(64 * r)):int64`; `x5:int64`; `pc:num`] S8_TRI) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
    ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
    ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
    S8_NAME_TAC "s1" (["lo",`memory :> bytes(base:int64,8 * 8)`] @
       map2 (fun i r -> ("t" ^ string_of_int i, r)) (19--25) (butlast s8_win_regs)) THEN
    SUBGOAL_THEN `read (memory :> bytes(word_add base (word 128),8 * 8 * (r - 2))) s1 = highdigits uh 8`
     ASSUME_TAC THENL [S8_HIGH_TAC `uh:num`; ALL_TAC] THEN
    ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [8;9;11;12;14;15;17;19] (2--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[LOWDIGITS_0; MULT_CLAUSES; ADD_CLAUSES; GSYM S8_BLOCK] THEN S8_REAL_TAC;
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x538` (s8_pass_at `0 + (r - 2)`) THEN CONJ_TAC THENL
   [M4_ITER_TAC s8_pass_iv `0` `r - 2` THEN X_GEN_TAC `l:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    S8_GHOST_WIN THEN GHOST_INTRO_TAC `cf:bool` `read CF` THEN
    GHOST_INTRO_TAC `lo:num` `bignum_from_memory(base,8 * (l + 1))` THEN
    MP_TAC(SPECL [`xb:int64`; `64 * (l + 2)`; `64 * r`] S8_PTR_EQ) THEN
    ANTS_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `l < r - 2 ==> ~(64 * (l + 2) = 64 * r)`] THEN DISCH_TAC THEN
    S8_PASS_MUL_TAC THEN
    S8_READ8_TAC `s1:armstate` `word_add base (word(64 * (l + 2))):int64` `8 * (r - 2 - l)` `0` `base:int64` `64 * (l + 2)` THEN
    S8_READ8_TAC `s1:armstate` `word_add xb (word 64):int64` `8 * (r - 1)` `8 * (l + 1)` `xb:int64` `64 * (l + 2)` THEN
    SUBGOAL_THEN `read (memory :> bytes(word_add base (word(64 * ((l + 1) + 2))),8 * 8 * (r - 2 - (l + 1)))) s1 =
                  highdigits (highdigits uh (8 * (l + 1))) 8`
     MP_TAC THENL [S8_HIGH_TAC `highdigits uh (8 * (l + 1))`; REWRITE_TAC[HIGHDIGITS_HIGHDIGITS] THEN DISCH_TAC] THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC (2--3) THEN
    ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [8;10;12;13;15;16;18;20] (4--23) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    REPEAT CONJ_TAC THEN TRY(S8_OFFSET_TAC THEN NO_TAC) THEN TRY(AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
    ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[S8_LOWDIGITS_BLOCK] THEN
    REWRITE_TAC[ARITH_RULE `512 * ((l + 1) + 1) = (512 * l + 512) + 512 /\ 512 * (l + 1) = 512 * l + 512`; EXP_ADD] THEN
    S8_NUMS_TAC THEN MATCH_MP_TAC(S8_NUMS S8_PASS_COMBINE) THEN
    MAP_EVERY EXISTS_TAC [s8_vl; `bitval cf`; s8_tl] THEN ASM_REWRITE_TAC[] THEN S8_ACC_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `?l. r = l + 2` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `r - 2` THEN S8_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(l + 2) - 1 = l + 1`]) THEN
  REWRITE_TAC[ARITH_RULE `(l + 2) - 2 = l /\ (l + 2) - 1 = l + 1`; SUB_REFL] THEN
  S8_GHOST_WIN THEN GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(base,8 * (l + 1))` THEN
  SUBGOAL_THEN `val(word_sub (word_add xb (word (64 * (l + 2)))) (word_add xb (word (64 * (l + 2)))):int64) = 0`
   ASSUME_TAC THENL [REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]; ALL_TAC] THEN
  S8_PASS_MUL_TAC THEN
  S8_READ8_TAC `s1:armstate` `word_add xb (word 64):int64` `8 * (l + 1)` `0` `xb:int64` `64` THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (2--9) THEN
  S8_ADDR_TAC [`word_sub (word_add xb (word (64 * (l + 2)))) (word_add xb (word 128)):int64 = word(64 * l)`] THEN
  S8_ADDR_TAC [`word_sub (word_add base (word (64 * (l + 2)))) (word(64 * l)):int64 = word_add base (word 128)`] THEN
  SUBGOAL_THEN `read(memory :> bytes(base,8 * 8 * (l + 2))) s9 = lo + (2 EXP (512 * l) * 2 EXP 512) * m8`
   ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `l + 2 = (l + 1) + 1`] THEN ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN
    ASM_REWRITE_TAC[ARITH_RULE `512 * (l + 1) = 512 * l + 512`; EXP_ADD]; ALL_TAC] THEN
  ABBREV_TAC `nn = lo + (2 EXP (512 * l) * 2 EXP 512) * m8` THEN
  MP_TAC(SPECL [`uh:num`; `8 * (l + 1)`] LOWDIGITS_SELF) THEN
  MP_TAC(SPECL [`hh:num`; `8 * (l + 1)`] LOWDIGITS_SELF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
  ASM_CASES_TAC `l = 0` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `l = 0`)) THEN
    SUBGOAL_THEN `val(word(64 * 0):int64) = 0` ASSUME_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC (10--11) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN REWRITE_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
    CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && free_in `nn:num` (concl th) && free_in s8_tr (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word(64 * l):int64) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `64 * l < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN S8_ARITH_TAC; ALL_TAC] THEN
  S8_READ8_TAC `s9:armstate` `base:int64` `8 * (l + 2)` `16` `base:int64` `128` THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (10--21) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (parse_term ("read(memory :> bytes(word_add base (word 128),8 * 8)) s21 = bignum_of_wordlist " ^
     s8_digits_from "nn" "16")) MP_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN S8_BYTES8_TAC;
    DISCH_THEN(SUBST1_TAC o SYM o CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV))] THEN
  SUBGOAL_THEN `read(memory :> bytes(word_add base (word(64 * (l + 2))),8 * 8)) s21 =
                bignum_of_wordlist [t19; t20; t21; t22; t23; t24; t25; t26]` ASSUME_TAC THENL
   [S8_BYTES8_TAC; ALL_TAC] THEN
  REWRITE_TAC[S8_NUMS S8_SPLIT3] THEN REWRITE_TAC[ARITH_RULE `l + 3 = (l + 2) + 1`] THEN
  ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && free_in `nn:num` (concl th) && free_in s8_tr (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `512 * (l + 2) = (512 * l + 512) + 512`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP (512 * l)`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN GEN_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* All the rows of the first phase, 0x2f0 to 0x680: the array ends up        *)
(* holding s8_off a kk, every product of two different words of a, with its  *)
(* top seven words still in the window.                                      *)
(* ------------------------------------------------------------------------- *)

let S8_ROW_ARITH = prove(parse_term (Printf.sprintf
 "!a i. s8_tri %s = s8_trin(highdigits a (8 * i)) /\\
        bignum_of_wordlist %s = lowdigits (highdigits a (8 * i)) 8"
   (String.concat " " (map (fun p -> if p = 0 then "(word(bigdigit a (8 * i)))"
                                     else Printf.sprintf "(word(bigdigit a (8 * i + %d)))" p) (0--7)))
   (s8_digits_from "a" "8 * i")),
  REPEAT GEN_TAC THEN REWRITE_TAC[s8_trin; GSYM S8_BLOCK; BIGDIGIT_HIGHDIGITS; ADD_CLAUSES]);;

let S8_BYTES_APPEND16 = prove
 (`!base c s. read(memory :> bytes(base,8 * 16 * (c + 1))) s =
              read(memory :> bytes(base,8 * 16 * c)) s +
              2 EXP (1024 * c) * read(memory :> bytes(word_add base (word(128 * c)),8 * 16)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `16 * (c + 1) = 16 * c + 16`; BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `64 * 16 * c = 1024 * c /\ 8 * 16 * c = 128 * c`] THEN ARITH_TAC);;

let S8_ROWS_COMBINE = prove
 (`!e lo m16 rest vv uh tri aa hh off.
     lo + e * (vv + 2 EXP 512 * uh) = off /\
     m16 + 2 EXP 1024 * rest = (vv + 2 EXP 512 * uh) + tri + 2 EXP 512 * aa * hh
     ==> (lo + e * m16) + (e * 2 EXP 1024) * rest = off + e * (tri + 2 EXP 512 * aa * hh)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN MP_TAC) THEN
  SPEC_TAC(`2 EXP 512`,`d:num`) THEN SPEC_TAC(`2 EXP 1024`,`d2:num`) THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let s8_rows_inv = Printf.sprintf
   "read X2 s = word_add tp (word(128 * i)) /\\ read X1 s = word_add (word_add x (word(64 * i))) (word 64) /\\
    read X3 s = word_add x (word(64 * kk)) /\\ read X5 s = word(64 * kk) /\\ %s /\\
    bignum_from_memory(x,8 * kk) s = a /\\
    bignum_from_memory(tp,16 * i) s +
    2 EXP (1024 * i) * (bignum_of_wordlist %s +
       2 EXP 512 * bignum_from_memory(word_add (word_add tp (word(128 * i))) (word 64),8 * ((kk - i) - 1)) s) =
    s8_off a i"
   (String.concat " /\\ " (map (fun p -> if p = 0 then "read X6 s = word(bigdigit a (8 * i))" else
       Printf.sprintf "read X%d s = word(bigdigit a (8 * i + %d))" (6 + p) p) (0--7)))
   s8_win;;
let s8_rows_iv = parse_term
  ("\\(i:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x2f0) /\\ " ^ s8_rows_inv);;
let s8_rows_at (t:term) = rand(concl(BETA_CONV(mk_comb(s8_rows_iv,t))));;
let s8_rows_mid (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term ("\\(i:num) (s:armstate). " ^ s8_rows_inv),t))));;

let s8_rows_tm = parse_term (Printf.sprintf
 "!tp x kk a pc.
   1 <= kk /\\ kk < 2 EXP 56 /\\
   nonoverlapping (tp:int64,128 * kk) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (tp,128 * kk) (x:int64,64 * kk)
   ==> ensures arm
     (\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x2f0) /\\
          read X2 s = tp /\\ read X1 s = word_add x (word 64) /\\ read X3 s = word_add x (word(64 * kk)) /\\
          read X5 s = word(64 * kk) /\\ %s /\\ %s /\\
          bignum_from_memory(x,8 * kk) s = a /\\
          bignum_from_memory(word_add tp (word 64),8 * (kk - 1)) s = 0)
     (\\s. read PC s = word(pc + 0x680) /\\ read X2 s = word_add tp (word(128 * (kk - 1) + 64)) /\\
          read X14 s = x /\\
          bignum_from_memory(tp,16 * (kk - 1) + 8) s +
          2 EXP (64 * (16 * (kk - 1) + 8)) *
          bignum_of_wordlist [read X19 s; read X20 s; read X21 s; read X22 s; read X23 s; read X24 s; read X25 s] =
          s8_off a kk)
     (MAYCHANGE [PC; X0; X1; X2; X4; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
                 X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(tp,128 * kk)])"
   (String.concat " /\\ " (map (fun p -> Printf.sprintf "read X%d s = word(bigdigit a %d)" (6 + p) p) (0--7)))
   (String.concat " /\\ " (map (fun p -> Printf.sprintf "read X%d s = word 0" p) (19--26))));;

let s8_adigits (i:term) = map (fun p -> mk_comb(`word:num->int64`,mk_comb(mk_comb(`bigdigit`,`a:num`),
     if p = 0 then i else mk_binop `(+):num->num->num` i (mk_small_numeral p)))) (0--7);;
let s8_vvars = map (fun i -> mk_var("v" ^ string_of_int i,`:int64`)) (19--26);;

let S8_ROWS = prove(s8_rows_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `8 * kk` `a:num` THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC (s8_rows_at `0`) THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; SUB_0; EXP; s8_off; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[bignum_of_wordlist; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2f0` (s8_rows_mid `0 + (kk - 1)`) THEN CONJ_TAC THENL
   [M4_ITER_TAC s8_rows_iv `0` `kk - 1` THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    S8_GHOST_WIN THEN
    GHOST_INTRO_TAC `uh:num` `bignum_from_memory(word_add (word_add tp (word(128 * i))) (word 64),8 * ((kk - i) - 1))` THEN
    GHOST_INTRO_TAC `lo:num` `bignum_from_memory(tp,16 * i)` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    S8_READ8_TAC `s0:armstate` `x:int64` `8 * kk` `8 * i` `word_add x (word(64 * i)):int64` `0` THEN
    SUBGOAL_THEN `read (memory :> bytes(word_add (word_add x (word(64 * i))) (word 64),8 * 8 * ((kk - i) - 1))) s0 =
                  highdigits a (8 * i + 8)` ASSUME_TAC THENL [S8_HIGH_TAC `a:num`; ALL_TAC] THEN
    SUBGOAL_THEN `word_add x (word (64 * kk)):int64 = word_add (word_add x (word (64 * i))) (word (64 * (kk - i)))`
     ASSUME_TAC THENL [S8_OFFSET_TAC; ALL_TAC] THEN
    MP_TAC(SPECL ([`word_add tp (word(128 * i)):int64`; `word_add x (word(64 * i)):int64`; `kk - i`] @
       s8_adigits `8 * i` @ s8_vvars @
       [`uh:num`; `highdigits a (8 * i + 8)`; `word(64 * kk):int64`; `pc:num`]) S8_ROW_REL) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [S8_ARITH_TAC; S8_ARITH_TAC; NONOVERLAPPING_TAC; NONOVERLAPPING_TAC]; ALL_TAC] THEN
    ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [S8_OFFSET_TAC; ALL_TAC]) THEN
    REWRITE_TAC[BIGDIGIT_HIGHDIGITS; ARITH_RULE `(8 * i + 8) + p = 8 * (i + 1) + p`; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[S8_BYTES_APPEND16] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `word_add (word_add tp (word (128 * (i + 1)))) (word 64):int64 =
                  word_add (word_add tp (word (128 * i))) (word 192) /\ kk - (i + 1) - 1 = kk - i - 2`
     (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THENL [S8_OFFSET_TAC; S8_ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[S8_OFF_STEP; GSYM S8_ROW_ARITH] THEN
    REWRITE_TAC[ARITH_RULE `1024 * (i + 1) = 1024 * i + 1024`; EXP_ADD] THEN
    S8_NUMS_TAC THEN MATCH_MP_TAC(S8_NUMS S8_ROWS_COMBINE) THEN
    MAP_EVERY EXISTS_TAC [s8_vl; `uh:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `?i. kk = i + 1` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `kk - 1` THEN S8_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(i + 1) - 1 = i /\ (i + 1) - i - 1 = 0`; MULT_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL; ADD_CLAUSES] THEN
  S8_GHOST_WIN THEN GHOST_INTRO_TAC `lo:num` `bignum_from_memory(tp,16 * i)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL ([`word_add tp (word(128 * i)):int64`] @ s8_adigits `8 * i` @ s8_vvars @
     [`word_add (word_add x (word(64 * i))) (word 64):int64`; `word_add x (word(64 * (i + 1))):int64`;
      `word(64 * (i + 1)):int64`; `pc:num`]) S8_TRI) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
  S8_NAME_TAC "s1" (["m8",`memory :> bytes(word_add tp (word(128 * i)):int64,8 * 8)`] @
       map2 (fun i r -> ("t" ^ string_of_int i, r)) (19--25) (butlast s8_win_regs)) THEN
  S8_ADDR_TAC [`word_sub (word_add x (word (64 * (i + 1)))) (word_add (word_add x (word (64 * i))) (word 64)):int64 = word 0`;
               `word_sub (word_add x (word (64 * (i + 1)))) (word (64 * (i + 1))):int64 = x`] THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC [2] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [S8_OFFSET_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE `8 * 16 * i = 128 * i`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8 * 16 * i = 128 * i`]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a:num`; `8 * i + 8`] HIGHDIGITS_ZERO) THEN
  ASM_REWRITE_TAC[ARITH_RULE `64 * (8 * i + 8) = 64 * 8 * (i + 1)`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[S8_OFF_STEP; GSYM S8_ROW_ARITH; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `64 * 16 * i = 1024 * i /\ 64 * (16 * i + 8) = 1024 * i + 512`; EXP_ADD] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && free_in s8_vl (concl th)))) THEN
  SPEC_TAC(`2 EXP 512`,`d:num`) THEN GEN_TAC THEN CONV_TAC NUM_RING);;

(* ------------------------------------------------------------------------- *)
(* The second phase, 0x680 to 0x7e4: doubles the sum the first phase left    *)
(* and adds the squares of a's words, which makes the array a * a.           *)
(* ------------------------------------------------------------------------- *)

(* EXTR by 63 of h:l is the word of 2 * (h:l) one place up. *)
let S8_EXTR = prove
 (`!(h:int64) (l:int64).
     val(word_subword (word_join h l:int128) (63,64):int64) + 2 EXP 64 * (val h DIV 2 EXP 63) =
     2 * val h + val l DIV 2 EXP 63`,
  REPEAT GEN_TAC THEN SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_RULE `63 <= 64`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MP_TAC(ISPEC `h:int64` VAL_BOUND_64) THEN ARITH_TAC);;

let S8_SHL1 = prove
 (`!(h:int64). val(word_shl h 1) + 2 EXP 64 * (val h DIV 2 EXP 63) = 2 * val h`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 * 9223372036854775808`; MOD_MULT2] THEN ARITH_TAC);;

(* Seven more words of an array. *)
let S8_APPEND7 = prove(parse_term (Printf.sprintf
 "!(base:int64) n s. read(memory :> bytes(base,8 * (n + 7))) s =
     read(memory :> bytes(base,8 * n)) s +
     2 EXP (64 * n) * bignum_of_wordlist [read(memory :> bytes64(word_add base (word(8 * n)))) s; %s]"
   (String.concat "; " (map (fun p -> Printf.sprintf "read(memory :> bytes64(word_add base (word(8 * n + %d)))) s" (8 * p)) (1--6)))),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SPLIT] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ARITH_TAC);;

let S8_WORD_SUB = prove
 (`!a b. b <= a ==> word_sub (word a) (word b):int64 = word(a - b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUB]);;

let S8_LOWDIGITS_2 = prove
 (`!n. lowdigits n 2 = bigdigit n 0 + 2 EXP 64 * bigdigit n 1`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 = (0 + 1) + 1`; LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let S8_DSQ_1 = prove
 (`!a. s8_dsq a 1 = bigdigit a 0 * bigdigit a 0`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ARITH_RULE `1 = 0 + 1`] THEN
  REWRITE_TAC[S8_DSQ_STEP; s8_dsq; MULT_CLAUSES; ADD_CLAUSES; EXP]);;

(* Closes an equation between numbers from the accumulated equations and
   the given ones, all linear once the products are taken as atoms. *)
let S8_LIN_TAC (ths:thm list) : tactic =
  let rw = REWRITE_RULE[bignum_of_wordlist; VAL_WORD_BIGDIGIT; ADD_CLAUSES; VAL_WORD_BITVAL; GSYM REAL_OF_NUM_CLAUSES] in
  CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BIGDIGIT; GSYM REAL_OF_NUM_CLAUSES] THEN
  MAP_EVERY (MP_TAC o rw o CONV_RULE(DEPTH_CONV NUM_EXP_CONV)) ths THEN
  ACCUMULATOR_POP_ASSUM_LIST(MAP_EVERY (MP_TAC o rw)) THEN
  CONV_TAC REAL_ARITH;;

let s8_extr (h:term) (l:term) = ISPECL [h;l] S8_EXTR;;
let s8_td (j:string) = parse_term (Printf.sprintf "word(bigdigit tt (%s)):int64" j);;

let S8_LOWDIGITS_ADD8 = prove(parse_term (Printf.sprintf
  "!v n. lowdigits v (n + 8) = lowdigits v n + 2 EXP (64 * n) * bignum_of_wordlist [word(bigdigit v n):int64; %s]"
  (String.concat "; " (map (fun p -> Printf.sprintf "word(bigdigit v (n + %d)):int64" p) (1--7)))),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 8 = (((((((n + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1`;
              LOWDIGITS_CLAUSES; bignum_of_wordlist; VAL_WORD_BIGDIGIT] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; EXP_ADD] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let S8_SA_COMBINE = prove
 (`!e lo r0 d1 l2 dd m8 r1 d9 t8 sq.
     lo + e * r0 + (e * 2 EXP 128) * d1 = 2 * l2 + dd /\
     m8 + 2 EXP 512 * r1 + 2 EXP 640 * d9 = r0 + 2 EXP 128 * d1 + 2 EXP 128 * (2 * t8 + sq)
     ==> (lo + e * m8) + (e * 2 EXP 512) * r1 + (e * 2 EXP 640) * d9 =
         2 * (l2 + (e * 2 EXP 128) * t8) + dd + (e * 2 EXP 128) * sq`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN MP_TAC) THEN
  SPEC_TAC(`2 EXP 128`,`c1:num`) THEN SPEC_TAC(`2 EXP 512`,`c2:num`) THEN SPEC_TAC(`2 EXP 640`,`c3:num`) THEN
  REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

(* As S8_LIN_TAC, with the assumptions that are equations between numbers
   and say nothing of a state. *)
let S8_LINA_TAC (ths:thm list) : tactic =
  fun (asl,w) ->
    let ok c = is_eq c && type_of(lhs c) = `:num` &&
               not (exists (fun v -> type_of v = `:armstate`) (frees c)) in
    S8_LIN_TAC (ths @ filter (ok o concl) (map snd asl)) (asl,w);;

(* Digit indices (a + m) + n with m and n numerals, as a + (m + n) worked out. *)
let S8_DIGIT_IDX_CONV : conv =
  let th = prove(`bigdigit v ((a + b) + c) = bigdigit v (a + b + c)`, REWRITE_TAC[ADD_ASSOC]) in
  DEPTH_CONV(GEN_REWRITE_CONV I [th] THENC RAND_CONV(RAND_CONV NUM_ADD_CONV));;

let S8_BOUND7 = prove
 (`!lo n (w0:int64) (w1:int64) (w2:int64) (w3:int64) (w4:int64) (w5:int64) (w6:int64).
     lo < 2 EXP (64 * n)
     ==> lo + 2 EXP (64 * n) * bignum_of_wordlist [w0; w1; w2; w3; w4; w5; w6] < 2 EXP (64 * (n + 7))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[w0; w1; w2; w3; w4; w5; w6]:int64 list`; `7`] BIGNUM_OF_WORDLIST_BOUND) THEN
  REWRITE_TAC[LENGTH; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`bignum_of_wordlist [w0; w1; w2; w3; w4; w5; w6]`,`ww:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 * (n + 7) = 64 * n + 448`; EXP_ADD] THEN
  MATCH_MP_TAC(ARITH_RULE `lo < e /\ e * (ww + 1) <= e * c ==> lo + e * ww < e * c`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let S8_DSQ_ADD3 = prove
 (`!a n. s8_dsq a (n + 3) = s8_dsq a n + 2 EXP (128 * n) *
         (bigdigit a n * bigdigit a n + 2 EXP 128 * bigdigit a (n + 1) * bigdigit a (n + 1) +
          2 EXP 256 * bigdigit a (n + 2) * bigdigit a (n + 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `n + 3 = ((n + 1) + 1) + 1`; S8_DSQ_STEP] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ARITH_TAC);;

(* A number of five words as their list. *)
let S8_FIVE = prove
 (`!h. h < 2 EXP 320
       ==> h = bignum_of_wordlist [word(bigdigit h 0):int64; word(bigdigit h 1); word(bigdigit h 2);
                                   word(bigdigit h 3); word(bigdigit h 4)]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lowdigits h 5 = h` (fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THENL
   [MATCH_MP_TAC LOWDIGITS_SELF THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BIGDIGIT;
              ARITH_RULE `5 = ((((0 + 1) + 1) + 1) + 1) + 1`; LOWDIGITS_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let S8_SA_FINAL = prove
 (`!e lo r0 d1 l2 dd m8 c t5 sq total.
     lo + e * r0 + (e * 2 EXP 128) * d1 = 2 * l2 + dd /\
     m8 + 2 EXP 512 * bitval c = r0 + 2 EXP 128 * d1 + 2 EXP 128 * (2 * t5 + sq) /\
     total = 2 * (l2 + (e * 2 EXP 128) * t5) + dd + (e * 2 EXP 128) * sq /\
     total < e * 2 EXP 512
     ==> lo + e * m8 = total`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `lo + e * (m8 + 2 EXP 512) = total` MP_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
      SPEC_TAC(`2 EXP 128`,`c1:num`) THEN SPEC_TAC(`2 EXP 512`,`c2:num`) THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING;
      UNDISCH_TAC `total < e * 2 EXP 512` THEN REWRITE_TAC[LEFT_ADD_DISTRIB] THEN ARITH_TAC];
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN MP_TAC) THEN
    SPEC_TAC(`2 EXP 128`,`c1:num`) THEN REPEAT GEN_TAC THEN DISCH_TAC THEN CONV_TAC NUM_RING]);;

let s8_sa_const =
   "read SP s = tp /\\ read X29 s = fr /\\ read X5 s = word(64 * kk) /\\
    read (memory :> bytes64(word_add fr (word 104))) s = m /\\
    read (memory :> bytes64(word_add fr (word 112))) s = w /\\
    bignum_from_memory(m,8) s = n8 /\\ bignum_from_memory(x,8 * kk) s = a";;

let s8_sa_inv = s8_sa_const ^ " /\\ tt < 2 EXP (64 * (16 * kk - 1)) /\\
    read X2 s = word_add tp (word(64 * r)) /\\ read X1 s = word_add x (word(32 * (r + 1))) /\\
    read X27 s = word(64 * kk - 32 * (r + 1)) /\\
    read X11 s = word(bigdigit a (4 * r + 2)) /\\ read X13 s = word(bigdigit a (4 * r + 3)) /\\
    read X16 s = word(bigdigit tt (8 * r + 2)) /\\ read X17 s = word(bigdigit tt (8 * r + 3)) /\\
    read X14 s = word(bigdigit tt (8 * r + 4)) /\\
    val(read X8 s) + 2 EXP 64 * val(read X9 s) = bigdigit a (4 * r + 1) * bigdigit a (4 * r + 1) /\\
    val(read X15 s) + 2 EXP 64 * (bigdigit tt (8 * r + 2) DIV 2 EXP 63) =
    2 * bigdigit tt (8 * r + 2) + bigdigit tt (8 * r + 1) DIV 2 EXP 63 /\\
    bignum_from_memory(word_add tp (word(64 * r + 40)),16 * kk - (8 * r + 6)) s = highdigits tt (8 * r + 5) /\\
    bignum_from_memory(tp,8 * r) s +
    2 EXP (512 * r) * (val(read X19 s) + 2 EXP 64 * val(read X20 s) + 2 EXP 128 * bitval(read CF s)) +
    2 EXP (64 * (8 * r + 2)) * (bigdigit tt (8 * r + 1) DIV 2 EXP 63) =
    2 * lowdigits tt (8 * r + 2) + s8_dsq a (4 * r + 1)";;
let s8_sa_iv = parse_term
  ("\\(r:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x6c4) /\\ " ^ s8_sa_inv);;
let s8_sa_mid (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term ("\\(r:num) (s:armstate). " ^ s8_sa_inv),t))));;

let s8_sa_hyps =
  "1 <= kk /\\ kk < 2 EXP 56 /\\ bigdigit tt 0 = 0 /\\ aligned 16 tp /\\
   nonoverlapping (tp:int64,128 * kk) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (tp,128 * kk) (x:int64,64 * kk) /\\
   nonoverlapping (tp,128 * kk) (m:int64,64) /\\
   nonoverlapping (tp,128 * kk) (word_add fr (word 104):int64,16) /\\
   2 * tt + s8_dsq a (8 * kk) < 2 EXP (1024 * kk)";;
let s8_sa_maychange =
  "MAYCHANGE [PC; X1; X2; X3; X4; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
              X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(tp,128 * kk)]";;
let s8_sa_pre = Printf.sprintf
  "aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x680) /\\
   %s /\\
   read X2 s = word_add tp (word(128 * (kk - 1) + 64)) /\\ read X14 s = x /\\ read X26 s = w26 /\\
   bignum_from_memory(tp,16 * (kk - 1) + 8) s +
   2 EXP (64 * (16 * (kk - 1) + 8)) *
   bignum_of_wordlist [read X19 s; read X20 s; read X21 s; read X22 s; read X23 s; read X24 s; read X25 s] =
   tt" s8_sa_const;;
let s8_sa_post = Printf.sprintf
  "read PC s = word(pc + 0x7e4) /\\
   read SP s = tp /\\ read X29 s = fr /\\ read X5 s = word(64 * kk) /\\
   read X2 s = tp /\\ read X1 s = word_add m (word 64) /\\ read X3 s = word_add m (word(64 * kk)) /\\
   read X4 s = w /\\ read X30 s = word 0 /\\ read X27 s = word 8 /\\
   read X28 s = word(val w * val(read X19 s)) /\\
   bignum_of_wordlist [read X6 s; read X7 s; read X8 s; read X9 s; read X10 s; read X11 s; read X12 s; read X13 s] = n8 /\\
   bignum_of_wordlist %s = lowdigits (2 * tt + s8_dsq a (8 * kk)) 8 /\\
   bignum_from_memory(tp,16 * kk) s = 2 * tt + s8_dsq a (8 * kk)" s8_win;;
let s8_sa_at (pc:int) (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term (Printf.sprintf
  "\\(r:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\ %s" pc s8_sa_inv),t))));;
let s8_sa_iv754 = parse_term
  ("\\(r:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x754) /\\ " ^ s8_sa_inv);;
let s8_sa_vars = "tp x kk a tt fr m w n8 w26";;

(* The statement "!vars. hyps ==> ensures arm pre post may". *)
let s8_mk (vars:string) (hyps:string) (pre:term) (post:term) (may:string) : term =
  let body = parse_term (Printf.sprintf "%s ==> ensures arm (pre_p:armstate->bool) (post_p:armstate->bool) (%s)" hyps may) in
  let body' = vsubst [pre,`pre_p:armstate->bool`; post,`post_p:armstate->bool`] body in
  let fv = frees body' in
  let vs = List.concat (map (fun n -> filter (fun v -> fst(dest_var v) = n) fv) (String.split_on_char ' ' vars)) in
  list_mk_forall(vs,body');;

let s8_sa_pre_tm = s8_mk (s8_sa_vars ^ " pc") s8_sa_hyps (parse_term ("\\s. " ^ s8_sa_pre)) (s8_sa_at 0x6c4 `0`) s8_sa_maychange;;
let s8_sa_body_tm = s8_mk (s8_sa_vars ^ " r pc") (s8_sa_hyps ^ " /\\ r < 2 * kk - 1")
  (s8_sa_at 0x6c4 `r:num`) (s8_sa_at 0x754 `r + 1`) s8_sa_maychange;;
let s8_sa_tail_tm = s8_mk (s8_sa_vars ^ " r pc") (s8_sa_hyps ^ " /\\ 2 * kk = r + 1")
  (s8_sa_at 0x754 `r:num`) (parse_term ("\\s. " ^ s8_sa_post)) s8_sa_maychange;;
let s8_sa_tm = s8_mk (s8_sa_vars ^ " pc") s8_sa_hyps
  (parse_term ("\\s. " ^ s8_sa_pre)) (parse_term ("\\s. " ^ s8_sa_post)) s8_sa_maychange;;

let S8_SA_PRE = prove(s8_sa_pre_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?i. kk = i + 1` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `kk - 1` THEN S8_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(i + 1) - 1 = i`; MULT_CLAUSES; ADD_CLAUSES] THEN
  MAP_EVERY (fun (v,r) -> GHOST_INTRO_TAC (mk_var(v,`:int64`)) (mk_comb(`read:(armstate,int64)component->armstate->int64`,r)))
   ["w19",`X19`; "w20",`X20`; "w21",`X21`; "w22",`X22`; "w23",`X23`; "w24",`X24`; "w25",`X25`] THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(tp,16 * i + 8)` THEN
  BIGNUM_TERMRANGE_TAC `16 * i + 8` `lo:num` THEN BIGNUM_TERMRANGE_TAC `8 * (i + 1)` `a:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `tt < 2 EXP (64 * (16 * (i + 1) - 1))` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) - 1 = (16 * i + 8) + 7`] THEN EXPAND_TAC "tt" THEN
    MATCH_MP_TAC S8_BOUND7 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lo = lowdigits tt (16 * i + 8)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "tt" THEN REWRITE_TAC[lowdigits; MOD_MULT_ADD] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  MAP_EVERY (fun j -> S8_READ_TAC `s0:armstate` `tp:int64` `16 * i + 8` (mk_small_numeral j)
      (subst [mk_small_numeral(8 * j),`n:num`] `word_add tp (word n):int64`)) (1--4) THEN
  S8_READ_TAC `s0:armstate` `x:int64` `8 * (i + 1)` `0` `x:int64` THEN
  MAP_EVERY (fun j -> S8_READ_TAC `s0:armstate` `x:int64` `8 * (i + 1)` (mk_small_numeral j)
      (subst [mk_small_numeral(8 * j),`n:num`] `word_add x (word n):int64`)) (1--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BIGDIGIT_LOWDIGITS;
    ARITH_RULE `1 < 16 * i + 8 /\ 2 < 16 * i + 8 /\ 3 < 16 * i + 8 /\ 4 < 16 * i + 8`]) THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [7;11;15] (1--17) THEN
  SUBGOAL_THEN `read(memory :> bytes(tp,8 * (16 * i + 15))) s17 = tt` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * i + 15 = (16 * i + 8) + 7`; S8_APPEND7] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `128 * i + 64 = 8 * (16 * i + 8)`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `read(memory :> bytes(word_add tp (word 40),8 * (16 * (i + 1) - 6))) s17 = highdigits tt 5` ASSUME_TAC THENL
   [S8_HIGH_TAC `tt:num`; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC S8_WORD_SUB THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [S8_LIN_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [S8_LIN_TAC[s8_extr (s8_td "2") (s8_td "1")]; ALL_TAC] THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; S8_LOWDIGITS_2; S8_DSQ_1] THEN
  S8_LIN_TAC[ISPEC (s8_td "1") S8_SHL1]);;

(* One pass of the loop, 0x6c4 to its branch at 0x754. A load pair's second
   word is read at the pointer's own offset plus eight, so the pointers
   stepped in the pass need that form of address too. *)
let S8_SA_BODY = prove(s8_sa_body_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  MAP_EVERY (fun (v,r) -> GHOST_INTRO_TAC (mk_var(v,`:int64`)) (mk_comb(`read:(armstate,int64)component->armstate->int64`,r)))
   ["q8",`X8`; "q9",`X9`; "e15",`X15`; "r19",`X19`; "r20",`X20`] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN GHOST_INTRO_TAC `lo:num` `bignum_from_memory(tp,8 * r)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (p,addr) -> S8_READ_TAC `s0:armstate` `word_add tp (word(64 * r + 40)):int64` `16 * kk - (8 * r + 6)`
      (mk_small_numeral p) addr)
   [0,`word_add tp (word(64 * r + 40)):int64`; 1,`word_add tp (word(64 * r + 48)):int64`;
    2,`word_add tp (word(64 * r + 56)):int64`; 3,`word_add tp (word(64 * r + 64)):int64`;
    4,`word_add tp (word(64 * r + 72)):int64`; 5,`word_add tp (word(64 * r + 80)):int64`;
    6,`word_add tp (word(64 * r + 88)):int64`; 7,`word_add (word_add tp (word(64 * r))) (word 96):int64`] THEN
  MAP_EVERY (fun (p,addr) -> S8_READ_TAC `s0:armstate` `x:int64` `8 * kk`
      (subst [mk_small_numeral(4 + p),`n:num`] `4 * r + n`) addr)
   [0,`word_add x (word(32 * (r + 1))):int64`; 1,`word_add x (word(32 * (r + 1) + 8)):int64`;
    2,`word_add x (word(32 * (r + 1) + 16)):int64`; 3,`word_add (word_add x (word(32 * (r + 1)))) (word 24):int64`] THEN
  RULE_ASSUM_TAC(CONV_RULE S8_DIGIT_IDX_CONV) THEN
  SUBGOAL_THEN `read(memory :> bytes(word_add tp (word(64 * (r + 1) + 40)),8 * (16 * kk - (8 * (r + 1) + 6)))) s0 =
                highdigits (highdigits tt (8 * r + 5)) 8` MP_TAC THENL
   [S8_HIGH_TAC `highdigits tt (8 * r + 5)`;
    REWRITE_TAC[HIGHDIGITS_HIGHDIGITS; ARITH_RULE `(8 * r + 5) + 8 = 8 * (r + 1) + 5`] THEN DISCH_TAC] THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [1;4;6;9;13;16;19;21;23;26;32;34] (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * (r + 1) + 1 = 8 * r + 9 /\ 8 * (r + 1) + 2 = 8 * r + 10 /\ 8 * (r + 1) + 3 = 8 * r + 11 /\
                          8 * (r + 1) + 4 = 8 * r + 12 /\ 4 * (r + 1) + 1 = 4 * r + 5 /\ 4 * (r + 1) + 2 = 4 * r + 6 /\
                          4 * (r + 1) + 3 = 4 * r + 7`] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [S8_OFFSET_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `32 <= 64 * kk - 32 * (r + 1)` (fun th -> SIMP_TAC[th; S8_WORD_SUB]) THENL
     [S8_ARITH_TAC; AP_TERM_TAC THEN S8_ARITH_TAC]; ALL_TAC] THEN
  CONJ_TAC THENL [S8_LIN_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [S8_LIN_TAC[s8_extr (s8_td "8 * r + 10") (s8_td "8 * r + 9")]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN
  SUBGOAL_THEN `read(memory :> bytes(word_add tp (word(64 * r)),8 * 8)) s36 =
                bignum_of_wordlist [r19; r20; sum_s1; sum_s4; sum_s13; sum_s16; sum_s19; sum_s21]`
   ASSUME_TAC THENL [S8_BYTES8_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * r + 10 = (8 * r + 2) + 8 /\ 4 * r + 5 = (4 * r + 1) + 4`; S8_LOWDIGITS_ADD8; S8_DSQ_ADD4] THEN
  CONV_TAC S8_DIGIT_IDX_CONV THEN
  (let pw = [ARITH_RULE `512 * (r + 1) = 512 * r + 512 /\ 64 * ((8 * r + 2) + 8) = 512 * r + 640 /\
                         64 * (8 * r + 2) = 512 * r + 128 /\ 128 * (4 * r + 1) = 512 * r + 128`; EXP_ADD] in
   RULE_ASSUM_TAC(REWRITE_RULE pw) THEN REWRITE_TAC pw) THEN
  MATCH_MP_TAC S8_SA_COMBINE THEN
  MAP_EVERY EXISTS_TAC [`val(r19:int64) + 2 EXP 64 * val(r20:int64) + 2 EXP 128 * bitval cf`;
                        `bigdigit tt (8 * r + 1) DIV 2 EXP 63`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  S8_LINA_TAC(map (fun j -> s8_extr (s8_td (Printf.sprintf "8 * r + %d" (j + 1))) (s8_td (Printf.sprintf "8 * r + %d" j))) (2--8)));;

(* The last pass, 0x754 to 0x7e4, which also loads what the reduction needs. *)
let S8_SA_TAIL = prove(s8_sa_tail_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  MAP_EVERY (fun (v,r) -> GHOST_INTRO_TAC (mk_var(v,`:int64`)) (mk_comb(`read:(armstate,int64)component->armstate->int64`,r)))
   ["q8",`X8`; "q9",`X9`; "e15",`X15`; "r19",`X19`; "r20",`X20`] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN GHOST_INTRO_TAC `lo:num` `bignum_from_memory(tp,8 * r)` THEN
  BIGNUM_TERMRANGE_TAC `8 * r` `lo:num` THEN BIGNUM_TERMRANGE_TAC `8` `n8:num` THEN
  SUBGOAL_THEN `1 <= r /\ 64 * kk - 32 * (r + 1) = 0` STRIP_ASSUME_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (p,addr) -> S8_READ_TAC `s0:armstate` `word_add tp (word(64 * r + 40)):int64` `16 * kk - (8 * r + 6)`
      (mk_small_numeral p) addr)
   [0,`word_add tp (word(64 * r + 40)):int64`; 1,`word_add tp (word(64 * r + 48)):int64`] THEN
  S8_READ8_TAC `s0:armstate` `tp:int64` `8 * r` `0` `tp:int64` `0` THEN
  S8_READ8_TAC `s0:armstate` `m:int64` `8` `0` `m:int64` `0` THEN
  RULE_ASSUM_TAC(CONV_RULE S8_DIGIT_IDX_CONV) THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [3;5;7;10;14;17;20;23] (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read(memory :> bytes(word_add tp (word(64 * r)),8 * 8)) s36 =
                bignum_of_wordlist [r19; r20; sum_s3; sum_s5; sum_s14; sum_s17; sum_s20; sum_s23]`
   ASSUME_TAC THENL [S8_BYTES8_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lo + 2 EXP (512 * r) * bignum_of_wordlist [r19; r20; sum_s3; sum_s5; sum_s14; sum_s17; sum_s20; sum_s23] =
                2 * tt + s8_dsq a (8 * kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC S8_SA_FINAL THEN
    MAP_EVERY EXISTS_TAC [`val(r19:int64) + 2 EXP 64 * val(r20:int64) + 2 EXP 128 * bitval cf`;
                          `bigdigit tt (8 * r + 1) DIV 2 EXP 63`; `lowdigits tt (8 * r + 2)`; `s8_dsq a (4 * r + 1)`;
                          `carry_s23:bool`;
                          `bignum_of_wordlist [word(bigdigit tt (8 * r + 2)):int64; word(bigdigit tt (8 * r + 3));
                             word(bigdigit tt (8 * r + 4)); word(bigdigit tt (8 * r + 5)); word(bigdigit tt (8 * r + 6))]`;
                          `bigdigit a (4 * r + 1) * bigdigit a (4 * r + 1) +
                           2 EXP 128 * bigdigit a (4 * r + 2) * bigdigit a (4 * r + 2) +
                           2 EXP 256 * bigdigit a (4 * r + 3) * bigdigit a (4 * r + 3)`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && free_in `lo:num` (concl th) && free_in `cf:bool` (concl th))) THEN
      REWRITE_TAC[ARITH_RULE `64 * (8 * r + 2) = 512 * r + 128`; EXP_ADD];
      S8_LINA_TAC((CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[VAL_WORD_0] (s8_extr `word 0:int64` (s8_td "8 * r + 6")))) ::
         map (fun j -> s8_extr (s8_td (Printf.sprintf "8 * r + %d" (j + 1))) (s8_td (Printf.sprintf "8 * r + %d" j))) (2--5));
      SUBGOAL_THEN `8 * kk = (4 * r + 1) + 3` SUBST1_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[S8_DSQ_ADD3] THEN CONV_TAC S8_DIGIT_IDX_CONV THEN
        REWRITE_TAC[ARITH_RULE `128 * (4 * r + 1) = 512 * r + 128`; EXP_ADD] THEN
        SUBGOAL_THEN `highdigits tt (8 * r + 2) < 2 EXP 320` MP_TAC THENL
         [REWRITE_TAC[highdigits] THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
          SUBGOAL_THEN `64 * (8 * r + 2) + 320 = 64 * (16 * kk - 1)` SUBST1_TAC THENL [S8_ARITH_TAC; ASM_REWRITE_TAC[]];
          DISCH_THEN(MP_TAC o MATCH_MP S8_FIVE) THEN REWRITE_TAC[BIGDIGIT_HIGHDIGITS; ADD_CLAUSES] THEN
          CONV_TAC S8_DIGIT_IDX_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
          MP_TAC(SPECL [`tt:num`; `8 * r + 2`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
          REWRITE_TAC[ARITH_RULE `64 * (8 * r + 2) = 512 * r + 128`; EXP_ADD] THEN
          DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN ARITH_TAC];
      SUBGOAL_THEN `2 EXP (512 * r) * 2 EXP 512 = 2 EXP (1024 * kk)` (fun th -> ASM_REWRITE_TAC[th]) THEN
        REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN S8_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; S8_BLOCK] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && free_in `lo:num` (concl th) && free_in `sum_s23:int64` (concl th))) THEN
    SUBGOAL_THEN `512 * r = 64 * 8 + 512 * (r - 1)` SUBST1_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[lowdigits; EXP_ADD; GSYM MULT_ASSOC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `lo + e * x = e * x + lo`] THEN REWRITE_TAC[MOD_MULT_ADD];
    SUBGOAL_THEN `16 * kk = 8 * (r + 1)` SUBST1_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN ASM_REWRITE_TAC[]]);;

(* The whole phase: the entry, the first pass, the passes the loop repeats,
   and the last. *)
let S8_SA = prove(s8_sa_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x754` (s8_sa_mid `(0 + 1) + (2 * kk - 2)`) THEN CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x754` (s8_sa_mid `0 + 1`) THEN CONJ_TAC THENL
     [ENSURES_SEQUENCE_TAC `pc + 0x6c4` (s8_sa_mid `0`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_SA_PRE) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_SA_BODY) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC];
      ALL_TAC];
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_SA_TAIL) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC] THEN
  M4_ITER_TAC s8_sa_iv754 `0 + 1` `2 * kk - 2` THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x6c4` (s8_sa_mid `r:num`) THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    MAP_EVERY (fun (v,r) -> GHOST_INTRO_TAC (mk_var(v,`:int64`)) (mk_comb(`read:(armstate,int64)component->armstate->int64`,r)))
     ["q8",`X8`; "q9",`X9`; "e15",`X15`; "r19",`X19`; "r20",`X20`] THEN
    GHOST_INTRO_TAC `cf:bool` `read CF` THEN GHOST_INTRO_TAC `lo:num` `bignum_from_memory(tp,8 * r)` THEN
    SUBGOAL_THEN `~(val(word(64 * kk - 32 * (r + 1)):int64) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `64 * kk - 32 * (r + 1) < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN S8_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_SA_BODY) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One round of the reduction, 0x7e4 to its branch at 0xa34, for r >= 2      *)
(* blocks of n: the window and the r blocks above base, with the carry tc    *)
(* into the top one, gain q * n for the eight words q the round leaves at    *)
(* base, and lose their low block.                                           *)
(* ------------------------------------------------------------------------- *)

let S8_BIT_WORD = prove
 (`!x:int64. val x <= 1 ==> ?b. x = word(bitval b)`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN STRIP_TAC THENL
   [EXISTS_TAC `F`; EXISTS_TAC `T`] THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_BITVAL; BITVAL_CLAUSES]);;

let S8_REDPASS_COMBINE = prove
 (`!e lo m8 vc tt w2 ub ww ly qq ln nb.
     2 EXP 512 * (lo + e * vc) = (ww + 2 EXP 512 * ly) + qq * ln /\
     m8 + 2 EXP 512 * tt = vc + qq * nb /\
     w2 = tt + ub
     ==> 2 EXP 512 * ((lo + e * m8) + (e * 2 EXP 512) * w2) =
         (ww + 2 EXP 512 * (ly + (e * 2 EXP 512) * ub)) + qq * (ln + (e * 2 EXP 512) * nb)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN MP_TAC) THEN
  SPEC_TAC(`2 EXP 512`,`d:num`) THEN GEN_TAC THEN CONV_TAC NUM_RING);;

let S8_REDPASS_NOCARRY = prove
 (`!c x ee tt ww ly qq ln.
     2 EXP 512 * (x + ee * (tt + 2 EXP 512 * bitval c)) = (ww + 2 EXP 512 * ly) + qq * ln /\
     ww < 2 EXP 512 /\ ly < ee /\ qq < 2 EXP 512 /\ ln < ee * 2 EXP 512
     ==> ~c`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN STRIP_TAC THEN
  SUBGOAL_THEN `qq * ln <= (2 EXP 512 - 1) * (ee * 2 EXP 512 - 1)` MP_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= ee` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  MAP_EVERY UNDISCH_TAC [`ww < 2 EXP 512`; `ly < ee`] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; LEFT_SUB_DISTRIB; RIGHT_SUB_DISTRIB; MULT_CLAUSES; MULT_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`qq * ln`,`p1:num`) THEN SPEC_TAC(`13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 * x`,`p2:num`) THEN
  REPEAT GEN_TAC THEN ARITH_TAC);;

let s8_ndigits (i:string) = String.concat " /\\ " (map (fun p ->
  if p = 0 then Printf.sprintf "read X6 s = word(bigdigit n (%s))" i
  else Printf.sprintf "read X%d s = word(bigdigit n (%s + %d))" (6 + p) i p) (0--7));;
let s8_ndigits0 = String.concat " /\\ " (map (fun p -> Printf.sprintf "read X%d s = word(bigdigit n %d)" (6 + p) p) (0--7));;

let s8_round_hyps =
  "2 <= r /\\ r < 2 EXP 56 /\\ (bigdigit n 0 * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   nonoverlapping (base:int64,64 * (r + 1)) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (base,64 * (r + 1)) (m:int64,64 * r) /\\
   nonoverlapping (base,64 * (r + 1)) (word_add fr (word 112):int64,8)";;
let s8_round_maychange =
  "MAYCHANGE [PC; X0; X1; X2; X4; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
              X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(base,64 * (r + 1))]";;
let s8_round_const =
  "read X3 s = word_add m (word(64 * r)) /\\ read X5 s = word(64 * r) /\\ read X29 s = fr /\\
   read (memory :> bytes64(word_add fr (word 112))) s = w /\\ bignum_from_memory(m,8 * r) s = n";;
let s8_round_pre = Printf.sprintf
  "\\s. aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x7e4) /\\ %s /\\
       read X2 s = base /\\ read X1 s = word_add m (word 64) /\\ read X4 s = w /\\ read X27 s = word 8 /\\
       read X28 s = word(val w * val(w19:int64)) /\\ read X30 s = word(bitval tc) /\\ %s /\\ %s /\\
       bignum_from_memory(word_add base (word 64),8 * r) s = yh"
  s8_round_const s8_ndigits0 (s8_reads 19 "w" 19);;
let s8_round_post = Printf.sprintf
  "\\s. read PC s = word(pc + 0xa34) /\\ read X2 s = word_add base (word 64) /\\
       read X1 s = word_add m (word 64) /\\ read X4 s = w /\\ read X27 s = word 8 /\\ %s /\\
       read X28 s = word(val w * val(read X19 s)) /\\ val(read X30 s) <= 1 /\\
       (read ZF s <=> word_add base (word(64 * (r + 1))) = fr) /\\
       bignum_of_wordlist %s = bignum_from_memory(word_add base (word 64),8) s /\\
       2 EXP 512 * (bignum_from_memory(word_add base (word 64),8 * r) s + 2 EXP (512 * r) * val(read X30 s)) =
       (bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] + 2 EXP 512 * yh) +
       2 EXP (512 * r) * bitval tc + bignum_from_memory(base,8) s * n"
  s8_ndigits0 s8_win;;
let s8_round_tm = s8_mk "base m r n w yh tc fr w19 w20 w21 w22 w23 w24 w25 w26 pc" s8_round_hyps
  (parse_term s8_round_pre) (parse_term s8_round_post) s8_round_maychange;;

(* At 0x8cc, before the pass that multiplies q by block j + 1 of n. *)
let s8_rp_inv = Printf.sprintf
  "%s /\\ read X2 s = word_add base (word(64 * (j + 1))) /\\ read X0 s = word_add base (word 64) /\\
   read X1 s = word_add m (word(64 * (j + 2))) /\\ read X27 s = word 18446744073709551552 /\\
   read X4 s = word(bigdigit (bignum_from_memory(base,8) s) 0) /\\ read X30 s = word(bitval tc) /\\ %s /\\
   bignum_from_memory(word_add base (word(64 * (j + 2))),8 * (r - 1 - j)) s = highdigits yh (8 * (j + 1)) /\\
   2 EXP 512 * (bignum_from_memory(word_add base (word 64),8 * j) s +
                2 EXP (512 * j) * (bignum_of_wordlist %s + 2 EXP 512 * bitval(read CF s))) =
   (bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] + 2 EXP 512 * lowdigits yh (8 * (j + 1))) +
   bignum_from_memory(base,8) s * lowdigits n (8 * (j + 1))"
  s8_round_const (s8_ndigits "8 * (j + 1)") s8_win;;
let s8_rp_iv = parse_term
  ("\\(j:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x8cc) /\\ " ^ s8_rp_inv);;
let s8_rp_mid (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term ("\\(j:num) (s:armstate). " ^ s8_rp_inv),t))));;

let S8_RP0 = prove
 (`!d tt ww p s u. d * tt = ww + p /\ s = tt + u ==> d * s = (ww + d * u) + p`,
  REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let s8_nb (i:string) = parse_term ("bignum_of_wordlist " ^ s8_digits_from "n" i);;
let s8_yb (i:string) = parse_term ("bignum_of_wordlist " ^ s8_digits_from "yh" i);;
let s8_sums (l:int list) = mk_flist(map (fun i -> mk_var("sum_s" ^ string_of_int i,`:int64`)) l);;

let S8_RP1 = prove
 (`!d x ee tt ww ly p s ub.
     d * (x + ee * tt) = (ww + d * ly) + p /\ s = tt + ub
     ==> d * (x + ee * s) = (ww + d * (ly + ee * ub)) + p`,
  REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let S8_LE_BITVAL = prove
 (`!b. 1 <= bitval b <=> b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let S8_RP2 = prove
 (`!d x ee tt ww ly p s c ub c0.
     d * (x + ee * tt) = (ww + d * ly) + p /\ s + d * c = tt + ub + c0
     ==> d * ((x + ee * s) + (ee * d) * c) = (ww + d * (ly + ee * ub)) + (ee * d) * c0 + p`,
  REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

(* As S8_ACC_TAC, for sums whose carry in came from comparing a bit with one. *)
let S8_ACC1_TAC : tactic =
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BIGDIGIT; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MAP_EVERY (MP_TAC o
    REWRITE_RULE[VAL_WORD_BIGDIGIT; ADD_CLAUSES; VAL_WORD_BITVAL; S8_LE_BITVAL])) THEN
  CONV_TAC REAL_ARITH;;
let s8_qb = parse_term ("bignum_of_wordlist " ^ s8_digits "qq");;
let s8_qdigits = map (fun p -> mk_comb(`word:num->int64`,mk_comb(mk_comb(`bigdigit`,`qq:num`),mk_small_numeral p))) (0--7);;
let s8_nblock (i:term) = map (fun p -> mk_comb(`word:num->int64`,mk_comb(mk_comb(`bigdigit`,`n:num`),
     if p = 0 then i else mk_binop `(+):num->num->num` i (mk_small_numeral p)))) (0--7);;
let s8_block_j1 (v:term) = REWRITE_RULE[ARITH_RULE `512 * (j + 1) = 512 * j + 512`; EXP_ADD]
  (SPECL [v; `j + 1`] S8_LOWDIGITS_BLOCK);;

(* The pass at 0x8cc, from its invariant: runs the multiplication, names
   its results m8 and t19.., whose carry out is zero, and leaves the
   equation for the j + 1 blocks now done. *)
let S8_RP_MUL_TAC : tactic =
  S8_GHOST_WIN THEN GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `qq:num` `bignum_from_memory(base,8)` THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(word_add base (word 64),8 * j)` THEN
  BIGNUM_TERMRANGE_TAC `8` `qq:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  S8_READ8_TAC `s0:armstate` `base:int64` `8` `0` `base:int64` `0` THEN
  MP_TAC(SPECL ([`word_add base (word(64 * (j + 1))):int64`; `base:int64`] @ s8_qdigits @ s8_nblock `8 * (j + 1)` @
     s8_vvars @ [`cf:bool`; `pc:num`]) S8_MUL8_TAIL) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
  ANTS_TAC THENL [CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
  S8_NAME_TAC "s1" (["m8",`memory :> bytes(word_add base (word(64 * (j + 1))):int64,8 * 8)`; "cf'",`CF`]) THEN
  S8_NAME_WIN_TAC "s1" "t" THEN
  S8_ADDR_TAC [`word_add (word_add base (word (64 * (j + 1)))) (word 64):int64 = word_add base (word(64 * (j + 2)))`] THEN
  SUBGOAL_THEN (mk_eq(s8_qb,`qq:num`)) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[S8_BLOCK] THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`2 EXP (512 * j)`; `lo:num`; `m8:num`; mk_binop `(+):num->num->num` s8_vl `2 EXP 512 * bitval cf`;
                mk_binop `(+):num->num->num` s8_tl `2 EXP 512 * bitval cf'`;
                mk_binop `(+):num->num->num` s8_tl `2 EXP 512 * bitval cf'`; `0`; s8_wl;
                `lowdigits yh (8 * (j + 1))`; `qq:num`; `lowdigits n (8 * (j + 1))`; s8_nb "8 * (j + 1)"]
               S8_REDPASS_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES];
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; GSYM(s8_block_j1 `n:num`)] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `~cf'` ASSUME_TAC THENL
   [MATCH_MP_TAC S8_REDPASS_NOCARRY THEN
    MAP_EVERY EXISTS_TAC [`lo + 2 EXP (512 * j) * m8`; `2 EXP (512 * j) * 2 EXP 512`; s8_tl; s8_wl;
      `lowdigits yh (8 * (j + 1))`; `qq:num`; `lowdigits n (8 * ((j + 1) + 1))`] THEN
    ASM_REWRITE_TAC[S8_WL8_BOUND] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    REWRITE_TAC[ARITH_RULE `(512 * j + 512) + 512 = 64 * 8 * ((j + 1) + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `512 * j + 512 = 64 * 8 * (j + 1)`; LOWDIGITS_BOUND];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~cf'`; BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES]);;

let S8_ROUND = prove(s8_round_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `8 * r` `n:num` THEN BIGNUM_TERMRANGE_TAC `8 * r` `yh:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x8cc` (s8_rp_mid `0`) THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`m:int64`; `64 * r`; `64`] S8_PTR_EQ) THEN
    ANTS_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= r ==> ~(64 * r = 64)`] THEN DISCH_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL ([`base:int64`] @ s8_nblock `0` @ [`w:int64`] @
       map (fun i -> mk_var("w" ^ string_of_int i,`:int64`)) (19--26) @ [`pc:num`])
       (REWRITE_RULE[ADD_CLAUSES] S8_RED8)) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS; VAL_WORD_BIGDIGIT; ADD_CLAUSES] THEN
    ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
    ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
    S8_NAME_TAC "s1" ["qq",`memory :> bytes(base:int64,8 * 8)`] THEN S8_NAME_WIN_TAC "s1" "t" THEN
    S8_READ8_TAC `s1:armstate` `word_add base (word 64):int64` `8 * r` `0` `base:int64` `64` THEN
    S8_READ8_TAC `s1:armstate` `m:int64` `8 * r` `8` `m:int64` `64` THEN
    S8_READ_TAC `s1:armstate` `base:int64` `8` `0` `base:int64` THEN
    SUBGOAL_THEN `read(memory :> bytes(word_add base (word(64 * (0 + 2))),8 * 8 * (r - 1 - 0))) s1 = highdigits yh (8 * (0 + 1))`
     ASSUME_TAC THENL [S8_HIGH_TAC `yh:num`; ALL_TAC] THEN
    ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [6;7;9;10;12;13;14;15] (2--23) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
    ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; ADD_CLAUSES; MULT_CLAUSES; GSYM S8_BLOCK] THEN
    MATCH_MP_TAC S8_RP0 THEN EXISTS_TAC s8_tl THEN CONJ_TAC THENL
     [S8_NUMS_TAC THEN FIRST_ASSUM ACCEPT_TAC; S8_ACC_TAC];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x8cc` (s8_rp_mid `0 + (r - 2)`) THEN CONJ_TAC THENL
   [M4_ITER_TAC s8_rp_iv `0` `r - 2` THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`m:int64`; `64 * r`; `64 * (j + 2)`] S8_PTR_EQ) THEN
    ANTS_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `j < r - 2 ==> ~(64 * r = 64 * (j + 2))`] THEN DISCH_TAC THEN
    S8_RP_MUL_TAC THEN
    S8_READ8_TAC `s1:armstate` `word_add base (word(64 * (j + 2))):int64` `8 * (r - 1 - j)` `0` `base:int64` `64 * (j + 2)` THEN
    S8_READ8_TAC `s1:armstate` `m:int64` `8 * r` `8 * (j + 2)` `m:int64` `64 * (j + 2)` THEN
    S8_READ_TAC `s1:armstate` `base:int64` `8` `0` `base:int64` THEN
    SUBGOAL_THEN `read (memory :> bytes(word_add base (word(64 * ((j + 1) + 2))),8 * 8 * (r - 1 - (j + 1)))) s1 =
                  highdigits (highdigits yh (8 * (j + 1))) 8`
     MP_TAC THENL [S8_HIGH_TAC `highdigits yh (8 * (j + 1))`;
                   REWRITE_TAC[HIGHDIGITS_HIGHDIGITS; ARITH_RULE `8 * (j + 1) + 8 = 8 * ((j + 1) + 1)`] THEN DISCH_TAC] THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC (2--8) THEN
    ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [10;11;13;14;16;17;19;21] (9--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(S8_OFFSET_TAC THEN NO_TAC) THEN TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
    SUBGOAL_THEN `word_add (word_add base (word 64)) (word(64 * j)):int64 = word_add base (word(64 * (j + 1)))`
     ASSUME_TAC THENL [S8_OFFSET_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(s8_block_j1 `yh:num`) THEN REWRITE_TAC[ARITH_RULE `512 * (j + 1) = 512 * j + 512`; EXP_ADD] THEN
    S8_NUMS_TAC THEN MATCH_MP_TAC S8_RP1 THEN EXISTS_TAC s8_tl THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; S8_ACC_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `?j. r = j + 2` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `r - 2` THEN S8_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(j + 2) - 2 = j /\ (j + 2) - 1 - j = 1`; MULT_CLAUSES] THEN
  SUBGOAL_THEN `val(word_sub (word_add m (word (64 * (j + 2)))) (word_add m (word (64 * (j + 2)))):int64) = 0`
   ASSUME_TAC THENL [REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]; ALL_TAC] THEN
  S8_RP_MUL_TAC THEN
  S8_READ8_TAC `s1:armstate` `word_add base (word(64 * (j + 2))):int64` `8` `0` `base:int64` `64 * (j + 2)` THEN
  S8_READ8_TAC `s1:armstate` `m:int64` `8 * (j + 2)` `0` `m:int64` `0` THEN
  SUBGOAL_THEN `word_add (word_add base (word 64)) (word(64 * j)):int64 = word_add base (word(64 * (j + 1)))`
   ASSUME_TAC THENL [S8_OFFSET_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read(memory :> bytes(word_add base (word 64),8 * 8 * (j + 1))) s1 = lo + 2 EXP (512 * j) * m8`
   ASSUME_TAC THENL [ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `nn = lo + 2 EXP (512 * j) * m8` THEN
  S8_READ8_TAC `s1:armstate` `word_add base (word 64):int64` `8 * (j + 1)` `0` `base:int64` `64` THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (2--7) THEN
  S8_ADDR_TAC [`word_sub (word_add m (word (64 * (j + 2)))) (word (64 * (j + 2))):int64 = m`] THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC [8] THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [12;13;15;17;19;20;22;23] (9--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_BOUND; VAL_EQ_0; WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `word_add (word_add base (word (64 * (j + 2)))) (word 64):int64 = word_add base (word (64 * ((j + 2) + 1))) /\
                word_add (word_add base (word 64)) (word(64 * (j + 1))):int64 = word_add base (word(64 * (j + 2)))`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN S8_OFFSET_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) S8_BYTES8] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `read(memory :> bytes(word_add base (word(64 * (j + 2))),8 * 8)) s37 =
                bignum_of_wordlist [sum_s12; sum_s13; sum_s15; sum_s17; sum_s19; sum_s20; sum_s22; sum_s23]`
   ASSUME_TAC THENL [S8_BYTES8_TAC; ALL_TAC] THEN
  SUBST_ALL_TAC(ARITH_RULE `j + 2 = (j + 1) + 1`) THEN ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lowdigits n (8 * ((j + 1) + 1)) = n /\ lowdigits yh (8 * ((j + 1) + 1)) = yh` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(s8_block_j1 `yh:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && free_in s8_tl (concl th)
                           then REWRITE_RULE[ASSUME `lowdigits n (8 * ((j + 1) + 1)) = n`] th else th) THEN
  REWRITE_TAC[ARITH_RULE `512 * ((j + 1) + 1) = (512 * j + 512) + 512`] THEN
  REWRITE_TAC[ARITH_RULE `512 * (j + 1) = 512 * j + 512`; EXP_ADD] THEN
  S8_NUMS_TAC THEN MATCH_MP_TAC S8_RP2 THEN EXISTS_TAC s8_tl THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; S8_ACC1_TAC]);;

(* ------------------------------------------------------------------------- *)
(* All the rounds of the reduction, 0x7e4 to 0xa38, for kk >= 2 blocks:      *)
(* after g rounds the kk * 2 - g blocks left, times 2^(512 * g), are the     *)
(* number reduced plus n times the g blocks of q below them.                 *)
(* ------------------------------------------------------------------------- *)

let S8_SPLIT_Y = prove
 (`!(b:int64) kk g. g < kk
     ==> !s. bignum_from_memory(b,8 * (2 * kk - g)) s =
             bignum_from_memory(b,8) s +
             2 EXP 512 * (bignum_from_memory(word_add b (word 64),8 * kk) s +
                          2 EXP (512 * kk) *
                          bignum_from_memory(word_add b (word(64 * (kk + 1))),8 * (kk - g - 1)) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `8 * (2 * kk - g) = 8 + (8 * kk + 8 * (kk - g - 1))` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `64 * 8 = 512 /\ 64 * 8 * kk = 512 * kk /\ 8 * 8 = 64 /\ 64 + 8 * 8 * kk = 64 * (kk + 1)`] THEN ARITH_TAC);;

let S8_SPLIT_Y2 = prove
 (`!(b:int64) kk g. g < kk
     ==> !s. bignum_from_memory(word_add b (word 64),8 * (2 * kk - (g + 1))) s =
             bignum_from_memory(word_add b (word 64),8 * kk) s +
             2 EXP (512 * kk) *
             bignum_from_memory(word_add b (word(64 * (kk + 1))),8 * (kk - g - 1)) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `8 * (2 * kk - (g + 1)) = 8 * kk + 8 * (kk - g - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `64 * 8 * kk = 512 * kk /\ 64 + 8 * 8 * kk = 64 * (kk + 1)`] THEN ARITH_TAC);;

let S8_RSTEP_COMBINE = prove
 (`!e ee w0 yh rr tc aa q0 nn y1 c1 q1.
     e * ((w0 + 2 EXP 512 * (yh + ee * rr)) + ee * tc) = aa + q0 * nn /\
     2 EXP 512 * (y1 + ee * c1) = (w0 + 2 EXP 512 * yh) + ee * tc + q1 * nn
     ==> (e * 2 EXP 512) * ((y1 + ee * rr) + ee * c1) = aa + (q0 + e * q1) * nn`,
  REPEAT GEN_TAC THEN SPEC_TAC(`2 EXP 512`,`d:num`) THEN GEN_TAC THEN CONV_TAC NUM_RING);;

let S8_WORD_ADD_EQ = prove
 (`!(x:int64) p q. p < 2 EXP 64 /\ q < 2 EXP 64 ==> (word_add x (word p) = word_add x (word q) <=> p = q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_RULE `word_add (x:int64) a = word_add x b <=> a = b`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]);;

let s8_red_hyps =
  "2 <= kk /\\ kk < 2 EXP 56 /\\ (bigdigit n 0 * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\
   word_add tp (word(128 * kk)) = fr /\\
   nonoverlapping (tp:int64,128 * kk) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (tp,128 * kk) (m:int64,64 * kk) /\\
   nonoverlapping (tp,128 * kk) (fr:int64,128)";;
let s8_red_maychange =
  "MAYCHANGE [PC; X0; X1; X2; X4; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
              X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(tp,128 * kk)]";;
let s8_red_const =
  "read SP s = tp /\\ read X29 s = fr /\\ read X5 s = word(64 * kk) /\\ read X3 s = word_add m (word(64 * kk)) /\\
   read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
   read (memory :> bytes64(word_add fr (word 96))) s = z /\\
   read (memory :> bytes64(word_add fr (word 112))) s = w /\\ bignum_from_memory(m,8 * kk) s = n";;
let s8_red_inv = Printf.sprintf
  "%s /\\ read X2 s = word_add tp (word(64 * g)) /\\ read X1 s = word_add m (word 64) /\\ read X4 s = w /\\
   read X27 s = word 8 /\\ %s /\\ read X28 s = word(val w * val(read X19 s)) /\\ val(read X30 s) <= 1 /\\
   bignum_of_wordlist %s = bignum_from_memory(word_add tp (word(64 * g)),8) s /\\
   2 EXP (512 * g) * (bignum_from_memory(word_add tp (word(64 * g)),8 * (2 * kk - g)) s +
                      2 EXP (512 * kk) * val(read X30 s)) =
   aa + bignum_from_memory(tp,8 * g) s * n"
  s8_red_const s8_ndigits0 s8_win;;
let s8_red_at (pc:int) (extra:string) (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term (Printf.sprintf
  "\\(g:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\ %s%s"
  pc s8_red_inv extra),t))));;
let s8_red_zf = " /\\ (read ZF s <=> g = kk)";;
let s8_red_vars = "tp m kk n w aa fr ra z";;
let s8_rstep_tm = s8_mk (s8_red_vars ^ " g pc") (s8_red_hyps ^ " /\\ g < kk")
  (s8_red_at 0x7e4 "" `g:num`) (s8_red_at 0xa34 s8_red_zf `g + 1`) s8_red_maychange;;

let S8_RSTEP = prove(s8_rstep_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`word_add tp (word(64 * g)):int64`; `kk:num`; `g:num`] S8_SPLIT_Y) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  S8_GHOST_WIN THEN GHOST_INTRO_TAC `c30:int64` `read X30` THEN
  GHOST_INTRO_TAC `w0:num` `bignum_from_memory(word_add tp (word(64 * g)),8)` THEN
  GHOST_INTRO_TAC `yh:num` `bignum_from_memory(word_add (word_add tp (word(64 * g))) (word 64),8 * kk)` THEN
  GHOST_INTRO_TAC `rr:num` `bignum_from_memory(word_add (word_add tp (word(64 * g))) (word(64 * (kk + 1))),8 * (kk - g - 1))` THEN
  GHOST_INTRO_TAC `q0:num` `bignum_from_memory(tp,8 * g)` THEN
  ASM_CASES_TAC `val(c30:int64) <= 1` THENL [ALL_TAC; ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `tc:bool` SUBST_ALL_TAC o MATCH_MP S8_BIT_WORD) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL ([`word_add tp (word(64 * g)):int64`; `m:int64`; `kk:num`; `n:num`; `w:int64`; `yh:num`; `tc:bool`; `fr:int64`] @
     s8_vvars @ [`pc:num`]) S8_ROUND) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
  S8_NAME_TAC "s1" ["y1",`memory :> bytes(word_add (word_add tp (word(64 * g))) (word 64):int64,8 * 8 * kk)`;
                    "q1",`memory :> bytes(word_add tp (word(64 * g)):int64,8 * 8)`; "c1",`X30`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_add tp (word(64 * (g + 1))):int64 = word_add (word_add tp (word(64 * g))) (word 64)`
   (fun th -> REWRITE_TAC[th]) THENL [S8_OFFSET_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    MP_TAC(SPECL [`word_add tp (word(64 * g)):int64`; `kk:num`; `g:num`] S8_SPLIT_Y2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ONCE_REWRITE_TAC[S8_BYTES_APPEND] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `512 * (g + 1) = 512 * g + 512`; EXP_ADD] THEN
    MATCH_MP_TAC S8_RSTEP_COMBINE THEN MAP_EVERY EXISTS_TAC [`w0:num`; `yh:num`; `bitval tc`] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rand(concl th) = `fr:int64` &&
                                                    free_in `tp:int64` (lhand(concl th)))) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    SUBGOAL_THEN `64 * g + 64 * (kk + 1) < 2 EXP 64 /\ 128 * kk < 2 EXP 64`
     (fun th -> SIMP_TAC[th; S8_WORD_ADD_EQ]) THEN S8_ARITH_TAC]);;

(* The branch at the end of a round: back to the next round, or out. *)
let s8_rnext_tac : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  S8_GHOST_WIN THEN GHOST_INTRO_TAC `c30:int64` `read X30` THEN
  GHOST_INTRO_TAC `w0:num` `bignum_from_memory(word_add tp (word(64 * g)),8)` THEN
  GHOST_INTRO_TAC `yy:num` `bignum_from_memory(word_add tp (word(64 * g)),8 * (2 * kk - g))` THEN
  GHOST_INTRO_TAC `q0:num` `bignum_from_memory(tp,8 * g)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let s8_rloop_tm = s8_mk (s8_red_vars ^ " g pc") (s8_red_hyps ^ " /\\ ~(g = kk)")
  (s8_red_at 0xa34 s8_red_zf `g:num`) (s8_red_at 0x7e4 "" `g:num`) s8_red_maychange;;
let s8_rexit_tm = s8_mk (s8_red_vars ^ " g pc") (s8_red_hyps ^ " /\\ g = kk")
  (s8_red_at 0xa34 s8_red_zf `g:num`) (s8_red_at 0xa38 "" `g:num`) s8_red_maychange;;
let S8_RLOOP = prove(s8_rloop_tm,s8_rnext_tac);;
let S8_REXIT = prove(s8_rexit_tm,s8_rnext_tac);;

let s8_red_mid (extra:string) (t:term) =
  rand(concl(BETA_CONV(mk_comb(parse_term ("\\(g:num) (s:armstate). " ^ s8_red_inv ^ extra),t))));;
let s8_red_iv = parse_term (Printf.sprintf
  "\\(g:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0xa34) /\\ %s%s"
  s8_red_inv s8_red_zf);;
let s8_reduce_tm = s8_mk (s8_red_vars ^ " pc") s8_red_hyps
  (s8_red_at 0x7e4 "" `0`) (s8_red_at 0xa38 "" `kk:num`) s8_red_maychange;;

let S8_REDUCE = prove(s8_reduce_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xa34` (s8_red_mid s8_red_zf `(0 + 1) + (kk - 1)`) THEN CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0xa34` (s8_red_mid s8_red_zf `0 + 1`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_RSTEP) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `(0 + 1) + (kk - 1) = kk` SUBST1_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_REXIT) THEN ASM_REWRITE_TAC[]] THEN
  M4_ITER_TAC s8_red_iv `0 + 1` `kk - 1` THEN X_GEN_TAC `g:num` THEN STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x7e4` (s8_red_mid "" `g:num`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_RLOOP) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC;
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_RSTEP) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The final subtraction and selection, 0xa38 to 0xbf0, for kk >= 2 blocks.  *)
(* ------------------------------------------------------------------------- *)

let s8_tu = "word_add tp (word(64 * kk))";;
let s8_fin_hyps =
  "2 <= kk /\\ kk < 2 EXP 56 /\\
   nonoverlapping (z:int64,64 * kk) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (z,64 * kk) (m:int64,64 * kk) /\\
   nonoverlapping (z,64 * kk) (tp:int64,128 * kk) /\\
   nonoverlapping (z,64 * kk) (fr:int64,128) /\\
   nonoverlapping (tp,128 * kk) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (tp,128 * kk) (m,64 * kk) /\\
   nonoverlapping (tp,128 * kk) (fr,128)";;
let s8_fin_maychange =
  "MAYCHANGE [PC; X0; X1; X2; X3; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
              X19; X20; X21; X22; X23; X24; X25; X26; X27; X30] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
   MAYCHANGE [memory :> bytes(z,64 * kk); memory :> bytes(tp,128 * kk)]";;
let s8_regs (reg:int) (v:string) (idx:int -> string) (ps:int list) : string =
  String.concat " /\\ " (map (fun p -> Printf.sprintf "read X%d s = word(bigdigit %s (%s))" (reg + p) v (idx p)) ps);;

(* The subtraction's loop, at its head, with block c pending: z holds
   t - n's low 8c words, x14 and x15 the next two with CF their borrow, and
   x21..x26 and x8..x13 the six words of t and n after them. *)
let s8_sub_inv = Printf.sprintf
  "read X0 s = word_add z (word(64 * c)) /\\ read X3 s = z /\\
   read X1 s = word_add m (word(64 * (c + 1))) /\\ read X2 s = word_add (%s) (word(64 * (c + 1))) /\\
   read X27 s = word(64 * kk - 64 * (c + 1)) /\\ read X5 s = word(64 * kk) /\\ read SP s = tp /\\
   read X30 s = cw /\\ read X29 s = fr /\\ read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
   %s /\\ %s /\\
   bignum_from_memory(m,8 * kk) s = n /\\ bignum_from_memory(%s,8 * kk) s = t /\\
   &(bignum_from_memory(z,8 * c) s) + &2 pow (512 * c) * (&(val(read X14 s)) + &2 pow 64 * &(val(read X15 s))):real =
   &2 pow (512 * c + 128) * &(bitval(~read CF s)) + &(lowdigits t (8 * c + 2)) - &(lowdigits n (8 * c + 2))"
  s8_tu (s8_regs 19 "t" (fun p -> Printf.sprintf "8 * c + %d" p) (2--7))
  (s8_regs 6 "n" (fun p -> Printf.sprintf "8 * c + %d" p) (2--7)) s8_tu;;
let s8_sub_at (pc:int) (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term (Printf.sprintf
  "\\(c:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\ %s"
  pc s8_sub_inv),t))));;
let s8_sub_vars = "z m n tp t cw fr ra kk";;
let s8_sub_body_tm = s8_mk (s8_sub_vars ^ " c pc") (s8_fin_hyps ^ " /\\ c + 2 <= kk")
  (s8_sub_at 0xa50 `c:num`) (s8_sub_at 0xab0 `c + 1`) s8_fin_maychange;;

let S8_SUB_BODY = prove(s8_sub_body_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w14:int64` `read X14` THEN GHOST_INTRO_TAC `w15:int64` `read X15` THEN
  GHOST_INTRO_TAC `zl:num` `bignum_from_memory(z,8 * c)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  S8_READ8_TAC `s0:armstate` `m:int64` `8 * kk` `8 * (c + 1)` `m:int64` `64 * (c + 1)` THEN
  S8_READ8_TAC `s0:armstate` `word_add tp (word(64 * kk)):int64` `8 * kk` `8 * (c + 1)`
     `word_add tp (word(64 * kk)):int64` `64 * (c + 1)` THEN
  MAP_EVERY (fun p -> S8_READ_TAC `s0:armstate` `word_add tp (word(64 * kk)):int64` `8 * kk`
      (if p = 0 then `8 * (c + 1)` else mk_binop `(+):num->num->num` `8 * (c + 1)` (mk_small_numeral p))
      (mk_comb(`word_add tp:int64->int64`,mk_comb(`word:num->int64`,
         if p = 0 then `64 * kk + 64 * (c + 1)`
         else mk_binop `(+):num->num->num` `64 * kk` (mk_binop `(+):num->num->num` `64 * (c + 1)` (mk_small_numeral(8 * p))))))) [0;2;4;6] THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X3`;`X27`] [1;3;5;7;9;11;21;24] (1--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [S8_OFFSET_TAC; S8_OFFSET_TAC; S8_OFFSET_TAC;
    SUBGOAL_THEN `64 <= 64 * kk - 64 * (c + 1)` (fun th -> SIMP_TAC[th; WORD_SUB2]) THENL
     [S8_ARITH_TAC; AP_TERM_TAC THEN S8_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[S8_BYTES_APPEND; S8_BYTES8] THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * (c + 1) + 2 = (8 * c + 2) + 8`; S8_LOWDIGITS_ADD8] THEN
  REWRITE_TAC[ARITH_RULE `(8 * c + 2) + 1 = 8 * c + 3 /\ (8 * c + 2) + 2 = 8 * c + 4 /\ (8 * c + 2) + 3 = 8 * c + 5 /\
                          (8 * c + 2) + 4 = 8 * c + 6 /\ (8 * c + 2) + 5 = 8 * c + 7 /\ (8 * c + 2) + 6 = 8 * (c + 1) /\
                          (8 * c + 2) + 7 = 8 * (c + 1) + 1`] THEN
  W(fun (asl,w) -> MAP_EVERY MP_TAC (m4_sub_eqs asl)) THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; VAL_WORD_BIGDIGIT] THEN
  REWRITE_TAC[ARITH_RULE `512 * (c + 1) = 512 * c + 512 /\ 64 * (8 * c + 2) = 512 * c + 128`; REAL_POW_ADD] THEN
  SPEC_TAC(`(&2 pow (512 * c)):real`,`e:real`) THEN GEN_TAC THEN
  REWRITE_TAC[BITVAL_NOT] THEN CONV_TAC REAL_RING);;

let s8_sub_post = Printf.sprintf
  "read X3 s = z /\\ read X2 s = tp /\\ read X1 s = %s /\\ read X5 s = word(64 * kk) /\\ read SP s = tp /\\
   read X29 s = fr /\\ read X30 s = ra /\\ bignum_from_memory(%s,8 * kk) s = t /\\
   read X6 s = word(bigdigit (bignum_from_memory(z,8 * kk) s) 0) /\\
   read X7 s = word(bigdigit (bignum_from_memory(z,8 * kk) s) 1) /\\
   read X8 s = word(bigdigit (bignum_from_memory(z,8 * kk) s) 2) /\\
   read X9 s = word(bigdigit (bignum_from_memory(z,8 * kk) s) 3) /\\
   read X19 s = word(bigdigit t 0) /\\ read X20 s = word(bigdigit t 1) /\\
   read X21 s = word(bigdigit t 2) /\\ read X22 s = word(bigdigit t 3) /\\
   &(bignum_from_memory(z,8 * kk) s):real = &2 pow (512 * kk) * &(bitval(t < n)) + &t - &n /\\
   (read CF s <=> ~(val(cw:int64) < bitval(t < n)))" s8_tu s8_tu;;
let s8_at (pc:int) (inv:string) = parse_term (Printf.sprintf
  "\\(s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\ %s" pc inv);;
let s8_sub_exit_tm = s8_mk (s8_sub_vars ^ " p pc") (s8_fin_hyps ^ " /\\ p + 1 = kk")
  (s8_sub_at 0xab0 `p:num`) (s8_at 0xafc s8_sub_post) s8_fin_maychange;;

let S8_LOWDIGITS_ADD6 = prove
 (`!a p. lowdigits a (p + 6) = lowdigits a p + 2 EXP (64 * p) *
     (bigdigit a p + 2 EXP 64 * bigdigit a (p + 1) + 2 EXP 128 * bigdigit a (p + 2) + 2 EXP 192 * bigdigit a (p + 3) +
      2 EXP 256 * bigdigit a (p + 4) + 2 EXP 320 * bigdigit a (p + 5))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `p + 6 = (((((p + 1) + 1) + 1) + 1) + 1) + 1`; LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; EXP_ADD] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let S8_SUB_EXIT = prove(s8_sub_exit_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rand(concl th) = `kk:num`)) THEN
  REWRITE_TAC[SUB_REFL] THEN
  GHOST_INTRO_TAC `cf:bool` `read CF` THEN
  GHOST_INTRO_TAC `w14:int64` `read X14` THEN GHOST_INTRO_TAC `w15:int64` `read X15` THEN
  GHOST_INTRO_TAC `zl:num` `bignum_from_memory(z,8 * p)` THEN
  BIGNUM_TERMRANGE_TAC `8 * (p + 1)` `t:num` THEN BIGNUM_TERMRANGE_TAC `8 * (p + 1)` `n:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (i,a) -> S8_READ_TAC `s0:armstate` `z:int64` `8 * p` i a)
    [`0`,`z:int64`; `1`,`word_add z (word 8):int64`; `2`,`word_add z (word 16):int64`; `3`,`word_add z (word 24):int64`] THEN
  MAP_EVERY (fun (i,a) -> S8_READ_TAC `s0:armstate` `word_add tp (word(64 * (p + 1))):int64` `8 * (p + 1)` i a)
    [`0`,`word_add tp (word(64 * (p + 1))):int64`; `1`,`word_add tp (word(64 * (p + 1) + 8)):int64`;
     `2`,`word_add tp (word(64 * (p + 1) + 16)):int64`; `3`,`word_add tp (word(64 * (p + 1) + 24)):int64`] THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X3`;`X27`] [2;6;8;10;12;14;16] (1--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`8 * (p + 1)`; `z:int64`; `s19:armstate`] BIGNUM_FROM_MEMORY_BOUND) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; S8_BYTES_APPEND; S8_BYTES8] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `512 * p = 64 * 8 * p`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIGDIGIT_ADD_HIGH; ARITH_RULE `2 <= p + 1 ==> 4 <= 8 * p`; ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  ABBREV_TAC `d = zl + 2 EXP (64 * 8 * p) * bignum_of_wordlist [w14; w15; sum_s2; sum_s6; sum_s8; sum_s10; sum_s12; sum_s14]` THEN
  SUBGOAL_THEN `&d:real = &2 pow (64 * 8 * (p + 1)) * &(bitval carry_s14) + &t - &n` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t:num`; `8 * (p + 1)`] LOWDIGITS_SELF) THEN MP_TAC(SPECL [`n:num`; `8 * (p + 1)`] LOWDIGITS_SELF) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `8 * (p + 1) = (8 * p + 2) + 6`; S8_LOWDIGITS_ADD6] THEN
    REWRITE_TAC[ARITH_RULE `(8 * p + 2) + 1 = 8 * p + 3 /\ (8 * p + 2) + 2 = 8 * p + 4 /\ (8 * p + 2) + 3 = 8 * p + 5 /\
                            (8 * p + 2) + 4 = 8 * p + 6 /\ (8 * p + 2) + 5 = 8 * p + 7`] THEN
    W(fun (asl,w) -> MAP_EVERY MP_TAC (m4_sub_eqs asl)) THEN
    EXPAND_TAC "d" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; VAL_WORD_BIGDIGIT] THEN
    REWRITE_TAC[ARITH_RULE `64 * ((8 * p + 2) + 6) = 512 * p + 512 /\ 64 * 8 * p = 512 * p /\ 64 * (8 * p + 2) = 512 * p + 128`;
                REAL_POW_ADD] THEN
    SPEC_TAC(`(&2 pow (512 * p)):real`,`e:real`) THEN GEN_TAC THEN
    REWRITE_TAC[BITVAL_NOT] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SBC_BORROW o check (fun th -> free_in `carry_s16:bool` (concl th) &&
     is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
  SUBGOAL_THEN `carry_s14 <=> t < n` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `d:num` (concl th) && is_eq(concl th) &&
       type_of(lhs(concl th)) = `:real`)) THEN
    MAP_EVERY UNDISCH_TAC [`d < 2 EXP (64 * 8 * (p + 1))`; `t < 2 EXP (64 * 8 * (p + 1))`;
                           `n < 2 EXP (64 * 8 * (p + 1))`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW] THEN
    SPEC_TAC(`2 EXP (64 * 8 * (p + 1))`,`ee:num`) THEN GEN_TAC THEN
    BOOL_CASES_TAC `carry_s14:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[NOT_LT]]);;

let s8_sub_pre = Printf.sprintf
  "read X2 s = %s /\\ read X1 s = word_add m (word 64) /\\ read X5 s = word(64 * kk) /\\ read SP s = tp /\\
   read X30 s = cw /\\ read X29 s = fr /\\ read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
   read (memory :> bytes64(word_add fr (word 96))) s = z /\\ %s /\\ %s /\\
   bignum_from_memory(m,8 * kk) s = n /\\ bignum_from_memory(%s,8 * kk) s = t"
  s8_tu (s8_regs 6 "n" string_of_int (0--7)) (s8_regs 19 "t" string_of_int (0--7)) s8_tu;;
let s8_sub_tm = s8_mk (s8_sub_vars ^ " pc") s8_fin_hyps (s8_at 0xa38 s8_sub_pre) (s8_at 0xafc s8_sub_post) s8_fin_maychange;;

let S8_SUB = prove(s8_sub_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_WHILE_UP_TAC `kk - 1` `pc + 0xa50` `pc + 0xab0`
    (parse_term ("\\(c:num) (s:armstate). " ^ s8_sub_inv)) THEN REPEAT CONJ_TAC THENL
   [S8_ARITH_TAC;
    (* entry *)
    RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; S8_LOWDIGITS_2; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    SUBGOAL_THEN `64 <= 64 * kk` ASSUME_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X3`;`X27`] [3;4] (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[WORD_SUB2];
      REWRITE_TAC[BITVAL_NOT] THEN
      W(fun (asl,w) -> MAP_EVERY MP_TAC (m4_sub_eqs asl)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; VAL_WORD_BIGDIGIT] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REAL_ARITH_TAC];
    (* one block *)
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_SUB_BODY) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC;
    (* back edge *)
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(val(word(64 * kk - 64 * (c + 1)):int64) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `64 * kk - 64 * (c + 1) < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN S8_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    GHOST_INTRO_TAC `cf:bool` `read CF` THEN
    GHOST_INTRO_TAC `w14:int64` `read X14` THEN GHOST_INTRO_TAC `w15:int64` `read X15` THEN
    GHOST_INTRO_TAC `zl:num` `bignum_from_memory(z,8 * c)` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* exit *)
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_SUB_EXIT) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC]);;

(* The selection's loop, at its head, with chunk c of t and of d = t - n in
   x19..x22 and x6..x9: z's low 4c words are selected, and z and t above
   chunk c are untouched. *)
let s8_sel_inv = Printf.sprintf
  "read X3 s = word_add z (word(32 * c)) /\\ read X2 s = word_add tp (word(32 * c)) /\\
   read X1 s = word_add (%s) (word(32 * c)) /\\
   read X27 s = word(64 * kk - 32 * (c + 1)) /\\ read X5 s = word(64 * kk) /\\ read SP s = tp /\\
   read X29 s = fr /\\ read X30 s = ra /\\ read CF s = cf /\\
   read X6 s = word(bigdigit d (4 * c)) /\\ read X7 s = word(bigdigit d (4 * c + 1)) /\\
   read X8 s = word(bigdigit d (4 * c + 2)) /\\ read X9 s = word(bigdigit d (4 * c + 3)) /\\
   read X19 s = word(bigdigit t (4 * c)) /\\ read X20 s = word(bigdigit t (4 * c + 1)) /\\
   read X21 s = word(bigdigit t (4 * c + 2)) /\\ read X22 s = word(bigdigit t (4 * c + 3)) /\\
   bignum_from_memory(word_add z (word(32 * c + 32)),8 * kk - 4 * (c + 1)) s = highdigits d (4 * (c + 1)) /\\
   bignum_from_memory(word_add (%s) (word(32 * c + 32)),8 * kk - 4 * (c + 1)) s = highdigits t (4 * (c + 1)) /\\
   bignum_from_memory(z,4 * c) s = lowdigits (if cf then d else t) (4 * c)" s8_tu s8_tu;;
let s8_sel_at (pc:int) (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term (Printf.sprintf
  "\\(c:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + %d) /\\ %s"
  pc s8_sel_inv),t))));;
let s8_sel_vars = "z tp t d cf fr ra m kk";;
let s8_sel_body_tm = s8_mk (s8_sel_vars ^ " c pc") (s8_fin_hyps ^ " /\\ c + 2 <= 2 * kk")
  (s8_sel_at 0xb00 `c:num`) (s8_sel_at 0xb48 `c + 1`) s8_fin_maychange;;

let s8_tu_tm = parse_term (s8_tu ^ ":int64");;
let s8_wadd (b:term) (off:string) : term =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,b),mk_comb(`word:num->int64`,parse_term off));;

let S8_SEL_BODY = prove(s8_sel_body_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (i,a) -> S8_READ_TAC `s0:armstate` `word_add z (word(32 * c + 32)):int64` `8 * kk - 4 * (c + 1)` i a)
    [`0`,`word_add z (word(32 * c + 32)):int64`; `1`,`word_add z (word(32 * c + 40)):int64`;
     `2`,`word_add z (word(32 * c + 48)):int64`; `3`,`word_add z (word(32 * c + 56)):int64`] THEN
  MAP_EVERY (fun (i,a) -> S8_READ_TAC `s0:armstate` (s8_wadd s8_tu_tm "32 * c + 32") `8 * kk - 4 * (c + 1)` i a)
    [`0`,s8_wadd `tp:int64` "64 * kk + 32 * c + 32"; `0`,s8_wadd s8_tu_tm "32 * c + 32";
     `1`,s8_wadd s8_tu_tm "32 * c + 40"; `1`,s8_wadd `tp:int64` "64 * kk + 32 * c + 40";
     `2`,s8_wadd `tp:int64` "64 * kk + 32 * c + 48"; `2`,s8_wadd s8_tu_tm "32 * c + 48";
     `3`,s8_wadd s8_tu_tm "32 * c + 56"; `3`,s8_wadd `tp:int64` "64 * kk + 32 * c + 56"] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add z (word(32 * (c + 1) + 32)),8 * (8 * kk - 4 * ((c + 1) + 1)))) s0 =
                highdigits (highdigits d (4 * (c + 1))) 4`
   MP_TAC THENL [S8_HIGH_TAC `highdigits d (4 * (c + 1))`;
                 REWRITE_TAC[HIGHDIGITS_HIGHDIGITS; ARITH_RULE `4 * (c + 1) + 4 = 4 * ((c + 1) + 1)`] THEN DISCH_TAC] THEN
  SUBGOAL_THEN (subst [s8_tu_tm,`tu:int64`]
    `read (memory :> bytes(word_add (tu:int64) (word(32 * (c + 1) + 32)),8 * (8 * kk - 4 * ((c + 1) + 1)))) s0 =
     highdigits (highdigits t (4 * (c + 1))) 4`)
   MP_TAC THENL [S8_HIGH_TAC `highdigits t (4 * (c + 1))`;
                 REWRITE_TAC[HIGHDIGITS_HIGHDIGITS; ARITH_RULE `4 * (c + 1) + 4 = 4 * ((c + 1) + 1)`] THEN DISCH_TAC] THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(S8_OFFSET_TAC THEN NO_TAC) THENL
   [SUBGOAL_THEN `32 <= 64 * kk - 32 * (c + 1)` (fun th -> SIMP_TAC[th; WORD_SUB2]) THENL
     [S8_ARITH_TAC; AP_TERM_TAC THEN S8_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[M4_BYTES_ADD4] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `4 * (c + 1) = 4 * c + 4`; LOWDIGITS_ADD4] THEN
  BOOL_CASES_TAC `cf:bool` THEN REWRITE_TAC[VAL_WORD_BIGDIGIT]);;
let s8_sel_post = "read X29 s = fr /\\ read X30 s = ra /\\ read SP s = tp /\\
                   bignum_from_memory(z,8 * kk) s = (if cf then d else t)";;
let s8_sel_exit_tm = s8_mk (s8_sel_vars ^ " p pc")
  (s8_fin_hyps ^ " /\\ p + 1 = 2 * kk /\\ t < 2 EXP (64 * 8 * kk) /\\ d < 2 EXP (64 * 8 * kk)")
  (s8_sel_at 0xb48 `p:num`) (s8_at 0xbf0 s8_sel_post) s8_fin_maychange;;

let S8_SEL_EXIT = prove(s8_sel_exit_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `64 * kk - 32 * (p + 1) = 0` SUBST1_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * kk = 4 * (p + 1)` ASSUME_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p + 1 = 2 * kk`)) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[M4_BYTES_ADD4] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(fun th -> if is_binary "<" (concl th) then SUBS[ASSUME `8 * kk = 4 * (p + 1)`] th else th) THEN
  BOOL_CASES_TAC `cf:bool` THEN REWRITE_TAC[] THEN
  W(fun (asl,w) -> let v = rand w in
    MP_TAC(SPECL [v; `4 * (p + 1)`] LOWDIGITS_SELF) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th])) THEN
  REWRITE_TAC[ARITH_RULE `4 * (p + 1) = 4 * p + 4`; LOWDIGITS_ADD4; VAL_WORD_BIGDIGIT]);;

let s8_sel_pre = Printf.sprintf
  "read X3 s = z /\\ read X2 s = tp /\\ read X1 s = %s /\\ read X5 s = word(64 * kk) /\\ read SP s = tp /\\
   read X29 s = fr /\\ read X30 s = ra /\\ bignum_from_memory(%s,8 * kk) s = t /\\ bignum_from_memory(z,8 * kk) s = d /\\
   read X6 s = word(bigdigit d 0) /\\ read X7 s = word(bigdigit d 1) /\\
   read X8 s = word(bigdigit d 2) /\\ read X9 s = word(bigdigit d 3) /\\
   read X19 s = word(bigdigit t 0) /\\ read X20 s = word(bigdigit t 1) /\\
   read X21 s = word(bigdigit t 2) /\\ read X22 s = word(bigdigit t 3) /\\ read CF s = cf" s8_tu s8_tu;;
let s8_sel_tm = s8_mk (s8_sel_vars ^ " pc") s8_fin_hyps (s8_at 0xafc s8_sel_pre) (s8_at 0xbf0 s8_sel_post) s8_fin_maychange;;

let S8_SEL = prove(s8_sel_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  BIGNUM_TERMRANGE_TAC `8 * kk` `t:num` THEN BIGNUM_TERMRANGE_TAC `8 * kk` `d:num` THEN
  ENSURES_WHILE_UP_TAC `2 * kk - 1` `pc + 0xb00` `pc + 0xb48`
    (parse_term ("\\(c:num) (s:armstate). " ^ s8_sel_inv)) THEN REPEAT CONJ_TAC THENL
   [S8_ARITH_TAC;
    (* entry *)
    RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; LOWDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    SUBGOAL_THEN `32 <= 64 * kk` ASSUME_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FIRST [ASM_SIMP_TAC[WORD_SUB2] THEN NO_TAC; M4_HIGH_TAC `d:num` THEN NO_TAC; M4_HIGH_TAC `t:num` THEN NO_TAC];
    (* one chunk *)
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_SEL_BODY) THEN EXISTS_TAC `m:int64` THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC;
    (* back edge *)
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(val(word(64 * kk - 32 * (c + 1)):int64) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `64 * kk - 32 * (c + 1) < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN S8_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BN_MUL_MONT_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* exit *)
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_SEL_EXIT) THEN EXISTS_TAC `m:int64` THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC]);;
(* The selected value is the Montgomery reduction of aa, from the
   relation the rounds leave. *)
let S8_FINAL_ARITH = prove
 (`!kk n aa q t cv d.
     ODD n /\ n < 2 EXP (512 * kk) /\ t < 2 EXP (512 * kk) /\ q < 2 EXP (512 * kk) /\
     2 EXP (512 * kk) * (t + 2 EXP (512 * kk) * cv) = aa + q * n /\
     &d:real = &2 pow (512 * kk) * &(bitval(t < n)) + &t - &n /\ aa <= 2 EXP (512 * kk) * n
     ==> (if ~(cv < bitval(t < n)) then d else t) = (inverse_mod n (2 EXP (512 * kk)) * aa) MOD n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`8 * kk`; `n:num`; `aa:num`; `1`; `q:num`; `t:num`; `cv:num`; `d:num`] M4_FINAL_ARITH) THEN
  REWRITE_TAC[ARITH_RULE `64 * 8 * kk = 512 * kk`; MULT_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && free_in `aa:num` (concl th))) THEN ARITH_TAC);;

let s8_fin_post = "read X29 s = fr /\\ read X30 s = ra /\\ read SP s = tp /\\
   (aa <= 2 EXP (512 * kk) * n
    ==> bignum_from_memory(z,8 * kk) s = (inverse_mod n (2 EXP (512 * kk)) * aa) MOD n)";;
let s8_fin_tm = s8_mk (s8_red_vars ^ " pc") (s8_fin_hyps ^ " /\\ ODD n")
  (s8_red_at 0xa38 "" `kk:num`) (s8_at 0xbf0 s8_fin_post) s8_fin_maychange;;

let S8_FIN = prove(s8_fin_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * kk - kk = kk`] THEN
  SUBGOAL_THEN (subst [s8_tu_tm,`tu:int64`]
    `!s. bignum_from_memory(tu:int64,8) s = lowdigits (bignum_from_memory(tu,8 * kk) s) 8`)
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `MIN (8 * kk) 8 = 8` SUBST1_TAC THENL [S8_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  S8_GHOST_WIN THEN GHOST_INTRO_TAC `cw:int64` `read X30` THEN
  GHOST_INTRO_TAC `t:num` (subst [s8_tu_tm,`tu:int64`] `bignum_from_memory(tu:int64,8 * kk)`) THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory(tp,8 * kk)` THEN
  BIGNUM_TERMRANGE_TAC `8 * kk` `t:num` THEN BIGNUM_TERMRANGE_TAC `8 * kk` `n:num` THEN
  BIGNUM_TERMRANGE_TAC `8 * kk` `q:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `v19:int64` (concl th) && is_eq(concl th))) THEN
  REWRITE_TAC[GSYM S8_BLOCK; BIGNUM_OF_WORDLIST_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `64 * 8 * kk = 512 * kk`]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xafc` (parse_term ("\\s. " ^ s8_sub_post)) THEN CONJ_TAC THENL
   [M4_USE_TAC2(SPECL [`z:int64`; `m:int64`; `n:num`; `tp:int64`; `t:num`; `cw:int64`; `fr:int64`; `ra:int64`;
                       `kk:num`; `pc:num`] S8_SUB);
    ALL_TAC] THEN
  GHOST_INTRO_TAC `d:num` `bignum_from_memory(z,8 * kk)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  M4_USE_TAC2(SPECL [`z:int64`; `tp:int64`; `t:num`; `d:num`; `~(val(cw:int64) < bitval(t < n))`;
                     `fr:int64`; `ra:int64`; `m:int64`; `kk:num`; `pc:num`] S8_SEL) THEN
  DISCH_TAC THEN MATCH_MP_TAC S8_FINAL_ARITH THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One block: the eight reduction steps, the upper half added, and the final *)
(* subtraction and selection, 0x7e4 to 0xbf0.                                *)
(* ------------------------------------------------------------------------- *)

let s8_one_ww = "bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26]";;
let s8_one_tm = s8_mk "tp m n w yh fr ra z w19 w20 w21 w22 w23 w24 w25 w26 pc"
  "(bigdigit n 0 * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\ ODD n /\\ aligned 16 (tp:int64) /\\
   nonoverlapping (tp,128) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (tp,128) (m:int64,64) /\\ nonoverlapping (tp,128) (fr:int64,128) /\\
   nonoverlapping (z:int64,64) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (z,64) (tp,128) /\\ nonoverlapping (z,64) (fr,128) /\\ nonoverlapping (z,64) (m,64)"
  (s8_at 0x7e4 (Printf.sprintf
    "read SP s = tp /\\ read X29 s = fr /\\ read X3 s = word_add m (word 64) /\\
     read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
     read (memory :> bytes64(word_add fr (word 96))) s = z /\\ bignum_from_memory(m,8) s = n /\\
     read X2 s = tp /\\ read X1 s = word_add m (word 64) /\\ read X4 s = w /\\ read X27 s = word 8 /\\
     read X28 s = word(val w * val(w19:int64)) /\\ %s /\\ %s /\\
     bignum_from_memory(word_add tp (word 64),8) s = yh" s8_ndigits0 (s8_reads 19 "w" 19)))
  (s8_at 0xbf0 (Printf.sprintf
    "read X29 s = fr /\\ read X30 s = ra /\\ read SP s = tp /\\
     (%s + 2 EXP 512 * yh <= 2 EXP 512 * n
      ==> bignum_from_memory(z,8) s = (inverse_mod n (2 EXP 512) * (%s + 2 EXP 512 * yh)) MOD n)" s8_one_ww s8_one_ww))
  "MAYCHANGE [PC; X0; X1; X2; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
              X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
   MAYCHANGE [memory :> bytes(z,64); memory :> bytes(tp,128)]";;

let S8_ONE = prove(s8_one_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `8` `n:num` THEN BIGNUM_TERMRANGE_TAC `8` `yh:num` THEN
  SUBGOAL_THEN (rhs(concl(REWRITE_CONV[ADD_CLAUSES] (mk_conj(mk_eq(s8_nb "0",`n:num`),mk_eq(s8_yb "0",`yh:num`)))))) STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; S8_BLOCK] THEN CONJ_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_add m (word 64)) (word_add m (word 64)):int64) = 0` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL ([`tp:int64`] @ s8_nblock `0` @ [`w:int64`] @
     map (fun i -> mk_var("w" ^ string_of_int i,`:int64`)) (19--26) @ [`pc:num`])
     (REWRITE_RULE[ADD_CLAUSES] S8_RED8)) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS; VAL_WORD_BIGDIGIT; ADD_CLAUSES] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
  S8_NAME_TAC "s1" ["qq",`memory :> bytes(tp:int64,8 * 8)`] THEN S8_NAME_WIN_TAC "s1" "t" THEN
  MP_TAC(SPECL [`8`; `tp:int64`; `s1:armstate`] BIGNUM_FROM_MEMORY_BOUND) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  S8_READ8_TAC `s1:armstate` `word_add tp (word 64):int64` `8` `0` `tp:int64` `64` THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [6;7;9;10;12;13;14;15] (2--16) THEN
  SUBGOAL_THEN `2 EXP 512 * (bignum_of_wordlist [sum_s6; sum_s7; sum_s9; sum_s10; sum_s12; sum_s13; sum_s14; sum_s15] +
                             2 EXP 512 * bitval carry_s15) =
                (bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] + 2 EXP 512 * yh) + qq * n`
   ASSUME_TAC THENL
   [MATCH_MP_TAC S8_RP0 THEN EXISTS_TAC `bignum_of_wordlist [t19; t20; t21; t22; t23; t24; t25; t26]` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `yh:num` && can (term_match [] `bignum_of_wordlist (l:int64 list)`) (lhs(concl th))
                          then GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th] else NO_TAC) THEN
    S8_ACC_TAC;
    ALL_TAC] THEN
  ARM_XACCSTEPS_TAC BN_MUL_MONT_EXEC [`SP`;`X0`;`X1`;`X2`;`X27`] [19;21;23;25;27;29;31;33;35] (17--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[S8_BYTES8] THEN
  REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) S8_BYTES8] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `tt = bignum_of_wordlist [sum_s6; sum_s7; sum_s9; sum_s10; sum_s12; sum_s13; sum_s14; sum_s15]` THEN
  ABBREV_TAC `dd = bignum_of_wordlist [sum_s19; sum_s21; sum_s23; sum_s25; sum_s27; sum_s29; sum_s31; sum_s33]` THEN
  SUBGOAL_THEN `bignum_of_wordlist
     [(if carry_s35 then sum_s6 else sum_s19:int64); (if carry_s35 then sum_s7 else sum_s21);
      (if carry_s35 then sum_s9 else sum_s23); (if carry_s35 then sum_s10 else sum_s25);
      (if carry_s35 then sum_s12 else sum_s27); (if carry_s35 then sum_s13 else sum_s29);
      (if carry_s35 then sum_s14 else sum_s31); (if carry_s35 then sum_s15 else sum_s33)] =
     (if carry_s35 then tt else dd)` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tt"; "dd"] THEN BOOL_CASES_TAC `carry_s35:bool` THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tt < 2 EXP 512 /\ dd < 2 EXP 512` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tt"; "dd"] THEN REWRITE_TAC[S8_WL8_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `&dd:real = &2 pow 512 * &(bitval carry_s33) + &tt - &n` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `n:num` &&
                             can (term_match [] `bignum_of_wordlist (l:int64 list)`) (lhs(concl th))
                          then GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [SYM th] else NO_TAC) THEN
    MAP_EVERY EXPAND_TAC ["tt"; "dd"] THEN S8_ACC_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SBC_BORROW o check (fun th -> free_in `carry_s35:bool` (concl th) &&
     is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
  REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN DISCH_THEN SUBST1_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  SUBGOAL_THEN `carry_s33 <=> tt < n` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `dd:num` (concl th) && is_eq(concl th) &&
       type_of(lhs(concl th)) = `:real`)) THEN
    MAP_EVERY UNDISCH_TAC [`dd < 2 EXP 512`; `tt < 2 EXP 512`; `n < 2 EXP 512`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW] THEN
    SPEC_TAC(`2 EXP 512`,`ee:num`) THEN GEN_TAC THEN
    BOOL_CASES_TAC `carry_s33:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`1`; `n:num`; `bignum_of_wordlist [w19; w20; w21; w22; w23; w24; w25; w26] + 2 EXP 512 * yh`;
                `qq:num`; `tt:num`; `bitval carry_s15`; `dd:num`] S8_FINAL_ARITH) THEN
  REWRITE_TAC[MULT_CLAUSES; COND_SWAP] THEN S8_NUMS_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The prologue, 0x268 to 0x2f0: loads the first block of a, makes the       *)
(* frame of 16k bytes and zeroes it from its ninth word on.                  *)
(* ------------------------------------------------------------------------- *)

let s8_pre_hyps =
  "1 <= kk /\\ kk < 2 EXP 56 /\\ word_sub fr (word(128 * kk)) = tp /\\
   nonoverlapping (tp:int64,128 * kk) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (tp,128 * kk) (x:int64,64 * kk) /\\
   nonoverlapping (tp,128 * kk) (word_add fr (word 112):int64,8) /\\
   nonoverlapping (word_add fr (word 112):int64,8) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (word_add fr (word 112):int64,8) (x,64 * kk)";;
let s8_pre_maychange =
  "MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
              X19; X20; X21; X22; X23; X24; X25; X26; X27; SP] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
   MAYCHANGE [memory :> bytes(tp,128 * kk); memory :> bytes(word_add fr (word 112),8)]";;
let s8_adig0 = String.concat " /\\ " (map (fun p -> Printf.sprintf "read X%d s = word(bigdigit a %d)" (6 + p) p) (0--7));;
let s8_pre_inv = Printf.sprintf
  "read SP s = tp /\\ read X29 s = fr /\\ read X1 s = x /\\ read X4 s = w /\\ read X5 s = word(64 * kk) /\\
   read X2 s = word_add tp (word(128 * (j + 1))) /\\ read X27 s = word(64 * kk - 64 * (j + 1)) /\\ %s /\\
   bignum_from_memory(x,8 * kk) s = a /\\ bignum_from_memory(word_add tp (word 64),16 * j + 8) s = 0" s8_adig0;;
let s8_pre_at (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term (Printf.sprintf
  "\\(j:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x2b8) /\\ %s"
  s8_pre_inv),t))));;
let s8_pre_vars = "x n0p w a kk fr tp";;
let s8_pre_pre =
  "read SP s = fr /\\ read X29 s = fr /\\ read X1 s = x /\\ read X4 s = n0p /\\ read X5 s = word(8 * kk) /\\
   read (memory :> bytes64 n0p) s = w /\\ bignum_from_memory(x,8 * kk) s = a";;
let s8_pre_post = Printf.sprintf
  "read SP s = tp /\\ read X29 s = fr /\\ read X2 s = tp /\\ read X1 s = word_add x (word 64) /\\
   read X3 s = word_add x (word(64 * kk)) /\\ read X5 s = word(64 * kk) /\\ read X4 s = w /\\
   read (memory :> bytes64(word_add fr (word 112))) s = w /\\ %s /\\ %s /\\
   bignum_from_memory(x,8 * kk) s = a /\\ bignum_from_memory(word_add tp (word 64),8 * (kk - 1)) s = 0"
  s8_adig0 (String.concat " /\\ " (map (fun p -> Printf.sprintf "read X%d s = word 0" p) (19--26)));;
let s8_pre_entry_tm = s8_mk (s8_pre_vars ^ " pc") s8_pre_hyps (s8_at 0x268 s8_pre_pre) (s8_pre_at `0`) s8_pre_maychange;;
let s8_pre_loop_tm = s8_mk (s8_pre_vars ^ " j pc") (s8_pre_hyps ^ " /\\ j + 1 < kk") (s8_pre_at `j:num`) (s8_pre_at `j + 1`) s8_pre_maychange;;
let s8_pre_exit_tm = s8_mk (s8_pre_vars ^ " j pc") (s8_pre_hyps ^ " /\\ j + 1 = kk") (s8_pre_at `j:num`) (s8_at 0x2f0 s8_pre_post) s8_pre_maychange;;
let s8_pre_tm = s8_mk (s8_pre_vars ^ " pc") s8_pre_hyps (s8_at 0x268 s8_pre_pre) (s8_at 0x2f0 s8_pre_post) s8_pre_maychange;;

let S8_WORD_SHL = prove
 (`!k. word_shl (word(8 * k):int64) 4 = word(128 * k) /\ word_shl (word(8 * k):int64) 3 = word(64 * k)`,
  GEN_TAC THEN REWRITE_TAC[WORD_SHL3] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let S8_ZERO8 = prove
 (`bignum_of_wordlist [word 0:int64; word 0; word 0; word 0; word 0; word 0; word 0; word 0] = 0`,
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV);;

let S8_BYTES8N = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) S8_BYTES8;;
let S8_BYTES16 = prove
 (`!(a:int64) s. read(memory :> bytes(a,8 * 16)) s =
                 read(memory :> bytes(a,64)) s + 2 EXP 512 * read(memory :> bytes(word_add a (word 64),64)) s`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`a:int64`; `8`; `8`; `s:armstate`] BIGNUM_FROM_MEMORY_SPLIT) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;
(* Zero words read back as a zero array. *)
let S8_ZERO_TAC : tactic =
  REWRITE_TAC[S8_BYTES8N] THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[S8_ZERO8] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];;

let S8_PRE_ENTRY = prove(s8_pre_entry_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `64 <= 64 * kk` ASSUME_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  S8_READ8_TAC `s0:armstate` `x:int64` `8 * kk` `0` `x:int64` `0` THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[S8_WORD_SHL]) THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && rhs(concl th) = `tp:int64` then th
                           else REWRITE_RULE[ASSUME `word_sub fr (word(128 * kk)):int64 = tp`] th) THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (11--15) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[WORD_SUB2]; S8_ZERO_TAC]);;

let S8_PRE_LOOP = prove(s8_pre_loop_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(word(64 * kk - 64 * (j + 1)):int64) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `64 * kk - 64 * (j + 1) < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THEN S8_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [S8_OFFSET_TAC;
    SUBGOAL_THEN `64 <= 64 * kk - 64 * (j + 1)` (fun th -> SIMP_TAC[th; WORD_SUB2]) THENL
     [S8_ARITH_TAC; AP_TERM_TAC THEN S8_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `16 * (j + 1) + 8 = (16 * j + 8) + 16`] THEN ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  SUBGOAL_THEN `word_add (word_add tp (word 64)) (word(8 * (16 * j + 8))):int64 = word_add tp (word(128 * (j + 1)))`
   SUBST1_TAC THENL [S8_OFFSET_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_REWRITE_TAC[S8_BYTES16; ADD_CLAUSES] THEN S8_ZERO_TAC);;

let S8_PRE_EXIT = prove(s8_pre_exit_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `64 * kk - 64 * (j + 1) = 0` SUBST1_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`word_add tp (word 64):int64`; `16 * j + 8`; `8 * (kk - 1)`; `s14:armstate`] LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
  SUBGOAL_THEN `MIN (16 * j + 8) (8 * (kk - 1)) = 8 * (kk - 1)` SUBST1_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let s8_pre_iv = parse_term (Printf.sprintf
  "\\(j:num) (s:armstate). aligned_bytes_loaded s (word pc) bn_mul_mont_mc /\\ read PC s = word(pc + 0x2b8) /\\ %s"
  s8_pre_inv);;
let s8_pre_mid (t:term) = rand(concl(BETA_CONV(mk_comb(parse_term ("\\(j:num) (s:armstate). " ^ s8_pre_inv),t))));;

let S8_PRE = prove(s8_pre_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2b8` (s8_pre_mid `0 + (kk - 1)`) THEN CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x2b8` (s8_pre_mid `0`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_PRE_ENTRY) THEN ASM_REWRITE_TAC[]; ALL_TAC];
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_PRE_EXIT) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC] THEN
  M4_ITER_TAC s8_pre_iv `0` `kk - 1` THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] S8_PRE_LOOP) THEN ASM_REWRITE_TAC[] THEN S8_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole routine after the register saves, 0x268 to 0xbf0.               *)
(* ------------------------------------------------------------------------- *)

(* The rounds, from the state the second phase leaves. *)
let s8_reduce0_pre = Printf.sprintf
  "%s /\\ read X2 s = tp /\\ read X1 s = word_add m (word 64) /\\ read X4 s = w /\\
   read X27 s = word 8 /\\ %s /\\ read X28 s = word(val w * val(read X19 s)) /\\ read X30 s = word 0 /\\
   bignum_of_wordlist %s = lowdigits aa 8 /\\ bignum_from_memory(tp,16 * kk) s = aa"
  s8_red_const s8_ndigits0 s8_win;;
let s8_reduce0_tm = s8_mk (s8_red_vars ^ " pc") s8_red_hyps
  (s8_at 0x7e4 s8_reduce0_pre) (s8_red_at 0xa38 "" `kk:num`) s8_red_maychange;;

let S8_REDUCE0 = prove(s8_reduce0_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC (s8_red_at 0x7e4 "" `0`) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; EXP; SUB_0; ADD_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL; VAL_WORD_0;
                    ARITH_RULE `0 <= 1 /\ 8 * 2 * kk = 16 * kk`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `aa:num`)) THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `MIN (16 * kk) 8 = 8` SUBST1_TAC THENL [S8_ARITH_TAC; REWRITE_TAC[]];
    MATCH_MP_TAC S8_REDUCE THEN ASM_REWRITE_TAC[]]);;

let S8_N0_CONG = prove
 (`!n w. (n * w + 1 == 0) (mod (2 EXP 64)) ==> (bigdigit n 0 * w + 1 == 0) (mod (2 EXP 64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; MULT_CLAUSES; EXP; DIV_1; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let S8_OFF_DIGIT0 = prove
 (`!a i. bigdigit (s8_off a i) 0 = 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; MULT_CLAUSES; EXP; DIV_1] THEN
  REWRITE_TAC[GSYM DIVIDES_MOD; S8_OFF_DIVIDES]);;

let s8_body_hyps =
  "1 <= kk /\\ kk < 2 EXP 56 /\\ (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\\ aligned 16 (fr:int64) /\\
   word_sub fr (word(128 * kk)) = tp /\\
   nonoverlapping (tp:int64,128 * kk) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (tp,128 * kk) (x:int64,64 * kk) /\\ nonoverlapping (tp,128 * kk) (m:int64,64 * kk) /\\
   nonoverlapping (tp,128 * kk) (fr,128) /\\
   nonoverlapping (z:int64,64 * kk) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (z,64 * kk) (tp,128 * kk) /\\ nonoverlapping (z,64 * kk) (m,64 * kk) /\\
   nonoverlapping (z,64 * kk) (fr,128) /\\
   nonoverlapping (fr,128) (word pc,LENGTH bn_mul_mont_mc) /\\
   nonoverlapping (fr,128) (x,64 * kk) /\\ nonoverlapping (fr,128) (m,64 * kk)";;
let s8_body_tm = s8_mk "z x m n0p w a n kk fr tp ra pc" s8_body_hyps
  (s8_at 0x268
    "read SP s = fr /\\ read X29 s = fr /\\ read (memory :> bytes64(word_add fr (word 8))) s = ra /\\
     read (memory :> bytes64(word_add fr (word 96))) s = z /\\
     read (memory :> bytes64(word_add fr (word 104))) s = m /\\
     read X1 s = x /\\ read X4 s = n0p /\\ read X5 s = word(8 * kk) /\\ read (memory :> bytes64 n0p) s = w /\\
     bignum_from_memory(x,8 * kk) s = a /\\ bignum_from_memory(m,8 * kk) s = n")
  (parse_term "\\s. read PC s = word(pc + 0xbf0) /\\ read X29 s = fr /\\ read X30 s = ra /\\ read SP s = tp /\\
     (a * a <= 2 EXP (512 * kk) * n
      ==> bignum_from_memory(z,8 * kk) s = (inverse_mod n (2 EXP (512 * kk)) * a * a) MOD n)")
  "MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
              X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X30; SP] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
   MAYCHANGE [memory :> bytes(z,64 * kk); memory :> bytes(tp,128 * kk); memory :> bytes(word_add fr (word 112),8)]";;

(* The theorem th without aligned_bytes_loaded in its postcondition: a
   big step keeps the code loaded itself, and takes the first such fact it
   finds for the state before. *)
let s8_drop_loaded (th:thm) : thm =
  let vs,bod = strip_forall(concl th) in
  let hyp,ens = dest_imp bod in
  let q = rand(rator ens) in
  let s,qb = dest_abs q in
  let q' = mk_abs(s,rand qb) in
  let ens' = mk_comb(mk_comb(rator(rator ens),q'),rand ens) in
  prove(list_mk_forall(vs,mk_imp(hyp,ens')),
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q THEN
    CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT2);
      MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC]);;

let S8_PRE_STEP = s8_drop_loaded S8_PRE;;
let S8_REDUCE_STEP = s8_drop_loaded S8_REDUCE0;;
let S8_FIN_STEP = s8_drop_loaded S8_FIN;;
let S8_ONE_STEP = s8_drop_loaded S8_ONE;;

let S8_BODY = prove(s8_body_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> SUBGOAL_THEN t (ASSUME_TAC o REWRITE_RULE[NONOVERLAPPING_CLAUSES; LENGTH_BN]) THENL
     [REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN] THEN NONOVERLAPPING_TAC; ALL_TAC])
   [`nonoverlapping (word_add fr (word 112):int64,8) (word pc,LENGTH bn_mul_mont_mc)`] THEN
  BIGNUM_TERMRANGE_TAC `8 * kk` `a:num` THEN BIGNUM_TERMRANGE_TAC `8 * kk` `n:num` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NEGMODINV_ODD) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP S8_N0_CONG) THEN
  SUBGOAL_THEN `aligned 16 (tp:int64)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `tp:int64`)) THEN
    ASM_SIMP_TAC[ALIGNED_WORD_SUB_EQ; ALIGNED_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
     [REWRITE_TAC[DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[divides] THEN EXISTS_TAC `8 * kk` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add tp (word(128 * kk)):int64 = fr` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `tp:int64`)) THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `64 * 8 * kk = 512 * kk`]) THEN
  MP_TAC(SPECL [`a:num`; `kk:num`] S8_OFF_FINAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 * s8_off a kk + s8_dsq a (8 * kk) < 2 EXP (1024 * kk)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1024 * kk = 512 * kk + 512 * kk`; EXP_ADD] THEN
    MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`x:int64`; `n0p:int64`; `w:int64`; `a:num`; `kk:num`; `fr:int64`; `tp:int64`; `pc:num`] S8_PRE_STEP) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s1" THEN
  MP_TAC(SPECL [`tp:int64`; `x:int64`; `kk:num`; `a:num`; `pc:num`] S8_ROWS) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s2" THEN
  S8_NAME_TAC "s2" ["w26",`X26`] THEN
  SUBGOAL_THEN `read (memory :> bytes(m:int64,8 * 8)) s2 = lowdigits n 8` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `n:num` && free_in `s2:armstate` (concl th)
                            then GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th] else NO_TAC) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `MIN (8 * kk) 8 = 8` SUBST1_TAC THENL [S8_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  MP_TAC(SPECL [`tp:int64`; `x:int64`; `kk:num`; `a:num`; `s8_off a kk`; `fr:int64`; `m:int64`; `w:int64`;
                `lowdigits n 8`; `w26:int64`; `pc:num`] S8_SA) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS; S8_OFF_DIGIT0] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s3" THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `read (memory :> bytes(m:int64,8 * 8)) s3 = lowdigits n 8`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && rhs(concl th) = `lowdigits n 8`)) THEN
  REWRITE_TAC[GSYM S8_BLOCK; BIGNUM_OF_WORDLIST_EQ] THEN STRIP_TAC THEN
  ASM_CASES_TAC `kk = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN REWRITE_TAC[MULT_CLAUSES] THEN
    SUBGOAL_THEN `bignum_of_wordlist [read X19 s3; read X20 s3; read X21 s3; read X22 s3;
                                      read X23 s3; read X24 s3; read X25 s3; read X26 s3] +
                  2 EXP 512 * read (memory :> bytes(word_add tp (word 64),8 * 8)) s3 = a * a` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `a * a` && free_in `memory` (concl th)
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_BIGNUM_FROM_MEMORY; ARITH_RULE `MIN 16 8 = 8`] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE `16 = 8 + 8`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      ALL_TAC] THEN
    S8_NAME_WIN_TAC "s3" "w" THEN
    ABBREV_TAC `yh = read (memory :> bytes(word_add tp (word 64),8 * 8)) s3` THEN
    MP_TAC(SPECL ([`tp:int64`; `m:int64`; `n:num`; `w:int64`; `yh:num`; `fr:int64`; `ra:int64`; `z:int64`] @
       map (fun i -> mk_var("w" ^ string_of_int i,`:int64`)) (19--26) @ [`pc:num`]) S8_ONE_STEP) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
    ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s4" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= kk` ASSUME_TAC THENL [S8_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`tp:int64`; `m:int64`; `kk:num`; `n:num`; `w:int64`; `a * a`; `fr:int64`; `ra:int64`; `z:int64`;
                `pc:num`] S8_REDUCE_STEP) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s4" THEN
  MP_TAC(SPECL [`tp:int64`; `m:int64`; `kk:num`; `n:num`; `w:int64`; `a * a`; `fr:int64`; `ra:int64`; `z:int64`;
                `pc:num`] S8_FIN_STEP) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The squaring from entry to return: the dispatch at 0x0 and 0x240 reaches  *)
(* it for a width that is a multiple of eight when x = y.                    *)
(* ------------------------------------------------------------------------- *)

let s8_subroutine_tm =
 `!z x y m n0p a b n w k pc stackpointer returnaddress.
     8 <= k /\ k < 2 EXP 58 /\ k MOD 8 = 0 /\ x = y /\
     (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [(z,8 * k); (word_sub stackpointer (word(16 * k + 128)),16 * k + 128)]
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k); (n0p,8)] /\
     nonoverlapping (z,8 * k) (word_sub stackpointer (word(16 * k + 128)),16 * k + 128)
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
                      memory :> bytes(word_sub stackpointer (word(16 * k + 128)),16 * k + 128)])`;;

let BN_MUL_MONT_SQR8X_SUBROUTINE_CORRECT = prove(s8_subroutine_tm,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`;
                       `a:num`; `b:num`; `n:num`; `w:int64`; `k:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 128 THEN
  MAP_EVERY X_GEN_TAC [`fr:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `x:int64 = y`)) THEN
  ASM_CASES_TAC `b:num = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC; ENSURES_INIT_TAC "s0" THEN ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] o
    check (fun th -> try fst(dest_pair(lhand(concl th))) = `z:int64` &&
                         fst(dest_pair(rand(concl th))) <> `word pc:int64` &&
                         snd(dest_pair(rand(concl th))) = `16 * k + 128` with _ -> false)) THEN
  FRAME_SPLIT_TAC `128` `128` THEN
  FRAME_SPLIT_TAC `16 * k + 128` `16 * k` THEN
  MAP_EVERY (fun (c1,l1,c2,l2) ->
    MP_TAC(SPECL [`word_add fr (word 128):int64`; c1; l1; c2; l2] SUBFRAME_DISJ) THEN
    ANTS_TAC THENL [UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC;
      DISCH_THEN(fun th -> ASSUME_TAC th THEN ASSUME_TAC(ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th))])
   [`128`,`128`,`16 * k + 128`,`16 * k`] THEN
  SUBGOAL_THEN `aligned 16 (fr:int64)` ASSUME_TAC THENL
   [SUBGOAL_THEN `aligned 16 (word 128:int64)` ASSUME_TAC THENL
     [REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64; DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    ASM_MESON_TAC[ALIGNED_WORD_ADD_EQ];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_sub (word_add (fr:int64) (word 128)) (word 128) = fr`;
    REWRITE_RULE[ARITH_RULE `16 * k + 128 = 16 * k + 128`]
     (SPECL [`fr:int64`; `16 * k`] (WORD_RULE `!fr:int64 c. word_sub (word_add fr (word 128)) (word(c + 128)) = word_sub fr (word c)`))]) THEN
  ABBREV_TAC `tp = word_sub fr (word(16 * k)):int64` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> free_in `16 * k + 128` (concl th)))) THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MP_TAC(SPEC `k:num` M4_DISPATCH) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`k:num`; `4`; `2`] MOD_MULT_MOD) THEN UNDISCH_TAC `k MOD 8 = 0` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `val(word_sub x x:int64) = 0` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]; ALL_TAC] THEN
  SUBGOAL_THEN `?kk. k = 8 * kk` (X_CHOOSE_THEN `kk:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `k DIV 8` THEN MP_TAC(SPECL [`k:num`; `8`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= kk /\ kk < 2 EXP 56` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8 * 8 * kk = 64 * kk /\ 16 * 8 * kk = 128 * kk`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst BN_MUL_MONT_EXEC]) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_and (word(8 * kk):int64) (word 7)) = 0`]) THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (3--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub x x:int64) = 0`]) THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (5--12) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> free_in `word_and (word(8 * kk):int64)` (concl th) ||
                                                    free_in `word_sub x x:int64` (concl th)))) THEN
  MP_TAC(SPECL [`z:int64`; `x:int64`; `m:int64`; `n0p:int64`; `w:int64`; `a:num`; `n:num`; `kk:num`;
                `fr:int64`; `tp:int64`; `returnaddress:int64`; `pc:num`]
     (REWRITE_RULE[ARITH_RULE `512 * kk = 64 * 8 * kk`] S8_BODY)) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst BN_MUL_MONT_EXEC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ARM_BIGSTEP_TAC BN_MUL_MONT_EXEC "s13" THEN
  ARM_STEPS_TAC BN_MUL_MONT_EXEC (14--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `bs = word_sub (word_add fr (word 128)) (word(16 * 8 * kk + 128)):int64` THEN
  SUBGOAL_THEN `fr:int64 = word_add bs (word(128 * kk)) /\ tp:int64 = bs` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tp"; "bs"] THEN
    REWRITE_TAC[ARITH_RULE `16 * 8 * kk + 128 = 128 * kk + 128`; WORD_ADD] THEN CONJ_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (maychange_term o concl)) THEN
  REWRITE_TAC[ASSUME `fr:int64 = word_add bs (word(128 * kk))`; ASSUME `tp:int64 = bs`] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* All three routines as one theorem: bn_mul_mont at every width from two    *)
(* words, with the largest of their frames, the squaring's.                  *)
(* ------------------------------------------------------------------------- *)

(* Uses the routine th, whose frame is the fsize bytes at off above the
   base bs of the 16k + 128 bytes the caller grants. *)
let BN_ROUTINE_TAC (th:thm) (fsize:term) (off:term) (split:tactic) : tactic =
  MP_TAC(SPECL [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`; `a:num`; `b:num`; `n:num`; `w:int64`;
                `k:num`; `pc:num`; `word_add bs (word(16 * k + 128)):int64`; `returnaddress:int64`] th) THEN
  SUBGOAL_THEN (subst [fsize,`fsize:num`; off,`off:num`]
     `word_sub (word_add bs (word(16 * k + 128))) (word fsize):int64 = word_add bs (word off)`)
   SUBST1_TAC THENL
   [SUBGOAL_THEN (subst [fsize,`fsize:num`; off,`off:num`] `16 * k + 128 = off + fsize`) SUBST1_TAC THENL
     [split; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ALLPAIRS; ALL; WORD_ADD_0] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; LENGTH_BN]) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; LENGTH_BN] THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; NONOVERLAPPING_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  DISCH_THEN(fun eth ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (rand(concl eth)) THEN
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ACCEPT_TAC eth]);;

let bn_mul_mont_tm =
 `!z x y m n0p a b n w k pc stackpointer returnaddress.
     2 <= k /\ k < 2 EXP 58 /\
     (k MOD 4 = 0 ==> val x + 32 < 2 EXP 64 /\ val m + 32 < 2 EXP 64) /\
     (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [(z,8 * k); (word_sub stackpointer (word(16 * k + 128)),16 * k + 128)]
       [(word pc,LENGTH bn_mul_mont_mc); (x,8 * k); (y,8 * k); (m,8 * k); (n0p,8)] /\
     nonoverlapping (z,8 * k) (word_sub stackpointer (word(16 * k + 128)),16 * k + 128)
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
                      memory :> bytes(word_sub stackpointer (word(16 * k + 128)),16 * k + 128)])`;;

let BN_MUL_MONT_SUBROUTINE_CORRECT = prove(bn_mul_mont_tm,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALLPAIRS; ALL] THEN STRIP_TAC THEN
  ABBREV_TAC `bs = word_sub stackpointer (word(16 * k + 128)):int64` THEN
  SUBGOAL_THEN `stackpointer:int64 = word_add bs (word(16 * k + 128))` SUBST_ALL_TAC THENL
   [EXPAND_TAC "bs" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_CASES_TAC `k MOD 4 = 0` THENL
   [ALL_TAC;
    BN_ROUTINE_TAC BN_MUL_MONT_GENERIC_SUBROUTINE_CORRECT `8 * k + 72` `8 * k + 56` ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `4 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN UNDISCH_TAC `k MOD 4 = 0` THEN
      ASM_SIMP_TAC[MOD_LT] THEN UNDISCH_TAC `2 <= k` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k MOD 8 = 0 /\ x:int64 = y` THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `8 <= k` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN UNDISCH_TAC `k MOD 8 = 0` THEN
      ASM_SIMP_TAC[MOD_LT] THEN UNDISCH_TAC `2 <= k` THEN ARITH_TAC; ALL_TAC] THEN
    BN_ROUTINE_TAC BN_MUL_MONT_SQR8X_SUBROUTINE_CORRECT `16 * k + 128` `0` ARITH_TAC;
    BN_ROUTINE_TAC BN_MUL_MONT_MUL4X_SUBROUTINE_CORRECT `8 * k + 160` `8 * k - 32` (UNDISCH_TAC `4 <= k` THEN ARITH_TAC)]);;
