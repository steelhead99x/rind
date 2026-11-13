(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The 64 rounds of x86_64's SHA-NI SHA-256 blocks, as rind's build emits    *)
(* them.                                                                     *)
(* ========================================================================= *)

(* Both asm! blocks in rind's low::x86_64::sha256, sha256_compress_blocks_shaext
   and sha256_finish_shaext, compress each block with the one rounds! body,
   LLVM's output of the SHA extensions' intrinsics Graviola wrote, which they
   hold at 0x52 and 0x6a. SHA256_SHAEXT_ROUNDS_CORRECT proves it once: from
   the block's 16 words, byte-swapped, in xmm14, xmm15, xmm1, and xmm12, the
   byte-swap mask in xmm4, K at rcx, and a state as the SHA extensions hold
   it, ABEF in xmm11 and CDGH in xmm10, it leaves there s2n-bignum's FIPS
   180-4 sha256_block of them. Each block's proof checks that its bytes hold
   these and applies the theorem where they run.

   The proof steps the 148 instructions symbolically, as awslabs/s2n-bignum
   pull request #450 does aws-lc's routine on the same instructions, on the
   model additions rind's fork of s2n-bignum carries. It keeps
   each register as four words of the spec, sha256_quad, rewriting each
   SHA256RNDS2 to two rounds and each SHA256MSG1, PALIGNR, PADDD, and
   SHA256MSG2 to message schedule words, so nothing case-splits on the
   data. *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/sha256_spec.ml";;

(* The rounds' bytes, which each block's listing includes at its offset. *)
let sha256_shaext_rounds =
[
  0x66; 0x44; 0x0f; 0x38; 0x00; 0xf4;
                           (* PSHUFB (%_% xmm14) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0x38; 0x00; 0xfc;
                           (* PSHUFB (%_% xmm15) (%_% xmm4) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc6;
                           (* MOVDQA (%_% xmm0) (%_% xmm14) *)
  0x66; 0x0f; 0xfe; 0x01;  (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0x66; 0x41; 0x0f; 0x6f; 0xd2;
                           (* MOVDQA (%_% xmm2) (%_% xmm10) *)
  0x41; 0x0f; 0x38; 0xcb; 0xd3;
                           (* SHA256RNDS2 (%_% xmm2) (%_% xmm11) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xdb;
                           (* MOVDQA (%_% xmm3) (%_% xmm11) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc7;
                           (* MOVDQA (%_% xmm0) (%_% xmm15) *)
  0x66; 0x0f; 0xfe; 0x41; 0x10;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,16))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x66; 0x0f; 0x38; 0x00; 0xcc;
                           (* PSHUFB (%_% xmm1) (%_% xmm4) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x0f; 0x6f; 0xc1;  (* MOVDQA (%_% xmm0) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0x00; 0xe4;
                           (* PSHUFB (%_% xmm12) (%_% xmm4) *)
  0x66; 0x0f; 0xfe; 0x41; 0x20;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,32))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x45; 0x0f; 0x38; 0xcc; 0xf7;
                           (* SHA256MSG1 (%_% xmm14) (%_% xmm15) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc4;
                           (* MOVDQA (%_% xmm0) (%_% xmm12) *)
  0x66; 0x0f; 0xfe; 0x41; 0x30;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,48))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x45; 0x0f; 0x6f; 0xec;
                           (* MOVDQA (%_% xmm13) (%_% xmm12) *)
  0x66; 0x44; 0x0f; 0x3a; 0x0f; 0xe9; 0x04;
                           (* PALIGNR (%_% xmm13) (%_% xmm1) (Imm8 (word 4)) *)
  0x66; 0x45; 0x0f; 0xfe; 0xee;
                           (* PADDD (%_% xmm13) (%_% xmm14) *)
  0x45; 0x0f; 0x38; 0xcd; 0xec;
                           (* SHA256MSG2 (%_% xmm13) (%_% xmm12) *)
  0x44; 0x0f; 0x38; 0xcc; 0xf9;
                           (* SHA256MSG1 (%_% xmm15) (%_% xmm1) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc5;
                           (* MOVDQA (%_% xmm0) (%_% xmm13) *)
  0x66; 0x0f; 0xfe; 0x41; 0x40;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,64))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x45; 0x0f; 0x6f; 0xf5;
                           (* MOVDQA (%_% xmm14) (%_% xmm13) *)
  0x66; 0x45; 0x0f; 0x3a; 0x0f; 0xf4; 0x04;
                           (* PALIGNR (%_% xmm14) (%_% xmm12) (Imm8 (word 4)) *)
  0x66; 0x45; 0x0f; 0xfe; 0xf7;
                           (* PADDD (%_% xmm14) (%_% xmm15) *)
  0x45; 0x0f; 0x38; 0xcd; 0xf5;
                           (* SHA256MSG2 (%_% xmm14) (%_% xmm13) *)
  0x41; 0x0f; 0x38; 0xcc; 0xcc;
                           (* SHA256MSG1 (%_% xmm1) (%_% xmm12) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc6;
                           (* MOVDQA (%_% xmm0) (%_% xmm14) *)
  0x66; 0x0f; 0xfe; 0x41; 0x50;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,80))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x45; 0x0f; 0x6f; 0xfe;
                           (* MOVDQA (%_% xmm15) (%_% xmm14) *)
  0x66; 0x45; 0x0f; 0x3a; 0x0f; 0xfd; 0x04;
                           (* PALIGNR (%_% xmm15) (%_% xmm13) (Imm8 (word 4)) *)
  0x66; 0x44; 0x0f; 0xfe; 0xf9;
                           (* PADDD (%_% xmm15) (%_% xmm1) *)
  0x45; 0x0f; 0x38; 0xcd; 0xfe;
                           (* SHA256MSG2 (%_% xmm15) (%_% xmm14) *)
  0x45; 0x0f; 0x38; 0xcc; 0xe5;
                           (* SHA256MSG1 (%_% xmm12) (%_% xmm13) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc7;
                           (* MOVDQA (%_% xmm0) (%_% xmm15) *)
  0x66; 0x0f; 0xfe; 0x41; 0x60;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,96))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x41; 0x0f; 0x6f; 0xcf;
                           (* MOVDQA (%_% xmm1) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0x3a; 0x0f; 0xce; 0x04;
                           (* PALIGNR (%_% xmm1) (%_% xmm14) (Imm8 (word 4)) *)
  0x66; 0x41; 0x0f; 0xfe; 0xcc;
                           (* PADDD (%_% xmm1) (%_% xmm12) *)
  0x41; 0x0f; 0x38; 0xcd; 0xcf;
                           (* SHA256MSG2 (%_% xmm1) (%_% xmm15) *)
  0x45; 0x0f; 0x38; 0xcc; 0xee;
                           (* SHA256MSG1 (%_% xmm13) (%_% xmm14) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x0f; 0x6f; 0xc1;  (* MOVDQA (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0xfe; 0x41; 0x70;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,112))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x44; 0x0f; 0x6f; 0xe1;
                           (* MOVDQA (%_% xmm12) (%_% xmm1) *)
  0x66; 0x45; 0x0f; 0x3a; 0x0f; 0xe7; 0x04;
                           (* PALIGNR (%_% xmm12) (%_% xmm15) (Imm8 (word 4)) *)
  0x66; 0x45; 0x0f; 0xfe; 0xe5;
                           (* PADDD (%_% xmm12) (%_% xmm13) *)
  0x44; 0x0f; 0x38; 0xcd; 0xe1;
                           (* SHA256MSG2 (%_% xmm12) (%_% xmm1) *)
  0x45; 0x0f; 0x38; 0xcc; 0xf7;
                           (* SHA256MSG1 (%_% xmm14) (%_% xmm15) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc4;
                           (* MOVDQA (%_% xmm0) (%_% xmm12) *)
  0x66; 0x0f; 0xfe; 0x81; 0x80; 0x00; 0x00; 0x00;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,128))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x45; 0x0f; 0x6f; 0xec;
                           (* MOVDQA (%_% xmm13) (%_% xmm12) *)
  0x66; 0x44; 0x0f; 0x3a; 0x0f; 0xe9; 0x04;
                           (* PALIGNR (%_% xmm13) (%_% xmm1) (Imm8 (word 4)) *)
  0x66; 0x45; 0x0f; 0xfe; 0xee;
                           (* PADDD (%_% xmm13) (%_% xmm14) *)
  0x45; 0x0f; 0x38; 0xcd; 0xec;
                           (* SHA256MSG2 (%_% xmm13) (%_% xmm12) *)
  0x44; 0x0f; 0x38; 0xcc; 0xf9;
                           (* SHA256MSG1 (%_% xmm15) (%_% xmm1) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x41; 0x0f; 0x38; 0xcc; 0xcc;
                           (* SHA256MSG1 (%_% xmm1) (%_% xmm12) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc5;
                           (* MOVDQA (%_% xmm0) (%_% xmm13) *)
  0x66; 0x45; 0x0f; 0x6f; 0xf5;
                           (* MOVDQA (%_% xmm14) (%_% xmm13) *)
  0x66; 0x45; 0x0f; 0x3a; 0x0f; 0xf4; 0x04;
                           (* PALIGNR (%_% xmm14) (%_% xmm12) (Imm8 (word 4)) *)
  0x66; 0x0f; 0xfe; 0x81; 0x90; 0x00; 0x00; 0x00;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,144))) *)
  0x66; 0x45; 0x0f; 0xfe; 0xf7;
                           (* PADDD (%_% xmm14) (%_% xmm15) *)
  0x45; 0x0f; 0x38; 0xcd; 0xf5;
                           (* SHA256MSG2 (%_% xmm14) (%_% xmm13) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x45; 0x0f; 0x38; 0xcc; 0xe5;
                           (* SHA256MSG1 (%_% xmm12) (%_% xmm13) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc6;
                           (* MOVDQA (%_% xmm0) (%_% xmm14) *)
  0x66; 0x45; 0x0f; 0x6f; 0xfe;
                           (* MOVDQA (%_% xmm15) (%_% xmm14) *)
  0x66; 0x45; 0x0f; 0x3a; 0x0f; 0xfd; 0x04;
                           (* PALIGNR (%_% xmm15) (%_% xmm13) (Imm8 (word 4)) *)
  0x66; 0x0f; 0xfe; 0x81; 0xa0; 0x00; 0x00; 0x00;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,160))) *)
  0x66; 0x44; 0x0f; 0xfe; 0xf9;
                           (* PADDD (%_% xmm15) (%_% xmm1) *)
  0x45; 0x0f; 0x38; 0xcd; 0xfe;
                           (* SHA256MSG2 (%_% xmm15) (%_% xmm14) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x45; 0x0f; 0x38; 0xcc; 0xee;
                           (* SHA256MSG1 (%_% xmm13) (%_% xmm14) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc7;
                           (* MOVDQA (%_% xmm0) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0x6f; 0xcf;
                           (* MOVDQA (%_% xmm1) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0x3a; 0x0f; 0xce; 0x04;
                           (* PALIGNR (%_% xmm1) (%_% xmm14) (Imm8 (word 4)) *)
  0x66; 0x0f; 0xfe; 0x81; 0xb0; 0x00; 0x00; 0x00;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,176))) *)
  0x66; 0x41; 0x0f; 0xfe; 0xcc;
                           (* PADDD (%_% xmm1) (%_% xmm12) *)
  0x41; 0x0f; 0x38; 0xcd; 0xcf;
                           (* SHA256MSG2 (%_% xmm1) (%_% xmm15) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x45; 0x0f; 0x38; 0xcc; 0xf7;
                           (* SHA256MSG1 (%_% xmm14) (%_% xmm15) *)
  0x66; 0x44; 0x0f; 0x6f; 0xe1;
                           (* MOVDQA (%_% xmm12) (%_% xmm1) *)
  0x66; 0x45; 0x0f; 0x3a; 0x0f; 0xe7; 0x04;
                           (* PALIGNR (%_% xmm12) (%_% xmm15) (Imm8 (word 4)) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x66; 0x45; 0x0f; 0xfe; 0xe5;
                           (* PADDD (%_% xmm12) (%_% xmm13) *)
  0x44; 0x0f; 0x38; 0xcd; 0xe1;
                           (* SHA256MSG2 (%_% xmm12) (%_% xmm1) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x44; 0x0f; 0x38; 0xcc; 0xf9;
                           (* SHA256MSG1 (%_% xmm15) (%_% xmm1) *)
  0x66; 0x45; 0x0f; 0x6f; 0xec;
                           (* MOVDQA (%_% xmm13) (%_% xmm12) *)
  0x66; 0x44; 0x0f; 0x3a; 0x0f; 0xe9; 0x04;
                           (* PALIGNR (%_% xmm13) (%_% xmm1) (Imm8 (word 4)) *)
  0x66; 0x0f; 0x6f; 0xc1;  (* MOVDQA (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0xfe; 0x81; 0xc0; 0x00; 0x00; 0x00;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,192))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x66; 0x45; 0x0f; 0xfe; 0xee;
                           (* PADDD (%_% xmm13) (%_% xmm14) *)
  0x45; 0x0f; 0x38; 0xcd; 0xec;
                           (* SHA256MSG2 (%_% xmm13) (%_% xmm12) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xcd;
                           (* MOVDQA (%_% xmm1) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x3a; 0x0f; 0xcc; 0x04;
                           (* PALIGNR (%_% xmm1) (%_% xmm12) (Imm8 (word 4)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc4;
                           (* MOVDQA (%_% xmm0) (%_% xmm12) *)
  0x66; 0x0f; 0xfe; 0x81; 0xd0; 0x00; 0x00; 0x00;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,208))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0xfe; 0xcf;
                           (* PADDD (%_% xmm1) (%_% xmm15) *)
  0x41; 0x0f; 0x38; 0xcd; 0xcd;
                           (* SHA256MSG2 (%_% xmm1) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x6f; 0xc5;
                           (* MOVDQA (%_% xmm0) (%_% xmm13) *)
  0x66; 0x0f; 0xfe; 0x81; 0xe0; 0x00; 0x00; 0x00;
                           (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,224))) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0xfe; 0x89; 0xf0; 0x00; 0x00; 0x00;
                           (* PADDD (%_% xmm1) (Memop Word128 (%% (rcx,240))) *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x0f; 0x6f; 0xc1;  (* MOVDQA (%_% xmm0) (%_% xmm1) *)
  0x0f; 0x38; 0xcb; 0xd3;  (* SHA256RNDS2 (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0x70; 0xc1; 0x0e;
                           (* PSHUFD (%_% xmm0) (%_% xmm1) (Imm8 (word 14)) *)
  0x0f; 0x38; 0xcb; 0xda;  (* SHA256RNDS2 (%_% xmm3) (%_% xmm2) *)
  0x66; 0x44; 0x0f; 0xfe; 0xdb;
                           (* PADDD (%_% xmm11) (%_% xmm3) *)
  0x66; 0x44; 0x0f; 0xfe; 0xd2
                           (* PADDD (%_% xmm10) (%_% xmm2) *)
];;

let sha256_shaext_rounds_mc = define_word_list "sha256_shaext_rounds_mc"
  (term_of_array (Array.of_list sha256_shaext_rounds));;

let SHA256_SHAEXT_ROUNDS_EXEC = X86_MK_EXEC_RULE sha256_shaext_rounds_mc;;

(* admin/prove writes K, the round constants and then the byte-swap mask, as
   rind's release build emits it, to x86_64/sha256_shaext_k.bin. The
   definition fails unless its bytes are FIPS 180-4's constants, those of
   sha256_constants, then the mask, each word little-endian. *)
let sha256_shaext_k =
  let words =
    map (dest_small_numeral o rand) (dest_list(rhs(concl sha256_constants))) @
    [0x00010203; 0x04050607; 0x08090a0b; 0x0c0d0e0f] in
  define_assert_word_list "sha256_shaext_k"
    (term_of_bytes (load_file "x86_64/sha256_shaext_k.bin"))
    (List.concat_map
      (fun w -> [w land 255; (w lsr 8) land 255; (w lsr 16) land 255; w lsr 24])
      words);;

(* ------------------------------------------------------------------------- *)
(* A vector register as four words of the spec, low lane first.              *)
(* ------------------------------------------------------------------------- *)

let sha256_quad = new_definition
 `sha256_quad (a:int32) (b:int32) (c:int32) (d:int32) : int128 =
    word_join (word_join d c:int64) (word_join b a:int64)`;;

(* The state as the SHA extensions hold it: A, B, E, and F, and C, D, G, and
   H, each from the top lane down. *)
let sha256_abef = new_definition
 `sha256_abef (l:int32 list) = sha256_quad (EL 5 l) (EL 4 l) (EL 1 l) (EL 0 l)`;;
let sha256_cdgh = new_definition
 `sha256_cdgh (l:int32 list) = sha256_quad (EL 7 l) (EL 6 l) (EL 3 l) (EL 2 l)`;;

let SHA256_QUAD_SUBWORDS = prove
 (`!a b c d:int32.
     word_subword (sha256_quad a b c d) (0,32) = a /\
     word_subword (sha256_quad a b c d) (32,32) = b /\
     word_subword (sha256_quad a b c d) (64,32) = c /\
     word_subword (sha256_quad a b c d) (96,32) = d`,
  REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST);;

let SHA256_QUAD_NESTED = prove
 (`!a b c d:int32.
     sha256_quad a b c d =
     (word_join:int32->96 word->int128) d
       ((word_join:int32->64 word->96 word) c ((word_join:int32->int32->int64) b a))`,
  REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST);;

let SHA256_QUAD_INJ = prove
 (`!a b c d x y z w:int32.
     sha256_quad a b c d = sha256_quad x y z w <=> a = x /\ b = y /\ c = z /\ d = w`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun p ->
    MP_TAC(AP_TERM (subst [p,`p:num#num`] `\q:int128. (word_subword q p:int32)`) th))
    [`0,32`; `32,32`; `64,32`; `96,32`]) THEN
  REWRITE_TAC[SHA256_QUAD_SUBWORDS] THEN SIMP_TAC[]);;

(* A word's bytes, as PSHUFB with the mask moves them. *)
let SHA256_BYTES_REVERSED = prove
 (`!x:int32.
     (word_join:int16->int16->int32)
       ((word_join:byte->byte->int16) (word_subword x (0,8)) (word_subword x (8,8)))
       ((word_join:byte->byte->int16) (word_subword x (16,8)) (word_subword x (24,8))) =
     word_bytereverse x`,
  CONV_TAC WORD_BLAST);;

let SHA256_BYTEREVERSE_BYTEREVERSE = prove
 (`!x:int32. word_bytereverse (word_bytereverse x) = x`,
  CONV_TAC WORD_BLAST);;

(* PALIGNR by four and eight bytes. *)
let SHA256_PALIGNR_QUAD = prove
 (`!a b c d e f g h:int32.
     word_subword (word_ushr ((word_join:int128->int128->256 word)
                                (sha256_quad a b c d) (sha256_quad e f g h)) 32)
                  (0,128) : int128 =
     sha256_quad f g h a /\
     word_subword (word_ushr ((word_join:int128->int128->256 word)
                                (sha256_quad a b c d) (sha256_quad e f g h)) 64)
                  (0,128) : int128 =
     sha256_quad g h a b`,
  REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST);;

(* A word's halves, as PBLENDW moves them. *)
let SHA256_HALVES = prove
 (`!x:int32. (word_join:int16->int16->int32) (word_subword x (16,16))
                                             (word_subword x (0,16)) = x`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* SHA256RNDS2 as two rounds of the spec.                                    *)
(* ------------------------------------------------------------------------- *)

let SHA256_RNDS2_ROUNDS = prove
 (`!l k0 w0 k1 w1 x y.
     sha256_rnds2 (sha256_cdgh l) (sha256_abef l)
                  (sha256_quad (word_add w0 k0) (word_add w1 k1) x y) =
     sha256_abef (sha256_round (sha256_round l k0 w0) k1 w1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha256_rnds2; sha256_abef; sha256_cdgh; SHA256_QUAD_SUBWORDS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha256_rnds2_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[sha256_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[SHA256_QUAD_NESTED] THEN
  REWRITE_TAC[GSYM sha_choose; GSYM sha_maj;
              GSYM sha_hash_sigma_0; GSYM sha_hash_sigma_1] THEN
  REWRITE_TAC[WORD_ADD_AC]);;

(* Two rounds move A, B, E, and F to C, D, G, and H. *)
let SHA256_CDGH_TWO_ROUNDS = prove
 (`!l k0 w0 k1 w1.
     sha256_cdgh (sha256_round (sha256_round l k0 w0) k1 w1) = sha256_abef l`,
  REWRITE_TAC[sha256_cdgh; sha256_abef; sha256_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

let SHA256_ABEF_CDGH = prove
 (`!m h n. sha256_abef (sha256_compress_rounds m h n) =
           sha256_cdgh (sha256_compress_rounds m h (n + 2))`,
  REWRITE_TAC[ARITH_RULE `n + 2 = (n + 1) + 1`; sha256_compress_rounds;
              SHA256_CDGH_TWO_ROUNDS]);;

(* The first SHA256RNDS2 runs on the state, and each later one on the ABEF
   two rounds back, which is the CDGH it needs. *)
let SHA256_RNDS2_FIRST = prove
 (`!m h x y.
     sha256_rnds2 (sha256_cdgh h) (sha256_abef h)
       (sha256_quad (word_add (sha256_msg_schedule m 0) (EL 0 sha256_constants))
                    (word_add (sha256_msg_schedule m 1) (EL 1 sha256_constants)) x y) =
     sha256_abef (sha256_compress_rounds m h 2)`,
  REWRITE_TAC[SHA256_RNDS2_ROUNDS; ARITH_RULE `2 = (0 + 1) + 1`] THEN
  REWRITE_TAC[sha256_compress_rounds] THEN REWRITE_TAC[ADD_CLAUSES]);;

let SHA256_RNDS2_STEP = prove
 (`!m h n x y.
     sha256_rnds2 (sha256_abef (sha256_compress_rounds m h n))
                  (sha256_abef (sha256_compress_rounds m h (n + 2)))
       (sha256_quad
         (word_add (sha256_msg_schedule m (n + 2)) (EL (n + 2) sha256_constants))
         (word_add (sha256_msg_schedule m (n + 3)) (EL (n + 3) sha256_constants)) x y) =
     sha256_abef (sha256_compress_rounds m h (n + 4))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [SHA256_ABEF_CDGH] THEN
  REWRITE_TAC[SHA256_RNDS2_ROUNDS] THEN
  REWRITE_TAC[ARITH_RULE `n + 4 = (n + 3) + 1`; ARITH_RULE `n + 3 = (n + 2) + 1`] THEN
  REWRITE_TAC[sha256_compress_rounds]);;

(* ------------------------------------------------------------------------- *)
(* SHA256MSG1, PALIGNR, PADDD, and SHA256MSG2 as the message schedule.       *)
(* ------------------------------------------------------------------------- *)

let SHA256_MSG1_QUAD = prove
 (`!w0 w1 w2 w3 w4 w5 w6 w7:int32.
     sha256_msg1 (sha256_quad w0 w1 w2 w3) (sha256_quad w4 w5 w6 w7) =
     sha256_quad (word_add w0 (sha_msg_sigma_0 w1)) (word_add w1 (sha_msg_sigma_0 w2))
                 (word_add w2 (sha_msg_sigma_0 w3)) (word_add w3 (sha_msg_sigma_0 w4))`,
  REWRITE_TAC[sha256_msg1; SHA256_QUAD_SUBWORDS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA256_QUAD_NESTED; GSYM sha_msg_sigma_0]);;

let SHA256_MSG2_QUAD = prove
 (`!p0 p1 p2 p3 w12 w13 w14 w15:int32.
     sha256_msg2 (sha256_quad p0 p1 p2 p3) (sha256_quad w12 w13 w14 w15) =
     sha256_quad (word_add p0 (sha_msg_sigma_1 w14)) (word_add p1 (sha_msg_sigma_1 w15))
                 (word_add p2 (sha_msg_sigma_1 (word_add p0 (sha_msg_sigma_1 w14))))
                 (word_add p3 (sha_msg_sigma_1 (word_add p1 (sha_msg_sigma_1 w15))))`,
  REWRITE_TAC[sha256_msg2; SHA256_QUAD_SUBWORDS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA256_QUAD_NESTED; GSYM sha_msg_sigma_1]);;

(* Each schedule word as the instructions sum it. *)
let SHA256_MSG_SCHEDULE_SHAEXT = prove
 (`!m t. sha256_msg_schedule m (t + 16) =
         word_add (word_add (sha256_msg_schedule m (t + 9))
                            (word_add (sha256_msg_schedule m t)
                                      (sha_msg_sigma_0 (sha256_msg_schedule m (t + 1)))))
                  (sha_msg_sigma_1 (sha256_msg_schedule m (t + 14)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [sha256_msg_schedule] THEN
  REWRITE_TAC[ARITH_RULE `~(t + 16 < 16) /\ (t + 16) - 2 = t + 14 /\
                          (t + 16) - 7 = t + 9 /\ (t + 16) - 15 = t + 1 /\
                          (t + 16) - 16 = t`] THEN
  REWRITE_TAC[WORD_ADD_AC]);;

let SHA256_MSG_SCHEDULE_FIRST = map (fun t ->
    CONV_RULE(RAND_CONV(RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC REWRITE_CONV[]))
      (REWR_CONV sha256_msg_schedule
        (mk_comb(`sha256_msg_schedule m`, mk_small_numeral t))))
  (0--15);;

(* ------------------------------------------------------------------------- *)
(* Stepping, with each vector register kept as a sha256_quad of the spec.    *)
(* ------------------------------------------------------------------------- *)

let SHA256_SHAEXT_FOLD_THS =
  map (fun t -> GSYM(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
         (SPECL [`m:int32 list`; mk_small_numeral t] SHA256_MSG_SCHEDULE_SHAEXT)))
      (0--47) @
  SHA256_RNDS2_FIRST ::
  map (fun i ->
    let th = CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
      (SPECL [`m:int32 list`; `h:int32 list`; mk_small_numeral(2*i)] SHA256_RNDS2_STEP) in
    if i = 0 then REWRITE_RULE[CONJUNCT1 sha256_compress_rounds] th else th)
  (0--30);;

(* The value a step writes to a vector register: its lanes reduced to words,
   then folded back into a sha256_quad, through the instruction lemmas. *)
let SHA256_SHAEXT_VALUE_CONV =
  TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
  REWRITE_CONV[SHA256_QUAD_SUBWORDS; SHA256_MSG1_QUAD; SHA256_MSG2_QUAD;
               SHA256_PALIGNR_QUAD] THENC
  REWRITE_CONV[sha256_quad] THENC TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
  REWRITE_CONV([SHA256_BYTES_REVERSED; SHA256_BYTEREVERSE_BYTEREVERSE; SHA256_HALVES;
                GSYM sha256_quad; GSYM SHA256_QUAD_NESTED] @ SHA256_SHAEXT_FOLD_THS);;

let is_ymm_fact th =
  try (match lhs(concl th) with
         Comb(Comb(Const("read",_),Const(n,_)),_) ->
           String.length n >= 3 && String.sub n 0 3 = "YMM"
       | _ -> false)
  with Failure _ -> false;;

(* A legacy SSE instruction keeps a register's top half, so each fact is
   `read YMMk s = word_join hi v`: reduce both. *)
let SHA256_SHAEXT_NORM_TAC =
  RULE_ASSUM_TAC(fun th -> if is_ymm_fact th then
    CONV_RULE(TRY_CONV(RAND_CONV(RAND_CONV SHA256_SHAEXT_VALUE_CONV THENC
                                 LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))) th
    else th);;

let SHA256_SHAEXT_STEPS_TAC execth ns =
  MAP_EVERY (fun n -> X86_STEPS_TAC execth [n] THEN SHA256_SHAEXT_NORM_TAC) ns;;

let READ_XMM_YMM = prove
 (`(!s. read XMM0 s = word_subword (read YMM0 s) (0,128)) /\
   (!s. read XMM1 s = word_subword (read YMM1 s) (0,128)) /\
   (!s. read XMM2 s = word_subword (read YMM2 s) (0,128)) /\
   (!s. read XMM3 s = word_subword (read YMM3 s) (0,128)) /\
   (!s. read XMM4 s = word_subword (read YMM4 s) (0,128)) /\
   (!s. read XMM10 s = word_subword (read YMM10 s) (0,128)) /\
   (!s. read XMM11 s = word_subword (read YMM11 s) (0,128)) /\
   (!s. read XMM12 s = word_subword (read YMM12 s) (0,128)) /\
   (!s. read XMM13 s = word_subword (read YMM13 s) (0,128)) /\
   (!s. read XMM14 s = word_subword (read YMM14 s) (0,128)) /\
   (!s. read XMM15 s = word_subword (read YMM15 s) (0,128))`,
  REWRITE_TAC[XMM0; XMM1; XMM2; XMM3; XMM4; XMM10; XMM11; XMM12; XMM13; XMM14;
              XMM15; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Names the vector registers' starting values, and states each XMM fact as
   one about them, the form stepping keeps. *)
let SHA256_SHAEXT_YMM_INIT_TAC =
  let ghost n =
    GHOST_INTRO_TAC (mk_var("y"^string_of_int n,`:int256`))
                    (parse_term("read YMM"^string_of_int n)) in
  MAP_EVERY ghost [0;1;2;3;4;10;11;12;13;14;15] THEN
  ENSURES_INIT_TAC "s0" THEN
  W(fun (asl,_) ->
    let ymms = filter is_ymm_fact (map snd asl) in
    RULE_ASSUM_TAC(fun th -> if is_ymm_fact th then th else
      REWRITE_RULE ymms (REWRITE_RULE[READ_XMM_YMM] th)));;

(* K's sixteen groups of round constants, and its mask. *)
let SHA256_SHAEXT_K_QUADS =
  let at j = mk_comb(`word:num->int64`,
                     mk_binop `(+):num->num->num` `k:num` (mk_small_numeral (16*j))) in
  let kconst t = mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral t),
                         `sha256_constants`) in
  let fact j v = mk_eq(subst [at j,`a:int64`] `read (memory :> bytes128 a) s`, v) in
  let quad j = list_mk_comb(`sha256_quad`, map (fun i -> kconst(4*j+i)) (0--3)) in
  prove
   (list_mk_forall([`s:x86state`; `k:num`],
      mk_imp(`bytes_loaded s (word (k + 0)) sha256_shaext_k`,
             list_mk_conj(map (fun j -> fact j (quad j)) (0--15) @
                          [fact 16 `word 16018520953223639909183530438118932995:int128`]))),
    REPEAT GEN_TAC THEN REWRITE_TAC[sha256_shaext_k] THEN
    CONV_TAC(LAND_CONV DATA64_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT); GSYM WORD_ADD] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[sha256_quad; sha256_constants] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC WORD_REDUCE_CONV);;

(* The facts of SHA256_SHAEXT_K_QUADS, at the addresses steps compute, from
   an assumption bytes_loaded s (word k) sha256_shaext_k. *)
let SHA256_SHAEXT_K_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `bytes_loaded s (word k) sha256_shaext_k`) (concl th)
    then MP_TAC(REWRITE_RULE[WORD_ADD] (REWRITE_RULE[ADD_CLAUSES]
                  (MATCH_MP SHA256_SHAEXT_K_QUADS
                    (ONCE_REWRITE_RULE[ARITH_RULE `k = k + 0`] th))))
    else failwith "SHA256_SHAEXT_K_TAC") THEN
  STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The rounds.                                                               *)
(* ------------------------------------------------------------------------- *)

let SHA256_SHAEXT_ROUNDS_CORRECT = prove
 (`!pc k m h.
     ensures x86
      (\s. bytes_loaded s (word pc) sha256_shaext_rounds_mc /\
           read RIP s = word pc /\
           read RCX s = word k /\
           bytes_loaded s (word k) sha256_shaext_k /\
           read XMM4 s = word 16018520953223639909183530438118932995 /\
           read XMM14 s = sha256_quad (word_bytereverse (EL 0 m)) (word_bytereverse (EL 1 m))
                                      (word_bytereverse (EL 2 m)) (word_bytereverse (EL 3 m)) /\
           read XMM15 s = sha256_quad (word_bytereverse (EL 4 m)) (word_bytereverse (EL 5 m))
                                      (word_bytereverse (EL 6 m)) (word_bytereverse (EL 7 m)) /\
           read XMM1 s = sha256_quad (word_bytereverse (EL 8 m)) (word_bytereverse (EL 9 m))
                                     (word_bytereverse (EL 10 m)) (word_bytereverse (EL 11 m)) /\
           read XMM12 s = sha256_quad (word_bytereverse (EL 12 m)) (word_bytereverse (EL 13 m))
                                      (word_bytereverse (EL 14 m)) (word_bytereverse (EL 15 m)) /\
           read XMM11 s = sha256_abef h /\
           read XMM10 s = sha256_cdgh h)
      (\s. read RIP s = word (pc + 755) /\
           read XMM11 s = sha256_abef (sha256_block m h) /\
           read XMM10 s = sha256_cdgh (sha256_block m h))
      (MAYCHANGE [RIP] ,,
       MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`pc:num`; `k:num`; `m:int32 list`; `h:int32 list`] THEN
  REWRITE_TAC[fst SHA256_SHAEXT_ROUNDS_EXEC] THEN
  SHA256_SHAEXT_YMM_INIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM SHA256_MSG_SCHEDULE_FIRST)) THEN
  SHA256_SHAEXT_K_TAC THEN
  SHA256_SHAEXT_STEPS_TAC SHA256_SHAEXT_ROUNDS_EXEC (1--148) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[READ_XMM_YMM] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
    (SPECL [`m:int32 list`; `h:int32 list`; `62`] SHA256_ABEF_CDGH)] THEN
  REWRITE_TAC[sha256_abef; sha256_cdgh; sha256_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[SHA256_QUAD_SUBWORDS; WORD_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* For the blocks around the rounds: their inputs in memory.                 *)
(* ------------------------------------------------------------------------- *)

(* Sixteen bytes of memory as four words, low address first. *)
let SHA256_READ_QUAD = prove
 (`!a s. read (memory :> bytes128 a) s =
         sha256_quad (read (memory :> bytes32 a) s)
                     (read (memory :> bytes32 (word_add a (word 4))) s)
                     (read (memory :> bytes32 (word_add a (word 8))) s)
                     (read (memory :> bytes32 (word_add a (word 12))) s)`,
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT);
              CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
  REWRITE_TAC[sha256_quad; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]);;

let SHA256_READ_QUAD_SPLIT = prove
 (`!a s x0 x1 x2 x3.
     read (memory :> bytes128 a) s = sha256_quad x0 x1 x2 x3
     ==> read (memory :> bytes32 a) s = x0 /\
         read (memory :> bytes32 (word_add a (word 4))) s = x1 /\
         read (memory :> bytes32 (word_add a (word 8))) s = x2 /\
         read (memory :> bytes32 (word_add a (word 12))) s = x3`,
  REWRITE_TAC[SHA256_READ_QUAD; SHA256_QUAD_INJ]);;

(* The memory M holds K at k, and from data n blocks, m 0 to m (n - 1), each
   word big-endian. *)
let sha256_shaext_blocks_in = new_definition
 `sha256_shaext_blocks_in (k:num) (data:int64) (n:num) (m:num->int32 list)
                          (M:int64->byte) <=>
    read (bytelist (word k,LENGTH sha256_shaext_k)) M = sha256_shaext_k /\
    !i j. i < n /\ j < 16
          ==> read (bytes32 (word_add data (word (64 * i + 4 * j)))) M =
              word_bytereverse (EL j (m i))`;;

(* Steps keep only facts `read c s = v` about the state they reach, so each
   proof names the memory mem0 with GHOST_INTRO_TAC, which steps keep, and
   states its inputs about mem0. This rewrites the facts about read memory s0
   to be about mem0. *)
let SHA256_SHAEXT_MEM0_TAC =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("memory",_)),_)),
           Var("mem0",_)) ->
        RULE_ASSUM_TAC(fun th' ->
          if concl th' = concl th then th' else REWRITE_RULE[th] th')
    | _ -> failwith "SHA256_SHAEXT_MEM0_TAC");;

(* Proves tm, facts about mem0 that defs unfold, from the precondition's. *)
let SHA256_SHAEXT_INPUTS_TAC defs tm =
  SUBGOAL_THEN tm STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "mem0" THEN
    REWRITE_TAC(defs @ [GSYM READ_COMPONENT_COMPOSE]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bytes_loaded]) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* bytes_loaded s (word k) sha256_shaext_k at the state named s, from
   sha256_shaext_blocks_in k data n m mem0. *)
let SHA256_SHAEXT_K_LOADED_TAC s =
  SUBGOAL_THEN (vsubst [mk_var(s,`:x86state`),`s:x86state`]
                  `bytes_loaded s (word k) sha256_shaext_k`) ASSUME_TAC THENL
   [REWRITE_TAC[bytes_loaded; READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[sha256_shaext_blocks_in] o
      check (can (term_match [] `sha256_shaext_blocks_in k data n m mem0`) o concl));
    ALL_TAC];;

(* Proves tm, a read of sixteen bytes at s0 as a sha256_quad, from bytes32
   facts about mem0. *)
let SHA256_SHAEXT_QUAD_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[SHA256_READ_QUAD; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE];
    ALL_TAC];;

(* Lane q of block i at s0, as a load from data's block i reads it. *)
let SHA256_SHAEXT_LANE_TAC i q =
  let a = if q = 0 then vsubst [i,`i:num`] `64 * i`
          else vsubst [i,`i:num`; mk_small_numeral(16*q),`c:num`] `64 * i + c` in
  let w j = vsubst [i,`i:num`; mk_small_numeral(4*q+j),`j:num`]
              `word_bytereverse (EL j ((m:num->int32 list) i))` in
  SHA256_SHAEXT_QUAD_TAC
   (mk_eq(vsubst [a,`a:num`] `read (memory :> bytes128 (word_add data (word a))) s0`,
          list_mk_comb(`sha256_quad`, map w (0--3))));;

(* Block i's four lanes at s0, from sha256_shaext_blocks_in k data n m mem0
   and i < n. *)
let SHA256_SHAEXT_BLOCK_TAC i =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `sha256_shaext_blocks_in k data n m mem0`) (concl th) then
      let th' = CONJUNCT2(REWRITE_RULE[sha256_shaext_blocks_in] th) in
      MAP_EVERY (fun j -> MP_TAC(SPECL [i; mk_small_numeral j] th')) (0--15)
    else failwith "SHA256_SHAEXT_BLOCK_TAC") THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY (SHA256_SHAEXT_LANE_TAC i) (0--3);;

(* The state's eight words at state, as the two loads read them. *)
let SHA256_SHAEXT_STATE_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 state) s0 = sha256_quad h0 h1 h2 h3 /\
    read (memory :> bytes128 (word_add state (word 16))) s0 = sha256_quad h4 h5 h6 h7`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SHA256_READ_QUAD; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* The state as the SHA extensions hold it, from the loads of state, to the
   invariant's form. *)
let SHA256_SHAEXT_LOADED_STATE_TAC =
  REWRITE_TAC[READ_XMM_YMM] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[CONJUNCT1 sha256_hash_blocks; sha256_abef; sha256_cdgh;
              MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];;
