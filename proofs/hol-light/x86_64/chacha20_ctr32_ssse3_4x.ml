(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ChaCha20 four blocks at a time with SSSE3, as rind's                      *)
(* x86_64-unknown-linux-gnu build emits it. Apple's copy, with no shared     *)
(* table section, is not covered.                                            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/chacha20poly1305.ml";;

(* admin/prove loads every x86_64 proof into one session, and an earlier one
   can leave integers first. *)
prioritize_num();;

let chacha20_ssse3_4x_sym s =
  if s = "WHOLE_READONLY" then "chacha20_ssse3_4x_data"
  else if String.ends_with ~suffix:"ZERO" s then "chacha20_ssse3_4x_zero"
  else if String.ends_with ~suffix:"ROT16" s then "chacha20_ssse3_4x_rot16"
  else failwith ("chacha20_ctr32_ssse3_4x: unexpected symbol " ^ s);;

let chacha20_ssse3_4x_mc,chacha20_ssse3_4x_tables =
  define_assert_relocs_from_elf ~map_symbol_name:chacha20_ssse3_4x_sym
    "chacha20_ssse3_4x_mc" "x86_64/chacha20_ctr32_ssse3_4x.o"
(fun b ADDR -> [b[
  0x49; 0x89; 0xe1;        (* MOV (% r9) (% rsp) *)
  0x48; 0x81; 0xec; 0x48; 0x01; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 328)) *)
  0x66; 0x44; 0x0f; 0x6f; 0x1d]; ADDR ("chacha20_ssse3_4x_data",(156)); b[
                           (* MOVDQA (%_% xmm11)
(Memop Word128
(Riprel (word_sx (iword (&chacha20_ssse3_4x_data - (&pc + -- &141)))))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x39;
                           (* MOVDQU (%_% xmm15) (Memop Word128 (%% (rcx,0))) *)
  0xf3; 0x0f; 0x6f; 0x79; 0x10;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rcx,16))) *)
  0xf3; 0x41; 0x0f; 0x6f; 0x18;
                           (* MOVDQU (%_% xmm3) (Memop Word128 (%% (r8,0))) *)
  0x48; 0x8d; 0x8c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% rcx) (%% (rsp,256)) *)
  0x4c; 0x8d; 0x15]; ADDR ("chacha20_ssse3_4x_data",(124)); b[
                           (* LEA (% r10)
(Riprel (word_sx (iword (&chacha20_ssse3_4x_data - (&pc + -- &79))))) *)
  0x4c; 0x8d; 0x1d]; ADDR ("chacha20_ssse3_4x_data",(140)); b[
                           (* LEA (% r11)
(Riprel (word_sx (iword (&chacha20_ssse3_4x_data - (&pc + -- &88))))) *)
  0x66; 0x45; 0x0f; 0x70; 0xc3; 0x00;
                           (* PSHUFD (%_% xmm8) (%_% xmm11) (Imm8 (word 0)) *)
  0x66; 0x45; 0x0f; 0x70; 0xcb; 0x55;
                           (* PSHUFD (%_% xmm9) (%_% xmm11) (Imm8 (word 85)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x44; 0x24; 0x40;
                           (* MOVDQA (Memop Word128 (%% (rsp,64))) (%_% xmm8) *)
  0x66; 0x45; 0x0f; 0x70; 0xd3; 0xaa;
                           (* PSHUFD (%_% xmm10) (%_% xmm11) (Imm8 (word 170)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x4c; 0x24; 0x50;
                           (* MOVDQA (Memop Word128 (%% (rsp,80))) (%_% xmm9) *)
  0x66; 0x45; 0x0f; 0x70; 0xdb; 0xff;
                           (* PSHUFD (%_% xmm11) (%_% xmm11) (Imm8 (word 255)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x54; 0x24; 0x60;
                           (* MOVDQA (Memop Word128 (%% (rsp,96))) (%_% xmm10) *)
  0x66; 0x44; 0x0f; 0x7f; 0x5c; 0x24; 0x70;
                           (* MOVDQA (Memop Word128 (%% (rsp,112))) (%_% xmm11) *)
  0x66; 0x45; 0x0f; 0x70; 0xe7; 0x00;
                           (* PSHUFD (%_% xmm12) (%_% xmm15) (Imm8 (word 0)) *)
  0x66; 0x45; 0x0f; 0x70; 0xef; 0x55;
                           (* PSHUFD (%_% xmm13) (%_% xmm15) (Imm8 (word 85)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x61; 0x80;
                           (* MOVDQA (Memop Word128 (%% (rcx,18446744073709551488))) (%_% xmm12) *)
  0x66; 0x45; 0x0f; 0x70; 0xf7; 0xaa;
                           (* PSHUFD (%_% xmm14) (%_% xmm15) (Imm8 (word 170)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x69; 0x90;
                           (* MOVDQA (Memop Word128 (%% (rcx,18446744073709551504))) (%_% xmm13) *)
  0x66; 0x45; 0x0f; 0x70; 0xff; 0xff;
                           (* PSHUFD (%_% xmm15) (%_% xmm15) (Imm8 (word 255)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x71; 0xa0;
                           (* MOVDQA (Memop Word128 (%% (rcx,18446744073709551520))) (%_% xmm14) *)
  0x66; 0x44; 0x0f; 0x7f; 0x79; 0xb0;
                           (* MOVDQA (Memop Word128 (%% (rcx,18446744073709551536))) (%_% xmm15) *)
  0x66; 0x0f; 0x70; 0xe7; 0x00;
                           (* PSHUFD (%_% xmm4) (%_% xmm7) (Imm8 (word 0)) *)
  0x66; 0x0f; 0x70; 0xef; 0x55;
                           (* PSHUFD (%_% xmm5) (%_% xmm7) (Imm8 (word 85)) *)
  0x66; 0x0f; 0x7f; 0x61; 0xc0;
                           (* MOVDQA (Memop Word128 (%% (rcx,18446744073709551552))) (%_% xmm4) *)
  0x66; 0x0f; 0x70; 0xf7; 0xaa;
                           (* PSHUFD (%_% xmm6) (%_% xmm7) (Imm8 (word 170)) *)
  0x66; 0x0f; 0x7f; 0x69; 0xd0;
                           (* MOVDQA (Memop Word128 (%% (rcx,18446744073709551568))) (%_% xmm5) *)
  0x66; 0x0f; 0x70; 0xff; 0xff;
                           (* PSHUFD (%_% xmm7) (%_% xmm7) (Imm8 (word 255)) *)
  0x66; 0x0f; 0x7f; 0x71; 0xe0;
                           (* MOVDQA (Memop Word128 (%% (rcx,18446744073709551584))) (%_% xmm6) *)
  0x66; 0x0f; 0x7f; 0x79; 0xf0;
                           (* MOVDQA (Memop Word128 (%% (rcx,18446744073709551600))) (%_% xmm7) *)
  0x66; 0x0f; 0x70; 0xc3; 0x00;
                           (* PSHUFD (%_% xmm0) (%_% xmm3) (Imm8 (word 0)) *)
  0x66; 0x0f; 0x70; 0xcb; 0x55;
                           (* PSHUFD (%_% xmm1) (%_% xmm3) (Imm8 (word 85)) *)
  0x66; 0x0f; 0xfe; 0x05]; ADDR ("chacha20_ssse3_4x_data",(28)); b[
                           (* PADDD (%_% xmm0)
(Memop Word128
(Riprel (word_sx (iword (&chacha20_ssse3_4x_data - (&pc + &182)))))) *)
  0x66; 0x0f; 0x70; 0xd3; 0xaa;
                           (* PSHUFD (%_% xmm2) (%_% xmm3) (Imm8 (word 170)) *)
  0x66; 0x0f; 0x7f; 0x49; 0x10;
                           (* MOVDQA (Memop Word128 (%% (rcx,16))) (%_% xmm1) *)
  0x66; 0x0f; 0x70; 0xdb; 0xff;
                           (* PSHUFD (%_% xmm3) (%_% xmm3) (Imm8 (word 255)) *)
  0x66; 0x0f; 0x7f; 0x51; 0x20;
                           (* MOVDQA (Memop Word128 (%% (rcx,32))) (%_% xmm2) *)
  0x66; 0x0f; 0x7f; 0x59; 0x30;
                           (* MOVDQA (Memop Word128 (%% (rcx,48))) (%_% xmm3) *)
  0xeb; 0x72;              (* JMP (Imm8 (word 114)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%%% (rax,0,rax))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x44; 0x24; 0x40;
                           (* MOVDQA (%_% xmm8) (Memop Word128 (%% (rsp,64))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x4c; 0x24; 0x50;
                           (* MOVDQA (%_% xmm9) (Memop Word128 (%% (rsp,80))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x54; 0x24; 0x60;
                           (* MOVDQA (%_% xmm10) (Memop Word128 (%% (rsp,96))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x5c; 0x24; 0x70;
                           (* MOVDQA (%_% xmm11) (Memop Word128 (%% (rsp,112))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x61; 0x80;
                           (* MOVDQA (%_% xmm12) (Memop Word128 (%% (rcx,18446744073709551488))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x69; 0x90;
                           (* MOVDQA (%_% xmm13) (Memop Word128 (%% (rcx,18446744073709551504))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x71; 0xa0;
                           (* MOVDQA (%_% xmm14) (Memop Word128 (%% (rcx,18446744073709551520))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x79; 0xb0;
                           (* MOVDQA (%_% xmm15) (Memop Word128 (%% (rcx,18446744073709551536))) *)
  0x66; 0x0f; 0x6f; 0x61; 0xc0;
                           (* MOVDQA (%_% xmm4) (Memop Word128 (%% (rcx,18446744073709551552))) *)
  0x66; 0x0f; 0x6f; 0x69; 0xd0;
                           (* MOVDQA (%_% xmm5) (Memop Word128 (%% (rcx,18446744073709551568))) *)
  0x66; 0x0f; 0x6f; 0x71; 0xe0;
                           (* MOVDQA (%_% xmm6) (Memop Word128 (%% (rcx,18446744073709551584))) *)
  0x66; 0x0f; 0x6f; 0x79; 0xf0;
                           (* MOVDQA (%_% xmm7) (Memop Word128 (%% (rcx,18446744073709551600))) *)
  0x66; 0x0f; 0x6f; 0x01;  (* MOVDQA (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0x66; 0x0f; 0x6f; 0x49; 0x10;
                           (* MOVDQA (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x66; 0x0f; 0x6f; 0x51; 0x20;
                           (* MOVDQA (%_% xmm2) (Memop Word128 (%% (rcx,32))) *)
  0x66; 0x0f; 0x6f; 0x59; 0x30;
                           (* MOVDQA (%_% xmm3) (Memop Word128 (%% (rcx,48))) *)
  0x66; 0x0f; 0xfe; 0x05]; ADDR ("chacha20_ssse3_4x_data",(44)); b[
                           (* PADDD (%_% xmm0)
(Memop Word128
(Riprel (word_sx (iword (&chacha20_ssse3_4x_data - (&pc + &307)))))) *)
  0x66; 0x0f; 0x7f; 0x74; 0x24; 0x20;
                           (* MOVDQA (Memop Word128 (%% (rsp,32))) (%_% xmm6) *)
  0x66; 0x0f; 0x7f; 0x7c; 0x24; 0x30;
                           (* MOVDQA (Memop Word128 (%% (rsp,48))) (%_% xmm7) *)
  0x66; 0x41; 0x0f; 0x6f; 0x3a;
                           (* MOVDQA (%_% xmm7) (Memop Word128 (%% (r10,0))) *)
  0xb8; 0x0a; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 10)) *)
  0x66; 0x0f; 0x7f; 0x01;  (* MOVDQA (Memop Word128 (%% (rcx,0))) (%_% xmm0) *)
  0xeb; 0x01;              (* JMP (Imm8 (word 1)) *)
  0x90;                    (* NOP *)
  0x66; 0x45; 0x0f; 0xfe; 0xc4;
                           (* PADDD (%_% xmm8) (%_% xmm12) *)
  0x66; 0x45; 0x0f; 0xfe; 0xcd;
                           (* PADDD (%_% xmm9) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0xef; 0xc0;
                           (* PXOR (%_% xmm0) (%_% xmm8) *)
  0x66; 0x41; 0x0f; 0xef; 0xc9;
                           (* PXOR (%_% xmm1) (%_% xmm9) *)
  0x66; 0x0f; 0x38; 0x00; 0xc7;
                           (* PSHUFB (%_% xmm0) (%_% xmm7) *)
  0x66; 0x0f; 0x38; 0x00; 0xcf;
                           (* PSHUFB (%_% xmm1) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0xe0;  (* PADDD (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0xfe; 0xe9;  (* PADDD (%_% xmm5) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0xef; 0xe4;
                           (* PXOR (%_% xmm12) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0xef; 0xed;
                           (* PXOR (%_% xmm13) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf4;
                           (* MOVDQA (%_% xmm6) (%_% xmm12) *)
  0x66; 0x41; 0x0f; 0x72; 0xf4; 0x0c;
                           (* PSLLD (%_% xmm12) (Imm8 (word 12)) *)
  0x66; 0x0f; 0x72; 0xd6; 0x14;
                           (* PSRLD (%_% xmm6) (Imm8 (word 20)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xfd;
                           (* MOVDQA (%_% xmm7) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x72; 0xf5; 0x0c;
                           (* PSLLD (%_% xmm13) (Imm8 (word 12)) *)
  0x66; 0x44; 0x0f; 0xeb; 0xe6;
                           (* POR (%_% xmm12) (%_% xmm6) *)
  0x66; 0x0f; 0x72; 0xd7; 0x14;
                           (* PSRLD (%_% xmm7) (Imm8 (word 20)) *)
  0x66; 0x41; 0x0f; 0x6f; 0x33;
                           (* MOVDQA (%_% xmm6) (Memop Word128 (%% (r11,0))) *)
  0x66; 0x44; 0x0f; 0xeb; 0xef;
                           (* POR (%_% xmm13) (%_% xmm7) *)
  0x66; 0x45; 0x0f; 0xfe; 0xc4;
                           (* PADDD (%_% xmm8) (%_% xmm12) *)
  0x66; 0x45; 0x0f; 0xfe; 0xcd;
                           (* PADDD (%_% xmm9) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0xef; 0xc0;
                           (* PXOR (%_% xmm0) (%_% xmm8) *)
  0x66; 0x41; 0x0f; 0xef; 0xc9;
                           (* PXOR (%_% xmm1) (%_% xmm9) *)
  0x66; 0x0f; 0x38; 0x00; 0xc6;
                           (* PSHUFB (%_% xmm0) (%_% xmm6) *)
  0x66; 0x0f; 0x38; 0x00; 0xce;
                           (* PSHUFB (%_% xmm1) (%_% xmm6) *)
  0x66; 0x0f; 0xfe; 0xe0;  (* PADDD (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0xfe; 0xe9;  (* PADDD (%_% xmm5) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0xef; 0xe4;
                           (* PXOR (%_% xmm12) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0xef; 0xed;
                           (* PXOR (%_% xmm13) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xfc;
                           (* MOVDQA (%_% xmm7) (%_% xmm12) *)
  0x66; 0x41; 0x0f; 0x72; 0xf4; 0x07;
                           (* PSLLD (%_% xmm12) (Imm8 (word 7)) *)
  0x66; 0x0f; 0x72; 0xd7; 0x19;
                           (* PSRLD (%_% xmm7) (Imm8 (word 25)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf5;
                           (* MOVDQA (%_% xmm6) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x72; 0xf5; 0x07;
                           (* PSLLD (%_% xmm13) (Imm8 (word 7)) *)
  0x66; 0x44; 0x0f; 0xeb; 0xe7;
                           (* POR (%_% xmm12) (%_% xmm7) *)
  0x66; 0x0f; 0x72; 0xd6; 0x19;
                           (* PSRLD (%_% xmm6) (Imm8 (word 25)) *)
  0x66; 0x41; 0x0f; 0x6f; 0x3a;
                           (* MOVDQA (%_% xmm7) (Memop Word128 (%% (r10,0))) *)
  0x66; 0x44; 0x0f; 0xeb; 0xee;
                           (* POR (%_% xmm13) (%_% xmm6) *)
  0x66; 0x0f; 0x7f; 0x24; 0x24;
                           (* MOVDQA (Memop Word128 (%% (rsp,0))) (%_% xmm4) *)
  0x66; 0x0f; 0x7f; 0x6c; 0x24; 0x10;
                           (* MOVDQA (Memop Word128 (%% (rsp,16))) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0x64; 0x24; 0x20;
                           (* MOVDQA (%_% xmm4) (Memop Word128 (%% (rsp,32))) *)
  0x66; 0x0f; 0x6f; 0x6c; 0x24; 0x30;
                           (* MOVDQA (%_% xmm5) (Memop Word128 (%% (rsp,48))) *)
  0x66; 0x45; 0x0f; 0xfe; 0xd6;
                           (* PADDD (%_% xmm10) (%_% xmm14) *)
  0x66; 0x45; 0x0f; 0xfe; 0xdf;
                           (* PADDD (%_% xmm11) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0xef; 0xd2;
                           (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x66; 0x41; 0x0f; 0xef; 0xdb;
                           (* PXOR (%_% xmm3) (%_% xmm11) *)
  0x66; 0x0f; 0x38; 0x00; 0xd7;
                           (* PSHUFB (%_% xmm2) (%_% xmm7) *)
  0x66; 0x0f; 0x38; 0x00; 0xdf;
                           (* PSHUFB (%_% xmm3) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0xe2;  (* PADDD (%_% xmm4) (%_% xmm2) *)
  0x66; 0x0f; 0xfe; 0xeb;  (* PADDD (%_% xmm5) (%_% xmm3) *)
  0x66; 0x44; 0x0f; 0xef; 0xf4;
                           (* PXOR (%_% xmm14) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0xef; 0xfd;
                           (* PXOR (%_% xmm15) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf6;
                           (* MOVDQA (%_% xmm6) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0x72; 0xf6; 0x0c;
                           (* PSLLD (%_% xmm14) (Imm8 (word 12)) *)
  0x66; 0x0f; 0x72; 0xd6; 0x14;
                           (* PSRLD (%_% xmm6) (Imm8 (word 20)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xff;
                           (* MOVDQA (%_% xmm7) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0x72; 0xf7; 0x0c;
                           (* PSLLD (%_% xmm15) (Imm8 (word 12)) *)
  0x66; 0x44; 0x0f; 0xeb; 0xf6;
                           (* POR (%_% xmm14) (%_% xmm6) *)
  0x66; 0x0f; 0x72; 0xd7; 0x14;
                           (* PSRLD (%_% xmm7) (Imm8 (word 20)) *)
  0x66; 0x41; 0x0f; 0x6f; 0x33;
                           (* MOVDQA (%_% xmm6) (Memop Word128 (%% (r11,0))) *)
  0x66; 0x44; 0x0f; 0xeb; 0xff;
                           (* POR (%_% xmm15) (%_% xmm7) *)
  0x66; 0x45; 0x0f; 0xfe; 0xd6;
                           (* PADDD (%_% xmm10) (%_% xmm14) *)
  0x66; 0x45; 0x0f; 0xfe; 0xdf;
                           (* PADDD (%_% xmm11) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0xef; 0xd2;
                           (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x66; 0x41; 0x0f; 0xef; 0xdb;
                           (* PXOR (%_% xmm3) (%_% xmm11) *)
  0x66; 0x0f; 0x38; 0x00; 0xd6;
                           (* PSHUFB (%_% xmm2) (%_% xmm6) *)
  0x66; 0x0f; 0x38; 0x00; 0xde;
                           (* PSHUFB (%_% xmm3) (%_% xmm6) *)
  0x66; 0x0f; 0xfe; 0xe2;  (* PADDD (%_% xmm4) (%_% xmm2) *)
  0x66; 0x0f; 0xfe; 0xeb;  (* PADDD (%_% xmm5) (%_% xmm3) *)
  0x66; 0x44; 0x0f; 0xef; 0xf4;
                           (* PXOR (%_% xmm14) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0xef; 0xfd;
                           (* PXOR (%_% xmm15) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xfe;
                           (* MOVDQA (%_% xmm7) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0x72; 0xf6; 0x07;
                           (* PSLLD (%_% xmm14) (Imm8 (word 7)) *)
  0x66; 0x0f; 0x72; 0xd7; 0x19;
                           (* PSRLD (%_% xmm7) (Imm8 (word 25)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf7;
                           (* MOVDQA (%_% xmm6) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0x72; 0xf7; 0x07;
                           (* PSLLD (%_% xmm15) (Imm8 (word 7)) *)
  0x66; 0x44; 0x0f; 0xeb; 0xf7;
                           (* POR (%_% xmm14) (%_% xmm7) *)
  0x66; 0x0f; 0x72; 0xd6; 0x19;
                           (* PSRLD (%_% xmm6) (Imm8 (word 25)) *)
  0x66; 0x41; 0x0f; 0x6f; 0x3a;
                           (* MOVDQA (%_% xmm7) (Memop Word128 (%% (r10,0))) *)
  0x66; 0x44; 0x0f; 0xeb; 0xfe;
                           (* POR (%_% xmm15) (%_% xmm6) *)
  0x66; 0x45; 0x0f; 0xfe; 0xc5;
                           (* PADDD (%_% xmm8) (%_% xmm13) *)
  0x66; 0x45; 0x0f; 0xfe; 0xce;
                           (* PADDD (%_% xmm9) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0xef; 0xd8;
                           (* PXOR (%_% xmm3) (%_% xmm8) *)
  0x66; 0x41; 0x0f; 0xef; 0xc1;
                           (* PXOR (%_% xmm0) (%_% xmm9) *)
  0x66; 0x0f; 0x38; 0x00; 0xdf;
                           (* PSHUFB (%_% xmm3) (%_% xmm7) *)
  0x66; 0x0f; 0x38; 0x00; 0xc7;
                           (* PSHUFB (%_% xmm0) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0xe3;  (* PADDD (%_% xmm4) (%_% xmm3) *)
  0x66; 0x0f; 0xfe; 0xe8;  (* PADDD (%_% xmm5) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0xef; 0xec;
                           (* PXOR (%_% xmm13) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0xef; 0xf5;
                           (* PXOR (%_% xmm14) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf5;
                           (* MOVDQA (%_% xmm6) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x72; 0xf5; 0x0c;
                           (* PSLLD (%_% xmm13) (Imm8 (word 12)) *)
  0x66; 0x0f; 0x72; 0xd6; 0x14;
                           (* PSRLD (%_% xmm6) (Imm8 (word 20)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xfe;
                           (* MOVDQA (%_% xmm7) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0x72; 0xf6; 0x0c;
                           (* PSLLD (%_% xmm14) (Imm8 (word 12)) *)
  0x66; 0x44; 0x0f; 0xeb; 0xee;
                           (* POR (%_% xmm13) (%_% xmm6) *)
  0x66; 0x0f; 0x72; 0xd7; 0x14;
                           (* PSRLD (%_% xmm7) (Imm8 (word 20)) *)
  0x66; 0x41; 0x0f; 0x6f; 0x33;
                           (* MOVDQA (%_% xmm6) (Memop Word128 (%% (r11,0))) *)
  0x66; 0x44; 0x0f; 0xeb; 0xf7;
                           (* POR (%_% xmm14) (%_% xmm7) *)
  0x66; 0x45; 0x0f; 0xfe; 0xc5;
                           (* PADDD (%_% xmm8) (%_% xmm13) *)
  0x66; 0x45; 0x0f; 0xfe; 0xce;
                           (* PADDD (%_% xmm9) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0xef; 0xd8;
                           (* PXOR (%_% xmm3) (%_% xmm8) *)
  0x66; 0x41; 0x0f; 0xef; 0xc1;
                           (* PXOR (%_% xmm0) (%_% xmm9) *)
  0x66; 0x0f; 0x38; 0x00; 0xde;
                           (* PSHUFB (%_% xmm3) (%_% xmm6) *)
  0x66; 0x0f; 0x38; 0x00; 0xc6;
                           (* PSHUFB (%_% xmm0) (%_% xmm6) *)
  0x66; 0x0f; 0xfe; 0xe3;  (* PADDD (%_% xmm4) (%_% xmm3) *)
  0x66; 0x0f; 0xfe; 0xe8;  (* PADDD (%_% xmm5) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0xef; 0xec;
                           (* PXOR (%_% xmm13) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0xef; 0xf5;
                           (* PXOR (%_% xmm14) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xfd;
                           (* MOVDQA (%_% xmm7) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x72; 0xf5; 0x07;
                           (* PSLLD (%_% xmm13) (Imm8 (word 7)) *)
  0x66; 0x0f; 0x72; 0xd7; 0x19;
                           (* PSRLD (%_% xmm7) (Imm8 (word 25)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf6;
                           (* MOVDQA (%_% xmm6) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0x72; 0xf6; 0x07;
                           (* PSLLD (%_% xmm14) (Imm8 (word 7)) *)
  0x66; 0x44; 0x0f; 0xeb; 0xef;
                           (* POR (%_% xmm13) (%_% xmm7) *)
  0x66; 0x0f; 0x72; 0xd6; 0x19;
                           (* PSRLD (%_% xmm6) (Imm8 (word 25)) *)
  0x66; 0x41; 0x0f; 0x6f; 0x3a;
                           (* MOVDQA (%_% xmm7) (Memop Word128 (%% (r10,0))) *)
  0x66; 0x44; 0x0f; 0xeb; 0xf6;
                           (* POR (%_% xmm14) (%_% xmm6) *)
  0x66; 0x0f; 0x7f; 0x64; 0x24; 0x20;
                           (* MOVDQA (Memop Word128 (%% (rsp,32))) (%_% xmm4) *)
  0x66; 0x0f; 0x7f; 0x6c; 0x24; 0x30;
                           (* MOVDQA (Memop Word128 (%% (rsp,48))) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0x24; 0x24;
                           (* MOVDQA (%_% xmm4) (Memop Word128 (%% (rsp,0))) *)
  0x66; 0x0f; 0x6f; 0x6c; 0x24; 0x10;
                           (* MOVDQA (%_% xmm5) (Memop Word128 (%% (rsp,16))) *)
  0x66; 0x45; 0x0f; 0xfe; 0xd7;
                           (* PADDD (%_% xmm10) (%_% xmm15) *)
  0x66; 0x45; 0x0f; 0xfe; 0xdc;
                           (* PADDD (%_% xmm11) (%_% xmm12) *)
  0x66; 0x41; 0x0f; 0xef; 0xca;
                           (* PXOR (%_% xmm1) (%_% xmm10) *)
  0x66; 0x41; 0x0f; 0xef; 0xd3;
                           (* PXOR (%_% xmm2) (%_% xmm11) *)
  0x66; 0x0f; 0x38; 0x00; 0xcf;
                           (* PSHUFB (%_% xmm1) (%_% xmm7) *)
  0x66; 0x0f; 0x38; 0x00; 0xd7;
                           (* PSHUFB (%_% xmm2) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0xe1;  (* PADDD (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0xfe; 0xea;  (* PADDD (%_% xmm5) (%_% xmm2) *)
  0x66; 0x44; 0x0f; 0xef; 0xfc;
                           (* PXOR (%_% xmm15) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0xef; 0xe5;
                           (* PXOR (%_% xmm12) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf7;
                           (* MOVDQA (%_% xmm6) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0x72; 0xf7; 0x0c;
                           (* PSLLD (%_% xmm15) (Imm8 (word 12)) *)
  0x66; 0x0f; 0x72; 0xd6; 0x14;
                           (* PSRLD (%_% xmm6) (Imm8 (word 20)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xfc;
                           (* MOVDQA (%_% xmm7) (%_% xmm12) *)
  0x66; 0x41; 0x0f; 0x72; 0xf4; 0x0c;
                           (* PSLLD (%_% xmm12) (Imm8 (word 12)) *)
  0x66; 0x44; 0x0f; 0xeb; 0xfe;
                           (* POR (%_% xmm15) (%_% xmm6) *)
  0x66; 0x0f; 0x72; 0xd7; 0x14;
                           (* PSRLD (%_% xmm7) (Imm8 (word 20)) *)
  0x66; 0x41; 0x0f; 0x6f; 0x33;
                           (* MOVDQA (%_% xmm6) (Memop Word128 (%% (r11,0))) *)
  0x66; 0x44; 0x0f; 0xeb; 0xe7;
                           (* POR (%_% xmm12) (%_% xmm7) *)
  0x66; 0x45; 0x0f; 0xfe; 0xd7;
                           (* PADDD (%_% xmm10) (%_% xmm15) *)
  0x66; 0x45; 0x0f; 0xfe; 0xdc;
                           (* PADDD (%_% xmm11) (%_% xmm12) *)
  0x66; 0x41; 0x0f; 0xef; 0xca;
                           (* PXOR (%_% xmm1) (%_% xmm10) *)
  0x66; 0x41; 0x0f; 0xef; 0xd3;
                           (* PXOR (%_% xmm2) (%_% xmm11) *)
  0x66; 0x0f; 0x38; 0x00; 0xce;
                           (* PSHUFB (%_% xmm1) (%_% xmm6) *)
  0x66; 0x0f; 0x38; 0x00; 0xd6;
                           (* PSHUFB (%_% xmm2) (%_% xmm6) *)
  0x66; 0x0f; 0xfe; 0xe1;  (* PADDD (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0xfe; 0xea;  (* PADDD (%_% xmm5) (%_% xmm2) *)
  0x66; 0x44; 0x0f; 0xef; 0xfc;
                           (* PXOR (%_% xmm15) (%_% xmm4) *)
  0x66; 0x44; 0x0f; 0xef; 0xe5;
                           (* PXOR (%_% xmm12) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xff;
                           (* MOVDQA (%_% xmm7) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0x72; 0xf7; 0x07;
                           (* PSLLD (%_% xmm15) (Imm8 (word 7)) *)
  0x66; 0x0f; 0x72; 0xd7; 0x19;
                           (* PSRLD (%_% xmm7) (Imm8 (word 25)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf4;
                           (* MOVDQA (%_% xmm6) (%_% xmm12) *)
  0x66; 0x41; 0x0f; 0x72; 0xf4; 0x07;
                           (* PSLLD (%_% xmm12) (Imm8 (word 7)) *)
  0x66; 0x44; 0x0f; 0xeb; 0xff;
                           (* POR (%_% xmm15) (%_% xmm7) *)
  0x66; 0x0f; 0x72; 0xd6; 0x19;
                           (* PSRLD (%_% xmm6) (Imm8 (word 25)) *)
  0x66; 0x41; 0x0f; 0x6f; 0x3a;
                           (* MOVDQA (%_% xmm7) (Memop Word128 (%% (r10,0))) *)
  0x66; 0x44; 0x0f; 0xeb; 0xe6;
                           (* POR (%_% xmm12) (%_% xmm6) *)
  0xff; 0xc8;              (* DEC (% eax) *)
  0x0f; 0x85; 0xd2; 0xfc; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966482)) *)
  0x66; 0x44; 0x0f; 0xfe; 0x44; 0x24; 0x40;
                           (* PADDD (%_% xmm8) (Memop Word128 (%% (rsp,64))) *)
  0x66; 0x44; 0x0f; 0xfe; 0x4c; 0x24; 0x50;
                           (* PADDD (%_% xmm9) (Memop Word128 (%% (rsp,80))) *)
  0x66; 0x44; 0x0f; 0xfe; 0x54; 0x24; 0x60;
                           (* PADDD (%_% xmm10) (Memop Word128 (%% (rsp,96))) *)
  0x66; 0x44; 0x0f; 0xfe; 0x5c; 0x24; 0x70;
                           (* PADDD (%_% xmm11) (Memop Word128 (%% (rsp,112))) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf0;
                           (* MOVDQA (%_% xmm6) (%_% xmm8) *)
  0x66; 0x45; 0x0f; 0x62; 0xc1;
                           (* PUNPCKLDQ (%_% xmm8) (%_% xmm9) *)
  0x66; 0x41; 0x0f; 0x6f; 0xfa;
                           (* MOVDQA (%_% xmm7) (%_% xmm10) *)
  0x66; 0x45; 0x0f; 0x62; 0xd3;
                           (* PUNPCKLDQ (%_% xmm10) (%_% xmm11) *)
  0x66; 0x41; 0x0f; 0x6a; 0xf1;
                           (* PUNPCKHDQ (%_% xmm6) (%_% xmm9) *)
  0x66; 0x41; 0x0f; 0x6a; 0xfb;
                           (* PUNPCKHDQ (%_% xmm7) (%_% xmm11) *)
  0x66; 0x45; 0x0f; 0x6f; 0xc8;
                           (* MOVDQA (%_% xmm9) (%_% xmm8) *)
  0x66; 0x45; 0x0f; 0x6c; 0xc2;
                           (* PUNPCKLQDQ (%_% xmm8) (%_% xmm10) *)
  0x66; 0x44; 0x0f; 0x6f; 0xde;
                           (* MOVDQA (%_% xmm11) (%_% xmm6) *)
  0x66; 0x0f; 0x6c; 0xf7;  (* PUNPCKLQDQ (%_% xmm6) (%_% xmm7) *)
  0x66; 0x45; 0x0f; 0x6d; 0xca;
                           (* PUNPCKHQDQ (%_% xmm9) (%_% xmm10) *)
  0x66; 0x44; 0x0f; 0x6d; 0xdf;
                           (* PUNPCKHQDQ (%_% xmm11) (%_% xmm7) *)
  0x66; 0x44; 0x0f; 0xfe; 0x61; 0x80;
                           (* PADDD (%_% xmm12) (Memop Word128 (%% (rcx,18446744073709551488))) *)
  0x66; 0x44; 0x0f; 0xfe; 0x69; 0x90;
                           (* PADDD (%_% xmm13) (Memop Word128 (%% (rcx,18446744073709551504))) *)
  0x66; 0x44; 0x0f; 0xfe; 0x71; 0xa0;
                           (* PADDD (%_% xmm14) (Memop Word128 (%% (rcx,18446744073709551520))) *)
  0x66; 0x44; 0x0f; 0xfe; 0x79; 0xb0;
                           (* PADDD (%_% xmm15) (Memop Word128 (%% (rcx,18446744073709551536))) *)
  0x66; 0x44; 0x0f; 0x7f; 0x04; 0x24;
                           (* MOVDQA (Memop Word128 (%% (rsp,0))) (%_% xmm8) *)
  0x66; 0x44; 0x0f; 0x7f; 0x4c; 0x24; 0x10;
                           (* MOVDQA (Memop Word128 (%% (rsp,16))) (%_% xmm9) *)
  0x66; 0x44; 0x0f; 0x6f; 0x44; 0x24; 0x20;
                           (* MOVDQA (%_% xmm8) (Memop Word128 (%% (rsp,32))) *)
  0x66; 0x44; 0x0f; 0x6f; 0x4c; 0x24; 0x30;
                           (* MOVDQA (%_% xmm9) (Memop Word128 (%% (rsp,48))) *)
  0x66; 0x45; 0x0f; 0x6f; 0xd4;
                           (* MOVDQA (%_% xmm10) (%_% xmm12) *)
  0x66; 0x45; 0x0f; 0x62; 0xe5;
                           (* PUNPCKLDQ (%_% xmm12) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x6f; 0xfe;
                           (* MOVDQA (%_% xmm7) (%_% xmm14) *)
  0x66; 0x45; 0x0f; 0x62; 0xf7;
                           (* PUNPCKLDQ (%_% xmm14) (%_% xmm15) *)
  0x66; 0x45; 0x0f; 0x6a; 0xd5;
                           (* PUNPCKHDQ (%_% xmm10) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x6a; 0xff;
                           (* PUNPCKHDQ (%_% xmm7) (%_% xmm15) *)
  0x66; 0x45; 0x0f; 0x6f; 0xec;
                           (* MOVDQA (%_% xmm13) (%_% xmm12) *)
  0x66; 0x45; 0x0f; 0x6c; 0xe6;
                           (* PUNPCKLQDQ (%_% xmm12) (%_% xmm14) *)
  0x66; 0x45; 0x0f; 0x6f; 0xfa;
                           (* MOVDQA (%_% xmm15) (%_% xmm10) *)
  0x66; 0x44; 0x0f; 0x6c; 0xd7;
                           (* PUNPCKLQDQ (%_% xmm10) (%_% xmm7) *)
  0x66; 0x45; 0x0f; 0x6d; 0xee;
                           (* PUNPCKHQDQ (%_% xmm13) (%_% xmm14) *)
  0x66; 0x44; 0x0f; 0x6d; 0xff;
                           (* PUNPCKHQDQ (%_% xmm15) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0x61; 0xc0;
                           (* PADDD (%_% xmm4) (Memop Word128 (%% (rcx,18446744073709551552))) *)
  0x66; 0x0f; 0xfe; 0x69; 0xd0;
                           (* PADDD (%_% xmm5) (Memop Word128 (%% (rcx,18446744073709551568))) *)
  0x66; 0x44; 0x0f; 0xfe; 0x41; 0xe0;
                           (* PADDD (%_% xmm8) (Memop Word128 (%% (rcx,18446744073709551584))) *)
  0x66; 0x44; 0x0f; 0xfe; 0x49; 0xf0;
                           (* PADDD (%_% xmm9) (Memop Word128 (%% (rcx,18446744073709551600))) *)
  0x66; 0x0f; 0x7f; 0x74; 0x24; 0x20;
                           (* MOVDQA (Memop Word128 (%% (rsp,32))) (%_% xmm6) *)
  0x66; 0x44; 0x0f; 0x7f; 0x5c; 0x24; 0x30;
                           (* MOVDQA (Memop Word128 (%% (rsp,48))) (%_% xmm11) *)
  0x66; 0x44; 0x0f; 0x6f; 0xf4;
                           (* MOVDQA (%_% xmm14) (%_% xmm4) *)
  0x66; 0x0f; 0x62; 0xe5;  (* PUNPCKLDQ (%_% xmm4) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf8;
                           (* MOVDQA (%_% xmm7) (%_% xmm8) *)
  0x66; 0x45; 0x0f; 0x62; 0xc1;
                           (* PUNPCKLDQ (%_% xmm8) (%_% xmm9) *)
  0x66; 0x44; 0x0f; 0x6a; 0xf5;
                           (* PUNPCKHDQ (%_% xmm14) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6a; 0xf9;
                           (* PUNPCKHDQ (%_% xmm7) (%_% xmm9) *)
  0x66; 0x0f; 0x6f; 0xec;  (* MOVDQA (%_% xmm5) (%_% xmm4) *)
  0x66; 0x41; 0x0f; 0x6c; 0xe0;
                           (* PUNPCKLQDQ (%_% xmm4) (%_% xmm8) *)
  0x66; 0x45; 0x0f; 0x6f; 0xce;
                           (* MOVDQA (%_% xmm9) (%_% xmm14) *)
  0x66; 0x44; 0x0f; 0x6c; 0xf7;
                           (* PUNPCKLQDQ (%_% xmm14) (%_% xmm7) *)
  0x66; 0x41; 0x0f; 0x6d; 0xe8;
                           (* PUNPCKHQDQ (%_% xmm5) (%_% xmm8) *)
  0x66; 0x44; 0x0f; 0x6d; 0xcf;
                           (* PUNPCKHQDQ (%_% xmm9) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0x01;  (* PADDD (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0x66; 0x0f; 0xfe; 0x49; 0x10;
                           (* PADDD (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x66; 0x0f; 0xfe; 0x51; 0x20;
                           (* PADDD (%_% xmm2) (Memop Word128 (%% (rcx,32))) *)
  0x66; 0x0f; 0xfe; 0x59; 0x30;
                           (* PADDD (%_% xmm3) (Memop Word128 (%% (rcx,48))) *)
  0x66; 0x44; 0x0f; 0x6f; 0xc0;
                           (* MOVDQA (%_% xmm8) (%_% xmm0) *)
  0x66; 0x0f; 0x62; 0xc1;  (* PUNPCKLDQ (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xfa;  (* MOVDQA (%_% xmm7) (%_% xmm2) *)
  0x66; 0x0f; 0x62; 0xd3;  (* PUNPCKLDQ (%_% xmm2) (%_% xmm3) *)
  0x66; 0x44; 0x0f; 0x6a; 0xc1;
                           (* PUNPCKHDQ (%_% xmm8) (%_% xmm1) *)
  0x66; 0x0f; 0x6a; 0xfb;  (* PUNPCKHDQ (%_% xmm7) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xc8;  (* MOVDQA (%_% xmm1) (%_% xmm0) *)
  0x66; 0x0f; 0x6c; 0xc2;  (* PUNPCKLQDQ (%_% xmm0) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xd8;
                           (* MOVDQA (%_% xmm3) (%_% xmm8) *)
  0x66; 0x44; 0x0f; 0x6c; 0xc7;
                           (* PUNPCKLQDQ (%_% xmm8) (%_% xmm7) *)
  0x66; 0x0f; 0x6d; 0xca;  (* PUNPCKHQDQ (%_% xmm1) (%_% xmm2) *)
  0x66; 0x0f; 0x6d; 0xdf;  (* PUNPCKHQDQ (%_% xmm3) (%_% xmm7) *)
  0x48; 0x81; 0xfa; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% rdx) (Imm32 (word 256)) *)
  0x0f; 0x82; 0x20; 0x01; 0x00; 0x00;
                           (* JB (Imm32 (word 288)) *)
  0xf3; 0x0f; 0x6f; 0x36;  (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,0))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x10;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,16))) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x20;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,32))) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x30;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,48))) *)
  0x66; 0x0f; 0xef; 0x34; 0x24;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,0))) *)
  0x66; 0x45; 0x0f; 0xef; 0xdc;
                           (* PXOR (%_% xmm11) (%_% xmm12) *)
  0x66; 0x0f; 0xef; 0xd4;  (* PXOR (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xf8;  (* PXOR (%_% xmm7) (%_% xmm0) *)
  0xf3; 0x0f; 0x7f; 0x37;  (* MOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm6) *)
  0xf3; 0x0f; 0x6f; 0x76; 0x40;
                           (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,64))) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rdi,16))) (%_% xmm11) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x50;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,80))) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rdi,32))) (%_% xmm2) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x60;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,96))) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rdi,48))) (%_% xmm7) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x70;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,112))) *)
  0x48; 0x8d; 0xb6; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,128)) *)
  0x66; 0x0f; 0xef; 0x74; 0x24; 0x10;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,16))) *)
  0x66; 0x45; 0x0f; 0xef; 0xdd;
                           (* PXOR (%_% xmm11) (%_% xmm13) *)
  0x66; 0x0f; 0xef; 0xd5;  (* PXOR (%_% xmm2) (%_% xmm5) *)
  0x66; 0x0f; 0xef; 0xf9;  (* PXOR (%_% xmm7) (%_% xmm1) *)
  0xf3; 0x0f; 0x7f; 0x77; 0x40;
                           (* MOVDQU (Memop Word128 (%% (rdi,64))) (%_% xmm6) *)
  0xf3; 0x0f; 0x6f; 0x36;  (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,0))) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x50;
                           (* MOVDQU (Memop Word128 (%% (rdi,80))) (%_% xmm11) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x10;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,16))) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x60;
                           (* MOVDQU (Memop Word128 (%% (rdi,96))) (%_% xmm2) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x20;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,32))) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x70;
                           (* MOVDQU (Memop Word128 (%% (rdi,112))) (%_% xmm7) *)
  0x48; 0x8d; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rdi,128)) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x30;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,48))) *)
  0x66; 0x0f; 0xef; 0x74; 0x24; 0x20;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,32))) *)
  0x66; 0x45; 0x0f; 0xef; 0xda;
                           (* PXOR (%_% xmm11) (%_% xmm10) *)
  0x66; 0x41; 0x0f; 0xef; 0xd6;
                           (* PXOR (%_% xmm2) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0xef; 0xf8;
                           (* PXOR (%_% xmm7) (%_% xmm8) *)
  0xf3; 0x0f; 0x7f; 0x37;  (* MOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm6) *)
  0xf3; 0x0f; 0x6f; 0x76; 0x40;
                           (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,64))) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rdi,16))) (%_% xmm11) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x50;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,80))) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rdi,32))) (%_% xmm2) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x60;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,96))) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rdi,48))) (%_% xmm7) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x70;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,112))) *)
  0x48; 0x8d; 0xb6; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,128)) *)
  0x66; 0x0f; 0xef; 0x74; 0x24; 0x30;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,48))) *)
  0x66; 0x45; 0x0f; 0xef; 0xdf;
                           (* PXOR (%_% xmm11) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0xef; 0xd1;
                           (* PXOR (%_% xmm2) (%_% xmm9) *)
  0x66; 0x0f; 0xef; 0xfb;  (* PXOR (%_% xmm7) (%_% xmm3) *)
  0xf3; 0x0f; 0x7f; 0x77; 0x40;
                           (* MOVDQU (Memop Word128 (%% (rdi,64))) (%_% xmm6) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x50;
                           (* MOVDQU (Memop Word128 (%% (rdi,80))) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x60;
                           (* MOVDQU (Memop Word128 (%% (rdi,96))) (%_% xmm2) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x70;
                           (* MOVDQU (Memop Word128 (%% (rdi,112))) (%_% xmm7) *)
  0x48; 0x8d; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rdi,128)) *)
  0x48; 0x81; 0xea; 0x00; 0x01; 0x00; 0x00;
                           (* SUB (% rdx) (Imm32 (word 256)) *)
  0x0f; 0x85; 0xc0; 0xf9; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294965696)) *)
  0xe9; 0x8a; 0x02; 0x00; 0x00;
                           (* JMP (Imm32 (word 650)) *)
  0x48; 0x81; 0xfa; 0xc0; 0x00; 0x00; 0x00;
                           (* CMP (% rdx) (Imm32 (word 192)) *)
  0x0f; 0x83; 0x6e; 0x01; 0x00; 0x00;
                           (* JAE (Imm32 (word 366)) *)
  0x48; 0x81; 0xfa; 0x80; 0x00; 0x00; 0x00;
                           (* CMP (% rdx) (Imm32 (word 128)) *)
  0x0f; 0x83; 0xa1; 0x00; 0x00; 0x00;
                           (* JAE (Imm32 (word 161)) *)
  0x48; 0x83; 0xfa; 0x40;  (* CMP (% rdx) (Imm8 (word 64)) *)
  0x73; 0x1b;              (* JAE (Imm8 (word 27)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x66; 0x44; 0x0f; 0x7f; 0x64; 0x24; 0x10;
                           (* MOVDQA (Memop Word128 (%% (rsp,16))) (%_% xmm12) *)
  0x66; 0x0f; 0x7f; 0x64; 0x24; 0x20;
                           (* MOVDQA (Memop Word128 (%% (rsp,32))) (%_% xmm4) *)
  0x66; 0x0f; 0x7f; 0x44; 0x24; 0x30;
                           (* MOVDQA (Memop Word128 (%% (rsp,48))) (%_% xmm0) *)
  0xe9; 0x35; 0x02; 0x00; 0x00;
                           (* JMP (Imm32 (word 565)) *)
  0xf3; 0x0f; 0x6f; 0x36;  (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,0))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x10;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,16))) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x20;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,32))) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x30;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,48))) *)
  0x66; 0x0f; 0xef; 0x34; 0x24;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,0))) *)
  0x66; 0x45; 0x0f; 0xef; 0xdc;
                           (* PXOR (%_% xmm11) (%_% xmm12) *)
  0x66; 0x0f; 0xef; 0xd4;  (* PXOR (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xf8;  (* PXOR (%_% xmm7) (%_% xmm0) *)
  0xf3; 0x0f; 0x7f; 0x37;  (* MOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm6) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rdi,16))) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rdi,32))) (%_% xmm2) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rdi,48))) (%_% xmm7) *)
  0x0f; 0x84; 0x0f; 0x02; 0x00; 0x00;
                           (* JE (Imm32 (word 527)) *)
  0x66; 0x0f; 0x6f; 0x74; 0x24; 0x10;
                           (* MOVDQA (%_% xmm6) (Memop Word128 (%% (rsp,16))) *)
  0x48; 0x8d; 0x76; 0x40;  (* LEA (% rsi) (%% (rsi,64)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x66; 0x0f; 0x7f; 0x34; 0x24;
                           (* MOVDQA (Memop Word128 (%% (rsp,0))) (%_% xmm6) *)
  0x66; 0x44; 0x0f; 0x7f; 0x6c; 0x24; 0x10;
                           (* MOVDQA (Memop Word128 (%% (rsp,16))) (%_% xmm13) *)
  0x48; 0x8d; 0x7f; 0x40;  (* LEA (% rdi) (%% (rdi,64)) *)
  0x66; 0x0f; 0x7f; 0x6c; 0x24; 0x20;
                           (* MOVDQA (Memop Word128 (%% (rsp,32))) (%_% xmm5) *)
  0x48; 0x83; 0xea; 0x40;  (* SUB (% rdx) (Imm8 (word 64)) *)
  0x66; 0x0f; 0x7f; 0x4c; 0x24; 0x30;
                           (* MOVDQA (Memop Word128 (%% (rsp,48))) (%_% xmm1) *)
  0xe9; 0xc3; 0x01; 0x00; 0x00;
                           (* JMP (Imm32 (word 451)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x1f; 0x40; 0x00;  (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0xf3; 0x0f; 0x6f; 0x36;  (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,0))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x10;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,16))) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x20;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,32))) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x30;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,48))) *)
  0x66; 0x0f; 0xef; 0x34; 0x24;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,0))) *)
  0x66; 0x45; 0x0f; 0xef; 0xdc;
                           (* PXOR (%_% xmm11) (%_% xmm12) *)
  0x66; 0x0f; 0xef; 0xd4;  (* PXOR (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xf8;  (* PXOR (%_% xmm7) (%_% xmm0) *)
  0xf3; 0x0f; 0x7f; 0x37;  (* MOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm6) *)
  0xf3; 0x0f; 0x6f; 0x76; 0x40;
                           (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,64))) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rdi,16))) (%_% xmm11) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x50;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,80))) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rdi,32))) (%_% xmm2) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x60;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,96))) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rdi,48))) (%_% xmm7) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x70;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,112))) *)
  0x66; 0x0f; 0xef; 0x74; 0x24; 0x10;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,16))) *)
  0x66; 0x45; 0x0f; 0xef; 0xdd;
                           (* PXOR (%_% xmm11) (%_% xmm13) *)
  0x66; 0x0f; 0xef; 0xd5;  (* PXOR (%_% xmm2) (%_% xmm5) *)
  0x66; 0x0f; 0xef; 0xf9;  (* PXOR (%_% xmm7) (%_% xmm1) *)
  0xf3; 0x0f; 0x7f; 0x77; 0x40;
                           (* MOVDQU (Memop Word128 (%% (rdi,64))) (%_% xmm6) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x50;
                           (* MOVDQU (Memop Word128 (%% (rdi,80))) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x60;
                           (* MOVDQU (Memop Word128 (%% (rdi,96))) (%_% xmm2) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x70;
                           (* MOVDQU (Memop Word128 (%% (rdi,112))) (%_% xmm7) *)
  0x0f; 0x84; 0x52; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 338)) *)
  0x66; 0x0f; 0x6f; 0x74; 0x24; 0x20;
                           (* MOVDQA (%_% xmm6) (Memop Word128 (%% (rsp,32))) *)
  0x48; 0x8d; 0xb6; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,128)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x66; 0x0f; 0x7f; 0x34; 0x24;
                           (* MOVDQA (Memop Word128 (%% (rsp,0))) (%_% xmm6) *)
  0x66; 0x44; 0x0f; 0x7f; 0x54; 0x24; 0x10;
                           (* MOVDQA (Memop Word128 (%% (rsp,16))) (%_% xmm10) *)
  0x48; 0x8d; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rdi,128)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x74; 0x24; 0x20;
                           (* MOVDQA (Memop Word128 (%% (rsp,32))) (%_% xmm14) *)
  0x48; 0x81; 0xea; 0x80; 0x00; 0x00; 0x00;
                           (* SUB (% rdx) (Imm32 (word 128)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x44; 0x24; 0x30;
                           (* MOVDQA (Memop Word128 (%% (rsp,48))) (%_% xmm8) *)
  0xe9; 0xfb; 0x00; 0x00; 0x00;
                           (* JMP (Imm32 (word 251)) *)
  0x66; 0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0xf3; 0x0f; 0x6f; 0x36;  (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,0))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x10;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,16))) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x20;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,32))) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x30;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,48))) *)
  0x66; 0x0f; 0xef; 0x34; 0x24;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,0))) *)
  0x66; 0x45; 0x0f; 0xef; 0xdc;
                           (* PXOR (%_% xmm11) (%_% xmm12) *)
  0x66; 0x0f; 0xef; 0xd4;  (* PXOR (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xf8;  (* PXOR (%_% xmm7) (%_% xmm0) *)
  0xf3; 0x0f; 0x7f; 0x37;  (* MOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm6) *)
  0xf3; 0x0f; 0x6f; 0x76; 0x40;
                           (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,64))) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rdi,16))) (%_% xmm11) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x50;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,80))) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rdi,32))) (%_% xmm2) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x60;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,96))) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rdi,48))) (%_% xmm7) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x70;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,112))) *)
  0x48; 0x8d; 0xb6; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,128)) *)
  0x66; 0x0f; 0xef; 0x74; 0x24; 0x10;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,16))) *)
  0x66; 0x45; 0x0f; 0xef; 0xdd;
                           (* PXOR (%_% xmm11) (%_% xmm13) *)
  0x66; 0x0f; 0xef; 0xd5;  (* PXOR (%_% xmm2) (%_% xmm5) *)
  0x66; 0x0f; 0xef; 0xf9;  (* PXOR (%_% xmm7) (%_% xmm1) *)
  0xf3; 0x0f; 0x7f; 0x77; 0x40;
                           (* MOVDQU (Memop Word128 (%% (rdi,64))) (%_% xmm6) *)
  0xf3; 0x0f; 0x6f; 0x36;  (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,0))) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x50;
                           (* MOVDQU (Memop Word128 (%% (rdi,80))) (%_% xmm11) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5e; 0x10;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rsi,16))) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x60;
                           (* MOVDQU (Memop Word128 (%% (rdi,96))) (%_% xmm2) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x20;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,32))) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x70;
                           (* MOVDQU (Memop Word128 (%% (rdi,112))) (%_% xmm7) *)
  0x48; 0x8d; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rdi,128)) *)
  0xf3; 0x0f; 0x6f; 0x7e; 0x30;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,48))) *)
  0x66; 0x0f; 0xef; 0x74; 0x24; 0x20;
                           (* PXOR (%_% xmm6) (Memop Word128 (%% (rsp,32))) *)
  0x66; 0x45; 0x0f; 0xef; 0xda;
                           (* PXOR (%_% xmm11) (%_% xmm10) *)
  0x66; 0x41; 0x0f; 0xef; 0xd6;
                           (* PXOR (%_% xmm2) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0xef; 0xf8;
                           (* PXOR (%_% xmm7) (%_% xmm8) *)
  0xf3; 0x0f; 0x7f; 0x37;  (* MOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm6) *)
  0xf3; 0x44; 0x0f; 0x7f; 0x5f; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rdi,16))) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rdi,32))) (%_% xmm2) *)
  0xf3; 0x0f; 0x7f; 0x7f; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rdi,48))) (%_% xmm7) *)
  0x74; 0x4b;              (* JE (Imm8 (word 75)) *)
  0x66; 0x0f; 0x6f; 0x74; 0x24; 0x30;
                           (* MOVDQA (%_% xmm6) (Memop Word128 (%% (rsp,48))) *)
  0x48; 0x8d; 0x76; 0x40;  (* LEA (% rsi) (%% (rsi,64)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x66; 0x0f; 0x7f; 0x34; 0x24;
                           (* MOVDQA (Memop Word128 (%% (rsp,0))) (%_% xmm6) *)
  0x66; 0x44; 0x0f; 0x7f; 0x7c; 0x24; 0x10;
                           (* MOVDQA (Memop Word128 (%% (rsp,16))) (%_% xmm15) *)
  0x48; 0x8d; 0x7f; 0x40;  (* LEA (% rdi) (%% (rdi,64)) *)
  0x66; 0x44; 0x0f; 0x7f; 0x4c; 0x24; 0x20;
                           (* MOVDQA (Memop Word128 (%% (rsp,32))) (%_% xmm9) *)
  0x48; 0x81; 0xea; 0xc0; 0x00; 0x00; 0x00;
                           (* SUB (% rdx) (Imm32 (word 192)) *)
  0x66; 0x0f; 0x7f; 0x5c; 0x24; 0x30;
                           (* MOVDQA (Memop Word128 (%% (rsp,48))) (%_% xmm3) *)
  0x42; 0x0f; 0xb6; 0x04; 0x16;
                           (* MOVZX (% eax) (Memop Byte (%%% (rsi,0,r10))) *)
  0x42; 0x0f; 0xb6; 0x0c; 0x14;
                           (* MOVZX (% ecx) (Memop Byte (%%% (rsp,0,r10))) *)
  0x4d; 0x8d; 0x52; 0x01;  (* LEA (% r10) (%% (r10,1)) *)
  0x31; 0xc8;              (* XOR (% eax) (% ecx) *)
  0x42; 0x88; 0x44; 0x17; 0xff;
                           (* MOV (Memop Byte (%%%% (rdi,0,r10,-- &1))) (% al) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xe6;              (* JNE (Imm8 (word 230)) *)
  0x49; 0x8d; 0x21;        (* LEA (% rsp) (%% (r9,0)) *)
  0xf3; 0xc3               (* RET *)
]]);;


let CHACHA_EXEC = X86_MK_EXEC_RULE chacha20_ssse3_4x_mc;;

(* ------------------------------------------------------------------------- *)
(* RFC 8439's encryption byte by byte: message byte p XOR byte p MOD 16 of   *)
(* the keystream's 16-byte piece p DIV 16, as the code computes it.          *)
(* ------------------------------------------------------------------------- *)

let EL_MAP2_LE = prove
 (`!(f:A->B->C) l1 l2 p.
     p < LENGTH l1 /\ LENGTH l1 <= LENGTH l2
     ==> EL p (MAP2 f l1 l2) = f (EL p l1) (EL p l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  X_GEN_TAC `l2:B list` THEN STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[LENGTH; LE_SUC; ARITH_RULE `~(SUC n <= 0)`] THEN
  INDUCT_TAC THEN REWRITE_TAC[MAP2_DEF; EL; HD; TL; LT_SUC; LE_SUC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let LENGTH_MAP2_LE = prove
 (`!(f:A->B->C) l1 l2. LENGTH (MAP2 f l1 l2) = LENGTH l1`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP2_DEF; LENGTH]);;

let EL_BYTELIST_OF_NUM = prove
 (`!k n r. r < k ==> EL r (bytelist_of_num k n) = word((n DIV 256 EXP r) MOD 256)`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT; bytelist_of_num] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; EXP; DIV_1; LT_SUC] THEN
  ASM_SIMP_TAC[DIV_DIV; MULT_SYM]);;

(* The words of a block before they are serialized. *)
let chacha20_block_words = new_definition
 `chacha20_block_words key counter nonce =
    let s = chacha20_state key counter nonce in
    MAP2 word_add (chacha20_rounds 10 s) s`;;

let EL_ITLIST_WORDS = prove
 (`!ws r. r < 4 * LENGTH ws
          ==> EL r (ITLIST (\w l. APPEND (bytelist_of_num 4 (val(w:int32))) l) ws []) =
              word_subword (EL (r DIV 4) ws) (8 * (r MOD 4),8):byte`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; MULT_CLAUSES; CONJUNCT1 LT; ITLIST] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_APPEND; LENGTH_BYTELIST_OF_NUM] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[EL_BYTELIST_OF_NUM; DIV_LT; MOD_LT; EL; HD] THEN
    REWRITE_TAC[word_subword; EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV;
    FIRST_X_ASSUM(MP_TAC o SPEC `r - 4`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `r DIV 4 = SUC((r - 4) DIV 4) /\ r MOD 4 = (r - 4) MOD 4` (fun th -> REWRITE_TAC[th; EL; TL]) THEN
    SUBGOAL_THEN `r = (r - 4) + 1 * 4` (fun th -> GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
     [ASM_ARITH_TAC; SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ] THEN ARITH_TAC]]);;

let LENGTH_CHACHA20_DOUBLE_ROUND = prove
 (`!s. LENGTH (chacha20_double_round s) = 16`,
  GEN_TAC THEN REWRITE_TAC[chacha20_double_round; chacha20_quarter_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_CHACHA20_STATE = prove
 (`!key counter nonce. LENGTH (chacha20_state key counter nonce) = 16`,
  REWRITE_TAC[chacha20_state; chacha20_words; LENGTH_APPEND; LENGTH; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_CHACHA20_BLOCK_WORDS = prove
 (`!key counter nonce. LENGTH (chacha20_block_words key counter nonce) = 16`,
  REWRITE_TAC[chacha20_block_words; LENGTH_MAP2_LE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_MAP2_LE; ARITH_RULE `10 = SUC 9`; chacha20_rounds; LENGTH_CHACHA20_DOUBLE_ROUND]);;

let CHACHA20_BLOCK_WORDS = prove
 (`!key counter nonce.
     chacha20_block key counter nonce =
     ITLIST (\w l. APPEND (bytelist_of_num 4 (val(w:int32))) l) (chacha20_block_words key counter nonce) []`,
  REWRITE_TAC[chacha20_block; chacha20_block_words] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let EL_CHACHA20_BLOCK = prove
 (`!key counter nonce r.
     r < 64 ==> EL r (chacha20_block key counter nonce) =
                word_subword (EL (r DIV 4) (chacha20_block_words key counter nonce)) (8 * (r MOD 4),8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CHACHA20_BLOCK_WORDS] THEN MATCH_MP_TAC EL_ITLIST_WORDS THEN
  ASM_REWRITE_TAC[LENGTH_CHACHA20_BLOCK_WORDS] THEN ASM_ARITH_TAC);;

let LENGTH_ITLIST_WORDS = prove
 (`!ws. LENGTH (ITLIST (\w l. APPEND (bytelist_of_num 4 (val(w:int32))) l) ws []) = 4 * LENGTH ws`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; LENGTH; LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM] THEN ARITH_TAC);;

let LENGTH_CHACHA20_BLOCK = prove
 (`!key counter nonce. LENGTH (chacha20_block key counter nonce) = 64`,
  REWRITE_TAC[CHACHA20_BLOCK_WORDS; LENGTH_ITLIST_WORDS; LENGTH_CHACHA20_BLOCK_WORDS] THEN ARITH_TAC);;

let LENGTH_CHACHA20_KEYSTREAM = prove
 (`!key counter nonce n. LENGTH (chacha20_keystream key counter nonce n) = 64 * n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[chacha20_keystream; LENGTH; LENGTH_APPEND; LENGTH_CHACHA20_BLOCK] THEN ARITH_TAC);;

let EL_CHACHA20_KEYSTREAM = prove
 (`!key counter nonce n p.
     p < 64 * n
     ==> EL p (chacha20_keystream key counter nonce n) =
         EL (p MOD 64) (chacha20_block key (word_add counter (word (p DIV 64))) nonce)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; chacha20_keystream] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_APPEND; LENGTH_CHACHA20_KEYSTREAM] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `p DIV 64 = n /\ p MOD 64 = p - 64 * n` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC);;

(* The keystream's 16-byte piece q, from block counter on: words
   4 (q MOD 4) to 4 (q MOD 4) + 3 of block q DIV 4, as memory holds them. *)
let chacha20_piece = new_definition
 `chacha20_piece key counter nonce q : int128 =
    let w = chacha20_block_words key (word_add counter (word (q DIV 4))) nonce
    and k = 4 * (q MOD 4) in
    word_join (word_join (EL (k + 3) w) (EL (k + 2) w):int64)
              (word_join (EL (k + 1) w) (EL k w):int64)`;;

let CHACHA20_PIECE_BYTE = prove
 (`!key counter nonce q r.
     r < 16
     ==> word_subword (chacha20_piece key counter nonce q) (8 * r,8):byte =
         word_subword (EL (4 * (q MOD 4) + r DIV 4)
                          (chacha20_block_words key (word_add counter (word (q DIV 4))) nonce))
                      (8 * (r MOD 4),8)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chacha20_piece] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`r:num`,`r:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let DIV_MOD_64_16 = prove
 (`!p. (p MOD 64) DIV 4 = 4 * ((p DIV 16) MOD 4) + (p MOD 16) DIV 4 /\
       (p MOD 64) MOD 4 = (p MOD 16) MOD 4 /\ p DIV 64 = (p DIV 16) DIV 4`,
  GEN_TAC THEN REWRITE_TAC[DIV_DIV; ARITH_RULE `16 * 4 = 64`] THEN
  SUBGOAL_THEN `p MOD 64 = (4 * ((p DIV 16) MOD 4)) * 4 + p MOD 16` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `(p DIV 16) DIV 4` THEN
    MP_TAC(SPECL [`p:num`; `16`] DIVISION) THEN MP_TAC(SPECL [`p DIV 16`; `4`] DIVISION) THEN
    ARITH_TAC;
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ] THEN REWRITE_TAC[MOD_MOD; ARITH_RULE `16 = 4 * 4`] THEN
    REWRITE_TAC[GSYM(ARITH_RULE `16 = 4 * 4`); MOD_MOD_EXP_MIN] THEN
    MP_TAC(SPECL [`p:num`; `16`; `4`] MOD_MOD) THEN REWRITE_TAC[ARITH_RULE `16 * 4 = 64`] THEN
    ARITH_TAC]);;

let CHACHA20_ENCRYPT_BYTE = prove
 (`!key counter nonce msg p.
     p < LENGTH msg
     ==> EL p (chacha20_encrypt key counter nonce msg) =
         word_xor (EL p msg)
                  (word_subword (chacha20_piece key counter nonce (p DIV 16)) (8 * (p MOD 16),8))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chacha20_encrypt] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_MAP2_LE o lhand o snd) THEN
  REWRITE_TAC[LENGTH_CHACHA20_KEYSTREAM] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[EL_CHACHA20_KEYSTREAM; ARITH_RULE `p < l ==> p < 64 * ((l + 63) DIV 64)`;
               EL_CHACHA20_BLOCK; MOD_LT_EQ; ARITH_EQ; CHACHA20_PIECE_BYTE] THEN
  REWRITE_TAC[DIV_MOD_64_16]);;

(* ------------------------------------------------------------------------- *)
(* Stepping. The code keeps four ChaCha20 states side by side, word k of     *)
(* state j in 32-bit lane j of one 128-bit register or stack slot. SSE       *)
(* instructions write an XMM register's low 128 bits and keep the rest of    *)
(* its YMM register, so the simulation tracks each YMM register whole, as an *)
(* unknown high half joined to the XMM value, as aes_hw_cbc_encrypt.ml does, *)
(* and after each step pushes each instruction into the lanes, folding the   *)
(* byte shuffles and shift pairs into rotations.                             *)
(* ------------------------------------------------------------------------- *)

(* Steps from state s(n-1) until the program counter is pc + target, naming
   the states sn, s(n+1), ... *)
let current_offset (asl,w) =
  let s = rand w in
  let pat = mk_eq(mk_comb(`read RIP`, s), `word(pc + k):int64`) in
  let th = snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
  dest_small_numeral(rand(rand(rand(concl th))));;

let rec X86_STEPS_UNTIL_TAC execth target n (asl,w as g) =
  if current_offset g = target then ALL_TAC g
  else (X86_STEPS_TAC execth [n] THEN
        X86_STEPS_UNTIL_TAC execth target (n + 1)) g;;

let WORD_SUBWORD_JOIN_128 = prove
 (`(!(h:int128) (l:int128). word_subword (word_join h l:256 word) (0,128):int128 = l) /\
   (!(h:int128) (l:int128). word_subword (word_join h l:256 word) (128,128):int128 = h)`,
  CONV_TAC WORD_BLAST);;

let XMM_YMMS =
  [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
   XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15];;

let YMM_OF_XMM = prove
 (`!(c:(x86state,256 word)component) s x.
     read (c :> zerotop_128) s = x ==> ?h. read c s = word_join (h:int128) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; zerotop_128; through; read] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `word_subword (read (c:(x86state,256 word)component) (s:x86state)) (128,128):int128` THEN
  CONV_TAC WORD_BLAST);;

let XMM_OF_YMM = prove
 (`!(c:(x86state,256 word)component) s h x.
     read c s = word_join (h:int128) x ==> read (c :> zerotop_128) s = x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; zerotop_128; through; read] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_BLAST);;

let ymm_regs =
  [`YMM0`; `YMM1`; `YMM2`; `YMM3`; `YMM4`; `YMM5`; `YMM6`; `YMM7`;
   `YMM8`; `YMM9`; `YMM10`; `YMM11`; `YMM12`; `YMM13`; `YMM14`; `YMM15`];;

(* For the current state s, each YMM register gets an equation: its known XMM
   value joined to a fresh high half, or a fresh value. *)
let GHOST_YMMS_TAC (asl,w as g) =
  let s = rand w in
  let tac k ymm =
    let xmm = List.nth [`XMM0`; `XMM1`; `XMM2`; `XMM3`; `XMM4`; `XMM5`; `XMM6`;
                        `XMM7`; `XMM8`; `XMM9`; `XMM10`; `XMM11`; `XMM12`;
                        `XMM13`; `XMM14`; `XMM15`] k in
    let pat = mk_eq(mk_comb(mk_comb(`read:(x86state,int128)component->x86state->int128`, xmm), s),
                    `x:int128`) in
    let hv = mk_var("ymmh"^string_of_int k, `:int128`) in
    let yv = mk_var("ymmv"^string_of_int k, `:256 word`) in
    fun (asl,w as g) ->
      try let th = snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
          let th' = MATCH_MP YMM_OF_XMM (REWRITE_RULE XMM_YMMS th) in
          X_CHOOSE_THEN (variant (freesl(w::map (concl o snd) asl)) hv) ASSUME_TAC th' g
      with Failure _ ->
        let ex = mk_exists(yv, mk_eq(list_mk_comb(`read:(x86state,256 word)component->x86state->256 word`, [ymm; s]), yv)) in
        (SUBGOAL_THEN ex (X_CHOOSE_THEN (variant (freesl(w::map (concl o snd) asl)) yv) ASSUME_TAC)
         THENL [MESON_TAC[]; ALL_TAC]) g in
  EVERY (List.mapi tac ymm_regs) g;;

(* The XMM values of the current state from its YMM equations. *)
let XMMS_OF_YMMS_TAC (asl,w as g) =
  let s = rand w in
  let pat = mk_eq(mk_comb(`read (c:(x86state,256 word)component)`, s),
                  `word_join (h:int128) (x:int128):256 word`) in
  let ths = mapfilter (fun (_,th) ->
     if can (term_match [] pat) (concl th)
     then let c = rand(rator(lhs(concl th))) in
          if mem c ymm_regs then MATCH_MP XMM_OF_YMM th else fail()
     else fail()) asl in
  MAP_EVERY (ASSUME_TAC o REWRITE_RULE(map SYM XMM_YMMS)) ths g;;

let X86_XSTEPS_TAC execth snums =
  MAP_EVERY (fun n ->
    X86_STEPS_TAC execth [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_JOIN_128])) snums;;

let CHACHA_JOIN_BITOPS = prove
 (`(!(a:int32) (b:int32) c d.
      word_xor (word_join a b:int64) (word_join c d) = word_join (word_xor a c) (word_xor b d)) /\
   (!(a:int64) (b:int64) c d.
      word_xor (word_join a b:int128) (word_join c d) = word_join (word_xor a c) (word_xor b d)) /\
   (!(a:int32) (b:int32) c d.
      word_or (word_join a b:int64) (word_join c d) = word_join (word_or a c) (word_or b d)) /\
   (!(a:int64) (b:int64) c d.
      word_or (word_join a b:int128) (word_join c d) = word_join (word_or a c) (word_or b d))`,
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* PSHUFB by the two masks, and each PSLLD, PSRLD and POR triple, in a lane. *)
let CHACHA_ROT_RULES = prove
 (`(!v:int32. word_join (word_join (word_subword v (8,8):byte) (word_subword v (0,8):byte):int16)
                        (word_join (word_subword v (24,8):byte) (word_subword v (16,8):byte):int16) =
              word_rol v 16) /\
   (!v:int32. word_join (word_join (word_subword v (16,8):byte) (word_subword v (8,8):byte):int16)
                        (word_join (word_subword v (0,8):byte) (word_subword v (24,8):byte):int16) =
              word_rol v 8) /\
   (!v:int32. word_or (word_shl v 12) (word_ushr v 20) = word_rol v 12) /\
   (!v:int32. word_or (word_shl v 7) (word_ushr v 25) = word_rol v 7)`,
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let CHACHA_LANE_CONV =
  TOP_DEPTH_CONV(GEN_REWRITE_CONV I [CHACHA_JOIN_BITOPS] ORELSEC WORD_SIMPLE_SUBWORD_CONV ORELSEC
                 WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  REWRITE_CONV[CHACHA_ROT_RULES];;

let CHACHA_LANE_TAC (asl,w as g) =
  let s = rand w in
  RULE_ASSUM_TAC(fun th -> if free_in s (concl th) && is_eq (concl th)
                           then CONV_RULE(RAND_CONV CHACHA_LANE_CONV) th else th) g;;

let rec CHACHA_UNTIL_TAC target n (asl,w as g) =
  if current_offset g = target then ALL_TAC g
  else (X86_XSTEPS_TAC CHACHA_EXEC [n] THEN CHACHA_LANE_TAC THEN
        CHACHA_UNTIL_TAC target (n + 1)) g;;

(* ------------------------------------------------------------------------- *)
(* One double round of the four states, the loop's body.                     *)
(* ------------------------------------------------------------------------- *)

(* x_k_j is word k of state j. *)
let chacha_xv k j = mk_var("x"^string_of_int k^"_"^string_of_int j, `:int32`);;

(* Lanes 0 to 3 of a 128-bit value from four 32-bit words. *)
let chacha_lanes f =
  let j64 x y = mk_icomb(mk_icomb(`word_join:int32->int32->int64`, x), y) in
  mk_icomb(mk_icomb(`word_join:int64->int64->int128`, j64 (f 3) (f 2)), j64 (f 1) (f 0));;

(* Where the loop keeps word k of the states: words 0 to 7 in xmm8 to xmm15,
   8 and 9 in xmm4 and xmm5, 10 and 11 on the stack, and 12 to 15 in xmm0 to
   xmm3. *)
let chacha_loc k =
  let rd c = mk_icomb(`read:(x86state,int128)component->x86state->int128`, c) in
  if k < 8 then rd (mk_const("XMM"^string_of_int (8+k),[]))
  else if k = 8 then rd `XMM4` else if k = 9 then rd `XMM5`
  else if k = 10 then rd `memory :> bytes128 (word_add stk (word 32))`
  else if k = 11 then rd `memory :> bytes128 (word_add stk (word 48))`
  else rd (mk_const("XMM"^string_of_int (k-12),[]));;

let chacha_rows f =
  list_mk_conj(map (fun k -> mk_eq(mk_comb(chacha_loc k, `s:x86state`), chacha_lanes (f k))) (0--15));;

let chacha_el k t = mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral k), t);;

let chacha_xlist j = mk_list(map (fun k -> chacha_xv k j) (0--15), `:int32`);;

(* The rotate-by-16 mask, which xmm7 holds at the loop's head and r10 also
   points to, and the rotate-by-8 one, which r11 points to. *)
let CHACHA_DR_GOAL =
  let tm = mk_imp(
   `aligned 16 (rp10:int64) /\ aligned 16 (rp11:int64) /\ aligned 16 (stk:int64) /\
    nonoverlapping (stk:int64,64) (rp10:int64,16) /\ nonoverlapping (stk:int64,64) (rp11:int64,16) /\
    nonoverlapping (stk:int64,64) (word pc:int64,0x9d4)`,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj [
     `bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\ read RIP s = word(pc + 0x180) /\
      read RSP s = stk /\ read R10 s = rp10 /\ read R11 s = rp11 /\
      read (memory :> bytes128 rp10) s = word 0x0d0c0f0e09080b0a0504070601000302 /\
      read (memory :> bytes128 rp11) s = word 0x0e0d0c0f0a09080b0605040702010003 /\
      read XMM7 s = word 0x0d0c0f0e09080b0a0504070601000302`;
     chacha_rows (fun k j -> chacha_xv k j)]);
    mk_abs(`s:x86state`, list_mk_conj [
     `read RIP s = word(pc + 0x4a6) /\ read XMM7 s = word 0x0d0c0f0e09080b0a0504070601000302`;
     chacha_rows (fun k j -> chacha_el k (mk_comb(`chacha20_double_round`, chacha_xlist j)))]);
    `MAYCHANGE [RIP] ,,
     MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
     MAYCHANGE [memory :> bytes(stk,64)] ,, MAYCHANGE [events]`]) in
  list_mk_forall(frees tm, tm);;

(* RFC 8439's double round of state j, word by word. *)
let CHACHA_DR_SPEC j =
  (REWRITE_CONV[chacha20_double_round] THENC DEPTH_CONV EL_CONV THENC
   REWRITE_CONV[chacha20_quarter_round] THENC TOP_DEPTH_CONV let_CONV)
  (mk_comb(`chacha20_double_round`, chacha_xlist j));;

let CHACHA_DR = prove
 (CHACHA_DR_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN
  CHACHA_UNTIL_TAC 0x4a6 1 THEN XMMS_OF_YMMS_TAC THEN ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC(map CHACHA_DR_SPEC (0--3)) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  ASM_REWRITE_TAC[] THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The ten double rounds, from the loop's head with eax = 10 to its exit.    *)
(* ------------------------------------------------------------------------- *)

(* State j, s_j, as a list of 16 words. *)
let chacha_sv j = mk_var("s"^string_of_int j, `:int32 list`);;

let chacha_rounds_rows i =
  chacha_rows (fun k j -> chacha_el k (list_mk_comb(`chacha20_rounds`, [i; chacha_sv j])));;

let CHACHA_ROUNDS_HYPS =
  `aligned 16 (rp10:int64) /\ aligned 16 (rp11:int64) /\ aligned 16 (stk:int64) /\
   nonoverlapping (stk:int64,64) (rp10:int64,16) /\ nonoverlapping (stk:int64,64) (rp11:int64,16) /\
   nonoverlapping (stk:int64,64) (word pc:int64,0x9d4)`;;

let CHACHA_ROUNDS_COMMON =
  `read RSP s = stk /\ read R10 s = rp10 /\ read R11 s = rp11 /\
   read (memory :> bytes128 rp10) s = word 0x0d0c0f0e09080b0a0504070601000302 /\
   read (memory :> bytes128 rp11) s = word 0x0e0d0c0f0a09080b0605040702010003 /\
   read XMM7 s = word 0x0d0c0f0e09080b0a0504070601000302`;;

let CHACHA_ROUNDS_FRAME =
  `MAYCHANGE [RIP; RAX] ,, MAYCHANGE SOME_FLAGS ,,
   MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
              ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
   MAYCHANGE [memory :> bytes(stk,64)] ,, MAYCHANGE [events]`;;

let CHACHA_ROUNDS_GOAL =
  let tm = mk_imp(CHACHA_ROUNDS_HYPS,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj [
     `bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\ read RIP s = word(pc + 0x180) /\
      read RAX s = word 10`; CHACHA_ROUNDS_COMMON;
     chacha_rows (fun k j -> chacha_el k (chacha_sv j))]);
    mk_abs(`s:x86state`, list_mk_conj [
     `read RIP s = word(pc + 0x4ae)`; CHACHA_ROUNDS_COMMON; chacha_rounds_rows `10`]);
    CHACHA_ROUNDS_FRAME]) in
  list_mk_forall(frees tm, tm);;

let CHACHA_ROUNDS_INV =
  mk_abs(`i:num`, mk_abs(`s:x86state`, mk_conj(list_mk_conj [
   `read RAX s = word (10 - i)`;
   CHACHA_ROUNDS_COMMON; chacha_rounds_rows `i:num`], `read ZF s <=> i = 10`)));;

(* The double round's words from state lists. *)
let CHACHA_DR_ELS = prove
 (`!l. chacha20_double_round
         [EL 0 l; EL 1 l; EL 2 l; EL 3 l; EL 4 l; EL 5 l; EL 6 l; EL 7 l;
          EL 8 l; EL 9 l; EL 10 l; EL 11 l; EL 12 l; EL 13 l; EL 14 l; EL 15 l] =
       chacha20_double_round (l:int32 list)`,
  GEN_TAC THEN REWRITE_TAC[chacha20_double_round] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let CHACHA_DR_AT i =
  INST (List.concat (map (fun j -> map (fun k -> chacha_el k (list_mk_comb(`chacha20_rounds`, [i; chacha_sv j])), chacha_xv k j) (0--15)) (0--3)))
       (SPEC_ALL CHACHA_DR);;
let CHACHA_ROUNDS = prove
 (CHACHA_ROUNDS_GOAL,
  REWRITE_TAC[SOME_FLAGS; GSYM CONJ_ASSOC] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `10` `pc + 0x180` `pc + 0x4a8` CHACHA_ROUNDS_INV THEN
  REWRITE_TAC[ARITH] THEN REPEAT CONJ_TAC THENL
   [(* Into the loop. *)
    REWRITE_TAC[chacha20_rounds; SUB_0] THEN ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* A double round, and the count. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[fst CHACHA_EXEC] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(CHACHA_DR_AT `i:num`) THEN ASM_REWRITE_TAC[] THEN
    X86_BIGSTEP_TAC CHACHA_EXEC "s1" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CHACHA_DR_ELS; GSYM(CONJUNCT2 chacha20_rounds)]) THEN
    X86_STEPS_TAC CHACHA_EXEC [2] THEN ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[GSYM ADD1] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `i < 10` THEN SPEC_TAC(`i:num`,`i:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN REWRITE_TAC[];
    (* Back to the head. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC CHACHA_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* Out of the loop. *)
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC CHACHA_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The input states added back, and the sums transposed into each block's    *)
(* four 16-byte pieces.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Where the code leaves 16-byte piece m of block j's keystream once it has
   added the input state and transposed: the first on the stack, the others
   in registers. *)
let chacha_piece_loc j m =
  let rd c = mk_icomb(`read:(x86state,int128)component->x86state->int128`, c) in
  if m = 0 then rd (subst [mk_small_numeral(16*j),`n:num`] `memory :> bytes128 (word_add stk (word n))`)
  else mk_icomb(`read:(x86state,int128)component->x86state->int128`,
    mk_const("XMM"^string_of_int (List.nth (List.nth [[12;4;0];[13;5;1];[10;14;8];[15;9;3]] j) (m-1)),[]));;

(* The stack copy of word k of the states, which the code adds after the
   rounds. *)
let chacha_copy_loc k =
  mk_icomb(`read:(x86state,int128)component->x86state->int128`,
    subst [mk_small_numeral(64+16*k),`n:num`] `memory :> bytes128 (word_add stk (word n))`);;

let chacha_sum k j =
  let s = chacha_sv j in
  list_mk_icomb "word_add" [chacha_el k (list_mk_comb(`chacha20_rounds`, [`10`; s])); chacha_el k s];;

let chacha_pieces =
  list_mk_conj(List.concat(map (fun j -> map (fun m ->
    mk_eq(mk_comb(chacha_piece_loc j m, `s:x86state`), chacha_lanes (fun t -> chacha_sum (4*m+t) j))) (0--3)) (0--3)));;

let chacha_copies =
  list_mk_conj(map (fun k -> mk_eq(mk_comb(chacha_copy_loc k, `s:x86state`), chacha_lanes (fun j -> chacha_el k (chacha_sv j)))) (0--15));;

let CHACHA_FINISH_GOAL =
  let tm = mk_imp(
   `aligned 16 (stk:int64) /\ nonoverlapping (stk:int64,320) (word pc:int64,0x9d4)`,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj [
     `bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\ read RIP s = word(pc + 0x4ae) /\
      read RSP s = stk /\ read RCX s = word_add stk (word 256)`;
     chacha_rounds_rows `10`; chacha_copies]);
    mk_abs(`s:x86state`, list_mk_conj [
     `read RIP s = word(pc + 0x618)`; chacha_pieces; chacha_copies]);
    `MAYCHANGE [RIP] ,,
     MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
     MAYCHANGE [memory :> bytes(stk,64)] ,, MAYCHANGE [events]`]) in
  list_mk_forall(frees tm, tm);;

let CHACHA_FINISH = prove
 (CHACHA_FINISH_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN
  CHACHA_UNTIL_TAC 0x618 1 THEN XMMS_OF_YMMS_TAC THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* The four blocks from the entry to the rounds, 0x163, to the keystream's   *)
(* pieces at 0x618.                                                          *)
(* ------------------------------------------------------------------------- *)

(* At 0x163 words 10 and 11 are still in xmm6 and xmm7, and the stack copy
   of row 12 is the previous group's. *)
let chacha_entry_rows =
  let rd c = mk_icomb(`read:(x86state,int128)component->x86state->int128`, c) in
  let loc k = if k = 10 then rd `XMM6` else if k = 11 then rd `XMM7` else chacha_loc k in
  list_mk_conj(map (fun k -> mk_eq(mk_comb(loc k, `s:x86state`),
    chacha_lanes (fun j -> chacha_el k (chacha_sv j)))) (0--15));;

let chacha_entry_copies =
  list_mk_conj(map (fun k -> mk_eq(mk_comb(chacha_copy_loc k, `s:x86state`),
    chacha_lanes (fun j -> chacha_el k (chacha_sv j)))) (subtract (0--15) [12]));;

let CHACHA_CORE_HYPS =
  `aligned 16 (rp10:int64) /\ aligned 16 (rp11:int64) /\ aligned 16 (stk:int64) /\
   nonoverlapping (stk:int64,320) (rp10:int64,16) /\ nonoverlapping (stk:int64,320) (rp11:int64,16) /\
   nonoverlapping (stk:int64,320) (word pc:int64,0x9d4)`;;

let CHACHA_CORE_COMMON =
  `read RSP s = stk /\ read RCX s = word_add stk (word 256) /\
   read R10 s = rp10 /\ read R11 s = rp11 /\
   read (memory :> bytes128 rp10) s = word 0x0d0c0f0e09080b0a0504070601000302 /\
   read (memory :> bytes128 rp11) s = word 0x0e0d0c0f0a09080b0605040702010003`;;

let CHACHA_CORE_FRAME =
  `MAYCHANGE [RIP; RAX] ,, MAYCHANGE SOME_FLAGS ,,
   MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
              ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
   MAYCHANGE [memory :> bytes(stk,320)] ,, MAYCHANGE [events]`;;

let CHACHA_CORE_GOAL =
  let tm = mk_imp(CHACHA_CORE_HYPS,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj [
     `bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\ read RIP s = word(pc + 0x163)`;
     CHACHA_CORE_COMMON; chacha_entry_rows; chacha_entry_copies]);
    mk_abs(`s:x86state`, list_mk_conj [
     `read RIP s = word(pc + 0x618)`; CHACHA_CORE_COMMON; chacha_pieces; chacha_copies]);
    CHACHA_CORE_FRAME]) in
  list_mk_forall(frees tm, tm);;

let CHACHA_CORE = prove
 (CHACHA_CORE_GOAL,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping (stk:int64,64) (rp10:int64,16) /\
                nonoverlapping (stk:int64,64) (rp11:int64,16) /\
                nonoverlapping (stk:int64,64) (word pc:int64,0x9d4)`
   STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN CHACHA_UNTIL_TAC 0x180 1 THEN
  XMMS_OF_YMMS_TAC THEN
  MP_TAC(SPEC_ALL CHACHA_ROUNDS) THEN ASM_REWRITE_TAC[SOME_FLAGS] THEN
  X86_BIGSTEP_TAC CHACHA_EXEC "s7" THEN
  MP_TAC(SPEC_ALL CHACHA_FINISH) THEN ASM_REWRITE_TAC[] THEN
  X86_BIGSTEP_TAC CHACHA_EXEC "s8" THEN
  ENSURES_FINAL_STATE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* Memory as bytes: chacha_bnum f p k is the k bytes f p, ..., f (p + k - 1)  *)
(* read little-endian.                                                       *)
(* ------------------------------------------------------------------------- *)

let chacha_bnum = define
 `(!f p. chacha_bnum (f:num->byte) p 0 = 0) /\
  (!f p k. chacha_bnum f p (SUC k) = val(f p) + 256 * chacha_bnum f (p + 1) k)`;;

let ADD_MULT_EXP_EQ = prove
 (`!e x y x' y'. x < e /\ x' < e
                 ==> (x + e * y = x' + e * y' <=> x = x' /\ y = y')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x + e * y) MOD e = (x' + e * y') MOD e /\
                (x + e * y) DIV e = (x' + e * y') DIV e` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(e = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

let FORALL_LT_SUC_SPLIT = prove
 (`!P m. (!i. i < SUC m ==> P i) <=> P 0 /\ (!i. i < m ==> P(SUC i))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC; LT_0]]);;

let READ_BYTES128_VAL = prove
 (`!(a:int64) s x. read (memory :> bytes128 a) s = x <=>
                   read (memory :> bytes(a,16)) s = val(x:int128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let CHACHA_BNUM_BOUND = prove
 (`!k f p. chacha_bnum f p k < 2 EXP (8 * k)`,
  INDUCT_TAC THEN REWRITE_TAC[chacha_bnum] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `(f:num->byte) p` VAL_BOUND) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->byte`; `p + 1`]) THEN
  REWRITE_TAC[DIMINDEX_8; ARITH_RULE `8 * SUC k = 8 * k + 8`; EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `256 * (chacha_bnum (f:num->byte) (p + 1) k + 1) <= 2 EXP (8 * k) * 256`
   MP_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
                 ASM_ARITH_TAC]);;

let CHACHA_BNUM_ADD = prove
 (`!k l f p. chacha_bnum f p (k + l) =
             chacha_bnum f p k + 2 EXP (8 * k) * chacha_bnum f (p + k) l`,
  INDUCT_TAC THEN REWRITE_TAC[chacha_bnum; ADD_CLAUSES; MULT_CLAUSES; EXP] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * SUC k = 8 + 8 * k`; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(p + 1) + k = SUC(p + k)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUM_RING);;

let CHACHA_BNUM_EQ = prove
 (`!k f g p. (!i. i < k ==> f(p + i) = g(p + i)) ==> chacha_bnum f p k = chacha_bnum g p k`,
  INDUCT_TAC THEN REWRITE_TAC[chacha_bnum] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ADD_CLAUSES; LT_0] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
  ASM_REWRITE_TAC[LT_SUC; ARITH_RULE `(p + 1) + i = p + SUC i`]);;

(* Byte i of the sum. *)
let CHACHA_BNUM_BYTE = prove
 (`!k f p i. i < k ==> (chacha_bnum f p k DIV 2 EXP (8 * i)) MOD 256 = val(f(p + i):byte)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE `i < k ==> k = i + SUC(k - i - 1)`)) THEN
  REWRITE_TAC[CHACHA_BNUM_ADD; chacha_bnum] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; CHACHA_BNUM_BOUND; DIV_LT; ADD_CLAUSES] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM DIMINDEX_8; VAL_BOUND]);;

(* The bytes at a and on are f p and on. *)
let READ_CHACHA_BNUM = prove
 (`!k f p (a:int64) s.
        read (memory :> bytes(a,k)) s = chacha_bnum f p k <=>
        !i. i < k ==> read (memory :> bytes8(word_add a (word i))) s = f(p + i)`,
  INDUCT_TAC THEN REWRITE_TAC[chacha_bnum; CONJUNCT1 LT] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC k = 1 + k`; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_BYTES8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ADD_MULT_EXP_EQ o lhand o snd) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `read (memory :> bytes8 a) s` VAL_BOUND) THEN
    MP_TAC(ISPEC `(f:num->byte) p` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VAL_EQ; GSYM ADD1; FORALL_LT_SUC_SPLIT] THEN
  REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `1 + i = SUC i`; ARITH_RULE `(p + 1) + i = SUC(p + i)`] THEN
  REWRITE_TAC[FORALL_LT_SUC_SPLIT; ADD_CLAUSES; WORD_ADD_0]);;

let READ_CHACHA_BNUM_SPLIT = prove
 (`!k l f p (a:int64) s.
        read (memory :> bytes(a,k + l)) s = chacha_bnum f p (k + l) <=>
        read (memory :> bytes(a,k)) s = chacha_bnum f p k /\
        read (memory :> bytes(word_add a (word k),l)) s = chacha_bnum f (p + k) l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; CHACHA_BNUM_ADD] THEN
  MATCH_MP_TAC ADD_MULT_EXP_EQ THEN
  REWRITE_TAC[READ_BYTES_BOUND; CHACHA_BNUM_BOUND]);;

(* A 16-byte piece. *)
let READ_CHACHA_BNUM_16 = prove
 (`!f p (a:int64) s.
        read (memory :> bytes(a,16)) s = chacha_bnum f p 16 <=>
        read (memory :> bytes128 a) s = word(chacha_bnum f p 16)`,
  REWRITE_TAC[READ_BYTES128_VAL] THEN REPEAT GEN_TAC THEN
  SIMP_TAC[VAL_WORD; DIMINDEX_128; MOD_LT; CHACHA_BNUM_BOUND;
           ARITH_RULE `2 EXP 128 = 2 EXP (8 * 16)`]);;

let READ_CHACHA_BNUM_CHUNKS = prove
 (`!m f p (a:int64) s.
        read (memory :> bytes(a,16 * m)) s = chacha_bnum f p (16 * m) <=>
        !q. q < m ==> read (memory :> bytes128(word_add a (word(16 * q)))) s =
                      word(chacha_bnum f (p + 16 * q) 16)`,
  INDUCT_TAC THEN REWRITE_TAC[chacha_bnum; CONJUNCT1 LT; MULT_CLAUSES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * m + 16 = 16 + 16 * m`; READ_CHACHA_BNUM_SPLIT] THEN
  ASM_REWRITE_TAC[READ_CHACHA_BNUM_16; FORALL_LT_SUC_SPLIT] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(p + 16) + 16 * i = p + 16 * SUC i`;
              ARITH_RULE `16 + 16 * i = 16 * SUC i`]);;

(* A 128-bit word is its 16 bytes. *)
let WORD_EQ_BYTES_128 = prove
 (`!x y:int128. (!i. i < 16 ==> word_subword x (8 * i,8):byte = word_subword y (8 * i,8))
                ==> x = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_128] THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b DIV 8`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `bit (b MOD 8):byte->bool`) THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; DIMINDEX_8; DIMINDEX_128] THEN
  SUBGOAL_THEN `8 * b DIV 8 + b MOD 8 = b /\ b MOD 8 < MIN 8 8` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`] THEN MP_TAC(SPECL [`b:num`; `8`] DIVISION) THEN ARITH_TAC);;

let WORD_SUBWORD_CHACHA_BNUM = prove
 (`!f p i. i < 16 ==> word_subword (word(chacha_bnum f p 16):int128) (8 * i,8):byte = f(p + i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; VAL_WORD; DIMINDEX_128] THEN
  SIMP_TAC[MOD_LT; CHACHA_BNUM_BOUND; ARITH_RULE `2 EXP 128 = 2 EXP (8 * 16)`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN ASM_SIMP_TAC[CHACHA_BNUM_BYTE; WORD_VAL]);;

let CHACHA_BNUM_XOR = prove
 (`!f g p. word_xor (word(chacha_bnum f p 16)) (word(chacha_bnum g p 16)):int128 =
           word(chacha_bnum (\i. word_xor (f i) (g i)) p 16)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_EQ_BYTES_128 THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SUBWORD_XOR; WORD_SUBWORD_CHACHA_BNUM]);;
(* ------------------------------------------------------------------------- *)
(* The keystream byte by byte, and each group of four blocks.                *)
(* ------------------------------------------------------------------------- *)

let chacha20_kbyte = new_definition
 `chacha20_kbyte key counter nonce p =
    word_subword (chacha20_piece key counter nonce (p DIV 16)) (8 * (p MOD 16),8):byte`;;

let CHACHA20_PIECE_CHUNK = prove
 (`!key counter nonce q.
     chacha20_piece key counter nonce q =
     word(chacha_bnum (chacha20_kbyte key counter nonce) (16 * q) 16)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_EQ_BYTES_128 THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SUBWORD_CHACHA_BNUM; chacha20_kbyte] THEN
  SUBGOAL_THEN `(16 * q + i) DIV 16 = q /\ (16 * q + i) MOD 16 = i` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC);;

(* Group g of four blocks starts at block counter + 4 g. *)
let CHACHA20_PIECE_SHIFT = prove
 (`!key counter nonce g q.
     chacha20_piece key (word_add counter (word(4 * g))) nonce q =
     chacha20_piece key counter nonce (16 * g + q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chacha20_piece] THEN
  SUBGOAL_THEN `(16 * g + q) DIV 4 = 4 * g + q DIV 4 /\ (16 * g + q) MOD 4 = q MOD 4`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ARITH_RULE `16 * g + q = (4 * g) * 4 + q`] THEN
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ];
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]]);;

let CHACHA20_STATE_EXPLICIT =
  let th = (REWRITE_CONV[chacha20_state; chacha20_words] THENC
            ONCE_DEPTH_CONV LIST_OF_SEQ_CONV THENC NUM_REDUCE_CONV THENC
            REWRITE_CONV[APPEND])
           `chacha20_state key counter nonce` in
  GEN_ALL th;;

let EL_CHACHA20_BLOCK_WORDS = prove
 (`!key counter nonce k.
     k < 16
     ==> EL k (chacha20_block_words key counter nonce) =
         word_add (EL k (chacha20_rounds 10 (chacha20_state key counter nonce)))
                  (EL k (chacha20_state key counter nonce))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chacha20_block_words] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN MATCH_MP_TAC EL_MAP2_LE THEN
  REWRITE_TAC[ARITH_RULE `10 = SUC 9`; chacha20_rounds; LENGTH_CHACHA20_DOUBLE_ROUND;
              LENGTH_CHACHA20_STATE] THEN
  ASM_ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* A whole group's 256 bytes XORed with its four blocks, 0x618 to 0x73a.      *)
(* ------------------------------------------------------------------------- *)

let chacha_kv n = mk_var("kp"^string_of_int n, `:int128`);;
let chacha_cv n = mk_var("c"^string_of_int n, `:int128`);;

let chacha_kpieces =
  list_mk_conj(List.concat(map (fun j -> map (fun m ->
    mk_eq(mk_comb(chacha_piece_loc j m, `s:x86state`), chacha_kv (4*j+m))) (0--3)) (0--3)));;

let chacha_chunk_loc n =
  mk_icomb(`read:(x86state,int128)component->x86state->int128`,
    subst [mk_small_numeral(16*n),`n:num`] `memory :> bytes128 (word_add a (word n))`);;

let chacha_chunks f =
  list_mk_conj(map (fun n -> mk_eq(mk_comb(chacha_chunk_loc n, `s:x86state`), f n)) (0--15));;

let CHACHA_XOR256_GOAL =
  let tm = mk_imp(
   `aligned 16 (stk:int64) /\ nonoverlapping (a:int64,256) (stk,64) /\
    nonoverlapping (a:int64,256) (word pc:int64,0x9d4) /\ 256 <= val(d:int64)`,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj [
     `bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\ read RIP s = word(pc + 0x618) /\
      read RSP s = stk /\ read RSI s = a /\ read RDI s = a /\ read RDX s = d`;
     chacha_kpieces; chacha_chunks chacha_cv]);
    mk_abs(`s:x86state`, list_mk_conj [
     `read RIP s = word(pc + 0x73a) /\ read RSP s = stk /\
      read RSI s = word_add a (word 256) /\ read RDI s = word_add a (word 256) /\
      read RDX s = word_sub d (word 256) /\ (read ZF s <=> val d = 256)`;
     chacha_chunks (fun n -> list_mk_icomb "word_xor" [chacha_cv n; chacha_kv n])]);
    `MAYCHANGE [RIP; RSI; RDI; RDX] ,, MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [ZMM2; ZMM6; ZMM7; ZMM11] ,,
     MAYCHANGE [memory :> bytes(a,256)] ,, MAYCHANGE [events]`]) in
  list_mk_forall(frees tm, tm);;

let CHACHA_XOR256 = prove
 (CHACHA_XOR256_GOAL,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(d:int64) < 256)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN CHACHA_UNTIL_TAC 0x73a 1 THEN
  XMMS_OF_YMMS_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* The last r bytes, 0 < r < 64, one at a time against the stack's block,     *)
(* 0x9b5 to 0x9cf.                                                           *)
(* ------------------------------------------------------------------------- *)

let CHACHA_BNUM_1 = prove
 (`!f p. chacha_bnum f p 1 = val(f p:byte)`,
  REWRITE_TAC[num_CONV `1`; chacha_bnum; MULT_CLAUSES; ADD_CLAUSES]);;

let CHACHA_BYTES_GOAL = `!pc data stk a r mf kf p.
  0 < r /\ r <= 64 /\ val a + r <= 2 EXP 64 /\
  nonoverlapping (a:int64,r) (stk:int64,64) /\ nonoverlapping (a:int64,r) (word pc:int64,0x9d4)
  ==> ensures x86
   (\s. bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\
        read RIP s = word(pc + 0x9b5) /\ read RSP s = stk /\
        read RSI s = a /\ read RDI s = a /\ read RDX s = word r /\ read R10 s = word 0 /\
        read (memory :> bytes(stk,64)) s = chacha_bnum kf p 64 /\
        read (memory :> bytes(a,r)) s = chacha_bnum mf p r)
   (\s. read RIP s = word(pc + 0x9cf) /\ read RSP s = stk /\
        read (memory :> bytes(a,r)) s = chacha_bnum (\j. word_xor (mf j) (kf j)) p r)
   (MAYCHANGE [RIP; RAX; RCX; RDX; R10] ,, MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(a,r)] ,, MAYCHANGE [events])`;;

let CHACHA_BYTES_INV = `\i s.
  (read RSP s = stk /\ read RSI s = a /\ read RDI s = a /\
   read RDX s = word(r - i) /\ read R10 s = word i /\
   read (memory :> bytes(stk,64)) s = chacha_bnum kf p 64 /\
   read (memory :> bytes(a,i)) s = chacha_bnum (\j. word_xor (mf j) (kf j)) p i /\
   read (memory :> bytes(word_add a (word i),r - i)) s = chacha_bnum mf (p + i) (r - i)) /\
  (read ZF s <=> i = r)`;;

(* The store's address, rdi + r10 - 1 once r10 is i + 1, is byte i. *)
let CHACHA_BYTES = prove
 (CHACHA_BYTES_GOAL,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `r:num` `pc + 0x9b5` `pc + 0x9cd` CHACHA_BYTES_INV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    (* Into the loop. *)
    REWRITE_TAC[SUB_0; ADD_CLAUSES; WORD_ADD_0; chacha_bnum; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* Byte i. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `i < r ==> r - i = 1 + (r - (i + 1))`] THEN
    REWRITE_TAC[READ_CHACHA_BNUM_SPLIT] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `read (memory :> bytes8(word_add a (word i))) s0 = mf(p + i) /\
                  read (memory :> bytes8(word_add stk (word i))) s0 = kf(p + i)`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `read (memory :> bytes(x,1)) s = y`) o concl)) THEN
        REWRITE_TAC[READ_MEMORY_BYTES_BYTES8; CHACHA_BNUM_1; VAL_EQ];
        FIRST_ASSUM(MP_TAC o check (can (term_match [] `read (memory :> bytes(stk,64)) s = y`) o concl)) THEN
        REWRITE_TAC[READ_CHACHA_BNUM] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `word (1 * val (word i:int64)):int64 = word i` ASSUME_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
      MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `r <= 64` THEN
      UNDISCH_TAC `i < r` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes8(word_add a (word (1 * val (word i:int64))))) s0 = mf(p + i) /\
                  read (memory :> bytes8(word_add stk (word (1 * val (word i:int64))))) s0 = kf(p + i)`
     STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X86_STEPS_TAC CHACHA_EXEC (1--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
    ABBREV_TAC `wa:int64 = word_add a (word (1 * val (word (i + 1):int64) + 18446744073709551615))` THEN
    SUBGOAL_THEN `wa:int64 = word_add a (word i)` ASSUME_TAC THENL
     [EXPAND_TAC "wa" THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `1 * val (word (i + 1):int64) = i + 1` SUBST1_TAC THENL
       [REWRITE_TAC[MULT_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
        MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `r <= 64` THEN
        UNDISCH_TAC `i < r` THEN ARITH_TAC;
        REWRITE_TAC[WORD_ADD; SYM(WORD_REDUCE_CONV `word_neg(word 1):int64`)] THEN
        CONV_TAC WORD_RULE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word (1 * val (word (i + 1):int64) + 18446744073709551615)):int64,1)
                     (word pc,0x9d4) /\
      nonoverlapping (word_add a (word (1 * val (word (i + 1):int64) + 18446744073709551615)):int64,1)
                     (a,i) /\
      nonoverlapping (word_add a (word (1 * val (word (i + 1):int64) + 18446744073709551615)):int64,1)
                     (stk,64) /\
      nonoverlapping (word_add a (word (1 * val (word (i + 1):int64) + 18446744073709551615)):int64,1)
                     (word_add (word_add a (word i)) (word 1),r - (i + 1))`
     STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
    X86_STEPS_TAC CHACHA_EXEC (5--6) THEN ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[CHACHA_BNUM_1; READ_MEMORY_BYTES_BYTES8; VAL_EQ] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `word_sub (word (1 + r - (i + 1))) (word 1):int64 = word (r - (i + 1))`
     (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_BLAST;
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC]) THEN
      ASM_REWRITE_TAC[GSYM ADD_ASSOC];
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `r - (i + 1) < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
       [UNDISCH_TAC `r <= 64` THEN ARITH_TAC; UNDISCH_TAC `i < r` THEN ARITH_TAC]];
    (* Back to the top. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC CHACHA_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* Out of the loop. *)
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC CHACHA_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_REFL; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]]);;
(* ------------------------------------------------------------------------- *)
(* Fewer than 256 bytes left at 0x618: the whole blocks, then the bytes of   *)
(* the last one, to 0x9cf.                                                   *)
(* ------------------------------------------------------------------------- *)

(* The keystream's piece n of this group, as bytes from offset p on. *)
let chacha_kchunk n =
  let off = if n = 0 then `p:num` else mk_binop `(+):num->num->num` `p:num` (mk_small_numeral(16*n)) in
  mk_comb(`word:num->int128`, list_mk_comb(`chacha_bnum`, [`kf:num->byte`; off; `16`]));;

let chacha_tail_pieces =
  list_mk_conj(List.concat(map (fun j -> map (fun m ->
    mk_eq(mk_comb(chacha_piece_loc j m, `s:x86state`), chacha_kchunk (4*j+m))) (0--3)) (0--3)));;

let CHACHA_TAIL_GOAL =
  let tm = mk_imp(
   `aligned 16 (stk:int64) /\ 0 < n /\ n < 256 /\ val (a:int64) + n <= 2 EXP 64 /\
    nonoverlapping (a:int64,n) (stk,64) /\ nonoverlapping (a:int64,n) (word pc:int64,0x9d4) /\
    nonoverlapping (stk:int64,64) (word pc:int64,0x9d4)`,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj [
     `bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\ read RIP s = word(pc + 0x618) /\
      read RSP s = stk /\ read RSI s = a /\ read RDI s = a /\ read RDX s = word n /\
      read (memory :> bytes(a,n)) s = chacha_bnum mf p n`;
     chacha_tail_pieces]);
    `\s. read RIP s = word(pc + 0x9cf) /\ read RSP s = stk /\
         read (memory :> bytes(a:int64,n)) s = chacha_bnum (\j. word_xor (mf j) (kf j)) p n`;
    `MAYCHANGE [RIP; RAX; RCX; RSI; RDI; RDX; R10] ,, MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [ZMM2; ZMM6; ZMM7; ZMM11] ,,
     MAYCHANGE [memory :> bytes(a:int64,n); memory :> bytes(stk:int64,64)] ,, MAYCHANGE [events]`]) in
  list_mk_forall(frees tm, tm);;

(* The current state's number. *)
let chacha_state_num (asl,w) =
  let s = rand(snd(splitlist dest_imp w)) in int_of_string(String.sub (fst(dest_var s)) 1 (String.length(fst(dest_var s)) - 1));;

(* Arithmetic from only the assumptions about numbers, for goals whose
   assumptions also describe a whole machine state. *)
let CHACHA_ARITH_TAC =
  POP_ASSUM_LIST(fun ths ->
    let ok th =
      let c = concl th in
      let c = if is_neg c then rand c else c in
      (is_eq c || is_binary "<" c || is_binary "<=" c) &&
      type_of(lhand c) = `:num` && not(can (find_term (fun t -> name_of t = "read")) c) in
    MAP_EVERY MP_TAC (filter ok ths)) THEN ARITH_TAC;;

let CHACHA_SPLIT_TAC t =
  let w = mk_small_numeral(64*t) and q = mk_small_numeral(4*t) in
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `read (memory :> bytes(a,n)) s = x`) o concl)) THEN
  SUBGOAL_THEN (subst [w,`w:num`; q,`q:num`] `n = 16 * q + (n - w)`)
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_CHACHA_BNUM_SPLIT; READ_CHACHA_BNUM_CHUNKS] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))) THEN
  REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC;;

(* The goal's bytes(a,n) from whole pieces up to 64 t and the bytes past them. *)
let CHACHA_COMBINE_TAC t =
  let w = mk_small_numeral(64*t) and q = mk_small_numeral(4*t) in
  SUBGOAL_THEN (subst [w,`w:num`; q,`q:num`] `n = 16 * q + (n - w)`)
   (fun th -> GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [CHACHA_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_CHACHA_BNUM_SPLIT; READ_CHACHA_BNUM_CHUNKS] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; GSYM CHACHA_BNUM_XOR] THEN ASM_REWRITE_TAC[];;

let CHACHA_STACK_TAC t =
  let p = if t = 0 then `p:num` else mk_binop `(+):num->num->num` `p:num` (mk_small_numeral(64*t)) in
  SUBGOAL_THEN (subst [p,`q:num`] `read (memory :> bytes(stk:int64,64)) s = chacha_bnum kf q 64`) MP_TAC;;

(* Which of the code's length tests pass for case t. *)
let CHACHA_BOUNDS_TAC t =
  MAP_EVERY (fun c ->
    let tm = mk_comb(`(<) n`, mk_small_numeral c) in
    SUBGOAL_THEN (if 64*t + 64 <= c then tm else mk_neg tm) ASSUME_TAC THENL
     [CHACHA_ARITH_TAC; ALL_TAC]) [64; 128; 192];;

let CHACHA_TAIL_CASE1_TAC t =
  let w = mk_small_numeral(64*t) in
  let je = List.nth [0; 0x7ba; 0x877; 0x982] t in
  let wsub = subst [w,`w:num`] `val(word_sub (word n) (word w):int64) = n - w` in
  let wsub2 = subst [w,`w:num`] `word_sub (word n) (word w):int64 = word(n - w)` in
  let neq = subst [w,`w:num`] `n:num = w` in
  let nz = subst [w,`w:num`] `~(n - w = 0)` in
  CHACHA_BOUNDS_TAC t THEN
  ENSURES_INIT_TAC "s0" THEN CHACHA_SPLIT_TAC t THEN GHOST_YMMS_TAC THEN
  CHACHA_UNTIL_TAC je 1 THEN
  SUBGOAL_THEN wsub (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN CHACHA_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC neq THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    (fun g -> X86_STEPS_TAC CHACHA_EXEC [chacha_state_num g + 1] g) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE(subst [w,`w:num`; mk_small_numeral(4*t),`q:num`] `w = 16 * q`);
                READ_CHACHA_BNUM_CHUNKS] THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; GSYM CHACHA_BNUM_XOR] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let CHACHA_TAIL_CASE2_TAC t =
  let w = mk_small_numeral(64*t) in
  let wsub2 = subst [w,`w:num`] `word_sub (word n) (word w):int64 = word(n - w)` in
  let nz = subst [w,`w:num`] `~(n - w = 0)` in
  SUBGOAL_THEN nz ASSUME_TAC THENL [CHACHA_ARITH_TAC; ALL_TAC] THEN
  (fun g -> CHACHA_UNTIL_TAC 0x9b5 (chacha_state_num g + 1) g) THEN XMMS_OF_YMMS_TAC THEN
  SUBGOAL_THEN wsub2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN CHACHA_ARITH_TAC; ALL_TAC] THEN
  (fun g -> let s = rand(snd g) in
    (SUBGOAL_THEN (subst [s,`s:x86state`; (if t = 0 then `p:num` else mk_binop `(+):num->num->num` `p:num` w),`q:num`]
       `read (memory :> bytes(stk:int64,64)) s = chacha_bnum kf q 64`) ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 = 16 * 4`; READ_CHACHA_BNUM_CHUNKS] THEN
      CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
      REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]) g) THEN
  MP_TAC(SPECL [`pc:num`; `data:num`; `stk:int64`; subst [w,`w:num`] `word_add a (word w):int64`;
                subst [w,`w:num`] `n - w`; `mf:num->byte`; `kf:num->byte`;
                (if t = 0 then `p:num` else mk_binop `(+):num->num->num` `p:num` w)] CHACHA_BYTES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY CHACHA_ARITH_TAC THEN TRY NONOVERLAPPING_TAC THEN
    REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CHACHA_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN
  (fun g -> X86_BIGSTEP_TAC CHACHA_EXEC ("s"^string_of_int(chacha_state_num g + 1)) g) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CHACHA_COMBINE_TAC t;;


(* Fewer than 64 bytes: the byte loop alone, on block 0. *)
let CHACHA_TAIL_CASE0_TAC =
  CHACHA_BOUNDS_TAC 0 THEN
  ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN CHACHA_UNTIL_TAC 0x9b5 1 THEN XMMS_OF_YMMS_TAC THEN
  (fun g -> let s = rand(snd g) in
    (SUBGOAL_THEN (subst [s,`s:x86state`]
       `read (memory :> bytes(stk:int64,64)) s = chacha_bnum kf p 64`) ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 = 16 * 4`; READ_CHACHA_BNUM_CHUNKS] THEN
      CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
      REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN ASM_REWRITE_TAC[];
      ALL_TAC]) g) THEN
  MP_TAC(SPECL [`pc:num`; `data:num`; `stk:int64`; `a:int64`; `n:num`; `mf:num->byte`;
                `kf:num->byte`; `p:num`] CHACHA_BYTES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CHACHA_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN
  (fun g -> X86_BIGSTEP_TAC CHACHA_EXEC ("s"^string_of_int(chacha_state_num g + 1)) g) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let CHACHA_TAIL_CASE_TAC t = CHACHA_TAIL_CASE1_TAC t THEN CHACHA_TAIL_CASE2_TAC t;;

let CHACHA_TAIL = prove
 (CHACHA_TAIL_GOAL,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `192 <= n \/ 128 <= n /\ n < 192 \/ 64 <= n /\ n < 128 \/ n < 64` MP_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN TRY DISCH_TAC THENL
   [CHACHA_TAIL_CASE_TAC 3; CHACHA_TAIL_CASE_TAC 2; CHACHA_TAIL_CASE_TAC 1; CHACHA_TAIL_CASE0_TAC]);;
(* ------------------------------------------------------------------------- *)
(* The next group's rows from the stack copies, 0x100 to 0x163, the counter  *)
(* row 4 on.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* The code's RIP-relative operands: the instruction ending at pc + e with
   displacement data - (pc + c) addresses data + t. *)
let CHACHA_RIPREL = prove
 (`(!pc data e c t. riprel32_within_bounds (data + t) (pc + e) /\ c + t = e
        ==> word(val(word(pc + e):int64) + val(word_sx(iword(&data - (&pc + &c)):int32):int64)):int64 =
            word(data + t)) /\
   (!pc data e c t. riprel32_within_bounds (data + t) (pc + e) /\ e + c = t
        ==> word(val(word(pc + e):int64) + val(word_sx(iword(&data - (&pc + -- &c)):int32):int64)):int64 =
            word(data + t))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `e:num`; `0`; `data + t`] RIP_REL_ADDR_FOLD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  REPLICATE_TAC 4 AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

let chacha_reload_rows =
  let rd c = mk_icomb(`read:(x86state,int128)component->x86state->int128`, c) in
  let loc k = if k = 10 then rd `XMM6` else if k = 11 then rd `XMM7` else chacha_loc k in
  list_mk_conj(map (fun k -> mk_eq(mk_comb(loc k, `s:x86state`),
    chacha_lanes (fun j -> if k = 12 then list_mk_icomb "word_add" [chacha_el k (chacha_sv j); `word 4:int32`]
                           else chacha_el k (chacha_sv j)))) (0--15));;

let CHACHA_RELOAD_GOAL =
  let tm = mk_imp(
   `aligned 16 (stk:int64) /\ aligned 16 (word(data + 48):int64) /\
    riprel32_within_bounds (data + 48) (pc + 0x163)`,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj [
     `bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\ read RIP s = word(pc + 0x100) /\
      read RSP s = stk /\ read RCX s = word_add stk (word 256) /\
      read (memory :> bytes128 (word(data + 48))) s = word 0x00000004000000040000000400000004`;
     chacha_copies]);
    mk_abs(`s:x86state`, list_mk_conj [
     `read RIP s = word(pc + 0x163)`; chacha_reload_rows]);
    `MAYCHANGE [RIP] ,,
     MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
     MAYCHANGE [events]`]) in
  list_mk_forall(frees tm, tm);;

let CHACHA_RELOAD = prove
 (CHACHA_RELOAD_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `data:num`; `0x163`; `307`; `48`] (CONJUNCT1 CHACHA_RIPREL)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN CHACHA_UNTIL_TAC 0x163 1 THEN XMMS_OF_YMMS_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* Group g's four states and keystream pieces in the specification's terms.  *)
(* ------------------------------------------------------------------------- *)

(* State j of group g: block 4 g + j. *)
let chacha_gstate j =
  let b = if j = 0 then `4 * g` else mk_binop `(+):num->num->num` `4 * g` (mk_small_numeral j) in
  list_mk_comb(`chacha20_state`, [`key:byte list`;
    list_mk_icomb "word_add" [`counter:int32`; mk_comb(`word:num->int32`, b)]; `nonce:byte list`]);;

let chacha_ginst = map (fun j -> chacha_gstate j, chacha_sv j) (0--3);;

(* Piece n of group g's keystream as bytes from offset 256 g on. *)
let chacha_gchunk n =
  let off = if n = 0 then `256 * g` else mk_binop `(+):num->num->num` `256 * g` (mk_small_numeral(16*n)) in
  mk_comb(`word:num->int128`, list_mk_comb(`chacha_bnum`,
    [`chacha20_kbyte key counter nonce`; off; `16`]));;

let CHACHA_PIECE_SUM j m =
  let n = 4*j + m in
  let lhs = subst chacha_ginst (chacha_lanes (fun t -> chacha_sum (4*m+t) j)) in
  let q = if n = 0 then `16 * g` else mk_binop `(+):num->num->num` `16 * g` (mk_small_numeral n) in
  prove(mk_eq(lhs, chacha_gchunk n),
    SUBGOAL_THEN (mk_eq(rand(rator(rand(chacha_gchunk n))), mk_binop `( * ):num->num->num` `16` q))
     SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM CHACHA20_PIECE_CHUNK; chacha20_piece] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN (subst [q,`q:num`; (if j = 0 then `4 * g` else mk_binop `(+):num->num->num` `4 * g` (mk_small_numeral j)),`b:num`;
                         mk_small_numeral m,`m:num`] `q DIV 4 = b /\ q MOD 4 = m`)
     (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC DIVMOD_UNIQ THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[EL_CHACHA20_BLOCK_WORDS; ARITH]);;

let CHACHA_PIECE_SUMS =
  end_itlist CONJ (List.concat(map (fun j -> map (fun m -> CHACHA_PIECE_SUM j m) (0--3)) (0--3)));;
(* ------------------------------------------------------------------------- *)
(* One group of the main loop, 0x618 to 0x618, with more than 256 bytes left. *)
(* ------------------------------------------------------------------------- *)

let CHACHA_GROUP_HYPS =
  `aligned 16 (stk:int64) /\ aligned 16 (word(data + 48):int64) /\
   aligned 16 (word(data + 128):int64) /\ aligned 16 (word(data + 144):int64) /\
   riprel32_within_bounds (data + 48) (pc + 0x163) /\
   val (buf:int64) + n <= 2 EXP 64 /\ n < 2 EXP 64 /\
   nonoverlapping (stk,320) (word data:int64,192) /\ nonoverlapping (stk,320) (word pc:int64,0x9d4) /\
   nonoverlapping (buf,n) (stk,320) /\ nonoverlapping (buf,n) (word data:int64,192) /\
   nonoverlapping (buf,n) (word pc:int64,0x9d4)`;;

(* The state at 0x618 once group g's keystream is ready: the bytes before
   256 g are encrypted, the rest are still the message. *)
let chacha_group g =
  let inst = [g,`g:num`] in
  mk_abs(`s:x86state`, list_mk_conj [
   subst inst
   `bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\ read RIP s = word(pc + 0x618) /\
    read RSP s = stk /\ read RCX s = word_add stk (word 256) /\
    read R10 s = word(data + 128) /\ read R11 s = word(data + 144) /\
    read (memory :> bytes128 (word(data + 48))) s = word 0x00000004000000040000000400000004 /\
    read (memory :> bytes128 (word(data + 128))) s = word 0x0d0c0f0e09080b0a0504070601000302 /\
    read (memory :> bytes128 (word(data + 144))) s = word 0x0e0d0c0f0a09080b0605040702010003 /\
    read RSI s = word_add buf (word(256 * g)) /\ read RDI s = word_add buf (word(256 * g)) /\
    read RDX s = word(n - 256 * g) /\
    read (memory :> bytes(buf,256 * g)) s =
      chacha_bnum (\j. word_xor ((mf:num->byte) j) (chacha20_kbyte key counter nonce j)) 0 (256 * g) /\
    read (memory :> bytes(word_add buf (word(256 * g)),n - 256 * g)) s =
      chacha_bnum mf (256 * g) (n - 256 * g)`;
   subst inst (list_mk_conj(List.concat(map (fun j -> map (fun m ->
     mk_eq(mk_comb(chacha_piece_loc j m, `s:x86state`), chacha_gchunk (4*j+m))) (0--3)) (0--3))));
   subst inst (list_mk_conj(map (fun k -> mk_eq(mk_comb(chacha_copy_loc k, `s:x86state`),
     chacha_lanes (fun j -> chacha_el k (chacha_gstate j)))) (0--15)))]);;

let CHACHA_GROUP_FRAME =
  `MAYCHANGE [RIP; RAX; RCX; RSI; RDI; RDX; R10] ,, MAYCHANGE SOME_FLAGS ,,
   MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
              ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
   MAYCHANGE [memory :> bytes(buf:int64,n); memory :> bytes(stk:int64,320)] ,,
   MAYCHANGE [events]`;;

let CHACHA_STEP_GOAL =
  let tm = mk_imp(mk_conj(CHACHA_GROUP_HYPS, `256 * g + 256 < n`),
   list_mk_icomb "ensures" [`x86`; chacha_group `g:num`; chacha_group `g + 1`; CHACHA_GROUP_FRAME]) in
  list_mk_forall(frees tm, tm);;

let chacha_mchunk n =
  let off = if n = 0 then `256 * g` else mk_binop `(+):num->num->num` `256 * g` (mk_small_numeral(16*n)) in
  mk_comb(`word:num->int128`, list_mk_comb(`chacha_bnum`, [`mf:num->byte`; off; `16`]));;

let CHACHA_XOR256_AT =
  INST ([`word_add buf (word(256 * g)):int64`,`a:int64`; `word(n - 256 * g):int64`,`d:int64`] @
        map (fun n -> chacha_gchunk n, chacha_kv n) (0--15) @
        map (fun n -> chacha_mchunk n, chacha_cv n) (0--15)) (SPEC_ALL CHACHA_XOR256);;

let chacha_next = map (fun j -> subst [`g + 1`,`g:num`] (chacha_gstate j), chacha_sv j) (0--3);;

let CHACHA_NEXT_COUNTERS = prove
 (`4 * g + 4 = 4 * (g + 1) /\ (4 * g + 1) + 4 = 4 * (g + 1) + 1 /\
   (4 * g + 2) + 4 = 4 * (g + 1) + 2 /\ (4 * g + 3) + 4 = 4 * (g + 1) + 3`,
  ARITH_TAC);;

(* Group g's rows, the counter row 4 on, as group g + 1's. *)
let CHACHA_NEXT_LANES =
  let old = map (fun j -> chacha_gstate j, chacha_sv j) (0--3) in
  let tm = list_mk_conj(map (fun k ->
    mk_eq(subst old (chacha_lanes (fun j ->
            if k = 12 then list_mk_icomb "word_add" [chacha_el k (chacha_sv j); `word 4:int32`]
            else chacha_el k (chacha_sv j))),
          subst chacha_next (chacha_lanes (fun j -> chacha_el k (chacha_sv j))))) (0--15)) in
  prove(tm, REWRITE_TAC[CHACHA20_STATE_EXPLICIT] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
            REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; CHACHA_NEXT_COUNTERS]);;

(* Replaces whole values of the state's components by the equations' right
   sides, leaving everything else alone. *)
let CHACHA_ASM_RHS_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read c (s:x86state):A`) (lhs c)
    then try CONV_RULE(RAND_CONV(GEN_REWRITE_CONV I ths)) th with Failure _ -> th
    else th);;

let READ_CHACHA_BNUM_256 = CONV_RULE NUM_REDUCE_CONV (SPEC `16` READ_CHACHA_BNUM_CHUNKS);;

let CHACHA_STEP = prove
 (CHACHA_STEP_GOAL,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  (* The group's 256 bytes as 16 pieces. *)
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read (memory :> bytes(word_add buf (word(256 * g)),n - 256 * g)) s = x`) o concl)) THEN
  SUBGOAL_THEN `n - 256 * g = 16 * 16 + (n - 256 * g - 256)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [CHACHA_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_CHACHA_BNUM_SPLIT; READ_CHACHA_BNUM_CHUNKS] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))) THEN
  REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  (* Their XOR, and back to the loop's top. *)
  SUBGOAL_THEN `val(word(n - 256 * g):int64) = n - 256 * g` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN CHACHA_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[WORD_ADD_0] CHACHA_XOR256_AT) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY CHACHA_ARITH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN X86_BIGSTEP_TAC CHACHA_EXEC "s1" THEN
  SUBGOAL_THEN `~(n - 256 * g = 256)` ASSUME_TAC THENL [CHACHA_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC CHACHA_EXEC [2] THEN
  (* The next group's rows, and its four blocks. *)
  MP_TAC(INST (map (fun j -> chacha_gstate j, chacha_sv j) (0--3)) (SPEC_ALL CHACHA_RELOAD)) THEN
  ASM_REWRITE_TAC[] THEN X86_BIGSTEP_TAC CHACHA_EXEC "s3" THEN
  CHACHA_ASM_RHS_TAC (CONJUNCTS CHACHA_NEXT_LANES) THEN
  MP_TAC(INST ([`word(data + 128):int64`,`rp10:int64`; `word(data + 144):int64`,`rp11:int64`] @
               chacha_next) (SPEC_ALL CHACHA_CORE)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN X86_BIGSTEP_TAC CHACHA_EXEC "s4" THEN
  (* Group g + 1's state. *)
  ENSURES_FINAL_STATE_TAC THEN
  CHACHA_ASM_RHS_TAC(CONJUNCTS(INST [`g + 1`,`g:num`] CHACHA_PIECE_SUMS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `256 * (g + 1) = 256 * g + 256`;
              ARITH_RULE `n - (256 * g + 256) = n - 256 * g - 256`] THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN CHACHA_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_CHACHA_BNUM_SPLIT] THEN ASM_REWRITE_TAC[READ_CHACHA_BNUM_256] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; GSYM CHACHA_BNUM_XOR] THEN ASM_REWRITE_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The last group, 256 bytes or fewer, 0x618 to 0x9cf.                        *)
(* ------------------------------------------------------------------------- *)

let CHACHA_DONE =
  `\s. read RIP s = word(pc + 0x9cf) /\ read RSP s = stk /\
       read (memory :> bytes(buf,n)) s =
       chacha_bnum (\j. word_xor ((mf:num->byte) j) (chacha20_kbyte key counter nonce j)) 0 n`;;

let CHACHA_LAST_GOAL =
  let tm = mk_imp(mk_conj(CHACHA_GROUP_HYPS, `256 * g < n /\ n <= 256 * g + 256`),
   list_mk_icomb "ensures" [`x86`; chacha_group `g:num`; CHACHA_DONE; CHACHA_GROUP_FRAME]) in
  list_mk_forall(frees tm, tm);;

let CHACHA_TAIL_AT =
  INST [`word_add buf (word(256 * g)):int64`,`a:int64`; `n - 256 * g`,`n:num`; `256 * g`,`p:num`;
        `chacha20_kbyte key counter nonce`,`kf:num->byte`] (SPEC_ALL CHACHA_TAIL);;

let VAL_CHACHA_GROUP = prove
 (`!buf:int64 n g. val buf + n <= 2 EXP 64 /\ 256 * g < n
                   ==> val(word_add buf (word(256 * g))) + (n - 256 * g) <= 2 EXP 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `256 * g < 2 EXP 64` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`val(buf:int64) + 256 * g`; `2 EXP 64`] MOD_LE) THEN ASM_ARITH_TAC);;

let CHACHA_LAST = prove
 (CHACHA_LAST_GOAL,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`buf:int64`; `n:num`; `g:num`] VAL_CHACHA_GROUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `n = 256 * g + 256` THENL
   [(* A whole group: its XOR, then out of the loop. *)
    SUBGOAL_THEN `n - 256 * g = 256` ASSUME_TAC THENL [CHACHA_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `read (memory :> bytes(word_add buf (word(256 * g)),n - 256 * g)) s = x`) o concl)) THEN
    ASM_REWRITE_TAC[READ_CHACHA_BNUM_256] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word(n - 256 * g):int64) = n - 256 * g` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[WORD_ADD_0] CHACHA_XOR256_AT) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY CHACHA_ARITH_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    ASM_REWRITE_TAC[SOME_FLAGS] THEN X86_BIGSTEP_TAC CHACHA_EXEC "s1" THEN
    X86_STEPS_TAC CHACHA_EXEC (2--3) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_CHACHA_BNUM_SPLIT; ADD_CLAUSES] THEN ASM_REWRITE_TAC[READ_CHACHA_BNUM_256] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; GSYM CHACHA_BNUM_XOR] THEN ASM_REWRITE_TAC[ETA_AX];
    (* Fewer: the tail. *)
    ENSURES_INIT_TAC "s0" THEN
    MP_TAC CHACHA_TAIL_AT THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY CHACHA_ARITH_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SOME_FLAGS] THEN X86_BIGSTEP_TAC CHACHA_EXEC "s1" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `n = 256 * g + (n - 256 * g)`
     (fun th -> GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [th]) THENL
     [CHACHA_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[READ_CHACHA_BNUM_SPLIT; ADD_CLAUSES] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main loop, from group g's 0x618 to the byte loop's exit at 0x9cf.     *)
(* ------------------------------------------------------------------------- *)

let CHACHA_LOOP_GOAL =
  let tm = mk_imp(mk_conj(CHACHA_GROUP_HYPS, `256 * g < n /\ n <= 256 * (g + k + 1)`),
   list_mk_icomb "ensures" [`x86`; chacha_group `g:num`; CHACHA_DONE; CHACHA_GROUP_FRAME]) in
  let fv = subtract (frees tm) [`k:num`; `g:num`] in
  mk_forall(`k:num`, list_mk_forall(fv @ [`g:num`], tm));;

let CHACHA_LOOP = prove
 (CHACHA_LOOP_GOAL,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `n <= 256 * g + 256` THEN
  TRY(MATCH_MP_TAC CHACHA_LAST THEN ASM_REWRITE_TAC[] THEN NO_TAC) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC (chacha_group `g + 1`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SOME_FLAGS] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC CHACHA_STEP THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The inputs: byte lists in memory as chacha_bnum, and the table.           *)
(* ------------------------------------------------------------------------- *)

let CHACHA_BNUM_LIST = prove
 (`!l f p. (!i. i < LENGTH l ==> f(p + i) = EL i l)
           ==> chacha_bnum f p (LENGTH l) = num_of_bytelist l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; chacha_bnum; num_of_bytelist] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; ADD_CLAUSES; EL; HD] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
  ASM_REWRITE_TAC[LT_SUC; EL; TL; ARITH_RULE `(p + 1) + i = p + SUC i`]);;

let EL_SUB_LIST_CHACHA = prove
 (`!(l:A list) p k i. i < k /\ p + k <= LENGTH l ==> EL i (SUB_LIST(p,k) l) = EL (p + i) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH] THENL [ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[LT] THEN INDUCT_TAC THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; ADD_CLAUSES; EL; HD; TL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `k:num`; `i:num`]) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; ADD_CLAUSES; EL; TL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHACHA_BNUM_SUB_LIST = prove
 (`!l p k. p + k <= LENGTH l
           ==> num_of_bytelist(SUB_LIST(p,k) l) = chacha_bnum (\i. EL i l) p k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`SUB_LIST(p,k) (l:byte list)`; `\i. EL i (l:byte list)`; `p:num`]
         CHACHA_BNUM_LIST) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  SUBGOAL_THEN `MIN k (LENGTH(l:byte list) - p) = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EL_SUB_LIST_CHACHA THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

let CHACHA_BNUM_BYTELIST = prove
 (`!l. num_of_bytelist l = chacha_bnum (\i. EL i l) 0 (LENGTH l)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CHACHA_BNUM_LIST THEN
  REWRITE_TAC[ADD_CLAUSES]);;

(* RFC 8439's initial state with the key and nonce words as chacha_bnum. *)
let CHACHA20_STATE_BNUM =
  let th = SPEC_ALL CHACHA20_STATE_EXPLICIT in
  let pat = `num_of_bytelist(SUB_LIST(p,4) (l:byte list))` in
  let subs = map (fun t -> let i = term_match [] pat t in
                    instantiate i `chacha_bnum (\i. EL i (l:byte list)) p 4`, t)
                 (find_terms (can (term_match [] pat)) (rand(concl th))) in
  let tm = mk_imp(`LENGTH(key:byte list) = 32 /\ LENGTH(nonce:byte list) = 12`,
                  mk_eq(lhs(concl th), subst subs (rand(concl th)))) in
  prove(list_mk_forall(frees tm, tm),
    REPEAT STRIP_TAC THEN REWRITE_TAC[CHACHA20_STATE_EXPLICIT] THEN
    ASM_SIMP_TAC[CHACHA_BNUM_SUB_LIST; ARITH]);;

let READ_BYTES32_VAL = prove
 (`!(a:int64) s x. read (memory :> bytes32 a) s = x <=>
                   read (memory :> bytes(a,4)) s = val(x:int32)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES32_WBYTES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_CHACHA_BNUM_4 = prove
 (`!f p (a:int64) s.
        read (memory :> bytes(a,4)) s = chacha_bnum f p 4 <=>
        read (memory :> bytes32 a) s = word(chacha_bnum f p 4)`,
  REWRITE_TAC[READ_BYTES32_VAL] THEN REPEAT GEN_TAC THEN
  SIMP_TAC[VAL_WORD; DIMINDEX_32; MOD_LT; CHACHA_BNUM_BOUND;
           ARITH_RULE `2 EXP 32 = 2 EXP (8 * 4)`]);;

let READ_CHACHA_BNUM_WORDS = prove
 (`!m f p (a:int64) s.
        read (memory :> bytes(a,4 * m)) s = chacha_bnum f p (4 * m) <=>
        !q. q < m ==> read (memory :> bytes32(word_add a (word(4 * q)))) s =
                      word(chacha_bnum f (p + 4 * q) 4)`,
  INDUCT_TAC THEN REWRITE_TAC[chacha_bnum; CONJUNCT1 LT; MULT_CLAUSES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4 * m + 4 = 4 + 4 * m`; READ_CHACHA_BNUM_SPLIT] THEN
  ASM_REWRITE_TAC[READ_CHACHA_BNUM_4; FORALL_LT_SUC_SPLIT] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(p + 4) + 4 * i = p + 4 * SUC i`;
              ARITH_RULE `4 + 4 * i = 4 * SUC i`]);;

(* The table's 16-byte constants the code loads. *)
let chacha20_ssse3_4x_data = last chacha20_ssse3_4x_tables;;

let CHACHA_DATA_FACTS =
  let th = prove
   (`!s k. bytes_loaded s (word (k + 0)) chacha20_ssse3_4x_data
           ==> read (memory :> bytes128 (word(k + 32))) s = word 0x00000003000000020000000100000000 /\
               read (memory :> bytes128 (word(k + 48))) s = word 0x00000004000000040000000400000004 /\
               read (memory :> bytes128 (word(k + 128))) s = word 0x0d0c0f0e09080b0a0504070601000302 /\
               read (memory :> bytes128 (word(k + 144))) s = word 0x0e0d0c0f0a09080b0605040702010003 /\
               read (memory :> bytes128 (word(k + 160))) s = word 0x6b20657479622d323320646e61707865`,
    REPEAT GEN_TAC THEN REWRITE_TAC[chacha20_ssse3_4x_data] THEN
    CONV_TAC(LAND_CONV DATA64_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT); GSYM WORD_ADD] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV) in
  GEN_ALL(REWRITE_RULE[ADD_CLAUSES] th);;

let READ_BYTES128_WORDS = prove
 (`!(a:int64) s. read (memory :> bytes128 a) s =
     word_join (word_join (read (memory :> bytes32 (word_add a (word 12))) s)
                          (read (memory :> bytes32 (word_add a (word 8))) s):int64)
               (word_join (read (memory :> bytes32 (word_add a (word 4))) s)
                          (read (memory :> bytes32 a) s):int64)`,
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT);
              CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[]);;

let READ_MEMORY_BYTES_0 = prove
 (`!(a:int64) s. read (memory :> bytes(a,0)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]);;

(* The 4 m bytes at an address in the assumptions as m words. *)
let CHACHA_WORDS_TAC t m =
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] t) o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE (mk_eq(mk_small_numeral(4*m), mk_binop `( * ):num->num->num` `4` (mk_small_numeral m)))] THEN
  REWRITE_TAC[READ_CHACHA_BNUM_WORDS] THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN STRIP_TAC;;

(* The frame 328 bytes below the entry's stack pointer is 16-byte aligned. *)
let CHACHA_ALIGNED_TAC =
  REWRITE_TAC[WORD_ADD; WORD_RULE `word_sub (x:int64) (word 328) = word_sub (word_add x (word 8)) (word 336)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN ASM_REWRITE_TAC[];;

(* The inputs' lengths into their reads, keeping the lengths themselves. *)
let CHACHA_LEN_TAC =
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) && can (term_match [] `LENGTH(l:A list)`) (lhs(concl th)) then th
    else REWRITE_RULE[ASSUME `LENGTH(key:byte list) = 32`; ASSUME `LENGTH(nonce:byte list) = 12`;
                      ASSUME `LENGTH(msg:byte list) = n`] th);;

(* The first group's four states, blocks counter to counter + 3. *)
let chacha_sts = [`chacha20_state key counter nonce`;
  `chacha20_state key (word_add counter (word 1)) nonce`;
  `chacha20_state key (word_add counter (word 2)) nonce`;
  `chacha20_state key (word_add counter (word 3)) nonce`];;

let CHACHA_CORE_0 =
  INST ([`word(data + 128):int64`,`rp10:int64`; `word(data + 144):int64`,`rp11:int64`;
         `word_sub stackpointer (word 328):int64`,`stk:int64`] @
        zip chacha_sts (map chacha_sv (0--3))) (SPEC_ALL CHACHA_CORE);;

(* A conversion on an ensures theorem's precondition. *)
let CHACHA_PRE_CONV conv = RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV conv)));;

(* Group 0's terms in their simplest form. *)
let CHACHA_G0_RULE th =
  REWRITE_RULE[SUB_0; WORD_ADD_0; ADD_CLAUSES; READ_MEMORY_BYTES_0; CONJUNCT1 chacha_bnum;
               GSYM(NUM_REDUCE_CONV `2 EXP 64`)]
    (CONV_RULE NUM_REDUCE_CONV (INST [`0`,`g:num`] th));;

let CHACHA_LOOP_0 = CHACHA_G0_RULE
  (INST [`n:num`,`k:num`; `\i. EL i (msg:byte list)`,`mf:num->byte`;
         `word_sub stackpointer (word 328):int64`,`stk:int64`] (SPEC_ALL CHACHA_LOOP));;

let CHACHA_PIECE_SUMS_0 = CONJUNCTS(CHACHA_G0_RULE CHACHA_PIECE_SUMS);;

(* ------------------------------------------------------------------------- *)
(* The whole routine, as rind calls it: in place, on a nonempty buffer.      *)
(* ------------------------------------------------------------------------- *)

let CHACHA20_CTR32_SSSE3_4X_SUBROUTINE_GOAL =
 `!buf n keyp cnp key counter nonce msg pc data stackpointer returnaddress.
   0 < n /\ n < 2 EXP 64 /\ val buf + n <= 2 EXP 64 /\
   aligned 16 (word_add stackpointer (word 8)) /\ aligned 16 (word data:int64) /\
   riprel32_within_bounds (data + 160) (pc + 0x13) /\
   riprel32_within_bounds (data + 128) (pc + 0x31) /\
   riprel32_within_bounds (data + 144) (pc + 0x38) /\
   riprel32_within_bounds (data + 32) (pc + 0xd6) /\
   riprel32_within_bounds (data + 48) (pc + 0x163) /\
   ALL (nonoverlapping (word_sub stackpointer (word 328),336))
       [(word pc,0x9d4); (word data,192); (buf,n)] /\
   ALL (nonoverlapping (buf,n)) [(word pc,0x9d4); (word data,192)]
   ==> ensures x86
        (\s. bytes_loaded s (word pc) (chacha20_ssse3_4x_mc pc data) /\
             bytes_loaded s (word data) chacha20_ssse3_4x_data /\
             read RIP s = word pc /\ read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [buf; buf; word n; keyp; cnp] s /\
             read (memory :> bytelist(keyp,32)) s = key /\
             read (memory :> bytes32 cnp) s = counter /\
             read (memory :> bytelist(word_add cnp (word 4),12)) s = nonce /\
             read (memory :> bytelist(buf,n)) s = msg)
        (\s. read RIP s = returnaddress /\ read RSP s = word_add stackpointer (word 8) /\
             read (memory :> bytelist(buf,n)) s = chacha20_encrypt key counter nonce msg)
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes(buf,n);
                    memory :> bytes(word_sub stackpointer (word 328),320)] ,,
         MAYCHANGE [events])`;;

let CHACHA20_CTR32_SSSE3_4X_SUBROUTINE_CORRECT = prove
 (CHACHA20_CTR32_SSSE3_4X_SUBROUTINE_GOAL,
  REWRITE_TAC[ALL; C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES; CHACHA_BNUM_BYTELIST] THEN
  ENSURES_INIT_TAC "s0" THEN
  (* The key and nonce as words, and the code's 16-byte loads of them. *)
  CHACHA_LEN_TAC THEN
  CHACHA_WORDS_TAC `read (memory :> bytes (keyp,32)) s0 = x` 8 THEN
  CHACHA_WORDS_TAC `read (memory :> bytes (word_add cnp (word 4),12)) s0 = x` 3 THEN
  MAP_EVERY (fun a -> MP_TAC(SPECL [a; `s0:x86state`] READ_BYTES128_WORDS) THEN
                      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                      CONV_TAC(LAND_CONV(DEPTH_CONV NUM_ADD_CONV)) THEN
                      ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
    [`keyp:int64`; `word_add keyp (word 16):int64`; `cnp:int64`] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (can (term_match []
    `read (memory :> bytes32 a) s0 = x`) o concl))) THEN
  (* The table's constants, the RIP-relative operands, and the alignments. *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CHACHA_DATA_FACTS) THEN
  MAP_EVERY (fun (th,e,c,t) -> MP_TAC(SPECL [`pc:num`; `data:num`; e; c; t] th) THEN
                               ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; DISCH_TAC])
   [CONJUNCT2 CHACHA_RIPREL, `0x13`, `141`, `160`; CONJUNCT2 CHACHA_RIPREL, `0x31`, `79`, `128`;
    CONJUNCT2 CHACHA_RIPREL, `0x38`, `88`, `144`; CONJUNCT1 CHACHA_RIPREL, `0xd6`, `182`, `32`] THEN
  SUBGOAL_THEN `aligned 16 (word(data + 32):int64) /\ aligned 16 (word(data + 48):int64) /\
                aligned 16 (word(data + 128):int64) /\ aligned 16 (word(data + 144):int64) /\
                aligned 16 (word(data + 160):int64) /\
                aligned 16 (word_sub stackpointer (word 328):int64)`
   STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN CHACHA_ALIGNED_TAC; ALL_TAC] THEN
  (* The rows and their stack copies, then group 0's rounds. *)
  GHOST_YMMS_TAC THEN X86_XSTEPS_TAC CHACHA_EXEC [1] THEN CHACHA_UNTIL_TAC 0x163 2 THEN
  XMMS_OF_YMMS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  MP_TAC(CONV_RULE(CHACHA_PRE_CONV(
    REWRITE_CONV[GEN `counter:int32` (MP (SPEC_ALL CHACHA20_STATE_BNUM)
                   (CONJ (ASSUME `LENGTH(key:byte list) = 32`) (ASSUME `LENGTH(nonce:byte list) = 12`)))] THENC
    DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV)) CHACHA_CORE_0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN X86_BIGSTEP_TAC CHACHA_EXEC "s43" THEN
  (* The main loop from group 0. *)
  CHACHA_ASM_RHS_TAC CHACHA_PIECE_SUMS_0 THEN MP_TAC CHACHA_LOOP_0 THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY CHACHA_ARITH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN X86_BIGSTEP_TAC CHACHA_EXEC "s44" THEN
  (* The return, and RFC 8439's encryption byte by byte. *)
  X86_STEPS_TAC CHACHA_EXEC (45--46) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (chacha20_encrypt key counter nonce msg) = n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[chacha20_encrypt; LENGTH_MAP2_LE]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC CHACHA_BNUM_EQ THEN REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CHACHA20_ENCRYPT_BYTE; chacha20_kbyte]);;
