(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-CBC on AES-NI on x86_64, both directions, as rind's build emits it.   *)
(* ========================================================================= *)

needs "x86_64/aes_hw_spec.ml";;

(* admin/prove writes the function's object, as rind's release build emits
   it, to x86_64/aes_hw_cbc_encrypt.o: its whole section as .text, which has
   no relocations. The definition fails unless its instructions are these. *)
let aes_hw_cbc_encrypt_mc = define_assert_from_elf
  "aes_hw_cbc_encrypt_mc" "x86_64/aes_hw_cbc_encrypt.o"
[
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x0f; 0x84; 0x67; 0x08; 0x00; 0x00;
                           (* JE (Imm32 (word 2151)) *)
  0x44; 0x8b; 0x91; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Memop Doubleword (%% (rcx,240))) *)
  0x49; 0x89; 0xcb;        (* MOV (% r11) (% rcx) *)
  0x45; 0x85; 0xc9;        (* TEST (% r9d) (% r9d) *)
  0x0f; 0x84; 0xa4; 0x00; 0x00; 0x00;
                           (* JE (Imm32 (word 164)) *)
  0x41; 0x0f; 0x10; 0x10;  (* MOVUPS (%_% xmm2) (Memop Word128 (%% (r8,0))) *)
  0x44; 0x89; 0xd0;        (* MOV (% eax) (% r10d) *)
  0x48; 0x83; 0xfa; 0x10;  (* CMP (% rdx) (Imm8 (word 16)) *)
  0x72; 0x66;              (* JB (Imm8 (word 102)) *)
  0x48; 0x83; 0xea; 0x10;  (* SUB (% rdx) (Imm8 (word 16)) *)
  0xeb; 0x01;              (* JMP (Imm8 (word 1)) *)
  0x90;                    (* NOP *)
  0x0f; 0x10; 0x1f;        (* MOVUPS (%_% xmm3) (Memop Word128 (%% (rdi,0))) *)
  0x48; 0x8d; 0x7f; 0x10;  (* LEA (% rdi) (%% (rdi,16)) *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0x0f; 0x10; 0x49; 0x10;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x0f; 0x57; 0xd8;        (* PXOR (%_% xmm3) (%_% xmm0) *)
  0x48; 0x8d; 0x49; 0x20;  (* LEA (% rcx) (%% (rcx,32)) *)
  0x0f; 0x57; 0xd3;        (* PXOR (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0x38; 0xdc; 0xd1;
                           (* AESENC (%_% xmm2) (%_% xmm1) *)
  0xff; 0xc8;              (* DEC (% eax) *)
  0x0f; 0x10; 0x09;        (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,0))) *)
  0x48; 0x8d; 0x49; 0x10;  (* LEA (% rcx) (%% (rcx,16)) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x66; 0x0f; 0x38; 0xdd; 0xd1;
                           (* AESENCLAST (%_% xmm2) (%_% xmm1) *)
  0x44; 0x89; 0xd0;        (* MOV (% eax) (% r10d) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x0f; 0x11; 0x16;        (* MOVUPS (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x48; 0x8d; 0x76; 0x10;  (* LEA (% rsi) (%% (rsi,16)) *)
  0x48; 0x83; 0xea; 0x10;  (* SUB (% rdx) (Imm8 (word 16)) *)
  0x73; 0xc0;              (* JAE (Imm8 (word 192)) *)
  0x48; 0x83; 0xc2; 0x10;  (* ADD (% rdx) (Imm8 (word 16)) *)
  0x75; 0x19;              (* JNE (Imm8 (word 25)) *)
  0x66; 0x0f; 0xef; 0xc0;  (* PXOR (%_% xmm0) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xc9;  (* PXOR (%_% xmm1) (%_% xmm1) *)
  0x41; 0x0f; 0x11; 0x10;  (* MOVUPS (Memop Word128 (%% (r8,0))) (%_% xmm2) *)
  0x66; 0x0f; 0xef; 0xd2;  (* PXOR (%_% xmm2) (%_% xmm2) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0xe9; 0xe1; 0x07; 0x00; 0x00;
                           (* JMP (Imm32 (word 2017)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x87; 0xf7;        (* XCHG (% rsi) (% rdi) *)
  0xf3; 0xa4;              (* MOVSB true (% rdi) (% rsi) (% rcx) *)
  0x66; 0x90;              (* NOP *)
  0xb9; 0x10; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 16)) *)
  0x48; 0x29; 0xd1;        (* SUB (% rcx) (% rdx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0xaa;              (* STOSB true *)
  0x66; 0x90;              (* NOP *)
  0x48; 0x8d; 0x7f; 0xf0;  (* LEA (% rdi) (%% (rdi,18446744073709551600)) *)
  0x44; 0x89; 0xd0;        (* MOV (% eax) (% r10d) *)
  0x48; 0x89; 0xfe;        (* MOV (% rsi) (% rdi) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0xe9; 0x74; 0xff; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294967156)) *)
  0x0f; 0x1f; 0x40; 0x00;  (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x48; 0x83; 0xfa; 0x10;  (* CMP (% rdx) (Imm8 (word 16)) *)
  0x75; 0x5a;              (* JNE (Imm8 (word 90)) *)
  0xf3; 0x0f; 0x6f; 0x17;  (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rdi,0))) *)
  0xf3; 0x41; 0x0f; 0x6f; 0x18;
                           (* MOVDQU (%_% xmm3) (Memop Word128 (%% (r8,0))) *)
  0x66; 0x0f; 0x6f; 0xe2;  (* MOVDQA (%_% xmm4) (%_% xmm2) *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0x0f; 0x10; 0x49; 0x10;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x48; 0x8d; 0x49; 0x20;  (* LEA (% rcx) (%% (rcx,32)) *)
  0x0f; 0x57; 0xd0;        (* PXOR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x41; 0xff; 0xca;        (* DEC (% r10d) *)
  0x0f; 0x10; 0x09;        (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,0))) *)
  0x48; 0x8d; 0x49; 0x10;  (* LEA (% rcx) (%% (rcx,16)) *)
  0x75; 0xef;              (* JNE (Imm8 (word 239)) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd1;
                           (* AESDECLAST (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0xef; 0xc0;  (* PXOR (%_% xmm0) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xc9;  (* PXOR (%_% xmm1) (%_% xmm1) *)
  0xf3; 0x41; 0x0f; 0x7f; 0x20;
                           (* MOVDQU (Memop Word128 (%% (r8,0))) (%_% xmm4) *)
  0x0f; 0x57; 0xd3;        (* PXOR (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x0f; 0x11; 0x16;        (* MOVUPS (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x0f; 0xef; 0xd2;  (* PXOR (%_% xmm2) (%_% xmm2) *)
  0xe9; 0x59; 0x07; 0x00; 0x00;
                           (* JMP (Imm32 (word 1881)) *)
  0x66; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x4c; 0x8d; 0x1c; 0x24;  (* LEA (% r11) (%% (rsp,0)) *)
  0x55;                    (* PUSH (% rbp) *)
  0x48; 0x83; 0xec; 0x10;  (* SUB (% rsp) (Imm8 (word 16)) *)
  0x48; 0x83; 0xe4; 0xf0;  (* AND (% rsp) (Imm8 (word 240)) *)
  0x48; 0x89; 0xcd;        (* MOV (% rbp) (% rcx) *)
  0x45; 0x0f; 0x10; 0x10;  (* MOVUPS (%_% xmm10) (Memop Word128 (%% (r8,0))) *)
  0x44; 0x89; 0xd0;        (* MOV (% eax) (% r10d) *)
  0x48; 0x83; 0xfa; 0x50;  (* CMP (% rdx) (Imm8 (word 80)) *)
  0x0f; 0x86; 0x13; 0x05; 0x00; 0x00;
                           (* JBE (Imm32 (word 1299)) *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0xf3; 0x0f; 0x6f; 0x17;  (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rdi,0))) *)
  0xf3; 0x0f; 0x6f; 0x5f; 0x10;
                           (* MOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,16))) *)
  0x66; 0x44; 0x0f; 0x6f; 0xda;
                           (* MOVDQA (%_% xmm11) (%_% xmm2) *)
  0xf3; 0x0f; 0x6f; 0x67; 0x20;
                           (* MOVDQU (%_% xmm4) (Memop Word128 (%% (rdi,32))) *)
  0x66; 0x44; 0x0f; 0x6f; 0xe3;
                           (* MOVDQA (%_% xmm12) (%_% xmm3) *)
  0xf3; 0x0f; 0x6f; 0x6f; 0x30;
                           (* MOVDQU (%_% xmm5) (Memop Word128 (%% (rdi,48))) *)
  0x66; 0x44; 0x0f; 0x6f; 0xec;
                           (* MOVDQA (%_% xmm13) (%_% xmm4) *)
  0xf3; 0x0f; 0x6f; 0x77; 0x40;
                           (* MOVDQU (%_% xmm6) (Memop Word128 (%% (rdi,64))) *)
  0x66; 0x44; 0x0f; 0x6f; 0xf5;
                           (* MOVDQA (%_% xmm14) (%_% xmm5) *)
  0xf3; 0x0f; 0x6f; 0x7f; 0x50;
                           (* MOVDQU (%_% xmm7) (Memop Word128 (%% (rdi,80))) *)
  0x66; 0x44; 0x0f; 0x6f; 0xfe;
                           (* MOVDQA (%_% xmm15) (%_% xmm6) *)
  0x48; 0x83; 0xfa; 0x70;  (* CMP (% rdx) (Imm8 (word 112)) *)
  0x0f; 0x86; 0xe2; 0x03; 0x00; 0x00;
                           (* JBE (Imm32 (word 994)) *)
  0x48; 0x83; 0xea; 0x70;  (* SUB (% rdx) (Imm8 (word 112)) *)
  0x48; 0x8d; 0x49; 0x70;  (* LEA (% rcx) (%% (rcx,112)) *)
  0xeb; 0x0a;              (* JMP (Imm8 (word 10)) *)
  0x66; 0x90;              (* NOP *)
  0x44; 0x0f; 0x11; 0x0e;  (* MOVUPS (Memop Word128 (%% (rsi,0))) (%_% xmm9) *)
  0x48; 0x8d; 0x76; 0x10;  (* LEA (% rsi) (%% (rsi,16)) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x47; 0x60;
                           (* MOVDQU (%_% xmm8) (Memop Word128 (%% (rdi,96))) *)
  0x66; 0x0f; 0xef; 0xd0;  (* PXOR (%_% xmm2) (%_% xmm0) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x4f; 0x70;
                           (* MOVDQU (%_% xmm9) (Memop Word128 (%% (rdi,112))) *)
  0x66; 0x0f; 0xef; 0xd8;  (* PXOR (%_% xmm3) (%_% xmm0) *)
  0x0f; 0x10; 0x49; 0xa0;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,18446744073709551520))) *)
  0x66; 0x0f; 0xef; 0xe0;  (* PXOR (%_% xmm4) (%_% xmm0) *)
  0x48; 0xc7; 0xc5; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbp) (Imm32 (word 4294967295)) *)
  0x48; 0x83; 0xfa; 0x70;  (* CMP (% rdx) (Imm8 (word 112)) *)
  0x66; 0x0f; 0xef; 0xe8;  (* PXOR (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xf0;  (* PXOR (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xf8;  (* PXOR (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0xef; 0xc0;
                           (* PXOR (%_% xmm8) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0xef; 0xc8;
                           (* PXOR (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0xb0;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,18446744073709551536))) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x48; 0x83; 0xd5; 0x00;  (* ADC (% rbp) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe5; 0x80; 0x00; 0x00; 0x00;
                           (* AND (% rbp) (Imm32 (word 128)) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0x48; 0x01; 0xfd;        (* ADD (% rbp) (% rdi) *)
  0x0f; 0x10; 0x49; 0xc0;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,18446744073709551552))) *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf0;
                           (* AESDEC (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf8;
                           (* AESDEC (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc0;
                           (* AESDEC (%_% xmm8) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc8;
                           (* AESDEC (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0xd0;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,18446744073709551568))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0x0f; 0x10; 0x49; 0xe0;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,18446744073709551584))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf0;
                           (* AESDEC (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf8;
                           (* AESDEC (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc0;
                           (* AESDEC (%_% xmm8) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc8;
                           (* AESDEC (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0xf0;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,18446744073709551600))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0x0f; 0x10; 0x09;        (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,0))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf0;
                           (* AESDEC (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf8;
                           (* AESDEC (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc0;
                           (* AESDEC (%_% xmm8) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc8;
                           (* AESDEC (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0x10;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,16))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0x0f; 0x10; 0x49; 0x20;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,32))) *)
  0x83; 0xf8; 0x0b;        (* CMP (% eax) (Imm8 (word 11)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf0;
                           (* AESDEC (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf8;
                           (* AESDEC (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc0;
                           (* AESDEC (%_% xmm8) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc8;
                           (* AESDEC (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0x30;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,48))) *)
  0x0f; 0x82; 0xcc; 0x00; 0x00; 0x00;
                           (* JB (Imm32 (word 204)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0x0f; 0x10; 0x49; 0x40;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,64))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf0;
                           (* AESDEC (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf8;
                           (* AESDEC (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc0;
                           (* AESDEC (%_% xmm8) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc8;
                           (* AESDEC (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0x50;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,80))) *)
  0x74; 0x6d;              (* JE (Imm8 (word 109)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0x0f; 0x10; 0x49; 0x60;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,96))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf0;
                           (* AESDEC (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf8;
                           (* AESDEC (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc0;
                           (* AESDEC (%_% xmm8) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc8;
                           (* AESDEC (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0x70;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,112))) *)
  0xeb; 0x0e;              (* JMP (Imm8 (word 14)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x1f; 0x40; 0x00;  (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0xef; 0xd0;
                           (* PXOR (%_% xmm10) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0xef; 0xd8;
                           (* PXOR (%_% xmm11) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0xef; 0xe0;
                           (* PXOR (%_% xmm12) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0xef; 0xe8;
                           (* PXOR (%_% xmm13) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0xef; 0xf0;
                           (* PXOR (%_% xmm14) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0xef; 0xf8;
                           (* PXOR (%_% xmm15) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0xf3; 0x0f; 0x6f; 0x4f; 0x50;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,80))) *)
  0x66; 0x41; 0x0f; 0x38; 0xdf; 0xd2;
                           (* AESDECLAST (%_% xmm2) (%_% xmm10) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x57; 0x60;
                           (* MOVDQU (%_% xmm10) (Memop Word128 (%% (rdi,96))) *)
  0x66; 0x0f; 0xef; 0xc8;  (* PXOR (%_% xmm1) (%_% xmm0) *)
  0x66; 0x41; 0x0f; 0x38; 0xdf; 0xdb;
                           (* AESDECLAST (%_% xmm3) (%_% xmm11) *)
  0x66; 0x44; 0x0f; 0xef; 0xd0;
                           (* PXOR (%_% xmm10) (%_% xmm0) *)
  0xf3; 0x0f; 0x6f; 0x47; 0x70;
                           (* MOVDQU (%_% xmm0) (Memop Word128 (%% (rdi,112))) *)
  0x66; 0x41; 0x0f; 0x38; 0xdf; 0xe4;
                           (* AESDECLAST (%_% xmm4) (%_% xmm12) *)
  0x48; 0x8d; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rdi,128)) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x5d; 0x00;
                           (* MOVDQU (%_% xmm11) (Memop Word128 (%% (rbp,0))) *)
  0x66; 0x41; 0x0f; 0x38; 0xdf; 0xed;
                           (* AESDECLAST (%_% xmm5) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0x38; 0xdf; 0xf6;
                           (* AESDECLAST (%_% xmm6) (%_% xmm14) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x65; 0x10;
                           (* MOVDQU (%_% xmm12) (Memop Word128 (%% (rbp,16))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x6d; 0x20;
                           (* MOVDQU (%_% xmm13) (Memop Word128 (%% (rbp,32))) *)
  0x66; 0x41; 0x0f; 0x38; 0xdf; 0xff;
                           (* AESDECLAST (%_% xmm7) (%_% xmm15) *)
  0x66; 0x44; 0x0f; 0x38; 0xdf; 0xc1;
                           (* AESDECLAST (%_% xmm8) (%_% xmm1) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x75; 0x30;
                           (* MOVDQU (%_% xmm14) (Memop Word128 (%% (rbp,48))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x7d; 0x40;
                           (* MOVDQU (%_% xmm15) (Memop Word128 (%% (rbp,64))) *)
  0x66; 0x45; 0x0f; 0x38; 0xdf; 0xca;
                           (* AESDECLAST (%_% xmm9) (%_% xmm10) *)
  0x66; 0x44; 0x0f; 0x6f; 0xd0;
                           (* MOVDQA (%_% xmm10) (%_% xmm0) *)
  0xf3; 0x0f; 0x6f; 0x4d; 0x50;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rbp,80))) *)
  0x0f; 0x10; 0x41; 0x90;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,18446744073709551504))) *)
  0x0f; 0x11; 0x16;        (* MOVUPS (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0x6f; 0xd3;
                           (* MOVDQA (%_% xmm2) (%_% xmm11) *)
  0x0f; 0x11; 0x5e; 0x10;  (* MOVUPS (Memop Word128 (%% (rsi,16))) (%_% xmm3) *)
  0x66; 0x41; 0x0f; 0x6f; 0xdc;
                           (* MOVDQA (%_% xmm3) (%_% xmm12) *)
  0x0f; 0x11; 0x66; 0x20;  (* MOVUPS (Memop Word128 (%% (rsi,32))) (%_% xmm4) *)
  0x66; 0x41; 0x0f; 0x6f; 0xe5;
                           (* MOVDQA (%_% xmm4) (%_% xmm13) *)
  0x0f; 0x11; 0x6e; 0x30;  (* MOVUPS (Memop Word128 (%% (rsi,48))) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0x6f; 0xee;
                           (* MOVDQA (%_% xmm5) (%_% xmm14) *)
  0x0f; 0x11; 0x76; 0x40;  (* MOVUPS (Memop Word128 (%% (rsi,64))) (%_% xmm6) *)
  0x66; 0x41; 0x0f; 0x6f; 0xf7;
                           (* MOVDQA (%_% xmm6) (%_% xmm15) *)
  0x0f; 0x11; 0x7e; 0x50;  (* MOVUPS (Memop Word128 (%% (rsi,80))) (%_% xmm7) *)
  0x66; 0x0f; 0x6f; 0xf9;  (* MOVDQA (%_% xmm7) (%_% xmm1) *)
  0x44; 0x0f; 0x11; 0x46; 0x60;
                           (* MOVUPS (Memop Word128 (%% (rsi,96))) (%_% xmm8) *)
  0x48; 0x8d; 0x76; 0x70;  (* LEA (% rsi) (%% (rsi,112)) *)
  0x48; 0x81; 0xea; 0x80; 0x00; 0x00; 0x00;
                           (* SUB (% rdx) (Imm32 (word 128)) *)
  0x0f; 0x87; 0x52; 0xfc; 0xff; 0xff;
                           (* JA (Imm32 (word 4294966354)) *)
  0x41; 0x0f; 0x28; 0xd1;  (* MOVAPS (%_% xmm2) (%_% xmm9) *)
  0x48; 0x8d; 0x49; 0x90;  (* LEA (% rcx) (%% (rcx,18446744073709551504)) *)
  0x48; 0x83; 0xc2; 0x70;  (* ADD (% rdx) (Imm8 (word 112)) *)
  0x0f; 0x8e; 0xb0; 0x02; 0x00; 0x00;
                           (* JLE (Imm32 (word 688)) *)
  0x44; 0x0f; 0x11; 0x0e;  (* MOVUPS (Memop Word128 (%% (rsi,0))) (%_% xmm9) *)
  0x48; 0x8d; 0x76; 0x10;  (* LEA (% rsi) (%% (rsi,16)) *)
  0x48; 0x83; 0xfa; 0x50;  (* CMP (% rdx) (Imm8 (word 80)) *)
  0x0f; 0x86; 0xf2; 0x00; 0x00; 0x00;
                           (* JBE (Imm32 (word 242)) *)
  0x41; 0x0f; 0x28; 0xd3;  (* MOVAPS (%_% xmm2) (%_% xmm11) *)
  0x48; 0x83; 0xfa; 0x60;  (* CMP (% rdx) (Imm8 (word 96)) *)
  0x77; 0x64;              (* JA (Imm8 (word 100)) *)
  0x44; 0x0f; 0x28; 0xc7;  (* MOVAPS (%_% xmm8) (%_% xmm7) *)
  0xe8; 0x6b; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1131)) *)
  0x66; 0x41; 0x0f; 0xef; 0xd2;
                           (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x45; 0x0f; 0x28; 0xd0;  (* MOVAPS (%_% xmm10) (%_% xmm8) *)
  0x66; 0x41; 0x0f; 0xef; 0xdb;
                           (* PXOR (%_% xmm3) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x16;  (* MOVDQU (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0xef; 0xe4;
                           (* PXOR (%_% xmm4) (%_% xmm12) *)
  0xf3; 0x0f; 0x7f; 0x5e; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rsi,16))) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x66; 0x41; 0x0f; 0xef; 0xed;
                           (* PXOR (%_% xmm5) (%_% xmm13) *)
  0xf3; 0x0f; 0x7f; 0x66; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rsi,32))) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xe4;  (* PXOR (%_% xmm4) (%_% xmm4) *)
  0x66; 0x41; 0x0f; 0xef; 0xf6;
                           (* PXOR (%_% xmm6) (%_% xmm14) *)
  0xf3; 0x0f; 0x7f; 0x6e; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rsi,48))) (%_% xmm5) *)
  0x66; 0x0f; 0xef; 0xed;  (* PXOR (%_% xmm5) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0xef; 0xff;
                           (* PXOR (%_% xmm7) (%_% xmm15) *)
  0xf3; 0x0f; 0x7f; 0x76; 0x40;
                           (* MOVDQU (Memop Word128 (%% (rsi,64))) (%_% xmm6) *)
  0x66; 0x0f; 0xef; 0xf6;  (* PXOR (%_% xmm6) (%_% xmm6) *)
  0x48; 0x8d; 0x76; 0x50;  (* LEA (% rsi) (%% (rsi,80)) *)
  0x66; 0x0f; 0x6f; 0xd7;  (* MOVDQA (%_% xmm2) (%_% xmm7) *)
  0x66; 0x0f; 0xef; 0xff;  (* PXOR (%_% xmm7) (%_% xmm7) *)
  0xe9; 0x4e; 0x02; 0x00; 0x00;
                           (* JMP (Imm32 (word 590)) *)
  0x44; 0x0f; 0x10; 0x47; 0x60;
                           (* MOVUPS (%_% xmm8) (Memop Word128 (%% (rdi,96))) *)
  0x45; 0x0f; 0x57; 0xc9;  (* PXOR (%_% xmm9) (%_% xmm9) *)
  0xe8; 0xe2; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1250)) *)
  0x44; 0x0f; 0x10; 0x4f; 0x50;
                           (* MOVUPS (%_% xmm9) (Memop Word128 (%% (rdi,80))) *)
  0x66; 0x41; 0x0f; 0xef; 0xd2;
                           (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x44; 0x0f; 0x10; 0x57; 0x60;
                           (* MOVUPS (%_% xmm10) (Memop Word128 (%% (rdi,96))) *)
  0x66; 0x41; 0x0f; 0xef; 0xdb;
                           (* PXOR (%_% xmm3) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x16;  (* MOVDQU (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0xef; 0xe4;
                           (* PXOR (%_% xmm4) (%_% xmm12) *)
  0xf3; 0x0f; 0x7f; 0x5e; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rsi,16))) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x66; 0x41; 0x0f; 0xef; 0xed;
                           (* PXOR (%_% xmm5) (%_% xmm13) *)
  0xf3; 0x0f; 0x7f; 0x66; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rsi,32))) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xe4;  (* PXOR (%_% xmm4) (%_% xmm4) *)
  0x66; 0x41; 0x0f; 0xef; 0xf6;
                           (* PXOR (%_% xmm6) (%_% xmm14) *)
  0xf3; 0x0f; 0x7f; 0x6e; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rsi,48))) (%_% xmm5) *)
  0x66; 0x0f; 0xef; 0xed;  (* PXOR (%_% xmm5) (%_% xmm5) *)
  0x66; 0x41; 0x0f; 0xef; 0xff;
                           (* PXOR (%_% xmm7) (%_% xmm15) *)
  0xf3; 0x0f; 0x7f; 0x76; 0x40;
                           (* MOVDQU (Memop Word128 (%% (rsi,64))) (%_% xmm6) *)
  0x66; 0x0f; 0xef; 0xf6;  (* PXOR (%_% xmm6) (%_% xmm6) *)
  0x66; 0x45; 0x0f; 0xef; 0xc1;
                           (* PXOR (%_% xmm8) (%_% xmm9) *)
  0xf3; 0x0f; 0x7f; 0x7e; 0x50;
                           (* MOVDQU (Memop Word128 (%% (rsi,80))) (%_% xmm7) *)
  0x66; 0x0f; 0xef; 0xff;  (* PXOR (%_% xmm7) (%_% xmm7) *)
  0x48; 0x8d; 0x76; 0x60;  (* LEA (% rsi) (%% (rsi,96)) *)
  0x66; 0x41; 0x0f; 0x6f; 0xd0;
                           (* MOVDQA (%_% xmm2) (%_% xmm8) *)
  0x66; 0x45; 0x0f; 0xef; 0xc0;
                           (* PXOR (%_% xmm8) (%_% xmm8) *)
  0x66; 0x45; 0x0f; 0xef; 0xc9;
                           (* PXOR (%_% xmm9) (%_% xmm9) *)
  0xe9; 0xca; 0x01; 0x00; 0x00;
                           (* JMP (Imm32 (word 458)) *)
  0x0f; 0x10; 0x17;        (* MOVUPS (%_% xmm2) (Memop Word128 (%% (rdi,0))) *)
  0x48; 0x83; 0xea; 0x10;  (* SUB (% rdx) (Imm8 (word 16)) *)
  0x0f; 0x86; 0x9f; 0x00; 0x00; 0x00;
                           (* JBE (Imm32 (word 159)) *)
  0x0f; 0x10; 0x5f; 0x10;  (* MOVUPS (%_% xmm3) (Memop Word128 (%% (rdi,16))) *)
  0x44; 0x0f; 0x28; 0xda;  (* MOVAPS (%_% xmm11) (%_% xmm2) *)
  0x48; 0x83; 0xea; 0x10;  (* SUB (% rdx) (Imm8 (word 16)) *)
  0x0f; 0x86; 0xcd; 0x00; 0x00; 0x00;
                           (* JBE (Imm32 (word 205)) *)
  0x0f; 0x10; 0x67; 0x20;  (* MOVUPS (%_% xmm4) (Memop Word128 (%% (rdi,32))) *)
  0x44; 0x0f; 0x28; 0xe3;  (* MOVAPS (%_% xmm12) (%_% xmm3) *)
  0x48; 0x83; 0xea; 0x10;  (* SUB (% rdx) (Imm8 (word 16)) *)
  0x0f; 0x86; 0xeb; 0x00; 0x00; 0x00;
                           (* JBE (Imm32 (word 235)) *)
  0x0f; 0x10; 0x6f; 0x30;  (* MOVUPS (%_% xmm5) (Memop Word128 (%% (rdi,48))) *)
  0x44; 0x0f; 0x28; 0xec;  (* MOVAPS (%_% xmm13) (%_% xmm4) *)
  0x48; 0x83; 0xea; 0x10;  (* SUB (% rdx) (Imm8 (word 16)) *)
  0x0f; 0x86; 0x19; 0x01; 0x00; 0x00;
                           (* JBE (Imm32 (word 281)) *)
  0x0f; 0x10; 0x77; 0x40;  (* MOVUPS (%_% xmm6) (Memop Word128 (%% (rdi,64))) *)
  0x44; 0x0f; 0x28; 0xf5;  (* MOVAPS (%_% xmm14) (%_% xmm5) *)
  0x44; 0x0f; 0x28; 0xfe;  (* MOVAPS (%_% xmm15) (%_% xmm6) *)
  0x0f; 0x57; 0xff;        (* PXOR (%_% xmm7) (%_% xmm7) *)
  0xe8; 0x35; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 821)) *)
  0x66; 0x41; 0x0f; 0xef; 0xd2;
                           (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x45; 0x0f; 0x28; 0xd7;  (* MOVAPS (%_% xmm10) (%_% xmm15) *)
  0x66; 0x41; 0x0f; 0xef; 0xdb;
                           (* PXOR (%_% xmm3) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x16;  (* MOVDQU (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0xef; 0xe4;
                           (* PXOR (%_% xmm4) (%_% xmm12) *)
  0xf3; 0x0f; 0x7f; 0x5e; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rsi,16))) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x66; 0x41; 0x0f; 0xef; 0xed;
                           (* PXOR (%_% xmm5) (%_% xmm13) *)
  0xf3; 0x0f; 0x7f; 0x66; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rsi,32))) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xe4;  (* PXOR (%_% xmm4) (%_% xmm4) *)
  0x66; 0x41; 0x0f; 0xef; 0xf6;
                           (* PXOR (%_% xmm6) (%_% xmm14) *)
  0xf3; 0x0f; 0x7f; 0x6e; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rsi,48))) (%_% xmm5) *)
  0x66; 0x0f; 0xef; 0xed;  (* PXOR (%_% xmm5) (%_% xmm5) *)
  0x48; 0x8d; 0x76; 0x40;  (* LEA (% rsi) (%% (rsi,64)) *)
  0x66; 0x0f; 0x6f; 0xd6;  (* MOVDQA (%_% xmm2) (%_% xmm6) *)
  0x66; 0x0f; 0xef; 0xf6;  (* PXOR (%_% xmm6) (%_% xmm6) *)
  0x66; 0x0f; 0xef; 0xff;  (* PXOR (%_% xmm7) (%_% xmm7) *)
  0x48; 0x83; 0xea; 0x10;  (* SUB (% rdx) (Imm8 (word 16)) *)
  0xe9; 0x1e; 0x01; 0x00; 0x00;
                           (* JMP (Imm32 (word 286)) *)
  0x44; 0x0f; 0x28; 0xda;  (* MOVAPS (%_% xmm11) (%_% xmm2) *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0x0f; 0x10; 0x49; 0x10;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x48; 0x8d; 0x49; 0x20;  (* LEA (% rcx) (%% (rcx,32)) *)
  0x0f; 0x57; 0xd0;        (* PXOR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0xff; 0xc8;              (* DEC (% eax) *)
  0x0f; 0x10; 0x09;        (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,0))) *)
  0x48; 0x8d; 0x49; 0x10;  (* LEA (% rcx) (%% (rcx,16)) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd1;
                           (* AESDECLAST (%_% xmm2) (%_% xmm1) *)
  0x41; 0x0f; 0x57; 0xd2;  (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x45; 0x0f; 0x28; 0xd3;  (* MOVAPS (%_% xmm10) (%_% xmm11) *)
  0xe9; 0xea; 0x00; 0x00; 0x00;
                           (* JMP (Imm32 (word 234)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x66; 0x90;              (* NOP *)
  0x44; 0x0f; 0x28; 0xe3;  (* MOVAPS (%_% xmm12) (%_% xmm3) *)
  0xe8; 0x37; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 311)) *)
  0x66; 0x41; 0x0f; 0xef; 0xd2;
                           (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x45; 0x0f; 0x28; 0xd4;  (* MOVAPS (%_% xmm10) (%_% xmm12) *)
  0x66; 0x41; 0x0f; 0xef; 0xdb;
                           (* PXOR (%_% xmm3) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x16;  (* MOVDQU (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x0f; 0x6f; 0xd3;  (* MOVDQA (%_% xmm2) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x48; 0x8d; 0x76; 0x10;  (* LEA (% rsi) (%% (rsi,16)) *)
  0xe9; 0xb2; 0x00; 0x00; 0x00;
                           (* JMP (Imm32 (word 178)) *)
  0x0f; 0x1f; 0x40; 0x00;  (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x44; 0x0f; 0x28; 0xec;  (* MOVAPS (%_% xmm13) (%_% xmm4) *)
  0xe8; 0x67; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 359)) *)
  0x66; 0x41; 0x0f; 0xef; 0xd2;
                           (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x45; 0x0f; 0x28; 0xd5;  (* MOVAPS (%_% xmm10) (%_% xmm13) *)
  0x66; 0x41; 0x0f; 0xef; 0xdb;
                           (* PXOR (%_% xmm3) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x16;  (* MOVDQU (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0xef; 0xe4;
                           (* PXOR (%_% xmm4) (%_% xmm12) *)
  0xf3; 0x0f; 0x7f; 0x5e; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rsi,16))) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xd4;  (* MOVDQA (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xe4;  (* PXOR (%_% xmm4) (%_% xmm4) *)
  0x48; 0x8d; 0x76; 0x20;  (* LEA (% rsi) (%% (rsi,32)) *)
  0xeb; 0x77;              (* JMP (Imm8 (word 119)) *)
  0x66; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x44; 0x0f; 0x28; 0xf5;  (* MOVAPS (%_% xmm14) (%_% xmm5) *)
  0xe8; 0x97; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 407)) *)
  0x66; 0x41; 0x0f; 0xef; 0xd2;
                           (* PXOR (%_% xmm2) (%_% xmm10) *)
  0x45; 0x0f; 0x28; 0xd6;  (* MOVAPS (%_% xmm10) (%_% xmm14) *)
  0x66; 0x41; 0x0f; 0xef; 0xdb;
                           (* PXOR (%_% xmm3) (%_% xmm11) *)
  0xf3; 0x0f; 0x7f; 0x16;  (* MOVDQU (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x41; 0x0f; 0xef; 0xe4;
                           (* PXOR (%_% xmm4) (%_% xmm12) *)
  0xf3; 0x0f; 0x7f; 0x5e; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rsi,16))) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x66; 0x41; 0x0f; 0xef; 0xed;
                           (* PXOR (%_% xmm5) (%_% xmm13) *)
  0xf3; 0x0f; 0x7f; 0x66; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rsi,32))) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xe4;  (* PXOR (%_% xmm4) (%_% xmm4) *)
  0x66; 0x0f; 0x6f; 0xd5;  (* MOVDQA (%_% xmm2) (%_% xmm5) *)
  0x66; 0x0f; 0xef; 0xed;  (* PXOR (%_% xmm5) (%_% xmm5) *)
  0x48; 0x8d; 0x76; 0x30;  (* LEA (% rsi) (%% (rsi,48)) *)
  0xeb; 0x29;              (* JMP (Imm8 (word 41)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xe4;  (* PXOR (%_% xmm4) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xed;  (* PXOR (%_% xmm5) (%_% xmm5) *)
  0x66; 0x0f; 0xef; 0xf6;  (* PXOR (%_% xmm6) (%_% xmm6) *)
  0x66; 0x0f; 0xef; 0xff;  (* PXOR (%_% xmm7) (%_% xmm7) *)
  0x66; 0x45; 0x0f; 0xef; 0xc0;
                           (* PXOR (%_% xmm8) (%_% xmm8) *)
  0x66; 0x45; 0x0f; 0xef; 0xc9;
                           (* PXOR (%_% xmm9) (%_% xmm9) *)
  0x45; 0x0f; 0x11; 0x10;  (* MOVUPS (Memop Word128 (%% (r8,0))) (%_% xmm10) *)
  0x48; 0x83; 0xe2; 0x0f;  (* AND (% rdx) (Imm8 (word 15)) *)
  0x75; 0x18;              (* JNE (Imm8 (word 24)) *)
  0x0f; 0x11; 0x16;        (* MOVUPS (Memop Word128 (%% (rsi,0))) (%_% xmm2) *)
  0x66; 0x0f; 0xef; 0xd2;  (* PXOR (%_% xmm2) (%_% xmm2) *)
  0xeb; 0x31;              (* JMP (Imm8 (word 49)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%%% (rax,0,rax))) *)
  0x0f; 0x29; 0x14; 0x24;  (* MOVAPS (Memop Word128 (%% (rsp,0))) (%_% xmm2) *)
  0x66; 0x0f; 0xef; 0xd2;  (* PXOR (%_% xmm2) (%_% xmm2) *)
  0x48; 0xc7; 0xc1; 0x10; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Imm32 (word 16)) *)
  0x48; 0x89; 0xf7;        (* MOV (% rdi) (% rsi) *)
  0x48; 0x29; 0xd1;        (* SUB (% rcx) (% rdx) *)
  0x48; 0x8d; 0x34; 0x24;  (* LEA (% rsi) (%% (rsp,0)) *)
  0xf3; 0xa4;              (* MOVSB true (% rdi) (% rsi) (% rcx) *)
  0x66; 0x90;              (* NOP *)
  0x66; 0x0f; 0x7f; 0x14; 0x24;
                           (* MOVDQA (Memop Word128 (%% (rsp,0))) (%_% xmm2) *)
  0x0f; 0x57; 0xc0;        (* PXOR (%_% xmm0) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xc9;  (* PXOR (%_% xmm1) (%_% xmm1) *)
  0x49; 0x8b; 0x6b; 0xf8;  (* MOV (% rbp) (Memop Quadword (%% (r11,18446744073709551608))) *)
  0x49; 0x8d; 0x23;        (* LEA (% rsp) (%% (r11,0)) *)
  0xf3; 0xc3;              (* RET *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x1f; 0x40; 0x00;  (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0xc1; 0xe0; 0x04;        (* SHL (% eax) (Imm8 (word 4)) *)
  0x0f; 0x10; 0x49; 0x10;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x0f; 0x57; 0xd0;        (* PXOR (%_% xmm2) (%_% xmm0) *)
  0x0f; 0x57; 0xd8;        (* PXOR (%_% xmm3) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0x20;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,32))) *)
  0x48; 0x8d; 0x4c; 0x01; 0x20;
                           (* LEA (% rcx) (%%%% (rcx,0,rax,&32)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x83; 0xc0; 0x10;  (* ADD (% rax) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x0f; 0x10; 0x0c; 0x01;  (* MOVUPS (%_% xmm1) (Memop Word128 (%%% (rcx,0,rax))) *)
  0x48; 0x83; 0xc0; 0x20;  (* ADD (% rax) (Imm8 (word 32)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x0f; 0x10; 0x44; 0x01; 0xf0;
                           (* MOVUPS (%_% xmm0) (Memop Word128 (%%%% (rcx,0,rax,-- &16))) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd0;
                           (* AESDECLAST (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd8;
                           (* AESDECLAST (%_% xmm3) (%_% xmm0) *)
  0xf3; 0xc3;              (* RET *)
  0x0f; 0x1f; 0x80; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0xc1; 0xe0; 0x04;        (* SHL (% eax) (Imm8 (word 4)) *)
  0x0f; 0x10; 0x49; 0x10;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x0f; 0x57; 0xd0;        (* PXOR (%_% xmm2) (%_% xmm0) *)
  0x0f; 0x57; 0xd8;        (* PXOR (%_% xmm3) (%_% xmm0) *)
  0x0f; 0x57; 0xe0;        (* PXOR (%_% xmm4) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0x20;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,32))) *)
  0x48; 0x8d; 0x4c; 0x01; 0x20;
                           (* LEA (% rcx) (%%%% (rcx,0,rax,&32)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x83; 0xc0; 0x10;  (* ADD (% rax) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x0f; 0x10; 0x0c; 0x01;  (* MOVUPS (%_% xmm1) (Memop Word128 (%%% (rcx,0,rax))) *)
  0x48; 0x83; 0xc0; 0x20;  (* ADD (% rax) (Imm8 (word 32)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x0f; 0x10; 0x44; 0x01; 0xf0;
                           (* MOVUPS (%_% xmm0) (Memop Word128 (%%%% (rcx,0,rax,-- &16))) *)
  0x75; 0xd3;              (* JNE (Imm8 (word 211)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd0;
                           (* AESDECLAST (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd8;
                           (* AESDECLAST (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xe0;
                           (* AESDECLAST (%_% xmm4) (%_% xmm0) *)
  0xf3; 0xc3;              (* RET *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0xc1; 0xe0; 0x04;        (* SHL (% eax) (Imm8 (word 4)) *)
  0x0f; 0x10; 0x49; 0x10;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x0f; 0x57; 0xd0;        (* PXOR (%_% xmm2) (%_% xmm0) *)
  0x0f; 0x57; 0xd8;        (* PXOR (%_% xmm3) (%_% xmm0) *)
  0x0f; 0x57; 0xe0;        (* PXOR (%_% xmm4) (%_% xmm0) *)
  0x0f; 0x57; 0xe8;        (* PXOR (%_% xmm5) (%_% xmm0) *)
  0x0f; 0x10; 0x41; 0x20;  (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,32))) *)
  0x48; 0x8d; 0x4c; 0x01; 0x20;
                           (* LEA (% rcx) (%%%% (rcx,0,rax,&32)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x0f; 0x1f; 0x00;        (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x48; 0x83; 0xc0; 0x10;  (* ADD (% rax) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x0f; 0x10; 0x0c; 0x01;  (* MOVUPS (%_% xmm1) (Memop Word128 (%%% (rcx,0,rax))) *)
  0x48; 0x83; 0xc0; 0x20;  (* ADD (% rax) (Imm8 (word 32)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x0f; 0x10; 0x44; 0x01; 0xf0;
                           (* MOVUPS (%_% xmm0) (Memop Word128 (%%%% (rcx,0,rax,-- &16))) *)
  0x75; 0xc9;              (* JNE (Imm8 (word 201)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd0;
                           (* AESDECLAST (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd8;
                           (* AESDECLAST (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xe0;
                           (* AESDECLAST (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xe8;
                           (* AESDECLAST (%_% xmm5) (%_% xmm0) *)
  0xf3; 0xc3;              (* RET *)
  0x66; 0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0xc1; 0xe0; 0x04;        (* SHL (% eax) (Imm8 (word 4)) *)
  0x0f; 0x10; 0x49; 0x10;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x0f; 0x57; 0xd0;        (* PXOR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xd8;  (* PXOR (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xe0;  (* PXOR (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x48; 0x8d; 0x4c; 0x01; 0x20;
                           (* LEA (% rcx) (%%%% (rcx,0,rax,&32)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0xef; 0xe8;  (* PXOR (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xf0;  (* PXOR (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0xef; 0xf8;  (* PXOR (%_% xmm7) (%_% xmm0) *)
  0x0f; 0x10; 0x04; 0x01;  (* MOVUPS (%_% xmm0) (Memop Word128 (%%% (rcx,0,rax))) *)
  0x48; 0x83; 0xc0; 0x10;  (* ADD (% rax) (Imm8 (word 16)) *)
  0xeb; 0x1d;              (* JMP (Imm8 (word 29)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x1f; 0x40; 0x00;  (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x0f; 0x10; 0x0c; 0x01;  (* MOVUPS (%_% xmm1) (Memop Word128 (%%% (rcx,0,rax))) *)
  0x48; 0x83; 0xc0; 0x20;  (* ADD (% rax) (Imm8 (word 32)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf0;
                           (* AESDEC (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf8;
                           (* AESDEC (%_% xmm7) (%_% xmm0) *)
  0x0f; 0x10; 0x44; 0x01; 0xf0;
                           (* MOVUPS (%_% xmm0) (Memop Word128 (%%%% (rcx,0,rax,-- &16))) *)
  0x75; 0xb5;              (* JNE (Imm8 (word 181)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd0;
                           (* AESDECLAST (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd8;
                           (* AESDECLAST (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xe0;
                           (* AESDECLAST (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xe8;
                           (* AESDECLAST (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xf0;
                           (* AESDECLAST (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xf8;
                           (* AESDECLAST (%_% xmm7) (%_% xmm0) *)
  0xf3; 0xc3;              (* RET *)
  0x0f; 0x1f; 0x80; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x0f; 0x10; 0x01;        (* MOVUPS (%_% xmm0) (Memop Word128 (%% (rcx,0))) *)
  0xc1; 0xe0; 0x04;        (* SHL (% eax) (Imm8 (word 4)) *)
  0x0f; 0x10; 0x49; 0x10;  (* MOVUPS (%_% xmm1) (Memop Word128 (%% (rcx,16))) *)
  0x0f; 0x57; 0xd0;        (* PXOR (%_% xmm2) (%_% xmm0) *)
  0x0f; 0x57; 0xd8;        (* PXOR (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xe0;  (* PXOR (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xe8;  (* PXOR (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0xef; 0xf0;  (* PXOR (%_% xmm6) (%_% xmm0) *)
  0x48; 0x8d; 0x4c; 0x01; 0x20;
                           (* LEA (% rcx) (%%%% (rcx,0,rax,&32)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0xef; 0xf8;  (* PXOR (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0xef; 0xc0;
                           (* PXOR (%_% xmm8) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0xef; 0xc8;
                           (* PXOR (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x04; 0x01;  (* MOVUPS (%_% xmm0) (Memop Word128 (%%% (rcx,0,rax))) *)
  0x48; 0x83; 0xc0; 0x10;  (* ADD (% rax) (Imm8 (word 16)) *)
  0xeb; 0x14;              (* JMP (Imm8 (word 20)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0x0f; 0x10; 0x0c; 0x01;  (* MOVUPS (%_% xmm1) (Memop Word128 (%%% (rcx,0,rax))) *)
  0x48; 0x83; 0xc0; 0x20;  (* ADD (% rax) (Imm8 (word 32)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd0;
                           (* AESDEC (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xd8;
                           (* AESDEC (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe0;
                           (* AESDEC (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xe8;
                           (* AESDEC (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf0;
                           (* AESDEC (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xde; 0xf8;
                           (* AESDEC (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc0;
                           (* AESDEC (%_% xmm8) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc8;
                           (* AESDEC (%_% xmm9) (%_% xmm0) *)
  0x0f; 0x10; 0x44; 0x01; 0xf0;
                           (* MOVUPS (%_% xmm0) (Memop Word128 (%%%% (rcx,0,rax,-- &16))) *)
  0x75; 0x9d;              (* JNE (Imm8 (word 157)) *)
  0x66; 0x0f; 0x38; 0xde; 0xd1;
                           (* AESDEC (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xd9;
                           (* AESDEC (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe1;
                           (* AESDEC (%_% xmm4) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xe9;
                           (* AESDEC (%_% xmm5) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf1;
                           (* AESDEC (%_% xmm6) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xde; 0xf9;
                           (* AESDEC (%_% xmm7) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc1;
                           (* AESDEC (%_% xmm8) (%_% xmm1) *)
  0x66; 0x44; 0x0f; 0x38; 0xde; 0xc9;
                           (* AESDEC (%_% xmm9) (%_% xmm1) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd0;
                           (* AESDECLAST (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xd8;
                           (* AESDECLAST (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xe0;
                           (* AESDECLAST (%_% xmm4) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xe8;
                           (* AESDECLAST (%_% xmm5) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xf0;
                           (* AESDECLAST (%_% xmm6) (%_% xmm0) *)
  0x66; 0x0f; 0x38; 0xdf; 0xf8;
                           (* AESDECLAST (%_% xmm7) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xdf; 0xc0;
                           (* AESDECLAST (%_% xmm8) (%_% xmm0) *)
  0x66; 0x44; 0x0f; 0x38; 0xdf; 0xc8;
                           (* AESDECLAST (%_% xmm9) (%_% xmm0) *)
  0xf3; 0xc3               (* RET *)
];;

let AES_HW_CBC_ENCRYPT_EXEC = X86_MK_EXEC_RULE aes_hw_cbc_encrypt_mc;;

(* ------------------------------------------------------------------------- *)
(* Blocks in memory.                                                         *)
(* ------------------------------------------------------------------------- *)

(* cbc_num f j m is the 16m bytes of the blocks f j, ..., f (j + m - 1) read
   as a little-endian number, as memory holds them one after another. *)
let cbc_num = define
 `(!f j. cbc_num (f:num->int128) j 0 = 0) /\
  (!f j m. cbc_num f j (SUC m) = val(f j) + 2 EXP 128 * cbc_num f (j + 1) m)`;;

let aes_key_num = new_definition
 `aes_key_num (ks:int128 list) = cbc_num (\i. EL i ks) 0 (LENGTH ks)`;;

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

let READ_BLOCKS = prove
 (`!m (f:num->int128) j (a:int64) s.
        read (memory :> bytes(a,16 * m)) s = cbc_num f j m <=>
        !i. i < m ==> read (memory :> bytes128(word_add a (word(16 * i)))) s =
                      f(j + i)`,
  INDUCT_TAC THEN REWRITE_TAC[cbc_num; CONJUNCT1 LT; MULT_CLAUSES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * m + 16 = 16 + 16 * m`; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ARITH_RULE `8 * 16 = 128`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ADD_MULT_EXP_EQ o lhand o snd) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `(f:num->int128) j` VAL_BOUND) THEN
    MP_TAC(ISPECL [`a:int64`; `16`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM READ_BYTES128_VAL] THEN
  REWRITE_TAC[FORALL_LT_SUC_SPLIT] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `(j + 1) + i = SUC(j + i)`]);;
let READ_KEY = prove
 (`!ks (a:int64) s.
     read (memory :> bytes(a,16 * LENGTH ks)) s = aes_key_num ks <=>
     !i. i < LENGTH ks
         ==> read (memory :> bytes128(word_add a (word(16 * i)))) s = EL i ks`,
  REWRITE_TAC[aes_key_num; READ_BLOCKS; ADD_CLAUSES]);;

let rec SUCS_CONV tm = TRY_CONV (num_CONV THENC RAND_CONV SUCS_CONV) tm;;

(* AES_EXPAND n: a key schedule of n round keys, as its elements. *)
let aes_expand n =
  let ks = `ks:int128 list` in
  let lst = mk_list(map (fun i -> mk_comb(mk_comb(`EL:num->int128 list->int128`,
                       mk_small_numeral i), ks)) (0--(n-1)), `:int128`) in
  let len = mk_eq(`LENGTH(ks:int128 list)`, mk_small_numeral n) in
  let eqth = prove(mk_imp(len, mk_eq(ks, lst)),
    SPEC_TAC(ks,ks) THEN
    GEN_TAC THEN CONV_TAC(LAND_CONV(RAND_CONV SUCS_CONV)) THEN
    REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
    REPEAT(REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC) in
  let th = UNDISCH eqth in
  let dth = REWRITE_CONV[aes_hw_decrypt; HD; TL; BUTLAST; LAST; NOT_CONS_NIL;
                         aes_hw_dec_rounds]
              (list_mk_comb(`aes_hw_decrypt`, [lst; `x:int128`]))
  and eth = REWRITE_CONV[aes_hw_encrypt; HD; TL; BUTLAST; LAST; NOT_CONS_NIL;
                         aes_hw_rounds]
              (list_mk_comb(`aes_hw_encrypt`, [lst; `x:int128`])) in
  let d = TRANS (AP_THM (AP_TERM `aes_hw_decrypt` th) `x:int128`) dth
  and e = TRANS (AP_THM (AP_TERM `aes_hw_encrypt` th) `x:int128`) eth in
  GEN ks (DISCH len (CONJ (GEN `x:int128` d) (GEN `x:int128` e)));;

let AES_EXPAND_11 = aes_expand 11;;
let AES_EXPAND_13 = aes_expand 13;;
let AES_EXPAND_15 = aes_expand 15;;

let AES_EXPAND_TAC =
  FIRST_ASSUM(fun th ->
    FIRST(map (fun eth g -> REWRITE_TAC[MATCH_MP eth th] g)
              [AES_EXPAND_11; AES_EXPAND_13; AES_EXPAND_15]));;

(* With r IN {9,11,13} and LENGTH ks = r + 2 among the assumptions, splits
   the goal into the three key sizes, with the key schedule read as its round
   keys EL i ks and AES as its rounds. *)
let KEY_CASES_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhand(concl th) = `LENGTH(ks:int128 list)`
    then REWRITE_TAC[GSYM th] THEN ASSUME_TAC th else failwith "") THEN
  REWRITE_TAC[READ_KEY] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `(r:num) IN s`) o concl)) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  AES_EXPAND_TAC;;

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
(* SSE instructions write an XMM register's low 128 bits and keep the rest of
   its YMM register, so the simulation tracks each YMM register whole, as an
   unknown high half joined to the XMM value. *)
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

let rec X86_XSTEPS_UNTIL_TAC execth target n (asl,w as g) =
  if current_offset g = target then ALL_TAC g
  else (X86_XSTEPS_TAC execth [n] THEN
        X86_XSTEPS_UNTIL_TAC execth target (n + 1)) g;;
(* Runs the code from the lemma's start to pc + target, for each key size. *)
let STRAIGHT_TAC target =
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  KEY_CASES_TAC THEN ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN
  X86_XSTEPS_UNTIL_TAC AES_HW_CBC_ENCRYPT_EXEC target 1 THEN
  XMMS_OF_YMMS_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let xmm_reg i = mk_const("XMM"^string_of_int i,[]);;
let zmm_reg i = mk_const("ZMM"^string_of_int i,[]);;
let read_s c = mk_comb(mk_icomb(`read:(x86state,A)component->x86state->A`, c), `s:x86state`);;

(* The helpers that decrypt 2, 3, 4, 6 and 8 blocks in xmm2 to xmm9 under the
   key schedule at rcx, with eax its rounds, and return. *)
let helper_goal start stop nb =
  let regs = map (fun i -> xmm_reg (i+2)) (0--(nb-1)) in
  let xs = map (fun i -> mk_var("x"^string_of_int (i+2), `:int128`)) (0--(nb-1)) in
  let s = `s:x86state` in
  let pre = list_mk_conj
   ([`bytes_loaded s (word pc) aes_hw_cbc_encrypt_mc`;
     mk_eq(`read RIP s`, mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral start)));
     `read RCX s = key`; `read RAX s = word r`;
     `read (memory :> bytes(key,16 * (r + 2))) s = aes_key_num ks`] @
    map2 (fun r x -> mk_eq(read_s r, x)) regs xs)
  and post = list_mk_conj
   (mk_eq(`read RIP s`, mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral stop))) ::
    map2 (fun r x -> mk_eq(read_s r, mk_comb(`aes_hw_decrypt ks`, x))) regs xs) in
  let zmms = mk_list(map zmm_reg (0--(nb+1)), `:(x86state,512 word)component`) in
  let frame = subst [zmms,`ZMMS:((x86state,512 word)component)list`]
   `MAYCHANGE [RIP; RAX; RCX] ,,
    MAYCHANGE (ZMMS:((x86state,512 word)component)list) ,,
    MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]` in
  let ens = list_mk_icomb "ensures" [`x86`; mk_abs(s,pre); mk_abs(s,post); frame] in
  list_mk_forall([`key:int64`; `ks:int128 list`; `r:num`] @ xs @ [`pc:num`],
    mk_imp(`r IN {9,11,13} /\ LENGTH (ks:int128 list) = r + 2`, ens));;

let DEC2 = time prove(helper_goal 0x880 0x8d7 2, STRAIGHT_TAC 0x8d7);;
let DEC3 = time prove(helper_goal 0x8e0 0x94e 3, STRAIGHT_TAC 0x94e);;
let DEC4 = time prove(helper_goal 0x950 0x9d8 4, STRAIGHT_TAC 0x9d8);;
let DEC6 = time prove(helper_goal 0x9e0 0xab7 6, STRAIGHT_TAC 0xab7);;
let DEC8 = time prove(helper_goal 0xac0 0xbc7 8, STRAIGHT_TAC 0xbc7);;
let READ_BLOCKS_CONS = prove
 (`!m (f:num->int128) j (a:int64) s.
        read (memory :> bytes(a,16 * (m + 1))) s = cbc_num f j (m + 1) <=>
        read (memory :> bytes128 a) s = f j /\
        read (memory :> bytes(word_add a (word 16),16 * m)) s =
        cbc_num f (j + 1) m`,
  REWRITE_TAC[READ_BLOCKS; GSYM ADD1; FORALL_LT_SUC_SPLIT] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `16 * i + 16 = 16 + 16 * i`;
              ARITH_RULE `SUC(j + i) = (j + 1) + i`]);;

let READ_BLOCKS_SNOC = prove
 (`!m (f:num->int128) j (a:int64) s.
        read (memory :> bytes(a,16 * (m + 1))) s = cbc_num f j (m + 1) <=>
        read (memory :> bytes(a,16 * m)) s = cbc_num f j m /\
        read (memory :> bytes128 (word_add a (word(16 * m)))) s = f(j + m)`,
  REWRITE_TAC[READ_BLOCKS; ARITH_RULE `i < m + 1 <=> i < m \/ i = m`] THEN
  MESON_TAC[]);;

(* SP 800-38A's CBC encryption of the blocks inp 0, inp 1, ... chained from
   iv: cbc_enc ks iv inp i is the ith ciphertext block. *)
let cbc_enc = define
 `(!ks iv inp. cbc_enc ks iv inp 0 = aes_hw_encrypt ks (word_xor (inp 0) iv)) /\
  (!ks iv inp i. cbc_enc ks iv inp (SUC i) =
                 aes_hw_encrypt ks (word_xor (inp (SUC i)) (cbc_enc ks iv inp i)))`;;

let CBC_ENC = prove
 (`!ks iv inp i.
     cbc_enc ks iv inp i =
     aes_hw_encrypt ks
       (word_xor (inp i) (if i = 0 then iv else cbc_enc ks iv inp (i - 1)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[cbc_enc; NOT_SUC; SUC_SUB1]);;
let WORD_ADD_BLOCK = prove
 (`!(a:int64) i. word_add (word_add a (word(16 * i))) (word 16) =
                 word_add a (word(16 * (i + 1)))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `16 * i + 16 = 16 * (i + 1)`]);;

let WORD_XOR_ROT = prove
 (`!a b c:int128. word_xor a (word_xor b c) = word_xor (word_xor b a) c`,
  CONV_TAC WORD_BITWISE_RULE);;

let VAL_WORD_SUB_BLOCKS = prove
 (`!n a b. b <= a /\ 16 * a < 2 EXP 64
           ==> val(word_sub (word(16 * a)) (word(16 * b)):int64) =
               16 * a - 16 * b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `16 * b < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; LE_MULT_LCANCEL]);;
let WORD_SUB_BLOCK = prove
 (`!(x:int64) i. word_sub (word_sub x (word(16 * i))) (word 16) =
                 word_sub x (word(16 * (i + 1)))`,
  REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`; WORD_ADD] THEN
  CONV_TAC WORD_RULE);;
(* ARITH_TAC over just the assumptions about numbers. *)
let NUM_ASM_ARITH_TAC =
  POP_ASSUM_LIST(fun ths ->
    let ok th =
      let c = concl th in
      let c = if is_neg c then rand c else c in
      frees c <> [] && forall (fun v -> type_of v = `:num`) (frees c) &&
      (is_eq c || is_binary "<" c || is_binary "<=" c) &&
      type_of(lhand c) = `:num` in
    MAP_EVERY MP_TAC (filter ok ths)) THEN ARITH_TAC;;
let ENC_LOOP_GOAL = `!key ks r buf n iv inp pc.
  r IN {9,11,13} /\ LENGTH ks = r + 2 /\ ~(n = 0) /\ 16 * n < 2 EXP 64 /\
  nonoverlapping (buf,16 * n) (key,16 * (r + 2)) /\
  nonoverlapping (buf,16 * n) (word pc,0xbc9)
  ==> ensures x86
   (\s. bytes_loaded s (word pc) aes_hw_cbc_encrypt_mc /\
        read RIP s = word(pc + 0x30) /\
        read RDI s = buf /\ read RSI s = buf /\
        read RDX s = word_sub (word(16 * n)) (word 16) /\
        read RCX s = key /\ read R11 s = key /\
        read RAX s = word r /\ read R10 s = word r /\
        read (memory :> bytes(key,16 * (r + 2))) s = aes_key_num ks /\
        read XMM2 s = iv /\
        read (memory :> bytes(buf,16 * n)) s = cbc_num inp 0 n)
   (\s. read RIP s = word(pc + 0x70) /\
        read RDX s = word 18446744073709551600 /\
        read XMM2 s = cbc_enc ks iv inp (n - 1) /\
        read (memory :> bytes(buf,16 * n)) s = cbc_num (cbc_enc ks iv inp) 0 n)
   (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI] ,,
    MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,,
    MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(buf,16 * n)] ,,
    MAYCHANGE [events])`;;

let ENC_INV = `\i s.
       (read RDI s = word_add buf (word(16 * i)) /\
        read RSI s = word_add buf (word(16 * i)) /\
        read RDX s = word_sub (word(16 * n)) (word(16 * (i + 1))) /\
        read RCX s = key /\ read R11 s = key /\
        read RAX s = word r /\ read R10 s = word r /\
        read (memory :> bytes(key,16 * (r + 2))) s = aes_key_num ks /\
        read XMM2 s = (if i = 0 then iv else cbc_enc ks iv inp (i - 1)) /\
        read (memory :> bytes(buf,16 * i)) s = cbc_num (cbc_enc ks iv inp) 0 i /\
        read (memory :> bytes(word_add buf (word(16 * i)),16 * (n - i))) s =
        cbc_num inp i (n - i)) /\
       (read CF s <=> i = n)`;;
(* The proofs below are scripts of tactics, each applied to the first goal
   still open, as HOL Light's interactive e applies them. *)
let prove_steps (tm,tacs) =
  match rev_itlist (fun tac gs -> by (VALID tac) gs) tacs
          (mk_goalstate([],tm)) with
    (_,[],just) ->
      let th = just null_inst [] in
      if hyp th = [] && aconv (concl th) tm then th
      else failwith "prove_steps: wrong theorem"
  | _ -> failwith "prove_steps: unsolved goals";;

(* SP 800-38A's CBC decryption of the blocks inp 0, inp 1, ... chained from
   iv: cbc_dec ks iv inp i is the ith plaintext block. *)
let cbc_dec = new_definition
 `cbc_dec ks iv (inp:num->int128) i =
    word_xor (aes_hw_decrypt ks (inp i)) (if i = 0 then iv else inp(i - 1))`;;

(* The code XORs the chaining block into AESDECLAST's round key. *)
let AESDECLAST_XOR = prove
 (`!s c k:int128. aesdeclast s (word_xor c k) = word_xor (aesdeclast s k) c`,
  REWRITE_TAC[aesdeclast] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

let READ_KEY_R = prove
 (`!ks (a:int64) s r.
     LENGTH ks = r + 2 /\
     read (memory :> bytes(a,16 * (r + 2))) s = aes_key_num ks
     ==> !i. i < r + 2
             ==> read (memory :> bytes128(word_add a (word(16 * i)))) s =
                 EL i ks`,
  MESON_TAC[READ_KEY]);;

let read_value c s asl =
  rhs(concl(snd(find (fun (_,th) ->
    let t = concl th in
    is_eq t && (let l = lhs t in
                is_comb l && rand l = s && is_comb(rator l) &&
                rand(rator l) = c)) asl)));;

(* Splits on the key size and expands AES into rounds, keeping the key
   schedule's region as it is, for proofs that call the helpers. *)
let KEY_CASES_KEEP_TAC =
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `(r:num) IN s`) o concl)) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && lhand(concl th) = `LENGTH(ks:int128 list)`
    then ASSUME_TAC(CONV_RULE(RAND_CONV NUM_REDUCE_CONV) th)
    else failwith "") THEN
  AES_EXPAND_TAC;;

(* In the current state, the round keys from the key schedule's region. *)
let KEY_READS_TAC (asl,w as g) =
  let s = rand w in
  let th = snd(find (fun (_,th) ->
    can (term_match [] (subst [s,`s:x86state`]
      `read (memory :> bytes (key,16 * (r + 2))) s = aes_key_num ks`)) (concl th)) asl) in
  let r = lhand(rand(rand(rand(rand(lhand(lhs(concl th))))))) in
  let lth = snd(find (fun (_,th) -> concl th =
     mk_eq(`LENGTH(ks:int128 list)`, mk_binop `(+):num->num->num` r `2`)) asl) in
  (MP_TAC(MATCH_MP READ_KEY_R (CONJ lth th)) THEN
   CONV_TAC(LAND_CONV(NUM_REDUCE_CONV THENC EXPAND_CASES_CONV THENC
                      NUM_REDUCE_CONV)) THEN
   REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC) g;;
let WORD_SUB_BLOCKS_END = prove
 (`!n. word_sub (word(16 * n)) (word(16 * (n + 1))):int64 =
       word 18446744073709551600`,
  REWRITE_TAC[ARITH_RULE `16 * (n + 1) = 16 * n + 16`; WORD_ADD] THEN
  GEN_TAC THEN TRANS_TAC EQ_TRANS `word_neg(word 16):int64` THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_REDUCE_CONV]);;

let ENC_LOOP = time prove_steps
 (ENC_LOOP_GOAL,
 [
  (REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   ENSURES_WHILE_PUP_TAC `n:num` `pc + 0x30` `pc + 0x6e` ENC_INV THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC);
  (* Into the loop. *)
  (REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; WORD_ADD_0; cbc_num] THEN
   REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
   ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (* Block i. *)
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   ASM_SIMP_TAC[ARITH_RULE `i < n ==> n - i = (n - (i + 1)) + 1`] THEN
   GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV o ABS_CONV o DEPTH_CONV)
     [READ_BLOCKS_CONS] THEN
   GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV o DEPTH_CONV)
     [READ_BLOCKS_SNOC] THEN
   REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB; ADD_CLAUSES] THEN
   ABBREV_TAC `chn:int128 = if i = 0 then iv else cbc_enc ks iv inp (i - 1)` THEN
   ONCE_REWRITE_TAC[CBC_ENC] THEN ASM_REWRITE_TAC[] THEN
   KEY_CASES_TAC THEN ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN
   X86_XSTEPS_UNTIL_TAC AES_HW_CBC_ENCRYPT_EXEC 0x6e 1 THEN
   XMMS_OF_YMMS_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_BLOCK]) THEN
   ASM_REWRITE_TAC[WORD_XOR_ROT; WORD_ADD_BLOCK; WORD_SUB_BLOCK] THEN
   W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_SUB_BLOCKS o lhand o lhand o snd) THEN
   (ANTS_TAC THENL [NUM_ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN NUM_ASM_ARITH_TAC]));
  (* Back to the top. *)
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC AES_HW_CBC_ENCRYPT_EXEC [1] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (* Out of the loop. *)
  (ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC AES_HW_CBC_ENCRYPT_EXEC [1] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_BLOCKS_END])
 ]);;
let WORD_ZX_ROUNDS = prove
 (`!r. r IN {9,11,13}
       ==> word_zx(word r:int32):int64 = word r /\
           word_zx(word_zx(word r:int32):int64):int32 = word r /\
           word_zx(word r:int32):int32 = word r`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let NONOVERLAPPING_KEY = prove
 (`!r (key:int64) x l.
     r IN {9,11,13} /\ nonoverlapping (x,l) (key,256)
     ==> nonoverlapping (x,l) (key,16 * (r + 2))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN NONOVERLAPPING_TAC);;

let VAL_WORD_BLOCKS = prove
 (`!n. 16 * n < 2 EXP 64 ==> val(word(16 * n):int64) = 16 * n`,
  SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

let ENC_CORE_GOAL = `!key ks r buf n iv inp ivec enc pc.
  r IN {9,11,13} /\ LENGTH ks = r + 2 /\ 16 * n < 2 EXP 64 /\
  ~(val(word_zx enc:int32) = 0) /\
  nonoverlapping (buf,16 * n) (key,256) /\
  nonoverlapping (buf,16 * n) (word pc,0xbc9) /\
  nonoverlapping (buf,16 * n) (ivec,16) /\
  nonoverlapping (ivec,16) (key,256) /\
  nonoverlapping (ivec,16) (word pc,0xbc9)
  ==> ensures x86
   (\s. bytes_loaded s (word pc) aes_hw_cbc_encrypt_mc /\
        read RIP s = word pc /\
        read RDI s = buf /\ read RSI s = buf /\ read RDX s = word(16 * n) /\
        read RCX s = key /\ read R8 s = ivec /\ read R9 s = enc /\
        read (memory :> bytes32(word_add key (word 240))) s = word r /\
        read (memory :> bytes(key,16 * (r + 2))) s = aes_key_num ks /\
        read (memory :> bytes128 ivec) s = iv /\
        read (memory :> bytes(buf,16 * n)) s = cbc_num inp 0 n)
   (\s. read RIP s = word(pc + 0x870) /\
        read (memory :> bytes(buf,16 * n)) s = cbc_num (cbc_enc ks iv inp) 0 n /\
        read (memory :> bytes128 ivec) s =
          (if n = 0 then iv else cbc_enc ks iv inp (n - 1)))
   (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R10; R11] ,,
    MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(buf,16 * n); memory :> bytes(ivec,16)] ,,
    MAYCHANGE [events])`;;
let READ_BYTES_0 = prove
 (`!(a:int64) s. read (memory :> bytes(a,0)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]);;

(* Ghosts the YMM registers that have no YMM equation in the current state,
   as after a call whose lemma speaks of their XMM values. *)
let REGHOST_YMMS_TAC (asl,w as g) =
  let s = rand w in
  let has_ymm ymm =
    exists (fun (_,th) ->
      let c = concl th in
      is_eq c && (let l = lhs c in
                  is_comb l && rand l = s && is_comb(rator l) &&
                  rand(rator l) = ymm)) asl in
  let tac k ymm =
    let xmm = List.nth [`XMM0`; `XMM1`; `XMM2`; `XMM3`; `XMM4`; `XMM5`; `XMM6`;
                        `XMM7`; `XMM8`; `XMM9`; `XMM10`; `XMM11`; `XMM12`;
                        `XMM13`; `XMM14`; `XMM15`] k in
    let pat = mk_eq(mk_comb(mk_comb(`read:(x86state,int128)component->x86state->int128`, xmm), s),
                    `x:int128`) in
    let hv = mk_var("ymmh"^string_of_int k, `:int128`) in
    let yv = mk_var("ymmv"^string_of_int k, `:256 word`) in
    fun (asl,w as g) ->
      if has_ymm ymm then ALL_TAC g else
      try let th = snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
          let th' = MATCH_MP YMM_OF_XMM (REWRITE_RULE XMM_YMMS th) in
          X_CHOOSE_THEN (variant (freesl(w::map (concl o snd) asl)) hv) ASSUME_TAC th' g
      with Failure _ ->
        let ex = mk_exists(yv, mk_eq(list_mk_comb(`read:(x86state,256 word)component->x86state->256 word`, [ymm; s]), yv)) in
        (SUBGOAL_THEN ex (X_CHOOSE_THEN (variant (freesl(w::map (concl o snd) asl)) yv) ASSUME_TAC)
         THENL [MESON_TAC[]; ALL_TAC]) g in
  EVERY (List.mapi tac ymm_regs) g;;

(* The one-block path of the decryption tail, 0x704 to 0x727. *)
let DEC1 = time prove(helper_goal 0x704 0x727 1, STRAIGHT_TAC 0x727);;
let READ_BLOCKS_0 = prove
 (`!m (f:num->int128) (a:int64) s.
        read (memory :> bytes(a,16 * m)) s = cbc_num f 0 m <=>
        !i. i < m ==> read (memory :> bytes128(word_add a (word(16 * i)))) s = f i`,
  REWRITE_TAC[READ_BLOCKS; ADD_CLAUSES]);;

let ENC_SUB_GOAL = `!buf n key ks r ivec iv inp enc pc stackpointer returnaddress.
  r IN {9,11,13} /\ LENGTH ks = r + 2 /\ 16 * n < 2 EXP 64 /\
  ~(val(word_zx enc:int32) = 0) /\
  ALL (nonoverlapping (buf,16 * n))
      [(key,256); (ivec,16); (word pc,0xbc9); (stackpointer,8)] /\
  ALL (nonoverlapping (ivec,16)) [(key,256); (word pc,0xbc9); (stackpointer,8)]
  ==> ensures x86
   (\s. bytes_loaded s (word pc) aes_hw_cbc_encrypt_mc /\
        read RIP s = word pc /\
        read RSP s = stackpointer /\
        read (memory :> bytes64 stackpointer) s = returnaddress /\
        C_ARGUMENTS [buf; buf; word(16 * n); key; ivec; enc] s /\
        read (memory :> bytes32(word_add key (word 240))) s = word r /\
        (!i. i < r + 2
             ==> read (memory :> bytes128(word_add key (word(16 * i)))) s = EL i ks) /\
        read (memory :> bytes128 ivec) s = iv /\
        (!i. i < n
             ==> read (memory :> bytes128(word_add buf (word(16 * i)))) s = inp i))
   (\s. read RIP s = returnaddress /\
        read RSP s = word_add stackpointer (word 8) /\
        (!i. i < n
             ==> read (memory :> bytes128(word_add buf (word(16 * i)))) s =
                 cbc_enc ks iv inp i) /\
        read (memory :> bytes128 ivec) s =
          (if n = 0 then iv else cbc_enc ks iv inp (n - 1)))
   (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [memory :> bytes(buf,16 * n); memory :> bytes(ivec,16)] ,,
    MAYCHANGE [events])`;;
let ENC_CORE = time prove
 (ENC_CORE_GOAL,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[MULT_CLAUSES; cbc_num; READ_BYTES_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC AES_HW_CBC_ENCRYPT_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(16 * n):int64) = 16 * n /\ ~(16 * n = 0) /\ ~(16 * n < 16)`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_BLOCKS] THEN UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping (buf,16 * n) (key:int64,16 * (r + 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_KEY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN
  X86_XSTEPS_TAC AES_HW_CBC_ENCRYPT_EXEC (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WORD_ZX_ROUNDS (ASSUME `r IN {9,11,13}`)]) THEN
  XMMS_OF_YMMS_TAC THEN
  MP_TAC(SPECL [`key:int64`; `ks:int128 list`; `r:num`; `buf:int64`; `n:num`;
                `iv:int128`; `inp:num->int128`; `pc:num`] ENC_LOOP) THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN
  X86_BIGSTEP_TAC AES_HW_CBC_ENCRYPT_EXEC "s13" THEN
  REGHOST_YMMS_TAC THEN X86_XSTEPS_TAC AES_HW_CBC_ENCRYPT_EXEC (14--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let AES_HW_CBC_ENCRYPT_ENCRYPT_SUBROUTINE_CORRECT = time prove
 (ENC_SUB_GOAL,
  REWRITE_TAC[ALL; C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `read (memory :> bytes(buf,16 * n)) s0 = cbc_num inp 0 n /\
                read (memory :> bytes(key,16 * (r + 2))) s0 = aes_key_num ks`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[READ_BLOCKS_0] THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM(ASSUME `LENGTH(ks:int128 list) = r + 2`); READ_KEY] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`key:int64`; `ks:int128 list`; `r:num`; `buf:int64`; `n:num`;
                `iv:int128`; `inp:num->int128`; `ivec:int64`; `enc:int64`; `pc:num`]
         ENC_CORE) THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN
  X86_BIGSTEP_TAC AES_HW_CBC_ENCRYPT_EXEC "s1" THEN
  X86_STEPS_TAC AES_HW_CBC_ENCRYPT_EXEC [2] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM READ_BLOCKS_0; ETA_AX]);;
(* The decryption's frame: rsp aligned down to 16 below the saved rbp, whose
   call slot lies in the 48 bytes below the return address. *)
let WORD_AND_NOT_SUB_16 = prove
 (`!x m:int64. word_and x (word_not m) = word_sub x (word_and x m)`,
  BITBLAST_TAC);;

let VAL_ALIGN_16 = prove
 (`!x:int64. val(word_and x (word 18446744073709551600)) = val x - val x MOD 16`,
  GEN_TAC THEN
  SUBGOAL_THEN `word 18446744073709551600:int64 = word_not(word(2 EXP 4 - 1))` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    REWRITE_TAC[WORD_AND_NOT_SUB_16; VAL_WORD_SUB_CASES; VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LE]]);;

let WORD_ALIGN_16 = prove
 (`!x:int64. word_and x (word 18446744073709551600) = word_sub x (word(val x MOD 16))`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_ALIGN_16; VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val(x:int64) MOD 16 MOD 2 EXP 64 = val x MOD 16` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [`val(x:int64)`; `16`] MOD_LT_EQ) THEN ARITH_TAC;
    REWRITE_TAC[MOD_LE]]);;

let ALIGN_SLOT = prove
 (`!stackpointer:int64. ?t. t < 16 /\
     word_sub (word_and (word_sub (word_sub stackpointer (word 8)) (word 16))
                        (word 18446744073709551600)) (word 8) =
     word_add (word_sub stackpointer (word 48)) (word(16 - t))`,
  GEN_TAC THEN REWRITE_TAC[WORD_ALIGN_16] THEN
  ABBREV_TAC `t = val(word_sub (word_sub stackpointer (word 8)) (word 16):int64) MOD 16` THEN
  EXISTS_TAC `t:num` THEN
  SUBGOAL_THEN `t < 16` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE] THEN CONV_TAC WORD_RULE);;
(* The decryption's state after its frame is set up, at 0x654 (the tails of
   one to five blocks) and 0x566 (six or seven): blocks 0 to j - 1 are done,
   m blocks remain from j, and xmm10 holds the block that chains into j. *)
let READ_BLOCKS_SPLIT = prove
 (`!j m (f:num->int128) (a:int64) s.
     read (memory :> bytes(a,16 * (j + m))) s = cbc_num f 0 (j + m) <=>
     read (memory :> bytes(a,16 * j)) s = cbc_num f 0 j /\
     read (memory :> bytes(word_add a (word(16 * j)),16 * m)) s = cbc_num f j m`,
  REWRITE_TAC[READ_BLOCKS; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM LEFT_ADD_DISTRIB] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `i < j` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i - j:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[ARITH_RULE `~(i < j) ==> j + i - j = i`]]]);;

let DFRAME = `MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; RBP; R10; R11] ,,
    MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
               ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(buf,16 * n); memory :> bytes(ivec,16);
               memory :> bytes(word_add stackpointer (word 18446744073709551608),8);
               memory :> bytes(word_sub fp (word 8),8)] ,,
    MAYCHANGE [events]`;;

let DHYP = `r IN {9,11,13} /\ LENGTH (ks:int128 list) = r + 2 /\ 16 * n < 2 EXP 64 /\
    ALL (nonoverlapping (buf:int64,16 * n))
        [(key:int64,16 * (r + 2)); (word pc,0xbc9); (ivec:int64,16);
         (word_add (stackpointer:int64) (word 18446744073709551608),8)] /\
    ALL (nonoverlapping (ivec,16))
        [(key,16 * (r + 2)); (word pc,0xbc9);
         (word_add stackpointer (word 18446744073709551608),8)] /\
    ALL (nonoverlapping (word_sub (fp:int64) (word 8),8))
        [(buf,16 * n); (ivec,16); (key,16 * (r + 2)); (word pc,0xbc9);
         (word_add stackpointer (word 18446744073709551608),8)]`;;

let DFIN = `\s. read RIP s = word(pc + 0x870) /\
    read RSP s = stackpointer /\ read RBP s = rbp0 /\
    read (memory :> bytes(buf,16 * n)) s = cbc_num (cbc_dec ks iv inp) 0 n /\
    read (memory :> bytes128 ivec) s = inp(n - 1)`;;

let dgoal hyp pre =
  let pre = mk_abs(`s:x86state`, mk_conj(
     `bytes_loaded s (word pc) aes_hw_cbc_encrypt_mc /\
      read RSP s = fp /\ read R11 s = stackpointer /\ read R8 s = ivec /\
      read RAX s = word r /\
      read (memory :> bytes(key,16 * (r + 2))) s = aes_key_num ks /\
      read (memory :> bytes64(word_add stackpointer (word 18446744073709551608))) s = rbp0`, pre)) in
  let ens = list_mk_icomb "ensures" [`x86`; pre; DFIN; DFRAME] in
  let tm = mk_imp(mk_conj(DHYP, hyp), ens) in
  list_mk_forall(filter (fun v -> mem v (frees tm))
   [`key:int64`; `ks:int128 list`; `r:num`; `buf:int64`; `n:num`;
    `j:num`; `m:num`; `p:num`; `e:num`; `iv:int128`; `inp:num->int128`; `ivec:int64`;
    `fp:int64`; `stackpointer:int64`; `rbp0:int64`; `pc:num`], tm);;

let TAIL_A_GOAL = dgoal
 `j + m = n /\ 1 <= m /\ m <= 5`
 `read RIP s = word(pc + 0x654) /\
  read RCX s = key /\
  read RDI s = word_add buf (word(16 * j)) /\
  read RSI s = word_add buf (word(16 * j)) /\
  read RDX s = word(16 * m) /\
  read XMM10 s = (if j = 0 then iv else inp(j - 1)) /\
  read (memory :> bytes(buf,16 * j)) s = cbc_num (cbc_dec ks iv inp) 0 j /\
  read (memory :> bytes(word_add buf (word(16 * j)),16 * m)) s = cbc_num inp j m`;;

let TAIL_B_GOAL = dgoal
 `j + m = n /\ 6 <= m /\ m <= 7`
 `read RIP s = word(pc + 0x566) /\
  read RCX s = key /\
  read RDI s = word_add buf (word(16 * j)) /\
  read RSI s = word_add buf (word(16 * j)) /\
  read RDX s = word(16 * m) /\
  read XMM10 s = (if j = 0 then iv else inp(j - 1)) /\
  read XMM2 s = inp j /\ read XMM3 s = inp(j + 1) /\ read XMM4 s = inp(j + 2) /\
  read XMM5 s = inp(j + 3) /\ read XMM6 s = inp(j + 4) /\ read XMM7 s = inp(j + 5) /\
  read XMM11 s = inp j /\ read XMM12 s = inp(j + 1) /\ read XMM13 s = inp(j + 2) /\
  read XMM14 s = inp(j + 3) /\ read XMM15 s = inp(j + 4) /\
  read (memory :> bytes(buf,16 * j)) s = cbc_num (cbc_dec ks iv inp) 0 j /\
  read (memory :> bytes(word_add buf (word(16 * j)),16 * m)) s = cbc_num inp j m`;;
(* For the tails: the m remaining blocks from j as single blocks at the
   addresses the simulation forms, and the reverse for the written ones. *)
let BLOCKS_EXPAND_CONV =
  REWRITE_CONV[READ_BLOCKS] THENC
  ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
  REWRITE_CONV[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_CLAUSES];;

let TAIL_BLOCKS_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read (memory :> bytes(word_add buf (word(16 * j)),16 * m)) s =
     cbc_num inp j m`) (concl th))) THEN
  CONV_TAC(LAND_CONV BLOCKS_EXPAND_CONV) THEN STRIP_TAC;;

let PRED_ADD = ARITH_RULE
 `!j. (j + 1) - 1 = j /\ (j + 2) - 1 = j + 1 /\ (j + 3) - 1 = j + 2 /\
      (j + 4) - 1 = j + 3 /\ (j + 5) - 1 = j + 4 /\ (j + 6) - 1 = j + 5 /\
      (j + 7) - 1 = j + 6 /\ (j + 8) - 1 = j + 7`;;

(* Calls a decryption helper from the current state, the blocks being the
   values of xmm2 onwards. *)
let CALL_TAC lemma nb sname (asl,w as g) =
  let s = rand w in
  let xs = map (fun i -> read_value (xmm_reg (i+2)) s asl) (0--(nb-1)) in
  (MP_TAC(SPECL ([`key:int64`; `ks:int128 list`; `r:num`] @ xs @ [`pc:num`]) lemma) THEN
   ASM_REWRITE_TAC[SOME_FLAGS] THEN
   X86_BIGSTEP_TAC AES_HW_CBC_ENCRYPT_EXEC sname THEN
   REGHOST_YMMS_TAC) g;;

let TAIL_FINAL_TAC =
  XMMS_OF_YMMS_TAC THEN ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  REWRITE_TAC[READ_BLOCKS_SPLIT; PRED_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV(fun t ->
    if can (term_match [] `read (memory :> bytes(word_add buf (word(16 * j)),16 * m)) s =
                            cbc_num f j m`) t
    then BLOCKS_EXPAND_CONV t else failwith "")) THEN
  ASM_REWRITE_TAC[cbc_dec; ADD_EQ_0; ARITH_EQ; ADD_SUB; PRED_ADD];;

let next_index (asl,w) =
  let s = fst(dest_var(rand w)) in
  int_of_string(String.sub s 1 (String.length s - 1)) + 1;;

let TAIL_PATH_TAC callpc lemma nb =
  ENSURES_INIT_TAC "s0" THEN TAIL_BLOCKS_TAC THEN GHOST_YMMS_TAC THEN
  X86_XSTEPS_UNTIL_TAC AES_HW_CBC_ENCRYPT_EXEC callpc 1 THEN XMMS_OF_YMMS_TAC THEN
  (fun g -> CALL_TAC lemma nb ("s"^string_of_int(next_index g)) g) THEN
  (fun g -> X86_XSTEPS_UNTIL_TAC AES_HW_CBC_ENCRYPT_EXEC 0x870 (next_index g) g) THEN
  TAIL_FINAL_TAC;;
let WORD_NUM_REDUCE_CONV =
  DEPTH_CONV(fun t ->
    if is_comb t && is_const(rator t) && fst(dest_const(rator t)) = "word" &&
       is_binary "*" (rand t) && is_numeral(lhand(rand t)) && is_numeral(rand(rand t))
    then RAND_CONV NUM_REDUCE_CONV t else failwith "");;

let TAIL_A = time prove
 (TAIL_A_GOAL,
  REWRITE_TAC[ALL; SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `j + m:num = n`)) THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5` MP_TAC THENL
   [UNDISCH_TAC `1 <= m` THEN UNDISCH_TAC `m <= 5` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC WORD_NUM_REDUCE_CONV THENL
   [TAIL_PATH_TAC 0x704 DEC1 1; TAIL_PATH_TAC 0x880 DEC2 2;
    TAIL_PATH_TAC 0x8e0 DEC3 3; TAIL_PATH_TAC 0x950 DEC4 4;
    TAIL_PATH_TAC 0x9e0 DEC6 6]);;

let TAIL_B = time prove
 (TAIL_B_GOAL,
  REWRITE_TAC[ALL; SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `j + m:num = n`)) THEN
  SUBGOAL_THEN `m = 6 \/ m = 7` MP_TAC THENL
   [UNDISCH_TAC `6 <= m` THEN UNDISCH_TAC `m <= 7` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC WORD_NUM_REDUCE_CONV THENL
   [TAIL_PATH_TAC 0x9e0 DEC6 6; TAIL_PATH_TAC 0xac0 DEC8 8]);;
let GFRAME = `MAYCHANGE [RIP; RDX; RSI; RDI; RBP] ,,
    MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
               ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(buf,16 * n)] ,,
    MAYCHANGE [events]`;;

let GROUP_PRE = `\s. bytes_loaded s (word pc) aes_hw_cbc_encrypt_mc /\
    read RIP s = word(pc + 0x198) /\
    read RCX s = word_add key (word 112) /\ read RAX s = word r /\
    read RDI s = word_add buf (word(16 * j)) /\
    read RSI s = word_add buf (word(16 * j)) /\
    read RDX s = word(16 * m - 112) /\
    read (memory :> bytes(key,16 * (r + 2))) s = aes_key_num ks /\
    read XMM0 s = EL 0 ks /\
    read XMM2 s = inp j /\ read XMM3 s = inp(j + 1) /\ read XMM4 s = inp(j + 2) /\
    read XMM5 s = inp(j + 3) /\ read XMM6 s = inp(j + 4) /\ read XMM7 s = inp(j + 5) /\
    read XMM11 s = inp j /\ read XMM12 s = inp(j + 1) /\ read XMM13 s = inp(j + 2) /\
    read XMM14 s = inp(j + 3) /\ read XMM15 s = inp(j + 4) /\
    read XMM10 s = (if j = 0 then iv else inp(j - 1)) /\
    read (memory :> bytes(buf,16 * j)) s = cbc_num (cbc_dec ks iv inp) 0 j /\
    read (memory :> bytes(word_add buf (word(16 * j)),16 * m)) s = cbc_num inp j m`;;

let GROUP_GOAL = list_mk_forall
 ([`key:int64`; `ks:int128 list`; `r:num`; `buf:int64`; `n:num`; `j:num`; `m:num`;
   `iv:int128`; `inp:num->int128`; `pc:num`],
  mk_imp
   (`r IN {9,11,13} /\ LENGTH (ks:int128 list) = r + 2 /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (buf:int64,16 * n) (key:int64,16 * (r + 2)) /\
     nonoverlapping (buf,16 * n) (word pc,0xbc9) /\
     j + m = n /\ 8 <= m`,
    list_mk_icomb "ensures" [`x86`; GROUP_PRE;
     `\s. read RIP s = word(pc + 0x538) /\
          read RDI s = word_add buf (word(16 * (j + 8))) /\
          read RSI s = word_add buf (word(16 * (j + 7))) /\
          read RDX s = word_sub (word(16 * m - 112)) (word 128) /\
          (read CF s <=> m < 15) /\ (read ZF s <=> m = 15) /\
          read XMM0 s = EL 0 ks /\
          read XMM9 s = cbc_dec ks iv inp (j + 7) /\
          read XMM10 s = inp(j + 7) /\
          read XMM2 s = inp(if 14 <= m then j + 8 else j) /\
          read XMM3 s = inp((if 14 <= m then j + 8 else j) + 1) /\
          read XMM4 s = inp((if 14 <= m then j + 8 else j) + 2) /\
          read XMM5 s = inp((if 14 <= m then j + 8 else j) + 3) /\
          read XMM6 s = inp((if 14 <= m then j + 8 else j) + 4) /\
          read XMM7 s = inp((if 14 <= m then j + 8 else j) + 5) /\
          read XMM11 s = inp(if 14 <= m then j + 8 else j) /\
          read XMM12 s = inp((if 14 <= m then j + 8 else j) + 1) /\
          read XMM13 s = inp((if 14 <= m then j + 8 else j) + 2) /\
          read XMM14 s = inp((if 14 <= m then j + 8 else j) + 3) /\
          read XMM15 s = inp((if 14 <= m then j + 8 else j) + 4) /\
          read (memory :> bytes(buf,16 * (j + 7))) s =
            cbc_num (cbc_dec ks iv inp) 0 (j + 7) /\
          read (memory :> bytes(word_add buf (word(16 * (j + 7))),16 * (m - 7))) s =
            cbc_num inp (j + 7) (m - 7)`;
     GFRAME]));;

let READ_BLOCKS_SPLIT_GEN = prove
 (`!k l (f:num->int128) j (a:int64) s.
     read (memory :> bytes(a,16 * (k + l))) s = cbc_num f j (k + l) <=>
     read (memory :> bytes(a,16 * k)) s = cbc_num f j k /\
     read (memory :> bytes(word_add a (word(16 * k)),16 * l)) s = cbc_num f (j + k) l`,
  REWRITE_TAC[READ_BLOCKS] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `i < k` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i - k:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[ARITH_RULE `~(i < k) ==> k + i - k = i`]]]);;

let BLOCK_AT = prove
 (`!(a:int64) (f:num->int128) j m s q k.
     read (memory :> bytes(word_add a (word(16 * j)),16 * m)) s = cbc_num f j m /\
     j <= q /\ q + k < j + m
     ==> read (memory :> bytes128(word_add a (word(16 * q + 16 * k)))) s = f(q + k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_BLOCKS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(q + k) - j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `j <= q ==> 16 * j + 16 * ((q + k) - j) = 16 * q + 16 * k`;
               ARITH_RULE `j <= q ==> j + ((q + k) - j) = q + k`]);;

let VAL_GROUP_RDX = prove
 (`!m. 16 * m < 2 EXP 64 ==> val(word(16 * m - 112):int64) = 16 * m - 112`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let ZF_GROUP = prove
 (`!m. 16 * m < 2 EXP 64 /\ 8 <= m
       ==> (val(word_sub (word(16 * m - 112)) (word 128):int64) = 0 <=> m = 15)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(16 * m - 112) MOD 2 EXP 64 = 16 * m - 112` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;
let PREFETCH = prove
 (`!(buf:int64) j m.
     word_add (word_and (word_add (word 18446744073709551615)
                                  (word(bitval(16 * m - 112 < 112))))
                        (word 128))
              (word_add buf (word(16 * j))):int64 =
     word_add buf (word(16 * (if 14 <= m then j + 8 else j)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * m - 112 < 112 <=> ~(14 <= m)`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0; LEFT_ADD_DISTRIB; WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* The first eight blocks of the group as single blocks, and the rest. *)
let GROUP_MEM_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read (memory :> bytes(word_add buf (word(16 * j)),16 * m)) s =
     cbc_num inp j m`) (concl th))) THEN
  SUBGOAL_THEN `m = 8 + (m - 8)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `8 <= m` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_BLOCKS_SPLIT_GEN] THEN
  CONV_TAC(LAND_CONV(LAND_CONV BLOCKS_EXPAND_CONV)) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  STRIP_TAC;;

(* The six blocks from q that the group loads for the next one. *)
let GROUP_Q_TAC =
  MAP_EVERY (fun k ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes(word_add buf (word(16 * j)),16 * m)) s =
                             cbc_num inp j m`) (concl th)
      then MP_TAC(SPECL [`q:num`; mk_small_numeral k]
              (MATCH_MP (REWRITE_RULE[IMP_CONJ] BLOCK_AT) th))
      else failwith "") THEN
    ANTS_TAC THENL [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_TAC) (0--5);;

(* rbp, from the carry of rdx - 0x70, as the address of block q. *)
let RBP_Q_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && can (term_match [] `read RBP s`) (lhs(concl th))
    then ASSUME_TAC(REWRITE_RULE[PREFETCH; ASSUME `(if 14 <= m then j + 8 else j) = q`] th)
    else failwith "");;

let BLOCKS7_CONV t =
  if can (term_match [] `read (memory :> bytes(word_add buf (word(16 * j)),16 * 7)) s =
                          cbc_num f j 7`) t
  then BLOCKS_EXPAND_CONV t else failwith "";;

let GROUP_FINAL_TAC =
  XMMS_OF_YMMS_TAC THEN ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; AESDECLAST_XOR]) THEN
  REWRITE_TAC[READ_BLOCKS_SPLIT; READ_BLOCKS_CONS;
              MATCH_MP (ARITH_RULE `8 <= m ==> m - 7 = (m - 8) + 1`) (ASSUME `8 <= m`)] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV BLOCKS7_CONV) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `(j + 7) + 1 = j + 8`; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[cbc_dec; ADD_EQ_0; ARITH_EQ; PRED_ADD] THEN AES_EXPAND_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `16 * m - 112 < 128 <=> m < 15`] THEN
  TRY(MATCH_MP_TAC ZF_GROUP THEN NUM_ASM_ARITH_TAC);;

let GROUP_SETUP_TAC =
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q = if 14 <= m then j + 8 else j` THEN
  SUBGOAL_THEN `j <= q /\ q + 6 <= j + m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN COND_CASES_TAC THEN NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * m < 2 EXP 64` ASSUME_TAC THENL [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(16 * m - 112):int64) = 16 * m - 112` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_GROUP_RDX THEN NUM_ASM_ARITH_TAC; ALL_TAC];;

let GROUP_CASE_TAC =
  ENSURES_INIT_TAC "s0" THEN GROUP_Q_TAC THEN GROUP_MEM_TAC THEN GHOST_YMMS_TAC THEN
  X86_XSTEPS_UNTIL_TAC AES_HW_CBC_ENCRYPT_EXEC 0x211 1 THEN RBP_Q_TAC THEN
  (fun g -> X86_XSTEPS_UNTIL_TAC AES_HW_CBC_ENCRYPT_EXEC 0x538 (next_index g) g) THEN
  GROUP_FINAL_TAC;;

let GROUP = time prove
 (GROUP_GOAL, GROUP_SETUP_TAC THEN KEY_CASES_TAC THEN GROUP_CASE_TAC);;
(* The 8-block loop, from its first group at 0x198 to 0x53e, where it has
   left block p, the last of its last group, in xmm9 and e blocks after it. *)
let LOOP_POST = `\s. read RIP s = word(pc + 0x53e) /\
    read RDI s = word_add buf (word(16 * (p + 1))) /\
    read RSI s = word_add buf (word(16 * p)) /\
    read RDX s = word_sub (word(16 * (e + 8) - 112)) (word 128) /\
    read XMM9 s = cbc_dec ks iv inp p /\
    read XMM10 s = inp p /\
    (6 <= e
     ==> read XMM2 s = inp(p + 1) /\ read XMM3 s = inp(p + 2) /\
         read XMM4 s = inp(p + 3) /\ read XMM5 s = inp(p + 4) /\
         read XMM6 s = inp(p + 5) /\ read XMM7 s = inp(p + 6) /\
         read XMM11 s = inp(p + 1) /\ read XMM12 s = inp(p + 2) /\
         read XMM13 s = inp(p + 3) /\ read XMM14 s = inp(p + 4) /\
         read XMM15 s = inp(p + 5)) /\
    read (memory :> bytes(buf,16 * p)) s = cbc_num (cbc_dec ks iv inp) 0 p /\
    read (memory :> bytes(word_add buf (word(16 * p)),16 * (e + 1))) s =
      cbc_num inp p (e + 1)`;;

let LOOP_GOAL = list_mk_forall
 ([`key:int64`; `ks:int128 list`; `r:num`; `buf:int64`; `n:num`;
   `iv:int128`; `inp:num->int128`; `pc:num`; `p:num`; `e:num`],
  mk_imp
   (`r IN {9,11,13} /\ LENGTH (ks:int128 list) = r + 2 /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (buf:int64,16 * n) (key:int64,16 * (r + 2)) /\
     nonoverlapping (buf,16 * n) (word pc,0xbc9) /\
     p + 1 + e = n /\ e < 8`,
    list_mk_forall([`m:num`; `j:num`],
     mk_imp(`j + m = n /\ 8 <= m /\ m MOD 8 = e`,
      list_mk_icomb "ensures" [`x86`; GROUP_PRE; LOOP_POST; GFRAME]))));;

let RDX_NEXT = prove
 (`!m. 16 <= m
       ==> word_sub (word(16 * m - 112)) (word 128):int64 = word(16 * (m - 8) - 112)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `16 * (m - 8) - 112 = (16 * m - 112) - 128` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `16 <= m ==> 128 <= 16 * m - 112`]);;

let MOD8_LAST = prove
 (`!m. 8 <= m /\ m < 16 ==> m MOD 8 = m - 8`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let MOD8_NEXT = prove
 (`!m. 16 <= m ==> (m - 8) MOD 8 = m MOD 8`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m = (m - 8) + 1 * 8` (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

let LOOP = time prove
 (LOOP_GOAL,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_CASES_TAC `m < 16` THENL
  [SUBGOAL_THEN `e = m - 8 /\ p = j + 7` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `m MOD 8 = e`)) THEN
    ASM_SIMP_TAC[MOD8_LAST] THEN UNDISCH_TAC `p + 1 + m MOD 8 = n` THEN
    ASM_SIMP_TAC[MOD8_LAST] THEN NUM_ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`key:int64`; `ks:int128 list`; `r:num`; `buf:int64`; `n:num`; `j:num`;
                `m:num`; `iv:int128`; `inp:num->int128`; `pc:num`] GROUP) THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN
  X86_BIGSTEP_TAC AES_HW_CBC_ENCRYPT_EXEC "s1" THEN
  SUBGOAL_THEN `m < 15 \/ m = 15` ASSUME_TAC THENL [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC AES_HW_CBC_ENCRYPT_EXEC [2] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `(j + 7) + 1 = j + 8`; ARITH_RULE `8 <= m ==> (m - 8) + 8 = m`;
               ARITH_RULE `8 <= m ==> (m - 8) + 1 = m - 7`;
               ARITH_RULE `6 <= m - 8 <=> 14 <= m`] THEN
  ASM_CASES_TAC `14 <= m` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV;
   SUBGOAL_THEN `16 <= m /\ 14 <= m /\ ~(m < 15) /\ ~(m = 15)` STRIP_ASSUME_TAC THENL
   [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m - 8`) THEN
  ANTS_TAC THENL [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j + 8`) THEN
  ASM_SIMP_TAC[MOD8_NEXT; ARITH_RULE `16 <= m ==> 8 <= m - 8`] THEN
  ANTS_TAC THENL [NUM_ASM_ARITH_TAC; DISCH_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`key:int64`; `ks:int128 list`; `r:num`; `buf:int64`; `n:num`; `j:num`;
                `m:num`; `iv:int128`; `inp:num->int128`; `pc:num`] GROUP) THEN
  ASM_REWRITE_TAC[SOME_FLAGS] THEN
  X86_BIGSTEP_TAC AES_HW_CBC_ENCRYPT_EXEC "s1" THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                 ARITH_RULE `16 * (j + 7) + 16 = 16 * (j + 8)`;
                 ARITH_RULE `(j + 7) + 1 = j + 8`] o
    REWRITE_RULE[MATCH_MP (ARITH_RULE `16 <= m ==> m - 7 = (m - 8) + 1`) (ASSUME `16 <= m`);
                 READ_BLOCKS_CONS] o
    check (fun th -> can (term_match []
    `read (memory :> bytes(word_add buf (word(16 * (j + 7))),16 * (m - 7))) s1 = x`) (concl th))) THEN
  REGHOST_YMMS_TAC THEN
  X86_XSTEPS_TAC AES_HW_CBC_ENCRYPT_EXEC (2--4) THEN XMMS_OF_YMMS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `16 * (j + 7) + 16 = 16 * (j + 8)`]) THEN
  SUBGOAL_THEN `read (memory :> bytes(buf,16 * (j + 8))) s4 =
                cbc_num (cbc_dec ks iv inp) 0 (j + 8)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `j + 8 = (j + 7) + 1`; READ_BLOCKS_SNOC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RDX_NEXT (ASSUME `16 <= m`)]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) && can (find_term ((=) `ensures:(x86state->x86state->bool)->(x86state->bool)->(x86state->bool)->(x86state->x86state->bool)->bool`)) (concl th))) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; PRED_ADD] THEN
  X86_BIGSTEP_TAC AES_HW_CBC_ENCRYPT_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* From the loop's exit at 0x53e: block p in xmm9 and e blocks after it. *)
let EXIT_GOAL = dgoal
 `(p + 1) + e = n /\ e < 8 /\
  nonoverlapping (word_add (stackpointer:int64) (word 18446744073709551608),8) (word pc,0xbc9)`
 `read RIP s = word(pc + 0x53e) /\
  read RCX s = word_add key (word 112) /\
  read RDI s = word_add buf (word(16 * (p + 1))) /\
  read RSI s = word_add buf (word(16 * p)) /\
  read RDX s = word_sub (word(16 * (e + 8) - 112)) (word 128) /\
  read XMM9 s = cbc_dec ks iv inp p /\
  read XMM10 s = inp p /\
  (6 <= e
   ==> read XMM2 s = inp(p + 1) /\ read XMM3 s = inp(p + 2) /\
       read XMM4 s = inp(p + 3) /\ read XMM5 s = inp(p + 4) /\
       read XMM6 s = inp(p + 5) /\ read XMM7 s = inp(p + 6) /\
       read XMM11 s = inp(p + 1) /\ read XMM12 s = inp(p + 2) /\
       read XMM13 s = inp(p + 3) /\ read XMM14 s = inp(p + 4) /\
       read XMM15 s = inp(p + 5)) /\
  read (memory :> bytes(buf,16 * p)) s = cbc_num (cbc_dec ks iv inp) 0 p /\
  read (memory :> bytes(word_add buf (word(16 * p)),16 * (e + 1))) s =
    cbc_num inp p (e + 1)`;;

let WORD_CLOSED_REDUCE_CONV =
  DEPTH_CONV(fun t ->
    if is_comb t && is_const(rator t) && fst(dest_const(rator t)) = "word" &&
       frees(rand t) = [] && not(is_numeral(rand t))
    then RAND_CONV NUM_REDUCE_CONV t else failwith "");;

let EXIT_SPLIT_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                 ARITH_RULE `16 * p + 16 = 16 * (p + 1)`] o
    REWRITE_RULE[READ_BLOCKS_CONS] o
    check (fun th -> can (term_match []
     `read (memory :> bytes(word_add buf (word(16 * p)),16 * (e + 1))) s = x`) (concl th)));;

let EXIT_STEP_TAC target =
  ENSURES_INIT_TAC "s0" THEN EXIT_SPLIT_TAC THEN GHOST_YMMS_TAC THEN
  X86_XSTEPS_UNTIL_TAC AES_HW_CBC_ENCRYPT_EXEC target 1 THEN
  XMMS_OF_YMMS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                              ARITH_RULE `16 * p + 16 = 16 * (p + 1)`]);;

let P1_ADD = ARITH_RULE
  `(p + 1) + 1 = p + 2 /\ (p + 1) + 2 = p + 3 /\ (p + 1) + 3 = p + 4 /\
   (p + 1) + 4 = p + 5 /\ (p + 1) + 5 = p + 6`;;

let EXIT_TAIL_TAC target lemma m (asl,w as g) =
  let s = rand w in
  (SUBGOAL_THEN (subst [s,`s:x86state`]
     `read (memory :> bytes(buf,16 * (p + 1))) s = cbc_num (cbc_dec ks iv inp) 0 (p + 1)`)
     ASSUME_TAC THENL
    [REWRITE_TAC[READ_BLOCKS_SNOC] THEN ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
   MP_TAC(REWRITE_RULE[P1_ADD]
          (SPECL [`key:int64`; `ks:int128 list`; `r:num`; `buf:int64`; `n:num`;
                 `p + 1`; mk_small_numeral m; `iv:int128`; `inp:num->int128`;
                 `ivec:int64`; `fp:int64`; `stackpointer:int64`; `rbp0:int64`; `pc:num`] lemma)) THEN
   CONV_TAC WORD_CLOSED_REDUCE_CONV THEN
   ASM_REWRITE_TAC[ALL; SOME_FLAGS; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
   TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
   X86_BIGSTEP_TAC AES_HW_CBC_ENCRYPT_EXEC ("s"^string_of_int(next_index g)) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) g;;


let EXIT = prove(EXIT_GOAL,
  REWRITE_TAC[ALL; SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5 \/ e = 6 \/ e = 7` MP_TAC THENL
   [UNDISCH_TAC `e < 8` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC WORD_CLOSED_REDUCE_CONV THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(p + 1) + 0 = n`)) THEN
    ENSURES_INIT_TAC "s0" THEN GHOST_YMMS_TAC THEN
    X86_XSTEPS_UNTIL_TAC AES_HW_CBC_ENCRYPT_EXEC 0x870 1 THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[READ_BLOCKS_SNOC; ADD_CLAUSES; ADD_SUB];
    EXIT_STEP_TAC 0x654 THEN EXIT_TAIL_TAC 0x654 TAIL_A 1;
    EXIT_STEP_TAC 0x654 THEN EXIT_TAIL_TAC 0x654 TAIL_A 2;
    EXIT_STEP_TAC 0x654 THEN EXIT_TAIL_TAC 0x654 TAIL_A 3;
    EXIT_STEP_TAC 0x654 THEN EXIT_TAIL_TAC 0x654 TAIL_A 4;
    EXIT_STEP_TAC 0x654 THEN EXIT_TAIL_TAC 0x654 TAIL_A 5;
    REWRITE_TAC[ARITH_RULE `(6 <= 6 <=> T) /\ (6 <= 7 <=> T)`] THEN
    EXIT_STEP_TAC 0x566 THEN EXIT_TAIL_TAC 0x566 TAIL_B 6;
    REWRITE_TAC[ARITH_RULE `(6 <= 6 <=> T) /\ (6 <= 7 <=> T)`] THEN
    EXIT_STEP_TAC 0x566 THEN EXIT_TAIL_TAC 0x566 TAIL_B 7]);;
