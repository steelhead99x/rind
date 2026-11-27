(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 block compression with AVX2 and BMI2, as rind's build emits it.   *)
(* ========================================================================= *)

(* rind's naked function low::x86_64::sha256::sha256_block_data_order_avx2 is
   OpenSSL's sha256_block_data_order_avx2 (crypto/sha/asm/sha256-x86_64.pl,
   the AVX2 path), which reads its round constants and byte-shuffle masks
   from the K256 table beside it. Its result is s2n-bignum's FIPS 180-4
   spec, sha256_hash_blocks, from s2n-bignum pull request #415, which
   rind's fork in thirdparty/s2n-bignum/ holds until it merges.

   The routine hashes blocks two at a time: it computes both blocks' message
   schedules at once, block A's in the low 128-bit lane of each register and
   block B's in the high one, running block A's 64 rounds alongside and
   storing every schedule word plus its round constant to the stack, from
   which it then runs block B's rounds. An odd last block runs block A's part
   only, with a block from the stack as a dummy B. The proof steps every
   instruction symbolically, both inner loops unrolled since their trip
   counts are fixed, and folds each round and each schedule word into the
   spec as it completes, naming each state word after the round that made
   it, so the terms stay small. *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/sha256_spec.ml";;

(* admin/prove writes the function's object, as rind's release build emits
   it, to x86_64/sha256_block_data_order_avx2.o: its instructions as .text,
   with relocations, and the K256 table as .rodata. The definition fails
   unless the instructions and relocations are these, and sha256_avx2_k256 is
   the table's bytes, which SHA256_AVX2_K256 checks against FIPS 180-4's
   constants. *)
let sha256_avx2_mc,sha256_avx2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(fun _ -> "sha256_avx2_k256")
    "sha256_avx2_mc" "x86_64/sha256_block_data_order_avx2.o"
(fun b ADDR -> [b[
  0x48; 0x89; 0xe0;        (* MOV (% rax) (% rsp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0x20; 0x02; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 544)) *)
  0x48; 0xc1; 0xe2; 0x04;  (* SHL (% rdx) (Imm8 (word 4)) *)
  0x48; 0x81; 0xe4; 0x00; 0xfc; 0xff; 0xff;
                           (* AND (% rsp) (Imm32 (word 4294966272)) *)
  0x48; 0x8d; 0x14; 0x96;  (* LEA (% rdx) (%%% (rsi,2,rdx)) *)
  0x48; 0x81; 0xc4; 0xc0; 0x01; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 448)) *)
  0x48; 0x89; 0x7c; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rdi) *)
  0x48; 0x89; 0x74; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rsi) *)
  0x48; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rdx) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0x48; 0x83; 0xee; 0xc0;  (* SUB (% rsi) (Imm8 (word 192)) *)
  0x8b; 0x07;              (* MOV (% eax) (Memop Doubleword (%% (rdi,0))) *)
  0x49; 0x89; 0xf4;        (* MOV (% r12) (% rsi) *)
  0x8b; 0x5f; 0x04;        (* MOV (% ebx) (Memop Doubleword (%% (rdi,4))) *)
  0x48; 0x39; 0xd6;        (* CMP (% rsi) (% rdx) *)
  0x8b; 0x4f; 0x08;        (* MOV (% ecx) (Memop Doubleword (%% (rdi,8))) *)
  0x4c; 0x0f; 0x44; 0xe4;  (* CMOVE (% r12) (% rsp) *)
  0x8b; 0x57; 0x0c;        (* MOV (% edx) (Memop Doubleword (%% (rdi,12))) *)
  0x44; 0x8b; 0x47; 0x10;  (* MOV (% r8d) (Memop Doubleword (%% (rdi,16))) *)
  0x44; 0x8b; 0x4f; 0x14;  (* MOV (% r9d) (Memop Doubleword (%% (rdi,20))) *)
  0x44; 0x8b; 0x57; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rdi,24))) *)
  0x44; 0x8b; 0x5f; 0x1c;  (* MOV (% r11d) (Memop Doubleword (%% (rdi,28))) *)
  0xc5; 0x7d; 0x6f; 0x05]; ADDR ("sha256_avx2_k256",(540)); b[
                           (* VMOVDQA (%_% ymm8)
(Memop Word256
(Riprel (word_sx (iword (&sha256_avx2_k256 - (&pc + -- &430)))))) *)
  0xc5; 0x7d; 0x6f; 0x0d]; ADDR ("sha256_avx2_k256",(572)); b[
                           (* VMOVDQA (%_% ymm9)
(Memop Word256
(Riprel (word_sx (iword (&sha256_avx2_k256 - (&pc + -- &454)))))) *)
  0xeb; 0x04;              (* JMP (Imm8 (word 4)) *)
  0x0f; 0x1f; 0x40; 0x00;  (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0xc5; 0xfd; 0x6f; 0x3d]; ADDR ("sha256_avx2_k256",(508)); b[
                           (* VMOVDQA (%_% ymm7)
(Memop Word256
(Riprel (word_sx (iword (&sha256_avx2_k256 - (&pc + -- &376)))))) *)
  0xc5; 0xfa; 0x6f; 0x46; 0xc0;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,18446744073709551552))) *)
  0xc5; 0xfa; 0x6f; 0x4e; 0xd0;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rsi,18446744073709551568))) *)
  0xc5; 0xfa; 0x6f; 0x56; 0xe0;
                           (* VMOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,18446744073709551584))) *)
  0xc5; 0xfa; 0x6f; 0x5e; 0xf0;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rsi,18446744073709551600))) *)
  0xc4; 0xc3; 0x7d; 0x38; 0x04; 0x24; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (Memop Word128 (%% (r12,0)))
(Imm8 (word 1)) *)
  0xc4; 0xc3; 0x75; 0x38; 0x4c; 0x24; 0x10; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (r12,16)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0xc3; 0x6d; 0x38; 0x54; 0x24; 0x20; 0x01;
                           (* VINSERTI128 (%_% ymm2) (%_% ymm2) (Memop Word128 (%% (r12,32)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xcf;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm7) *)
  0xc4; 0xc3; 0x65; 0x38; 0x5c; 0x24; 0x30; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (r12,48)))
(Imm8 (word 1)) *)
  0x48; 0x8d; 0x2d]; ADDR ("sha256_avx2_k256",(-4)); b[
                           (* LEA (% rbp) (Riprel (word_sx (iword (&sha256_avx2_k256 - (&pc + &204))))) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xd7;
                           (* VPSHUFB (%_% ymm2) (%_% ymm2) (%_% ymm7) *)
  0xc5; 0xfd; 0xfe; 0x65; 0x00;
                           (* VPADDD (%_% ymm4) (%_% ymm0) (Memop Word256 (%% (rbp,0))) *)
  0xc4; 0xe2; 0x65; 0x00; 0xdf;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm7) *)
  0xc5; 0xf5; 0xfe; 0x6d; 0x20;
                           (* VPADDD (%_% ymm5) (%_% ymm1) (Memop Word256 (%% (rbp,32))) *)
  0xc5; 0xed; 0xfe; 0x75; 0x40;
                           (* VPADDD (%_% ymm6) (%_% ymm2) (Memop Word256 (%% (rbp,64))) *)
  0xc5; 0xe5; 0xfe; 0x7d; 0x60;
                           (* VPADDD (%_% ymm7) (%_% ymm3) (Memop Word256 (%% (rbp,96))) *)
  0xc5; 0xfd; 0x7f; 0x24; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm4) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc5; 0xfd; 0x7f; 0x6c; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm5) *)
  0x48; 0x8b; 0x7c; 0x24; 0x58;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8d; 0x64; 0x24; 0xc0;
                           (* LEA (% rsp) (%% (rsp,18446744073709551552)) *)
  0x48; 0x89; 0x7c; 0x24; 0xf8;
                           (* MOV (Memop Quadword (%% (rsp,18446744073709551608))) (% rdi) *)
  0x89; 0xdf;              (* MOV (% edi) (% ebx) *)
  0xc5; 0xfd; 0x7f; 0x34; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm6) *)
  0x31; 0xcf;              (* XOR (% edi) (% ecx) *)
  0xc5; 0xfd; 0x7f; 0x7c; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm7) *)
  0x45; 0x89; 0xcc;        (* MOV (% r12d) (% r9d) *)
  0x48; 0x83; 0xed; 0x80;  (* SUB (% rbp) (Imm8 (word 128)) *)
  0xeb; 0x01;              (* JMP (Imm8 (word 1)) *)
  0x90;                    (* NOP *)
  0x48; 0x8d; 0x64; 0x24; 0xc0;
                           (* LEA (% rsp) (%% (rsp,18446744073709551552)) *)
  0xff; 0x74; 0x24; 0x38;  (* PUSH (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8d; 0x64; 0x24; 0x08;
                           (* LEA (% rsp) (%% (rsp,8)) *)
  0xc4; 0xe3; 0x75; 0x0f; 0xe0; 0x04;
                           (* VPALIGNR (%_% ymm4) (%_% ymm1) (%_% ymm0) (Imm8 (word 4)) *)
  0x44; 0x03; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% r11d) (Memop Doubleword (%% (rsp,128))) *)
  0x45; 0x21; 0xc4;        (* AND (% r12d) (% r8d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x65; 0x0f; 0xfa; 0x04;
                           (* VPALIGNR (%_% ymm7) (%_% ymm3) (%_% ymm2) (Imm8 (word 4)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% r8d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x04; 0x30;  (* LEA (% eax) (%%% (rax,0,r14)) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0xc5; 0xcd; 0x72; 0xd4; 0x07;
                           (* VPSRLD (%_% ymm6) (%_% ymm4) (Imm8 (word 7)) *)
  0xc4; 0x42; 0x38; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% r8d) (% r10d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 6)) *)
  0xc5; 0xfd; 0xfe; 0xc7;  (* VPADDD (%_% ymm0) (%_% ymm0) (%_% ymm7) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xc7;        (* MOV (% r15d) (% eax) *)
  0xc5; 0xc5; 0x72; 0xd4; 0x03;
                           (* VPSRLD (%_% ymm7) (%_% ymm4) (Imm8 (word 3)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% eax) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x1c; 0x2b;  (* LEA (% r11d) (%%% (r11,0,r13)) *)
  0x41; 0x31; 0xdf;        (* XOR (% r15d) (% ebx) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0e;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 14)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% eax) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% eax) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x14; 0x1a;  (* LEA (% edx) (%%% (rdx,0,r11)) *)
  0xc5; 0xc5; 0xef; 0xe6;  (* VPXOR (%_% ymm4) (%_% ymm7) (%_% ymm6) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xdf;              (* XOR (% edi) (% ebx) *)
  0xc5; 0xfd; 0x70; 0xfb; 0xfa;
                           (* VPSHUFD (%_% ymm7) (%_% ymm3) (Imm8 (word 250)) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x1c; 0x3b;  (* LEA (% r11d) (%%% (r11,0,rdi)) *)
  0x45; 0x89; 0xc4;        (* MOV (% r12d) (% r8d) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x0b;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 11)) *)
  0x44; 0x03; 0x94; 0x24; 0x84; 0x00; 0x00; 0x00;
                           (* ADD (% r10d) (Memop Doubleword (%% (rsp,132))) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% edx) (Imm8 (word 25)) *)
  0xc5; 0xdd; 0xef; 0xe5;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% edi) (% edx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x1c; 0x33;  (* LEA (% r11d) (%%% (r11,0,r14)) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0xc5; 0xd5; 0x72; 0xf5; 0x0b;
                           (* VPSLLD (%_% ymm5) (%_% ymm5) (Imm8 (word 11)) *)
  0xc4; 0x42; 0x68; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% edx) (% r9d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% edx) (Imm8 (word 6)) *)
  0xc5; 0xdd; 0xef; 0xe6;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xdf;        (* MOV (% edi) (% r11d) *)
  0xc5; 0xcd; 0x72; 0xd7; 0x0a;
                           (* VPSRLD (%_% ymm6) (%_% ymm7) (Imm8 (word 10)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% r11d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x14; 0x2a;  (* LEA (% r10d) (%%% (r10,0,r13)) *)
  0x31; 0xc7;              (* XOR (% edi) (% eax) *)
  0xc5; 0xdd; 0xef; 0xe5;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x0c; 0x11;  (* LEA (% ecx) (%%% (rcx,0,r10)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x11;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 17)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xc7;        (* XOR (% r15d) (% eax) *)
  0xc5; 0xfd; 0xfe; 0xc4;  (* VPADDD (%_% ymm0) (%_% ymm0) (%_% ymm4) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x14; 0x3a;  (* LEA (% r10d) (%%% (r10,0,r15)) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0x44; 0x03; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* ADD (% r9d) (Memop Doubleword (%% (rsp,136))) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 25)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x02;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 2)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% r15d) (% ecx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x14; 0x32;  (* LEA (% r10d) (%%% (r10,0,r14)) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0x42; 0x70; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% ecx) (% r8d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 6)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm8) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xd7;        (* MOV (% r15d) (% r10d) *)
  0xc5; 0xfd; 0xfe; 0xc6;  (* VPADDD (%_% ymm0) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% r10d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x0c; 0x29;  (* LEA (% r9d) (%%% (r9,0,r13)) *)
  0x45; 0x31; 0xdf;        (* XOR (% r15d) (% r11d) *)
  0xc5; 0xfd; 0x70; 0xf8; 0x50;
                           (* VPSHUFD (%_% ymm7) (%_% ymm0) (Imm8 (word 80)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x1c; 0x0b;  (* LEA (% ebx) (%%% (rbx,0,r9)) *)
  0xc5; 0xcd; 0x72; 0xd7; 0x0a;
                           (* VPSRLD (%_% ymm6) (%_% ymm7) (Imm8 (word 10)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xdf;        (* XOR (% edi) (% r11d) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x11;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 17)) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x0c; 0x39;  (* LEA (% r9d) (%%% (r9,0,rdi)) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0x44; 0x03; 0x84; 0x24; 0x8c; 0x00; 0x00; 0x00;
                           (* ADD (% r8d) (Memop Doubleword (%% (rsp,140))) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 25)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x02;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% ebx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x0c; 0x31;  (* LEA (% r9d) (%%% (r9,0,r14)) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0x62; 0x60; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% ebx) (% edx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 6)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf1;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm9) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xcf;        (* MOV (% edi) (% r9d) *)
  0xc5; 0xfd; 0xfe; 0xc6;  (* VPADDD (%_% ymm0) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% r9d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x04; 0x28;  (* LEA (% r8d) (%%% (r8,0,r13)) *)
  0x44; 0x31; 0xd7;        (* XOR (% edi) (% r10d) *)
  0xc5; 0xfd; 0xfe; 0x75; 0x00;
                           (* VPADDD (%_% ymm6) (%_% ymm0) (Memop Word256 (%% (rbp,0))) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x04; 0x00;  (* LEA (% eax) (%%% (rax,0,r8)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xd7;        (* XOR (% r15d) (% r10d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x04; 0x38;  (* LEA (% r8d) (%%% (r8,0,r15)) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc5; 0xfd; 0x7f; 0x34; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm6) *)
  0xc4; 0xe3; 0x6d; 0x0f; 0xe1; 0x04;
                           (* VPALIGNR (%_% ymm4) (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0x03; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* ADD (% edx) (Memop Doubleword (%% (rsp,160))) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% eax) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x7d; 0x0f; 0xfb; 0x04;
                           (* VPALIGNR (%_% ymm7) (%_% ymm0) (%_% ymm3) (Imm8 (word 4)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% eax) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x04; 0x30;  (* LEA (% r8d) (%%% (r8,0,r14)) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0xc5; 0xcd; 0x72; 0xd4; 0x07;
                           (* VPSRLD (%_% ymm6) (%_% ymm4) (Imm8 (word 7)) *)
  0xc4; 0x62; 0x78; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% eax) (% ecx) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% eax) (Imm8 (word 6)) *)
  0xc5; 0xf5; 0xfe; 0xcf;  (* VPADDD (%_% ymm1) (%_% ymm1) (%_% ymm7) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xc7;        (* MOV (% r15d) (% r8d) *)
  0xc5; 0xc5; 0x72; 0xd4; 0x03;
                           (* VPSRLD (%_% ymm7) (%_% ymm4) (Imm8 (word 3)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% r8d) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x14; 0x2a;  (* LEA (% edx) (%%% (rdx,0,r13)) *)
  0x45; 0x31; 0xcf;        (* XOR (% r15d) (% r9d) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0e;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 14)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x1c; 0x13;  (* LEA (% r11d) (%%% (r11,0,rdx)) *)
  0xc5; 0xc5; 0xef; 0xe6;  (* VPXOR (%_% ymm4) (%_% ymm7) (%_% ymm6) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xcf;        (* XOR (% edi) (% r9d) *)
  0xc5; 0xfd; 0x70; 0xf8; 0xfa;
                           (* VPSHUFD (%_% ymm7) (%_% ymm0) (Imm8 (word 250)) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x14; 0x3a;        (* LEA (% edx) (%%% (rdx,0,rdi)) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x0b;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 11)) *)
  0x03; 0x8c; 0x24; 0xa4; 0x00; 0x00; 0x00;
                           (* ADD (% ecx) (Memop Doubleword (%% (rsp,164))) *)
  0x45; 0x21; 0xdc;        (* AND (% r12d) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 25)) *)
  0xc5; 0xdd; 0xef; 0xe5;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% r11d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x14; 0x32;  (* LEA (% edx) (%%% (rdx,0,r14)) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0xc5; 0xd5; 0x72; 0xf5; 0x0b;
                           (* VPSLLD (%_% ymm5) (%_% ymm5) (Imm8 (word 11)) *)
  0xc4; 0x62; 0x20; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r11d) (% ebx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 6)) *)
  0xc5; 0xdd; 0xef; 0xe6;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xd7;              (* MOV (% edi) (% edx) *)
  0xc5; 0xcd; 0x72; 0xd7; 0x0a;
                           (* VPSRLD (%_% ymm6) (%_% ymm7) (Imm8 (word 10)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% edx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x0c; 0x29;  (* LEA (% ecx) (%%% (rcx,0,r13)) *)
  0x44; 0x31; 0xc7;        (* XOR (% edi) (% r8d) *)
  0xc5; 0xdd; 0xef; 0xe5;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% edx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% edx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x14; 0x0a;  (* LEA (% r10d) (%%% (r10,0,rcx)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x11;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 17)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xc7;        (* XOR (% r15d) (% r8d) *)
  0xc5; 0xf5; 0xfe; 0xcc;  (* VPADDD (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x0c; 0x39;  (* LEA (% ecx) (%%% (rcx,0,r15)) *)
  0x45; 0x89; 0xdc;        (* MOV (% r12d) (% r11d) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0x03; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* ADD (% ebx) (Memop Doubleword (%% (rsp,168))) *)
  0x45; 0x21; 0xd4;        (* AND (% r12d) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 25)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x02;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 2)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% r15d) (% r10d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x0c; 0x31;  (* LEA (% ecx) (%%% (rcx,0,r14)) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0x62; 0x28; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% r10d) (% eax) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 6)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm8) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xcf;        (* MOV (% r15d) (% ecx) *)
  0xc5; 0xf5; 0xfe; 0xce;  (* VPADDD (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% ecx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x1c; 0x2b;  (* LEA (% ebx) (%%% (rbx,0,r13)) *)
  0x41; 0x31; 0xd7;        (* XOR (% r15d) (% edx) *)
  0xc5; 0xfd; 0x70; 0xf9; 0x50;
                           (* VPSHUFD (%_% ymm7) (%_% ymm1) (Imm8 (word 80)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x0c; 0x19;  (* LEA (% r9d) (%%% (r9,0,rbx)) *)
  0xc5; 0xcd; 0x72; 0xd7; 0x0a;
                           (* VPSRLD (%_% ymm6) (%_% ymm7) (Imm8 (word 10)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xd7;              (* XOR (% edi) (% edx) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x11;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 17)) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x1c; 0x3b;        (* LEA (% ebx) (%%% (rbx,0,rdi)) *)
  0x45; 0x89; 0xd4;        (* MOV (% r12d) (% r10d) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0x03; 0x84; 0x24; 0xac; 0x00; 0x00; 0x00;
                           (* ADD (% eax) (Memop Doubleword (%% (rsp,172))) *)
  0x45; 0x21; 0xcc;        (* AND (% r12d) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 25)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x02;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 2)) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% edi) (% r9d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x1c; 0x33;  (* LEA (% ebx) (%%% (rbx,0,r14)) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0x42; 0x30; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r9d) (% r11d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 6)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf1;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm9) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xdf;              (* MOV (% edi) (% ebx) *)
  0xc5; 0xf5; 0xfe; 0xce;  (* VPADDD (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% ebx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x04; 0x28;  (* LEA (% eax) (%%% (rax,0,r13)) *)
  0x31; 0xcf;              (* XOR (% edi) (% ecx) *)
  0xc5; 0xf5; 0xfe; 0x75; 0x20;
                           (* VPADDD (%_% ymm6) (%_% ymm1) (Memop Word256 (%% (rbp,32))) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x04; 0x00;  (* LEA (% r8d) (%%% (r8,0,rax)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xcf;        (* XOR (% r15d) (% ecx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x04; 0x38;  (* LEA (% eax) (%%% (rax,0,r15)) *)
  0x45; 0x89; 0xcc;        (* MOV (% r12d) (% r9d) *)
  0xc5; 0xfd; 0x7f; 0x74; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm6) *)
  0x48; 0x8d; 0x64; 0x24; 0xc0;
                           (* LEA (% rsp) (%% (rsp,18446744073709551552)) *)
  0xff; 0x74; 0x24; 0x38;  (* PUSH (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8d; 0x64; 0x24; 0x08;
                           (* LEA (% rsp) (%% (rsp,8)) *)
  0xc4; 0xe3; 0x65; 0x0f; 0xe2; 0x04;
                           (* VPALIGNR (%_% ymm4) (%_% ymm3) (%_% ymm2) (Imm8 (word 4)) *)
  0x44; 0x03; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% r11d) (Memop Doubleword (%% (rsp,128))) *)
  0x45; 0x21; 0xc4;        (* AND (% r12d) (% r8d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x75; 0x0f; 0xf8; 0x04;
                           (* VPALIGNR (%_% ymm7) (%_% ymm1) (%_% ymm0) (Imm8 (word 4)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% r8d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x04; 0x30;  (* LEA (% eax) (%%% (rax,0,r14)) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0xc5; 0xcd; 0x72; 0xd4; 0x07;
                           (* VPSRLD (%_% ymm6) (%_% ymm4) (Imm8 (word 7)) *)
  0xc4; 0x42; 0x38; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% r8d) (% r10d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 6)) *)
  0xc5; 0xed; 0xfe; 0xd7;  (* VPADDD (%_% ymm2) (%_% ymm2) (%_% ymm7) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xc7;        (* MOV (% r15d) (% eax) *)
  0xc5; 0xc5; 0x72; 0xd4; 0x03;
                           (* VPSRLD (%_% ymm7) (%_% ymm4) (Imm8 (word 3)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% eax) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x1c; 0x2b;  (* LEA (% r11d) (%%% (r11,0,r13)) *)
  0x41; 0x31; 0xdf;        (* XOR (% r15d) (% ebx) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0e;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 14)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% eax) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% eax) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x14; 0x1a;  (* LEA (% edx) (%%% (rdx,0,r11)) *)
  0xc5; 0xc5; 0xef; 0xe6;  (* VPXOR (%_% ymm4) (%_% ymm7) (%_% ymm6) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xdf;              (* XOR (% edi) (% ebx) *)
  0xc5; 0xfd; 0x70; 0xf9; 0xfa;
                           (* VPSHUFD (%_% ymm7) (%_% ymm1) (Imm8 (word 250)) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x1c; 0x3b;  (* LEA (% r11d) (%%% (r11,0,rdi)) *)
  0x45; 0x89; 0xc4;        (* MOV (% r12d) (% r8d) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x0b;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 11)) *)
  0x44; 0x03; 0x94; 0x24; 0x84; 0x00; 0x00; 0x00;
                           (* ADD (% r10d) (Memop Doubleword (%% (rsp,132))) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% edx) (Imm8 (word 25)) *)
  0xc5; 0xdd; 0xef; 0xe5;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% edi) (% edx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x1c; 0x33;  (* LEA (% r11d) (%%% (r11,0,r14)) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0xc5; 0xd5; 0x72; 0xf5; 0x0b;
                           (* VPSLLD (%_% ymm5) (%_% ymm5) (Imm8 (word 11)) *)
  0xc4; 0x42; 0x68; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% edx) (% r9d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% edx) (Imm8 (word 6)) *)
  0xc5; 0xdd; 0xef; 0xe6;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xdf;        (* MOV (% edi) (% r11d) *)
  0xc5; 0xcd; 0x72; 0xd7; 0x0a;
                           (* VPSRLD (%_% ymm6) (%_% ymm7) (Imm8 (word 10)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% r11d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x14; 0x2a;  (* LEA (% r10d) (%%% (r10,0,r13)) *)
  0x31; 0xc7;              (* XOR (% edi) (% eax) *)
  0xc5; 0xdd; 0xef; 0xe5;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x0c; 0x11;  (* LEA (% ecx) (%%% (rcx,0,r10)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x11;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 17)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xc7;        (* XOR (% r15d) (% eax) *)
  0xc5; 0xed; 0xfe; 0xd4;  (* VPADDD (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x14; 0x3a;  (* LEA (% r10d) (%%% (r10,0,r15)) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0x44; 0x03; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* ADD (% r9d) (Memop Doubleword (%% (rsp,136))) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 25)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x02;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 2)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% r15d) (% ecx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x14; 0x32;  (* LEA (% r10d) (%%% (r10,0,r14)) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0x42; 0x70; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% ecx) (% r8d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 6)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm8) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xd7;        (* MOV (% r15d) (% r10d) *)
  0xc5; 0xed; 0xfe; 0xd6;  (* VPADDD (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% r10d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x0c; 0x29;  (* LEA (% r9d) (%%% (r9,0,r13)) *)
  0x45; 0x31; 0xdf;        (* XOR (% r15d) (% r11d) *)
  0xc5; 0xfd; 0x70; 0xfa; 0x50;
                           (* VPSHUFD (%_% ymm7) (%_% ymm2) (Imm8 (word 80)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x1c; 0x0b;  (* LEA (% ebx) (%%% (rbx,0,r9)) *)
  0xc5; 0xcd; 0x72; 0xd7; 0x0a;
                           (* VPSRLD (%_% ymm6) (%_% ymm7) (Imm8 (word 10)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xdf;        (* XOR (% edi) (% r11d) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x11;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 17)) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x0c; 0x39;  (* LEA (% r9d) (%%% (r9,0,rdi)) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0x44; 0x03; 0x84; 0x24; 0x8c; 0x00; 0x00; 0x00;
                           (* ADD (% r8d) (Memop Doubleword (%% (rsp,140))) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 25)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x02;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% ebx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x0c; 0x31;  (* LEA (% r9d) (%%% (r9,0,r14)) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0x62; 0x60; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% ebx) (% edx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 6)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf1;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm9) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xcf;        (* MOV (% edi) (% r9d) *)
  0xc5; 0xed; 0xfe; 0xd6;  (* VPADDD (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% r9d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x04; 0x28;  (* LEA (% r8d) (%%% (r8,0,r13)) *)
  0x44; 0x31; 0xd7;        (* XOR (% edi) (% r10d) *)
  0xc5; 0xed; 0xfe; 0x75; 0x40;
                           (* VPADDD (%_% ymm6) (%_% ymm2) (Memop Word256 (%% (rbp,64))) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x04; 0x00;  (* LEA (% eax) (%%% (rax,0,r8)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xd7;        (* XOR (% r15d) (% r10d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x04; 0x38;  (* LEA (% r8d) (%%% (r8,0,r15)) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc5; 0xfd; 0x7f; 0x34; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm6) *)
  0xc4; 0xe3; 0x7d; 0x0f; 0xe3; 0x04;
                           (* VPALIGNR (%_% ymm4) (%_% ymm0) (%_% ymm3) (Imm8 (word 4)) *)
  0x03; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* ADD (% edx) (Memop Doubleword (%% (rsp,160))) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% eax) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x6d; 0x0f; 0xf9; 0x04;
                           (* VPALIGNR (%_% ymm7) (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% eax) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x04; 0x30;  (* LEA (% r8d) (%%% (r8,0,r14)) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0xc5; 0xcd; 0x72; 0xd4; 0x07;
                           (* VPSRLD (%_% ymm6) (%_% ymm4) (Imm8 (word 7)) *)
  0xc4; 0x62; 0x78; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% eax) (% ecx) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% eax) (Imm8 (word 6)) *)
  0xc5; 0xe5; 0xfe; 0xdf;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm7) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xc7;        (* MOV (% r15d) (% r8d) *)
  0xc5; 0xc5; 0x72; 0xd4; 0x03;
                           (* VPSRLD (%_% ymm7) (%_% ymm4) (Imm8 (word 3)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% r8d) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x14; 0x2a;  (* LEA (% edx) (%%% (rdx,0,r13)) *)
  0x45; 0x31; 0xcf;        (* XOR (% r15d) (% r9d) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0e;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 14)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x1c; 0x13;  (* LEA (% r11d) (%%% (r11,0,rdx)) *)
  0xc5; 0xc5; 0xef; 0xe6;  (* VPXOR (%_% ymm4) (%_% ymm7) (%_% ymm6) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xcf;        (* XOR (% edi) (% r9d) *)
  0xc5; 0xfd; 0x70; 0xfa; 0xfa;
                           (* VPSHUFD (%_% ymm7) (%_% ymm2) (Imm8 (word 250)) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x14; 0x3a;        (* LEA (% edx) (%%% (rdx,0,rdi)) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x0b;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 11)) *)
  0x03; 0x8c; 0x24; 0xa4; 0x00; 0x00; 0x00;
                           (* ADD (% ecx) (Memop Doubleword (%% (rsp,164))) *)
  0x45; 0x21; 0xdc;        (* AND (% r12d) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 25)) *)
  0xc5; 0xdd; 0xef; 0xe5;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% r11d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x14; 0x32;  (* LEA (% edx) (%%% (rdx,0,r14)) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0xc5; 0xd5; 0x72; 0xf5; 0x0b;
                           (* VPSLLD (%_% ymm5) (%_% ymm5) (Imm8 (word 11)) *)
  0xc4; 0x62; 0x20; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r11d) (% ebx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 6)) *)
  0xc5; 0xdd; 0xef; 0xe6;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xd7;              (* MOV (% edi) (% edx) *)
  0xc5; 0xcd; 0x72; 0xd7; 0x0a;
                           (* VPSRLD (%_% ymm6) (%_% ymm7) (Imm8 (word 10)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% edx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x0c; 0x29;  (* LEA (% ecx) (%%% (rcx,0,r13)) *)
  0x44; 0x31; 0xc7;        (* XOR (% edi) (% r8d) *)
  0xc5; 0xdd; 0xef; 0xe5;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% edx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% edx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x14; 0x0a;  (* LEA (% r10d) (%%% (r10,0,rcx)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x11;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 17)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xc7;        (* XOR (% r15d) (% r8d) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x0c; 0x39;  (* LEA (% ecx) (%%% (rcx,0,r15)) *)
  0x45; 0x89; 0xdc;        (* MOV (% r12d) (% r11d) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0x03; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* ADD (% ebx) (Memop Doubleword (%% (rsp,168))) *)
  0x45; 0x21; 0xd4;        (* AND (% r12d) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 25)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x02;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 2)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% r15d) (% r10d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x0c; 0x31;  (* LEA (% ecx) (%%% (rcx,0,r14)) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0x62; 0x28; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% r10d) (% eax) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 6)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm8) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xcf;        (* MOV (% r15d) (% ecx) *)
  0xc5; 0xe5; 0xfe; 0xde;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% ecx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x1c; 0x2b;  (* LEA (% ebx) (%%% (rbx,0,r13)) *)
  0x41; 0x31; 0xd7;        (* XOR (% r15d) (% edx) *)
  0xc5; 0xfd; 0x70; 0xfb; 0x50;
                           (* VPSHUFD (%_% ymm7) (%_% ymm3) (Imm8 (word 80)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x0c; 0x19;  (* LEA (% r9d) (%%% (r9,0,rbx)) *)
  0xc5; 0xcd; 0x72; 0xd7; 0x0a;
                           (* VPSRLD (%_% ymm6) (%_% ymm7) (Imm8 (word 10)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xd7;              (* XOR (% edi) (% edx) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x11;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 17)) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x1c; 0x3b;        (* LEA (% ebx) (%%% (rbx,0,rdi)) *)
  0x45; 0x89; 0xd4;        (* MOV (% r12d) (% r10d) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0x03; 0x84; 0x24; 0xac; 0x00; 0x00; 0x00;
                           (* ADD (% eax) (Memop Doubleword (%% (rsp,172))) *)
  0x45; 0x21; 0xcc;        (* AND (% r12d) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 25)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x02;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 2)) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% edi) (% r9d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x1c; 0x33;  (* LEA (% ebx) (%%% (rbx,0,r14)) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0x42; 0x30; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r9d) (% r11d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 6)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf1;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm9) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xdf;              (* MOV (% edi) (% ebx) *)
  0xc5; 0xe5; 0xfe; 0xde;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% ebx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x04; 0x28;  (* LEA (% eax) (%%% (rax,0,r13)) *)
  0x31; 0xcf;              (* XOR (% edi) (% ecx) *)
  0xc5; 0xe5; 0xfe; 0x75; 0x60;
                           (* VPADDD (%_% ymm6) (%_% ymm3) (Memop Word256 (%% (rbp,96))) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x04; 0x00;  (* LEA (% r8d) (%%% (r8,0,rax)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xcf;        (* XOR (% r15d) (% ecx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x04; 0x38;  (* LEA (% eax) (%%% (rax,0,r15)) *)
  0x45; 0x89; 0xcc;        (* MOV (% r12d) (% r9d) *)
  0xc5; 0xfd; 0x7f; 0x74; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm6) *)
  0x48; 0x8d; 0xad; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rbp,128)) *)
  0x80; 0x7d; 0x03; 0x00;  (* CMP (Memop Byte (%% (rbp,3))) (Imm8 (word 0)) *)
  0x0f; 0x85; 0x35; 0xf7; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294965045)) *)
  0x44; 0x03; 0x5c; 0x24; 0x40;
                           (* ADD (% r11d) (Memop Doubleword (%% (rsp,64))) *)
  0x45; 0x21; 0xc4;        (* AND (% r12d) (% r8d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 25)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% r8d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x04; 0x30;  (* LEA (% eax) (%%% (rax,0,r14)) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0xc4; 0x42; 0x38; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% r8d) (% r10d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xc7;        (* MOV (% r15d) (% eax) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% eax) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x1c; 0x2b;  (* LEA (% r11d) (%%% (r11,0,r13)) *)
  0x41; 0x31; 0xdf;        (* XOR (% r15d) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% eax) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% eax) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x14; 0x1a;  (* LEA (% edx) (%%% (rdx,0,r11)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xdf;              (* XOR (% edi) (% ebx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x1c; 0x3b;  (* LEA (% r11d) (%%% (r11,0,rdi)) *)
  0x45; 0x89; 0xc4;        (* MOV (% r12d) (% r8d) *)
  0x44; 0x03; 0x54; 0x24; 0x44;
                           (* ADD (% r10d) (Memop Doubleword (%% (rsp,68))) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% edx) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% edi) (% edx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x1c; 0x33;  (* LEA (% r11d) (%%% (r11,0,r14)) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0xc4; 0x42; 0x68; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% edx) (% r9d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% edx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xdf;        (* MOV (% edi) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% r11d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x14; 0x2a;  (* LEA (% r10d) (%%% (r10,0,r13)) *)
  0x31; 0xc7;              (* XOR (% edi) (% eax) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x0c; 0x11;  (* LEA (% ecx) (%%% (rcx,0,r10)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xc7;        (* XOR (% r15d) (% eax) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x14; 0x3a;  (* LEA (% r10d) (%%% (r10,0,r15)) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0x44; 0x03; 0x4c; 0x24; 0x48;
                           (* ADD (% r9d) (Memop Doubleword (%% (rsp,72))) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 25)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% r15d) (% ecx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x14; 0x32;  (* LEA (% r10d) (%%% (r10,0,r14)) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0xc4; 0x42; 0x70; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% ecx) (% r8d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xd7;        (* MOV (% r15d) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% r10d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x0c; 0x29;  (* LEA (% r9d) (%%% (r9,0,r13)) *)
  0x45; 0x31; 0xdf;        (* XOR (% r15d) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x1c; 0x0b;  (* LEA (% ebx) (%%% (rbx,0,r9)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xdf;        (* XOR (% edi) (% r11d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x0c; 0x39;  (* LEA (% r9d) (%%% (r9,0,rdi)) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0x44; 0x03; 0x44; 0x24; 0x4c;
                           (* ADD (% r8d) (Memop Doubleword (%% (rsp,76))) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% ebx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x0c; 0x31;  (* LEA (% r9d) (%%% (r9,0,r14)) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0xc4; 0x62; 0x60; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% ebx) (% edx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xcf;        (* MOV (% edi) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% r9d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x04; 0x28;  (* LEA (% r8d) (%%% (r8,0,r13)) *)
  0x44; 0x31; 0xd7;        (* XOR (% edi) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x04; 0x00;  (* LEA (% eax) (%%% (rax,0,r8)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xd7;        (* XOR (% r15d) (% r10d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x04; 0x38;  (* LEA (% r8d) (%%% (r8,0,r15)) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0x03; 0x54; 0x24; 0x60;  (* ADD (% edx) (Memop Doubleword (%% (rsp,96))) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% eax) (Imm8 (word 25)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% eax) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x04; 0x30;  (* LEA (% r8d) (%%% (r8,0,r14)) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0xc4; 0x62; 0x78; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% eax) (% ecx) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% eax) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xc7;        (* MOV (% r15d) (% r8d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% r8d) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x14; 0x2a;  (* LEA (% edx) (%%% (rdx,0,r13)) *)
  0x45; 0x31; 0xcf;        (* XOR (% r15d) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x1c; 0x13;  (* LEA (% r11d) (%%% (r11,0,rdx)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xcf;        (* XOR (% edi) (% r9d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x14; 0x3a;        (* LEA (% edx) (%%% (rdx,0,rdi)) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0x03; 0x4c; 0x24; 0x64;  (* ADD (% ecx) (Memop Doubleword (%% (rsp,100))) *)
  0x45; 0x21; 0xdc;        (* AND (% r12d) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 25)) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% r11d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x14; 0x32;  (* LEA (% edx) (%%% (rdx,0,r14)) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0xc4; 0x62; 0x20; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r11d) (% ebx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xd7;              (* MOV (% edi) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% edx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x0c; 0x29;  (* LEA (% ecx) (%%% (rcx,0,r13)) *)
  0x44; 0x31; 0xc7;        (* XOR (% edi) (% r8d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% edx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% edx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x14; 0x0a;  (* LEA (% r10d) (%%% (r10,0,rcx)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xc7;        (* XOR (% r15d) (% r8d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x0c; 0x39;  (* LEA (% ecx) (%%% (rcx,0,r15)) *)
  0x45; 0x89; 0xdc;        (* MOV (% r12d) (% r11d) *)
  0x03; 0x5c; 0x24; 0x68;  (* ADD (% ebx) (Memop Doubleword (%% (rsp,104))) *)
  0x45; 0x21; 0xd4;        (* AND (% r12d) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 25)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% r15d) (% r10d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x0c; 0x31;  (* LEA (% ecx) (%%% (rcx,0,r14)) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0xc4; 0x62; 0x28; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% r10d) (% eax) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xcf;        (* MOV (% r15d) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% ecx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x1c; 0x2b;  (* LEA (% ebx) (%%% (rbx,0,r13)) *)
  0x41; 0x31; 0xd7;        (* XOR (% r15d) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x0c; 0x19;  (* LEA (% r9d) (%%% (r9,0,rbx)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xd7;              (* XOR (% edi) (% edx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x1c; 0x3b;        (* LEA (% ebx) (%%% (rbx,0,rdi)) *)
  0x45; 0x89; 0xd4;        (* MOV (% r12d) (% r10d) *)
  0x03; 0x44; 0x24; 0x6c;  (* ADD (% eax) (Memop Doubleword (%% (rsp,108))) *)
  0x45; 0x21; 0xcc;        (* AND (% r12d) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 25)) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% edi) (% r9d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x1c; 0x33;  (* LEA (% ebx) (%%% (rbx,0,r14)) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0xc4; 0x42; 0x30; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r9d) (% r11d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xdf;              (* MOV (% edi) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% ebx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x04; 0x28;  (* LEA (% eax) (%%% (rax,0,r13)) *)
  0x31; 0xcf;              (* XOR (% edi) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x04; 0x00;  (* LEA (% r8d) (%%% (r8,0,rax)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xcf;        (* XOR (% r15d) (% ecx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x04; 0x38;  (* LEA (% eax) (%%% (rax,0,r15)) *)
  0x45; 0x89; 0xcc;        (* MOV (% r12d) (% r9d) *)
  0x44; 0x03; 0x1c; 0x24;  (* ADD (% r11d) (Memop Doubleword (%% (rsp,0))) *)
  0x45; 0x21; 0xc4;        (* AND (% r12d) (% r8d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 25)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% r8d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x04; 0x30;  (* LEA (% eax) (%%% (rax,0,r14)) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0xc4; 0x42; 0x38; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% r8d) (% r10d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xc7;        (* MOV (% r15d) (% eax) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% eax) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x1c; 0x2b;  (* LEA (% r11d) (%%% (r11,0,r13)) *)
  0x41; 0x31; 0xdf;        (* XOR (% r15d) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% eax) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% eax) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x14; 0x1a;  (* LEA (% edx) (%%% (rdx,0,r11)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xdf;              (* XOR (% edi) (% ebx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x1c; 0x3b;  (* LEA (% r11d) (%%% (r11,0,rdi)) *)
  0x45; 0x89; 0xc4;        (* MOV (% r12d) (% r8d) *)
  0x44; 0x03; 0x54; 0x24; 0x04;
                           (* ADD (% r10d) (Memop Doubleword (%% (rsp,4))) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% edx) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% edi) (% edx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x1c; 0x33;  (* LEA (% r11d) (%%% (r11,0,r14)) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0xc4; 0x42; 0x68; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% edx) (% r9d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% edx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xdf;        (* MOV (% edi) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% r11d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x14; 0x2a;  (* LEA (% r10d) (%%% (r10,0,r13)) *)
  0x31; 0xc7;              (* XOR (% edi) (% eax) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x0c; 0x11;  (* LEA (% ecx) (%%% (rcx,0,r10)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xc7;        (* XOR (% r15d) (% eax) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x14; 0x3a;  (* LEA (% r10d) (%%% (r10,0,r15)) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0x44; 0x03; 0x4c; 0x24; 0x08;
                           (* ADD (% r9d) (Memop Doubleword (%% (rsp,8))) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 25)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% r15d) (% ecx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x14; 0x32;  (* LEA (% r10d) (%%% (r10,0,r14)) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0xc4; 0x42; 0x70; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% ecx) (% r8d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xd7;        (* MOV (% r15d) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% r10d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x0c; 0x29;  (* LEA (% r9d) (%%% (r9,0,r13)) *)
  0x45; 0x31; 0xdf;        (* XOR (% r15d) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x1c; 0x0b;  (* LEA (% ebx) (%%% (rbx,0,r9)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xdf;        (* XOR (% edi) (% r11d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x0c; 0x39;  (* LEA (% r9d) (%%% (r9,0,rdi)) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0x44; 0x03; 0x44; 0x24; 0x0c;
                           (* ADD (% r8d) (Memop Doubleword (%% (rsp,12))) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% ebx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x0c; 0x31;  (* LEA (% r9d) (%%% (r9,0,r14)) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0xc4; 0x62; 0x60; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% ebx) (% edx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xcf;        (* MOV (% edi) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% r9d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x04; 0x28;  (* LEA (% r8d) (%%% (r8,0,r13)) *)
  0x44; 0x31; 0xd7;        (* XOR (% edi) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x04; 0x00;  (* LEA (% eax) (%%% (rax,0,r8)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xd7;        (* XOR (% r15d) (% r10d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x04; 0x38;  (* LEA (% r8d) (%%% (r8,0,r15)) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0x03; 0x54; 0x24; 0x20;  (* ADD (% edx) (Memop Doubleword (%% (rsp,32))) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% eax) (Imm8 (word 25)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% eax) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x04; 0x30;  (* LEA (% r8d) (%%% (r8,0,r14)) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0xc4; 0x62; 0x78; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% eax) (% ecx) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% eax) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xc7;        (* MOV (% r15d) (% r8d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% r8d) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x14; 0x2a;  (* LEA (% edx) (%%% (rdx,0,r13)) *)
  0x45; 0x31; 0xcf;        (* XOR (% r15d) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x1c; 0x13;  (* LEA (% r11d) (%%% (r11,0,rdx)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xcf;        (* XOR (% edi) (% r9d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x14; 0x3a;        (* LEA (% edx) (%%% (rdx,0,rdi)) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0x03; 0x4c; 0x24; 0x24;  (* ADD (% ecx) (Memop Doubleword (%% (rsp,36))) *)
  0x45; 0x21; 0xdc;        (* AND (% r12d) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 25)) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% r11d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x14; 0x32;  (* LEA (% edx) (%%% (rdx,0,r14)) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0xc4; 0x62; 0x20; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r11d) (% ebx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xd7;              (* MOV (% edi) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% edx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x0c; 0x29;  (* LEA (% ecx) (%%% (rcx,0,r13)) *)
  0x44; 0x31; 0xc7;        (* XOR (% edi) (% r8d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% edx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% edx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x14; 0x0a;  (* LEA (% r10d) (%%% (r10,0,rcx)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xc7;        (* XOR (% r15d) (% r8d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x0c; 0x39;  (* LEA (% ecx) (%%% (rcx,0,r15)) *)
  0x45; 0x89; 0xdc;        (* MOV (% r12d) (% r11d) *)
  0x03; 0x5c; 0x24; 0x28;  (* ADD (% ebx) (Memop Doubleword (%% (rsp,40))) *)
  0x45; 0x21; 0xd4;        (* AND (% r12d) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 25)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% r15d) (% r10d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x0c; 0x31;  (* LEA (% ecx) (%%% (rcx,0,r14)) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0xc4; 0x62; 0x28; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% r10d) (% eax) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xcf;        (* MOV (% r15d) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% ecx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x1c; 0x2b;  (* LEA (% ebx) (%%% (rbx,0,r13)) *)
  0x41; 0x31; 0xd7;        (* XOR (% r15d) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x0c; 0x19;  (* LEA (% r9d) (%%% (r9,0,rbx)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xd7;              (* XOR (% edi) (% edx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x1c; 0x3b;        (* LEA (% ebx) (%%% (rbx,0,rdi)) *)
  0x45; 0x89; 0xd4;        (* MOV (% r12d) (% r10d) *)
  0x03; 0x44; 0x24; 0x2c;  (* ADD (% eax) (Memop Doubleword (%% (rsp,44))) *)
  0x45; 0x21; 0xcc;        (* AND (% r12d) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 25)) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% edi) (% r9d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x1c; 0x33;  (* LEA (% ebx) (%%% (rbx,0,r14)) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0xc4; 0x42; 0x30; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r9d) (% r11d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xdf;              (* MOV (% edi) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% ebx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x04; 0x28;  (* LEA (% eax) (%%% (rax,0,r13)) *)
  0x31; 0xcf;              (* XOR (% edi) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x04; 0x00;  (* LEA (% r8d) (%%% (r8,0,rax)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xcf;        (* XOR (% r15d) (% ecx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x04; 0x38;  (* LEA (% eax) (%%% (rax,0,r15)) *)
  0x45; 0x89; 0xcc;        (* MOV (% r12d) (% r9d) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,512))) *)
  0x44; 0x01; 0xf0;        (* ADD (% eax) (% r14d) *)
  0x48; 0x8d; 0xac; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,448)) *)
  0x03; 0x07;              (* ADD (% eax) (Memop Doubleword (%% (rdi,0))) *)
  0x03; 0x5f; 0x04;        (* ADD (% ebx) (Memop Doubleword (%% (rdi,4))) *)
  0x03; 0x4f; 0x08;        (* ADD (% ecx) (Memop Doubleword (%% (rdi,8))) *)
  0x03; 0x57; 0x0c;        (* ADD (% edx) (Memop Doubleword (%% (rdi,12))) *)
  0x44; 0x03; 0x47; 0x10;  (* ADD (% r8d) (Memop Doubleword (%% (rdi,16))) *)
  0x44; 0x03; 0x4f; 0x14;  (* ADD (% r9d) (Memop Doubleword (%% (rdi,20))) *)
  0x44; 0x03; 0x57; 0x18;  (* ADD (% r10d) (Memop Doubleword (%% (rdi,24))) *)
  0x44; 0x03; 0x5f; 0x1c;  (* ADD (% r11d) (Memop Doubleword (%% (rdi,28))) *)
  0x89; 0x07;              (* MOV (Memop Doubleword (%% (rdi,0))) (% eax) *)
  0x89; 0x5f; 0x04;        (* MOV (Memop Doubleword (%% (rdi,4))) (% ebx) *)
  0x89; 0x4f; 0x08;        (* MOV (Memop Doubleword (%% (rdi,8))) (% ecx) *)
  0x89; 0x57; 0x0c;        (* MOV (Memop Doubleword (%% (rdi,12))) (% edx) *)
  0x44; 0x89; 0x47; 0x10;  (* MOV (Memop Doubleword (%% (rdi,16))) (% r8d) *)
  0x44; 0x89; 0x4f; 0x14;  (* MOV (Memop Doubleword (%% (rdi,20))) (% r9d) *)
  0x44; 0x89; 0x57; 0x18;  (* MOV (Memop Doubleword (%% (rdi,24))) (% r10d) *)
  0x44; 0x89; 0x5f; 0x1c;  (* MOV (Memop Doubleword (%% (rdi,28))) (% r11d) *)
  0x48; 0x3b; 0x75; 0x50;  (* CMP (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x0f; 0x84; 0x9a; 0x03; 0x00; 0x00;
                           (* JE (Imm32 (word 922)) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x89; 0xdf;              (* MOV (% edi) (% ebx) *)
  0x31; 0xcf;              (* XOR (% edi) (% ecx) *)
  0x45; 0x89; 0xcc;        (* MOV (% r12d) (% r9d) *)
  0xeb; 0x0f;              (* JMP (Imm8 (word 15)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%%% (rax,0,rax))) *)
  0x44; 0x03; 0x5d; 0x10;  (* ADD (% r11d) (Memop Doubleword (%% (rbp,16))) *)
  0x45; 0x21; 0xc4;        (* AND (% r12d) (% r8d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 25)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% r8d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x04; 0x30;  (* LEA (% eax) (%%% (rax,0,r14)) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0xc4; 0x42; 0x38; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% r8d) (% r10d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x1c; 0x23;  (* LEA (% r11d) (%%% (r11,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xc7;        (* MOV (% r15d) (% eax) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% eax) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x1c; 0x2b;  (* LEA (% r11d) (%%% (r11,0,r13)) *)
  0x41; 0x31; 0xdf;        (* XOR (% r15d) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% eax) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% eax) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x14; 0x1a;  (* LEA (% edx) (%%% (rdx,0,r11)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xdf;              (* XOR (% edi) (% ebx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x1c; 0x3b;  (* LEA (% r11d) (%%% (r11,0,rdi)) *)
  0x45; 0x89; 0xc4;        (* MOV (% r12d) (% r8d) *)
  0x44; 0x03; 0x55; 0x14;  (* ADD (% r10d) (Memop Doubleword (%% (rbp,20))) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% edx) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% edi) (% edx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x1c; 0x33;  (* LEA (% r11d) (%%% (r11,0,r14)) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0xc4; 0x42; 0x68; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% edx) (% r9d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% edx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x14; 0x22;  (* LEA (% r10d) (%%% (r10,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xdf;        (* MOV (% edi) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% r11d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x14; 0x2a;  (* LEA (% r10d) (%%% (r10,0,r13)) *)
  0x31; 0xc7;              (* XOR (% edi) (% eax) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x0c; 0x11;  (* LEA (% ecx) (%%% (rcx,0,r10)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xc7;        (* XOR (% r15d) (% eax) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x14; 0x3a;  (* LEA (% r10d) (%%% (r10,0,r15)) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0x44; 0x03; 0x4d; 0x18;  (* ADD (% r9d) (Memop Doubleword (%% (rbp,24))) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 25)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% r15d) (% ecx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x14; 0x32;  (* LEA (% r10d) (%%% (r10,0,r14)) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0xc4; 0x42; 0x70; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% ecx) (% r8d) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x0c; 0x21;  (* LEA (% r9d) (%%% (r9,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xd7;        (* MOV (% r15d) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% r10d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x0c; 0x29;  (* LEA (% r9d) (%%% (r9,0,r13)) *)
  0x45; 0x31; 0xdf;        (* XOR (% r15d) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x1c; 0x0b;  (* LEA (% ebx) (%%% (rbx,0,r9)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xdf;        (* XOR (% edi) (% r11d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x45; 0x8d; 0x0c; 0x39;  (* LEA (% r9d) (%%% (r9,0,rdi)) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0x44; 0x03; 0x45; 0x1c;  (* ADD (% r8d) (Memop Doubleword (%% (rbp,28))) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 25)) *)
  0xc4; 0xe3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% ebx) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x0c; 0x31;  (* LEA (% r9d) (%%% (r9,0,r14)) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0xc4; 0x62; 0x60; 0xf2; 0xe2;
                           (* ANDN (% r12d) (% ebx) (% edx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 6)) *)
  0x47; 0x8d; 0x04; 0x20;  (* LEA (% r8d) (%%% (r8,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x44; 0x89; 0xcf;        (* MOV (% edi) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% r9d) (Imm8 (word 22)) *)
  0x47; 0x8d; 0x04; 0x28;  (* LEA (% r8d) (%%% (r8,0,r13)) *)
  0x44; 0x31; 0xd7;        (* XOR (% edi) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 2)) *)
  0x42; 0x8d; 0x04; 0x00;  (* LEA (% eax) (%%% (rax,0,r8)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xd7;        (* XOR (% r15d) (% r10d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x47; 0x8d; 0x04; 0x38;  (* LEA (% r8d) (%%% (r8,0,r15)) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0x03; 0x55; 0x30;        (* ADD (% edx) (Memop Doubleword (%% (rbp,48))) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe8; 0x19;
                           (* RORX (% r13d) (% eax) (Imm8 (word 25)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf8; 0x0b;
                           (* RORX (% r15d) (% eax) (Imm8 (word 11)) *)
  0x47; 0x8d; 0x04; 0x30;  (* LEA (% r8d) (%%% (r8,0,r14)) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0xc4; 0x62; 0x78; 0xf2; 0xe1;
                           (* ANDN (% r12d) (% eax) (% ecx) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf0; 0x06;
                           (* RORX (% r14d) (% eax) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x14; 0x22;  (* LEA (% edx) (%%% (rdx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x45; 0x89; 0xc7;        (* MOV (% r15d) (% r8d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe0; 0x16;
                           (* RORX (% r12d) (% r8d) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x14; 0x2a;  (* LEA (% edx) (%%% (rdx,0,r13)) *)
  0x45; 0x31; 0xcf;        (* XOR (% r15d) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf0; 0x0d;
                           (* RORX (% r14d) (% r8d) (Imm8 (word 13)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe8; 0x02;
                           (* RORX (% r13d) (% r8d) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x1c; 0x13;  (* LEA (% r11d) (%%% (r11,0,rdx)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x44; 0x31; 0xcf;        (* XOR (% edi) (% r9d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x14; 0x3a;        (* LEA (% edx) (%%% (rdx,0,rdi)) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0x03; 0x4d; 0x34;        (* ADD (% ecx) (Memop Doubleword (%% (rbp,52))) *)
  0x45; 0x21; 0xdc;        (* AND (% r12d) (% r11d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xeb; 0x19;
                           (* RORX (% r13d) (% r11d) (Imm8 (word 25)) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xfb; 0x0b;
                           (* RORX (% edi) (% r11d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x14; 0x32;  (* LEA (% edx) (%%% (rdx,0,r14)) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0xc4; 0x62; 0x20; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r11d) (% ebx) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf3; 0x06;
                           (* RORX (% r14d) (% r11d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x0c; 0x21;  (* LEA (% ecx) (%%% (rcx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xd7;              (* MOV (% edi) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe2; 0x16;
                           (* RORX (% r12d) (% edx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x0c; 0x29;  (* LEA (% ecx) (%%% (rcx,0,r13)) *)
  0x44; 0x31; 0xc7;        (* XOR (% edi) (% r8d) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf2; 0x0d;
                           (* RORX (% r14d) (% edx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xea; 0x02;
                           (* RORX (% r13d) (% edx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x14; 0x0a;  (* LEA (% r10d) (%%% (r10,0,rcx)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x45; 0x31; 0xc7;        (* XOR (% r15d) (% r8d) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x0c; 0x39;  (* LEA (% ecx) (%%% (rcx,0,r15)) *)
  0x45; 0x89; 0xdc;        (* MOV (% r12d) (% r11d) *)
  0x03; 0x5d; 0x38;        (* ADD (% ebx) (Memop Doubleword (%% (rbp,56))) *)
  0x45; 0x21; 0xd4;        (* AND (% r12d) (% r10d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xea; 0x19;
                           (* RORX (% r13d) (% r10d) (Imm8 (word 25)) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xfa; 0x0b;
                           (* RORX (% r15d) (% r10d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x0c; 0x31;  (* LEA (% ecx) (%%% (rcx,0,r14)) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0xc4; 0x62; 0x28; 0xf2; 0xe0;
                           (* ANDN (% r12d) (% r10d) (% eax) *)
  0x45; 0x31; 0xfd;        (* XOR (% r13d) (% r15d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf2; 0x06;
                           (* RORX (% r14d) (% r10d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x1c; 0x23;  (* LEA (% ebx) (%%% (rbx,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x41; 0x89; 0xcf;        (* MOV (% r15d) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe1; 0x16;
                           (* RORX (% r12d) (% ecx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x1c; 0x2b;  (* LEA (% ebx) (%%% (rbx,0,r13)) *)
  0x41; 0x31; 0xd7;        (* XOR (% r15d) (% edx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf1; 0x0d;
                           (* RORX (% r14d) (% ecx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe9; 0x02;
                           (* RORX (% r13d) (% ecx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x0c; 0x19;  (* LEA (% r9d) (%%% (r9,0,rbx)) *)
  0x44; 0x21; 0xff;        (* AND (% edi) (% r15d) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x31; 0xd7;              (* XOR (% edi) (% edx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x8d; 0x1c; 0x3b;        (* LEA (% ebx) (%%% (rbx,0,rdi)) *)
  0x45; 0x89; 0xd4;        (* MOV (% r12d) (% r10d) *)
  0x03; 0x45; 0x3c;        (* ADD (% eax) (Memop Doubleword (%% (rbp,60))) *)
  0x45; 0x21; 0xcc;        (* AND (% r12d) (% r9d) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xe9; 0x19;
                           (* RORX (% r13d) (% r9d) (Imm8 (word 25)) *)
  0xc4; 0xc3; 0x7b; 0xf0; 0xf9; 0x0b;
                           (* RORX (% edi) (% r9d) (Imm8 (word 11)) *)
  0x42; 0x8d; 0x1c; 0x33;  (* LEA (% ebx) (%%% (rbx,0,r14)) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0xc4; 0x42; 0x30; 0xf2; 0xe3;
                           (* ANDN (% r12d) (% r9d) (% r11d) *)
  0x41; 0x31; 0xfd;        (* XOR (% r13d) (% edi) *)
  0xc4; 0x43; 0x7b; 0xf0; 0xf1; 0x06;
                           (* RORX (% r14d) (% r9d) (Imm8 (word 6)) *)
  0x42; 0x8d; 0x04; 0x20;  (* LEA (% eax) (%%% (rax,0,r12)) *)
  0x45; 0x31; 0xf5;        (* XOR (% r13d) (% r14d) *)
  0x89; 0xdf;              (* MOV (% edi) (% ebx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xe3; 0x16;
                           (* RORX (% r12d) (% ebx) (Imm8 (word 22)) *)
  0x42; 0x8d; 0x04; 0x28;  (* LEA (% eax) (%%% (rax,0,r13)) *)
  0x31; 0xcf;              (* XOR (% edi) (% ecx) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xf3; 0x0d;
                           (* RORX (% r14d) (% ebx) (Imm8 (word 13)) *)
  0xc4; 0x63; 0x7b; 0xf0; 0xeb; 0x02;
                           (* RORX (% r13d) (% ebx) (Imm8 (word 2)) *)
  0x45; 0x8d; 0x04; 0x00;  (* LEA (% r8d) (%%% (r8,0,rax)) *)
  0x41; 0x21; 0xff;        (* AND (% r15d) (% edi) *)
  0x45; 0x31; 0xe6;        (* XOR (% r14d) (% r12d) *)
  0x41; 0x31; 0xcf;        (* XOR (% r15d) (% ecx) *)
  0x45; 0x31; 0xee;        (* XOR (% r14d) (% r13d) *)
  0x42; 0x8d; 0x04; 0x38;  (* LEA (% eax) (%%% (rax,0,r15)) *)
  0x45; 0x89; 0xcc;        (* MOV (% r12d) (% r9d) *)
  0x48; 0x8d; 0x6d; 0xc0;  (* LEA (% rbp) (%% (rbp,18446744073709551552)) *)
  0x48; 0x39; 0xe5;        (* CMP (% rbp) (% rsp) *)
  0x0f; 0x83; 0xe7; 0xfc; 0xff; 0xff;
                           (* JAE (Imm32 (word 4294966503)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,512))) *)
  0x44; 0x01; 0xf0;        (* ADD (% eax) (% r14d) *)
  0x48; 0x8d; 0xa4; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* LEA (% rsp) (%% (rsp,448)) *)
  0x03; 0x07;              (* ADD (% eax) (Memop Doubleword (%% (rdi,0))) *)
  0x03; 0x5f; 0x04;        (* ADD (% ebx) (Memop Doubleword (%% (rdi,4))) *)
  0x03; 0x4f; 0x08;        (* ADD (% ecx) (Memop Doubleword (%% (rdi,8))) *)
  0x03; 0x57; 0x0c;        (* ADD (% edx) (Memop Doubleword (%% (rdi,12))) *)
  0x44; 0x03; 0x47; 0x10;  (* ADD (% r8d) (Memop Doubleword (%% (rdi,16))) *)
  0x44; 0x03; 0x4f; 0x14;  (* ADD (% r9d) (Memop Doubleword (%% (rdi,20))) *)
  0x48; 0x8d; 0xb6; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,128)) *)
  0x44; 0x03; 0x57; 0x18;  (* ADD (% r10d) (Memop Doubleword (%% (rdi,24))) *)
  0x49; 0x89; 0xf4;        (* MOV (% r12) (% rsi) *)
  0x44; 0x03; 0x5f; 0x1c;  (* ADD (% r11d) (Memop Doubleword (%% (rdi,28))) *)
  0x48; 0x3b; 0x74; 0x24; 0x50;
                           (* CMP (% rsi) (Memop Quadword (%% (rsp,80))) *)
  0x89; 0x07;              (* MOV (Memop Doubleword (%% (rdi,0))) (% eax) *)
  0x4c; 0x0f; 0x44; 0xe4;  (* CMOVE (% r12) (% rsp) *)
  0x89; 0x5f; 0x04;        (* MOV (Memop Doubleword (%% (rdi,4))) (% ebx) *)
  0x89; 0x4f; 0x08;        (* MOV (Memop Doubleword (%% (rdi,8))) (% ecx) *)
  0x89; 0x57; 0x0c;        (* MOV (Memop Doubleword (%% (rdi,12))) (% edx) *)
  0x44; 0x89; 0x47; 0x10;  (* MOV (Memop Doubleword (%% (rdi,16))) (% r8d) *)
  0x44; 0x89; 0x4f; 0x14;  (* MOV (Memop Doubleword (%% (rdi,20))) (% r9d) *)
  0x44; 0x89; 0x57; 0x18;  (* MOV (Memop Doubleword (%% (rdi,24))) (% r10d) *)
  0x44; 0x89; 0x5f; 0x1c;  (* MOV (Memop Doubleword (%% (rdi,28))) (% r11d) *)
  0x0f; 0x86; 0x85; 0xec; 0xff; 0xff;
                           (* JBE (Imm32 (word 4294962309)) *)
  0x48; 0x8d; 0x2c; 0x24;  (* LEA (% rbp) (%% (rsp,0)) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0x4c; 0x8b; 0x7e; 0xd0;  (* MOV (% r15) (Memop Quadword (%% (rsi,18446744073709551568))) *)
  0x4c; 0x8b; 0x76; 0xd8;  (* MOV (% r14) (Memop Quadword (%% (rsi,18446744073709551576))) *)
  0x4c; 0x8b; 0x6e; 0xe0;  (* MOV (% r13) (Memop Quadword (%% (rsi,18446744073709551584))) *)
  0x4c; 0x8b; 0x66; 0xe8;  (* MOV (% r12) (Memop Quadword (%% (rsi,18446744073709551592))) *)
  0x48; 0x8b; 0x6e; 0xf0;  (* MOV (% rbp) (Memop Quadword (%% (rsi,18446744073709551600))) *)
  0x48; 0x8b; 0x5e; 0xf8;  (* MOV (% rbx) (Memop Quadword (%% (rsi,18446744073709551608))) *)
  0x48; 0x8d; 0x26;        (* LEA (% rsp) (%% (rsi,0)) *)
  0xf3; 0xc3               (* RET *)
]]);;
let sha256_avx2_k256 = hd sha256_avx2_data;;
let SHA256_AVX2_EXEC = X86_MK_EXEC_RULE sha256_avx2_mc;;


(* ------------------------------------------------------------------------- *)
(* The 32-bit scalar instructions' results as plain 32-bit words.            *)
(* ------------------------------------------------------------------------- *)

let SHA256_ZX_ZX = prove
 (`!x:int32. (word_zx:int64->int32) (word_zx x) = x`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH]);;

let SHA256_SX_ZX = prove
 (`!x:int32. (word_sx:int64->int32) (word_zx x) = x`,
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH; SHA256_ZX_ZX]);;

let SHA256_LEA32 = prove
 (`!x y:int32. (word_sx:int64->int32)
      (word_add (word_zx x) (word (1 * val ((word_zx:int32->int64) y)))) = word_add x y`,
  REWRITE_TAC[MULT_CLAUSES; WORD_VAL] THEN
  SIMP_TAC[WORD_SX_ZX; WORD_ZX_ADD; DIMINDEX_32; DIMINDEX_64; ARITH; SHA256_ZX_ZX]);;

let SHA256_SUB_ADD = WORD_RULE `!a p:int32. word_add (word_sub a p) p = a`;;

(* ------------------------------------------------------------------------- *)
(* The rounds. Sigma0 of a is added to the new a a round late, and Maj       *)
(* reuses the previous round's b xor c.                                      *)
(* ------------------------------------------------------------------------- *)

let SHA256_CH_ADD = prove
 (`!e f g x:int32. word_add (word_add x (word_and f e)) (word_and (word_not e) g) =
                   word_add x (sha_choose e f g)`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; sha_choose] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BLAST);;

let SHA256_MAJ_XOR = prove
 (`!a b c:int32. word_xor (word_and (word_xor b c) (word_xor a b)) b = sha_maj a b c`,
  REWRITE_TAC[sha_maj] THEN CONV_TAC WORD_BLAST);;

let SHA256_SIGMA1_RORX = prove
 (`!e:int32. word_xor (word_xor (word_ror e 25) (word_ror e 11)) (word_ror e 6) =
             sha_hash_sigma_1 e`,
  REWRITE_TAC[sha_hash_sigma_1] THEN CONV_TAC WORD_BLAST);;

let SHA256_SIGMA0_RORX = prove
 (`!a:int32. word_xor (word_xor (word_ror a 13) (word_ror a 22)) (word_ror a 2) =
             sha_hash_sigma_0 a`,
  REWRITE_TAC[sha_hash_sigma_0] THEN CONV_TAC WORD_BLAST);;

let SHA256_AVX2_ROUND = prove
 (`!S k w a b c d e f g h:int32.
     EL 0 S = a /\ EL 1 S = b /\ EL 2 S = c /\ EL 3 S = d /\
     EL 4 S = e /\ EL 5 S = f /\ EL 6 S = g /\ EL 7 S = h
     ==> word_add
          (word_add (word_add (word_add (word_add h (word_add w k)) (word_and f e))
                              (word_and (word_not e) g))
                    (word_xor (word_xor (word_ror e 25) (word_ror e 11)) (word_ror e 6)))
          (word_xor (word_and (word_xor b c) (word_xor a b)) b) =
         word_sub (EL 0 (sha256_round S k w)) (sha_hash_sigma_0 a) /\
         word_add d
          (word_add (word_add (word_add (word_add h (word_add w k)) (word_and f e))
                              (word_and (word_not e) g))
                    (word_xor (word_xor (word_ror e 25) (word_ror e 11)) (word_ror e 6))) =
         EL 4 (sha256_round S k w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[sha256_round] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SHA256_CH_ADD; SHA256_MAJ_XOR; SHA256_SIGMA1_RORX] THEN
  CONV_TAC WORD_RULE);;

let SHA256_ROUND_SHIFT = prove
 (`!S k w. EL 1 (sha256_round S k w) = EL 0 S /\ EL 2 (sha256_round S k w) = EL 1 S /\
           EL 3 (sha256_round S k w) = EL 2 S /\ EL 5 (sha256_round S k w) = EL 4 S /\
           EL 6 (sha256_round S k w) = EL 5 S /\ EL 7 (sha256_round S k w) = EL 6 S`,
  REWRITE_TAC[sha256_round] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let SHA256_CR_SHIFT = prove
 (`!M H t.
     EL 1 (sha256_compress_rounds M H (t + 1)) = EL 0 (sha256_compress_rounds M H t) /\
     EL 2 (sha256_compress_rounds M H (t + 1)) = EL 1 (sha256_compress_rounds M H t) /\
     EL 3 (sha256_compress_rounds M H (t + 1)) = EL 2 (sha256_compress_rounds M H t) /\
     EL 5 (sha256_compress_rounds M H (t + 1)) = EL 4 (sha256_compress_rounds M H t) /\
     EL 6 (sha256_compress_rounds M H (t + 1)) = EL 5 (sha256_compress_rounds M H t) /\
     EL 7 (sha256_compress_rounds M H (t + 1)) = EL 6 (sha256_compress_rounds M H t)`,
  REWRITE_TAC[sha256_compress_rounds; SHA256_ROUND_SHIFT]);;

(* Every state word is named after the round that made it: the a-line
   EL 0 (C j) or the e-line EL 4 (C j) of round j, where C j is
   sha256_compress_rounds M H j, or a word of H, so a word keeps its name as
   the rounds go by and each round's fold is fixed in advance. *)
let sha256_cr t = mk_comb(`sha256_compress_rounds (M:int32 list) (H:int32 list)`, mk_small_numeral t);;
let sha256_el k l = mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral k), l);;
let sha256_canon t k =
  let base = if k < 4 then 0 else 4 in
  let j = t - (k - base) in
  if j >= 1 then sha256_el base (sha256_cr j) else sha256_el (k - t) `H:int32 list`;;

(* |- EL k (C t) = its name *)
let rec SHA256_CANON t k =
  let tm = sha256_el k (sha256_cr t) in
  if t = 0 then REWRITE_CONV[sha256_compress_rounds] tm
  else if k = 0 || k = 4 then REFL tm
  else
    let th = CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
      (SPECL [`M:int32 list`; `H:int32 list`; mk_small_numeral (t-1)] SHA256_CR_SHIFT) in
    TRANS (REWRITE_CONV[th] tm) (SHA256_CANON (t-1) (k-1));;

let SHA256_K_AT t =
  (REWRITE_CONV[sha256_constants] THENC EL_CONV)
    (mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral t), `sha256_constants`));;

(* Round t's new a, less Sigma0 of the old, and its new e, as the routine
   computes them from the names of the round's inputs. *)
let SHA256_ROUND_AT t =
  let k = rhs(concl(SHA256_K_AT t))
  and w = mk_comb(`sha256_msg_schedule (M:int32 list)`, mk_small_numeral t) in
  let th = ISPECL ([sha256_cr t; k; w] @ map (sha256_canon t) (0--7)) SHA256_AVX2_ROUND in
  let th = MP th (end_itlist CONJ (map (SHA256_CANON t) (0--7))) in
  let step = CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
    (INST [`M:int32 list`,`m:int32 list`; `H:int32 list`,`hsh:int32 list`;
           mk_small_numeral t,`n:num`] (CONJUNCT2 sha256_compress_rounds)) in
  REWRITE_RULE[GSYM (REWRITE_RULE[SHA256_K_AT t] step)] th;;

let SHA256_ROUND_THS = map SHA256_ROUND_AT (0--63);;

(* ------------------------------------------------------------------------- *)
(* The message schedule, in each 32-bit lane of the 256-bit registers.       *)
(* ------------------------------------------------------------------------- *)

let SHA256_SUBWORD_USHR = prove
 (`!(x:N word) n p l. p + n + l <= dimindex(:N)
     ==> (word_subword (word_ushr x n) (p,l):M word) = word_subword x (p + n,l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD_AC] THEN
  ASM_CASES_TAC `i < l` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ASM_ARITH_TAC);;

let SHA256_USHR_CONV tm =
  let th = PART_MATCH (lhand o rand) SHA256_SUBWORD_USHR tm in
  let th = MP th (EQT_ELIM (DEPTH_CONV(DIMINDEX_CONV ORELSEC NUM_RED_CONV) (lhand (concl th)))) in
  CONV_RULE (RAND_CONV (RAND_CONV (LAND_CONV NUM_ADD_CONV))) th;;

(* sigma0 from 32-bit shifts, and sigma1's rotations from 64-bit shifts of a
   word duplicated into both halves, whose low halves vpshufb gathers byte by
   byte. *)
let SHA256_SIGMA0_AVX2 = prove
 (`!x:int32.
     word_xor (word_xor (word_xor (word_xor (word_ushr x 3) (word_ushr x 7)) (word_shl x 14))
                        (word_ushr (word_ushr x 7) 11))
              (word_shl (word_shl x 14) 11) = sha_msg_sigma_0 x`,
  REWRITE_TAC[sha_msg_sigma_0] THEN CONV_TAC WORD_BLAST);;

let SHA256_SIGMA1_AVX2 = prove
 (`!w:int32.
     (word_join:int16->int16->int32)
      ((word_join:byte->byte->int16)
        (word_xor (word_xor (word_subword (word_ushr w 10) (24,8)) (word_subword w (9,8)))
                  (word_subword w (11,8)))
        (word_xor (word_xor (word_subword (word_ushr w 10) (16,8)) (word_subword w (1,8)))
                  (word_subword w (3,8))))
      ((word_join:byte->byte->int16)
        (word_xor (word_xor (word_subword w (18,8))
                            (word_subword ((word_join:int32->int32->int64) w w) (25,8)))
                  (word_subword ((word_join:int32->int32->int64) w w) (27,8)))
        (word_xor (word_xor (word_subword w (10,8)) (word_subword w (17,8)))
                  (word_subword w (19,8)))) = sha_msg_sigma_1 w`,
  REWRITE_TAC[sha_msg_sigma_1] THEN CONV_TAC WORD_BLAST);;

(* The routine's sum for schedule word t, in the order it adds them. *)
let SHA256_SCHED_AT t =
  let s j = mk_comb(`sha256_msg_schedule (M:int32 list)`, mk_small_numeral j) in
  let tm = subst [s (t-16),`w0:int32`; s (t-7),`w9:int32`; s (t-15),`w1:int32`;
                  s (t-2),`w14:int32`; s t,`wt:int32`]
    `word_add (word_add (word_add w0 w9) (sha_msg_sigma_0 w1)) (sha_msg_sigma_1 w14) = wt` in
  prove(tm, CONV_TAC(RAND_CONV(REWR_CONV sha256_msg_schedule)) THEN
            CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

let SHA256_SCHED_THS = map SHA256_SCHED_AT (16--63);;

let SHA256_SCHED_SMALL = map (fun t ->
  let tm = mk_comb(`sha256_msg_schedule (M:int32 list)`, mk_small_numeral t) in
  SYM(CONV_RULE(RAND_CONV(RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC REWRITE_CONV[]))
        (REWR_CONV sha256_msg_schedule tm))) (0--15);;

(* vpshufb's byte swap undoing the load of a big-endian word. *)
let SHA256_BSWAP = prove
 (`!w:int32. (word_join:int16->int16->int32)
      ((word_join:byte->byte->int16) (word_subword (word_bytereverse w) (0,8))
                                     (word_subword (word_bytereverse w) (8,8)))
      ((word_join:byte->byte->int16) (word_subword (word_bytereverse w) (16,8))
                                     (word_subword (word_bytereverse w) (24,8))) = w`,
  CONV_TAC WORD_BLAST);;

let SHA256_LANE_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_XOR ORELSEC
    SHA256_USHR_CONV ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV([SHA256_SIGMA0_AVX2; SHA256_SIGMA1_AVX2; WORD_ADD_0; SHA256_BSWAP] @
               SHA256_SCHED_THS);;

(* ------------------------------------------------------------------------- *)
(* Pointers, stack stores, and the step tactic.                              *)
(* ------------------------------------------------------------------------- *)

let SHA256_SUB_CONST = prove
 (`!x:int64 n. word_sub x (word n) = word_add x (word_neg (word n))`,
  CONV_TAC WORD_RULE);;

let SHA256_PTR_CONV =
  REWRITE_CONV[SHA256_SUB_CONST] THENC DEPTH_CONV WORD_RED_CONV THENC
  REWRITE_CONV[WORD_ADD_ASSOC_CONSTS] THENC
  DEPTH_CONV (NUM_ADD_CONV ORELSEC WORD_RED_CONV);;

let SHA256_RIPREL_FOLD = prove
 (`!pc ofs ofs2 k.
     riprel32_within_bounds (k + (ofs + ofs2)) (pc + ofs) ==>
     word (val (word (pc+ofs):(64)word) +
           val (word_sx (iword (&k - (&pc + -- &ofs2)):int32):(64)word)):int64 =
     word_add (word k) (word (ofs + ofs2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  ASM_MESON_TAC[RIP_REL_ADDR_FOLD]);;

let SHA256_RIPREL_FOLD0 = prove
 (`!pc ofs k.
     riprel32_within_bounds k (pc + ofs) ==>
     word (val (word (pc+ofs):(64)word) +
           val (word_sx (iword (&k - (&pc + &ofs)):int32):(64)word)):int64 =
     word k`,
  MESON_TAC[RIP_REL_ADDR_FOLD]);;

(* The routine's 64-bit registers, each as a base plus a constant. *)
let SHA256_PTR_TAC =
  let is64 th = let c = concl th in is_eq c && type_of (lhs c) = `:int64` &&
    (try fst(dest_const(fst(strip_comb (lhs c)))) = "read" with Failure _ -> false) &&
    (try mem (fst(dest_const(fst(strip_comb (rhs c))))) ["word_add"; "word_sub"]
     with Failure _ -> false) in
  RULE_ASSUM_TAC(fun th -> if is64 th then CONV_RULE(RAND_CONV SHA256_PTR_CONV) th else th);;

let SHA256_LANE_TAC =
  let simdable = can (term_match [] `read X (s:x86state):int256 = whatever`) in
  TRY(FIRST_X_ASSUM
    (ASSUME_TAC o CONV_RULE(RAND_CONV SHA256_LANE_CONV) o check (simdable o concl)));;

(* A 256-bit store to the stack frame at base as eight 32-bit facts, which
   the rounds read. *)
let SHA256_SPLIT_TAC =
  let pat = `read (memory :> bytes256 (word_add base (word n))) s = v` in
  let split k th = CONJUNCTS
    (GEN_REWRITE_RULE I [el k (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] th) in
  let norm = CONV_RULE (BINOP2_CONV SHA256_PTR_CONV SHA256_LANE_CONV) in
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [`base:int64`] pat) (concl th) then
      MAP_EVERY (ASSUME_TAC o norm) (flat (map (split 2) (flat (map (split 1) (split 0 th)))))
    else failwith "SHA256_SPLIT_TAC"));;

let SHA256_NORM_RULE =
  REWRITE_RULE[SHA256_ZX_ZX; SHA256_LEA32; SHA256_SX_ZX; SHA256_SUB_ADD; WORD_ADD_0;
               SHA256_SIGMA0_RORX];;

let SHA256_STEP_TAC n =
  X86_STEPS_TAC SHA256_AVX2_EXEC [n] THEN
  RULE_ASSUM_TAC SHA256_NORM_RULE THEN SHA256_PTR_TAC THEN
  SHA256_LANE_TAC THEN SHA256_SPLIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE SHA256_ROUND_THS);;


(* ------------------------------------------------------------------------- *)
(* The round constants and byte-shuffle masks in the K256 table.             *)
(* ------------------------------------------------------------------------- *)

(* Each 32-byte row holds four round constants twice, once for each lane;
   after them come vpshufb's byte-swap mask and the two masks that gather
   sigma1's halves, and the inner loop stops at the zero byte the first mask
   has where a row's last constant would. *)
let SHA256_AVX2_K256 = prove
 (`!s k. bytes_loaded s (word k) sha256_avx2_k256
        ==> read (memory :> bytes256 (word k)) s = word 0xe9b5dba5b5c0fbcf71374491428a2f98e9b5dba5b5c0fbcf71374491428a2f98 /\
      read (memory :> bytes256 (word_add (word k) (word 32))) s = word 0xab1c5ed5923f82a459f111f13956c25bab1c5ed5923f82a459f111f13956c25b /\
      read (memory :> bytes256 (word_add (word k) (word 64))) s = word 0x550c7dc3243185be12835b01d807aa98550c7dc3243185be12835b01d807aa98 /\
      read (memory :> bytes256 (word_add (word k) (word 96))) s = word 0xc19bf1749bdc06a780deb1fe72be5d74c19bf1749bdc06a780deb1fe72be5d74 /\
      read (memory :> bytes256 (word_add (word k) (word 128))) s = word 0x240ca1cc0fc19dc6efbe4786e49b69c1240ca1cc0fc19dc6efbe4786e49b69c1 /\
      read (memory :> bytes256 (word_add (word k) (word 160))) s = word 0x76f988da5cb0a9dc4a7484aa2de92c6f76f988da5cb0a9dc4a7484aa2de92c6f /\
      read (memory :> bytes256 (word_add (word k) (word 192))) s = word 0xbf597fc7b00327c8a831c66d983e5152bf597fc7b00327c8a831c66d983e5152 /\
      read (memory :> bytes256 (word_add (word k) (word 224))) s = word 0x1429296706ca6351d5a79147c6e00bf31429296706ca6351d5a79147c6e00bf3 /\
      read (memory :> bytes256 (word_add (word k) (word 256))) s = word 0x53380d134d2c6dfc2e1b213827b70a8553380d134d2c6dfc2e1b213827b70a85 /\
      read (memory :> bytes256 (word_add (word k) (word 288))) s = word 0x92722c8581c2c92e766a0abb650a735492722c8581c2c92e766a0abb650a7354 /\
      read (memory :> bytes256 (word_add (word k) (word 320))) s = word 0xc76c51a3c24b8b70a81a664ba2bfe8a1c76c51a3c24b8b70a81a664ba2bfe8a1 /\
      read (memory :> bytes256 (word_add (word k) (word 352))) s = word 0x106aa070f40e3585d6990624d192e819106aa070f40e3585d6990624d192e819 /\
      read (memory :> bytes256 (word_add (word k) (word 384))) s = word 0x34b0bcb52748774c1e376c0819a4c11634b0bcb52748774c1e376c0819a4c116 /\
      read (memory :> bytes256 (word_add (word k) (word 416))) s = word 0x682e6ff35b9cca4f4ed8aa4a391c0cb3682e6ff35b9cca4f4ed8aa4a391c0cb3 /\
      read (memory :> bytes256 (word_add (word k) (word 448))) s = word 0x8cc7020884c8781478a5636f748f82ee8cc7020884c8781478a5636f748f82ee /\
      read (memory :> bytes256 (word_add (word k) (word 480))) s = word 0xc67178f2bef9a3f7a4506ceb90befffac67178f2bef9a3f7a4506ceb90befffa /\
      read (memory :> bytes256 (word_add (word k) (word 512))) s = word 0x0c0d0e0f08090a0b04050607000102030c0d0e0f08090a0b0405060700010203 /\
      read (memory :> bytes256 (word_add (word k) (word 544))) s = word 0xffffffffffffffff0b0a090803020100ffffffffffffffff0b0a090803020100 /\
      read (memory :> bytes256 (word_add (word k) (word 576))) s = word 0x0b0a090803020100ffffffffffffffff0b0a090803020100ffffffffffffffff /\
      read (memory :> bytes8 (word_add (word k) (word 131))) s = word 228 /\
      read (memory :> bytes8 (word_add (word k) (word 259))) s = word 39 /\
      read (memory :> bytes8 (word_add (word k) (word 387))) s = word 25 /\
      read (memory :> bytes8 (word_add (word k) (word 515))) s = word 0`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV)
    [ARITH_RULE `k = k + 0`] THEN
  REWRITE_TAC[sha256_avx2_k256] THEN CONV_TAC(LAND_CONV DATA64_CONV) THEN REWRITE_TAC[bytes_loaded_nil] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  MAP_EVERY (fun off ->
    let a = mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` `k:num` (mk_small_numeral off)) in
    FIRST_ASSUM(fun th ->
      if rand(rand(rand(rator(lhand(concl th))))) <> a then failwith "" else
      let split k = GEN_REWRITE_RULE I [el k (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] in
      let th3 = CONJUNCT2(split 4 (CONJUNCT2(split 3 (CONJUNCT1(split 2 th))))) in
      ASSUME_TAC(CONV_RULE(RAND_CONV WORD_REDUCE_CONV)
        (REWRITE_RULE[GSYM WORD_ADD; GSYM ADD_ASSOC] th3))))
    [128; 256; 384; 512] THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
  REWRITE_TAC[CONJUNCT1 READ_MEMORY_BYTESIZED_SPLIT;
              CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)] THEN
  REWRITE_TAC[GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV);;


(* ------------------------------------------------------------------------- *)
(* The message, as the value of the whole input region.                      *)
(* ------------------------------------------------------------------------- *)

let SHA256_READ_SLICE32 = prove
 (`!a l v (s:x86state) off.
     read (memory :> bytes(a,l)) s = v /\ off + 4 <= l
     ==> read (memory :> bytes32 (word_add a (word off))) s =
         word((v DIV 2 EXP (8 * off)) MOD 2 EXP (8 * 4))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  SUBGOAL_THEN `MIN (l - off) 4 = 4` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* The lower loop's exit test compares the frame pointers it steps down. *)
let SHA256_COND_TAC (asl,w) =
  let is_cmp th = can (term_match [] `val (x:int64) <= val (y:int64)`) (concl th) ||
                  can (term_match [] `~(val (x:int64) <= val (y:int64))`) (concl th) in
  let cmps = filter is_cmp (map snd asl) in
  let is_ripcond th = let c = concl th in
    is_eq c && (try rator(lhs c) = `read RIP` with Failure _ -> false) && is_cond (rhs c) in
  RULE_ASSUM_TAC(fun th -> if is_ripcond th then REWRITE_RULE cmps th else th) (asl,w);;

let SHA256_BASE_CMPS = prove
 (`!base:int64. 32 <= val base /\ val base + 576 <= 2 EXP 64
   ==> val (word_add base (word 32)) <= val (word_add base (word 416)) /\
       val (word_add base (word 32)) <= val (word_add base (word 352)) /\
       val (word_add base (word 32)) <= val (word_add base (word 288)) /\
       val (word_add base (word 32)) <= val (word_add base (word 224)) /\
       val (word_add base (word 32)) <= val (word_add base (word 160)) /\
       val (word_add base (word 32)) <= val (word_add base (word 96)) /\
       val (word_add base (word 32)) <= val (word_add base (word 32)) /\
       ~(val (word_add base (word 32)) <=
         val (word_add base (word 18446744073709551584)))`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD_CASES; DIMINDEX_64] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Block A: from the loop's head to its feed-forward, with block B's         *)
(* schedule words left on the stack.                                        *)
(* ------------------------------------------------------------------------- *)

(* The frame is the 1024-byte-aligned area the prologue makes, which this
   calls base + 32: the loop's head finds the stack pointer at base + 480 and
   the context pointer, the end of the input, and the caller's stack pointer
   at base + 544, 560, and 568. Block A's rounds slide the stack pointer down
   64 bytes per eight rounds, leaving round t's schedule word plus constant,
   for block B, at base + sha256_avx2_slot t. *)
let sha256_avx2_slot = new_definition
 `sha256_avx2_slot t = 496 - 64 * (t DIV 8) + 32 * ((t MOD 8) DIV 4) + 4 * (t MOD 4)`;;

let SHA256_AVX2_BLOCK_A_GOAL =
 `!pc k256 base pa pb ctx rsp0 (H:int32 list) (MA:int32 list) (MB:int32 list).
     aligned 64 (word k256:int64) /\ aligned 32 (base:int64) /\
     nonoverlapping (word pc,0x1423) (base,544) /\
     nonoverlapping (word k256,640) (base,544) /\
     nonoverlapping (ctx,32) (base,544) /\ nonoverlapping (ctx,32) (word pc,0x1423) /\
     nonoverlapping (ctx,32) (word k256,640) /\
     riprel32_within_bounds (k256 + 512) (pc + 136) /\
     riprel32_within_bounds k256 (pc + 204)
     ==> ensures x86
      (\s. bytes_loaded s (word pc) (sha256_avx2_mc pc k256) /\
        read RIP s = word(pc + 0x80) /\
        read RSP s = word_add base (word 480) /\
        read RSI s = word_add pa (word 64) /\ read R12 s = pb /\
        read RAX s = word_zx (EL 0 H) /\
        read RBX s = word_zx (EL 1 H) /\
        read RCX s = word_zx (EL 2 H) /\
        read RDX s = word_zx (EL 3 H) /\
        read R8 s = word_zx (EL 4 H) /\
        read R9 s = word_zx (EL 5 H) /\
        read R10 s = word_zx (EL 6 H) /\
        read R11 s = word_zx (EL 7 H) /\
        read YMM8 s = word 0xffffffffffffffff0b0a090803020100ffffffffffffffff0b0a090803020100 /\
        read YMM9 s = word 0x0b0a090803020100ffffffffffffffff0b0a090803020100ffffffffffffffff /\
        bytes_loaded s (word k256) sha256_avx2_k256 /\
        read (memory :> bytes128 pa) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 3 MA)) (word_bytereverse (EL 2 MA)))
                                           (word_join (word_bytereverse (EL 1 MA)) (word_bytereverse (EL 0 MA))) /\
        read (memory :> bytes128 (word_add pa (word 16))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 7 MA)) (word_bytereverse (EL 6 MA)))
                                           (word_join (word_bytereverse (EL 5 MA)) (word_bytereverse (EL 4 MA))) /\
        read (memory :> bytes128 (word_add pa (word 32))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 11 MA)) (word_bytereverse (EL 10 MA)))
                                           (word_join (word_bytereverse (EL 9 MA)) (word_bytereverse (EL 8 MA))) /\
        read (memory :> bytes128 (word_add pa (word 48))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 15 MA)) (word_bytereverse (EL 14 MA)))
                                           (word_join (word_bytereverse (EL 13 MA)) (word_bytereverse (EL 12 MA))) /\
        read (memory :> bytes128 pb) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 3 MB)) (word_bytereverse (EL 2 MB)))
                                           (word_join (word_bytereverse (EL 1 MB)) (word_bytereverse (EL 0 MB))) /\
        read (memory :> bytes128 (word_add pb (word 16))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 7 MB)) (word_bytereverse (EL 6 MB)))
                                           (word_join (word_bytereverse (EL 5 MB)) (word_bytereverse (EL 4 MB))) /\
        read (memory :> bytes128 (word_add pb (word 32))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 11 MB)) (word_bytereverse (EL 10 MB)))
                                           (word_join (word_bytereverse (EL 9 MB)) (word_bytereverse (EL 8 MB))) /\
        read (memory :> bytes128 (word_add pb (word 48))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 15 MB)) (word_bytereverse (EL 14 MB)))
                                           (word_join (word_bytereverse (EL 13 MB)) (word_bytereverse (EL 12 MB))) /\
        read (memory :> bytes64 (word_add base (word 544))) s = ctx /\
        read (memory :> bytes64 (word_add base (word 568))) s = rsp0 /\
        read (memory :> bytes32 ctx) s = EL 0 H /\
        read (memory :> bytes32 (word_add ctx (word 4))) s = EL 1 H /\
        read (memory :> bytes32 (word_add ctx (word 8))) s = EL 2 H /\
        read (memory :> bytes32 (word_add ctx (word 12))) s = EL 3 H /\
        read (memory :> bytes32 (word_add ctx (word 16))) s = EL 4 H /\
        read (memory :> bytes32 (word_add ctx (word 20))) s = EL 5 H /\
        read (memory :> bytes32 (word_add ctx (word 24))) s = EL 6 H /\
        read (memory :> bytes32 (word_add ctx (word 28))) s = EL 7 H)
      (\s. read RIP s = word(pc + 0x105b) /\
        read RSP s = word_add base (word 32) /\
        read RBP s = word_add base (word 480) /\
        read RDI s = ctx /\
        read RAX s = word_zx (EL 0 (sha256_block MA H)) /\
        read RBX s = word_zx (EL 1 (sha256_block MA H)) /\
        read RCX s = word_zx (EL 2 (sha256_block MA H)) /\
        read RDX s = word_zx (EL 3 (sha256_block MA H)) /\
        read R8 s = word_zx (EL 4 (sha256_block MA H)) /\
        read R9 s = word_zx (EL 5 (sha256_block MA H)) /\
        read R10 s = word_zx (EL 6 (sha256_block MA H)) /\
        read R11 s = word_zx (EL 7 (sha256_block MA H)) /\
        read (memory :> bytes32 ctx) s = EL 0 (sha256_block MA H) /\
        read (memory :> bytes32 (word_add ctx (word 4))) s = EL 1 (sha256_block MA H) /\
        read (memory :> bytes32 (word_add ctx (word 8))) s = EL 2 (sha256_block MA H) /\
        read (memory :> bytes32 (word_add ctx (word 12))) s = EL 3 (sha256_block MA H) /\
        read (memory :> bytes32 (word_add ctx (word 16))) s = EL 4 (sha256_block MA H) /\
        read (memory :> bytes32 (word_add ctx (word 20))) s = EL 5 (sha256_block MA H) /\
        read (memory :> bytes32 (word_add ctx (word 24))) s = EL 6 (sha256_block MA H) /\
        read (memory :> bytes32 (word_add ctx (word 28))) s = EL 7 (sha256_block MA H) /\
        (!t. t < 64
             ==> read (memory :> bytes32 (word_add base (word (sha256_avx2_slot t)))) s =
                 word_add (sha256_msg_schedule MB t) (EL t sha256_constants)))
      (MAYCHANGE [RIP; RSP; RBP; RAX; RBX; RCX; RDX; RDI;
                  R8; R9; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(base,544); memory :> bytes(ctx,32)])`;;

let SHA256_AVX2_BLOCK_A = prove
 (SHA256_AVX2_BLOCK_A_GOAL,
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `k256:num`; `base:int64`; `pa:int64`; `pb:int64`; `ctx:int64`;
    `rsp0:int64`; `H:int32 list`; `MA:int32 list`; `MB:int32 list`] THEN
  STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS; fst SHA256_AVX2_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SHA256_AVX2_K256 o
    check (can (term_match [] `bytes_loaded s (word k) sha256_avx2_k256`) o concl)) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `word_bytereverse:int32->int32`)) (concl th)
    then REWRITE_RULE (map (INST [`MA:int32 list`,`M:int32 list`]) SHA256_SCHED_SMALL @
                       map (INST [`MB:int32 list`,`M:int32 list`]) SHA256_SCHED_SMALL) th
    else th) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SPECL [`pc:num`; `136`; `376`; `k256:num`] SHA256_RIPREL_FOLD) o
    CONV_RULE(LAND_CONV(RAND_CONV(ONCE_REWRITE_CONV[ARITH_RULE `512 = 136 + 376`]))) o
    check ((=) `riprel32_within_bounds (k256 + 512) (pc + 136)` o concl)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SPECL [`pc:num`; `204`; `k256:num`] SHA256_RIPREL_FOLD0) o
    check ((=) `riprel32_within_bounds k256 (pc + 204)` o concl)) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  SUBGOAL_THEN `aligned 32 (word k256:int64)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ALIGNED_WORD_WEAKEN; DIVIDES_CONV `32 divides 64`]; ALL_TAC] THEN
  MAP_EVERY SHA256_STEP_TAC (1--1985) THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[sha256_avx2_slot; sha256_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(map (INST [`MA:int32 list`,`M:int32 list`] o SHA256_CANON 64) (0--7) @
              map SHA256_K_AT (0--63)) THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC EL_CONV)) THEN
  REWRITE_TAC(map (INST [`MA:int32 list`,`M:int32 list`] o SHA256_CANON 64) (0--7)) THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Block B: its rounds from the schedule words block A left on the stack,    *)
(* then its feed-forward and the test for another pair.                     *)
(* ------------------------------------------------------------------------- *)

let SHA256_AVX2_BLOCK_B_GOAL =
 `!pc k256 base pa ctx endp (H:int32 list) (MB:int32 list).
     nonoverlapping (ctx,32) (base,576) /\ nonoverlapping (ctx,32) (word pc,0x1423) /\
     32 <= val base /\ val base + 576 <= 2 EXP 64
     ==> ensures x86
      (\s. bytes_loaded s (word pc) (sha256_avx2_mc pc k256) /\
        read RIP s = word(pc + 0x1065) /\
        read RSP s = word_add base (word 32) /\
        read RBP s = word_add base (word 480) /\
        read RSI s = word_add pa (word 64) /\
        read RAX s = word_zx (EL 0 H) /\
        read RBX s = word_zx (EL 1 H) /\
        read RCX s = word_zx (EL 2 H) /\
        read RDX s = word_zx (EL 3 H) /\
        read R8 s = word_zx (EL 4 H) /\
        read R9 s = word_zx (EL 5 H) /\
        read R10 s = word_zx (EL 6 H) /\
        read R11 s = word_zx (EL 7 H) /\
        read (memory :> bytes64 (word_add base (word 544))) s = ctx /\
        read (memory :> bytes64 (word_add base (word 560))) s = endp /\
        read (memory :> bytes32 ctx) s = EL 0 H /\
        read (memory :> bytes32 (word_add ctx (word 4))) s = EL 1 H /\
        read (memory :> bytes32 (word_add ctx (word 8))) s = EL 2 H /\
        read (memory :> bytes32 (word_add ctx (word 12))) s = EL 3 H /\
        read (memory :> bytes32 (word_add ctx (word 16))) s = EL 4 H /\
        read (memory :> bytes32 (word_add ctx (word 20))) s = EL 5 H /\
        read (memory :> bytes32 (word_add ctx (word 24))) s = EL 6 H /\
        read (memory :> bytes32 (word_add ctx (word 28))) s = EL 7 H /\
        (!t. t < 64
             ==> read (memory :> bytes32 (word_add base (word (sha256_avx2_slot t)))) s =
                 word_add (sha256_msg_schedule MB t) (EL t sha256_constants)))
      (\s. read RIP s = word(pc + 0x13f5) /\
        read RSP s = word_add base (word 480) /\
        read RSI s = word_add pa (word 192) /\
        read R12 s = (if val (word_sub (word_add pa (word 192)) endp) = 0
                      then word_add base (word 480) else word_add pa (word 192)) /\
        (read CF s <=> val (word_add pa (word 192)) < val endp) /\
        (read ZF s <=> val (word_sub (word_add pa (word 192)) endp) = 0) /\
        read RAX s = word_zx (EL 0 (sha256_block MB H)) /\
        read RBX s = word_zx (EL 1 (sha256_block MB H)) /\
        read RCX s = word_zx (EL 2 (sha256_block MB H)) /\
        read RDX s = word_zx (EL 3 (sha256_block MB H)) /\
        read R8 s = word_zx (EL 4 (sha256_block MB H)) /\
        read R9 s = word_zx (EL 5 (sha256_block MB H)) /\
        read R10 s = word_zx (EL 6 (sha256_block MB H)) /\
        read R11 s = word_zx (EL 7 (sha256_block MB H)) /\
        read (memory :> bytes32 ctx) s = EL 0 (sha256_block MB H) /\
        read (memory :> bytes32 (word_add ctx (word 4))) s = EL 1 (sha256_block MB H) /\
        read (memory :> bytes32 (word_add ctx (word 8))) s = EL 2 (sha256_block MB H) /\
        read (memory :> bytes32 (word_add ctx (word 12))) s = EL 3 (sha256_block MB H) /\
        read (memory :> bytes32 (word_add ctx (word 16))) s = EL 4 (sha256_block MB H) /\
        read (memory :> bytes32 (word_add ctx (word 20))) s = EL 5 (sha256_block MB H) /\
        read (memory :> bytes32 (word_add ctx (word 24))) s = EL 6 (sha256_block MB H) /\
        read (memory :> bytes32 (word_add ctx (word 28))) s = EL 7 (sha256_block MB H))
      (MAYCHANGE [RIP; RSP; RBP; RSI; RAX; RBX; RCX; RDX; RDI;
                  R8; R9; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(ctx,32)])`;;

let SHA256_AVX2_BLOCK_B = prove
 (SHA256_AVX2_BLOCK_B_GOAL,
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `k256:num`; `base:int64`; `pa:int64`; `ctx:int64`; `endp:int64`;
    `H:int32 list`; `MB:int32 list`] THEN
  STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS; fst SHA256_AVX2_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[sha256_avx2_slot] THEN CONV_TAC(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) THEN
  REWRITE_TAC(map SHA256_K_AT (0--63)) THEN STRIP_TAC THEN
  MP_TAC(SPEC `base:int64` SHA256_BASE_CMPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun n -> SHA256_STEP_TAC n THEN SHA256_COND_TAC) (1--1588) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[sha256_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC(map (INST [`MB:int32 list`,`M:int32 list`] o SHA256_CANON 64) (0--7)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* What the loop around the two halves needs: the frame the prologue makes,  *)
(* the input pointer's comparisons, the message as one read, and the table.  *)
(* ------------------------------------------------------------------------- *)

let SHA256_AVX2_BYTES_LOADED = prove
 (`bytes_loaded s tab sha256_avx2_k256 <=>
   read (memory :> bytes(tab,640)) s = num_of_bytelist sha256_avx2_k256`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV) (AP_TERM `LENGTH:byte list->num` sha256_avx2_k256)]);;

(* The prologue rounds the stack pointer, less 592, down to 1024 bytes and
   works 32 bytes above what this calls base. *)
let SHA256_AVX2_BASE = prove
 (`!stackpointer base:int64.
     1648 <= val stackpointer /\
     base = word_sub (word_and (word_sub stackpointer (word 592)) (word 18446744073709550592)) (word 32)
     ==> aligned 32 base /\ 32 <= val base /\ val base + 576 <= 2 EXP 64 /\
         val stackpointer - 1648 <= val base /\ val base + 624 <= val stackpointer`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_sub stackpointer (word 592):int64) = val stackpointer - 592` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[ARITH_RULE `1648 <= x ==> 592 <= x`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_and (word_sub stackpointer (word 592)) (word 18446744073709550592):int64) =
    1024 * ((val(stackpointer:int64) - 592) DIV 1024)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_BLAST
     `word_and (y:int64) (word 18446744073709550592) = word_shl (word_ushr y 10) 10`] THEN
    ASM_REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`val(stackpointer:int64) - 592`; `1024`] DIVISION) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= (val(stackpointer:int64) - 592) DIV 1024` ASSUME_TAC THENL
   [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(base:int64) = 1024 * ((val(stackpointer:int64) - 592) DIV 1024) - 32` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[aligned; DIMINDEX_64] THEN
  FIRST_ASSUM(fun th -> if (try lhs(concl th) = `val(base:int64)` with Failure _ -> false)
                        then REWRITE_TAC[th] else failwith "") THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[divides] THEN
    EXISTS_TAC `32 * ((val(stackpointer:int64) - 592) DIV 1024) - 1` THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* The input pointer, 64 bytes per block, and the end it is compared to. *)
let SHA256_AVX2_PTRS = prove
 (`!data:int64 n j.
     val data + 64 * (n + 1) < 2 EXP 64 /\ j <= n + 1
     ==> (val (word_sub (word_add data (word (64 * j))) (word_add data (word (64 * n)))) = 0 <=>
          j = n) /\
         (val (word_add data (word (64 * j))) < val (word_add data (word (64 * n))) <=> j < n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. k <= n + 1 ==> val(word_add data (word (64 * k)):int64) = val data + 64 * k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(data:int64) + 64 * (n + 1) < 2 EXP 64` THEN
    UNDISCH_TAC `k <= n + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64; ARITH_RULE `n <= n + 1`] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* Block b of the message, as block A or B's precondition reads it, from the
   whole input's value. *)
let SHA256_AVX2_DATA = prove
 (`!(s:x86state) data n dv (m:num->int32 list) b.
     read (memory :> bytes(data,64 * n)) s = dv /\
     (!i j. i < n /\ j < 16
            ==> (word((dv DIV 2 EXP (8 * (64 * i + 4 * j))) MOD 2 EXP (8 * 4)):int32) =
                word_bytereverse (EL j (m i))) /\
     b < n
     ==> let a = word_add data (word (64 * b)) in
         read (memory :> bytes128 a) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 3 (m b))) (word_bytereverse (EL 2 (m b))))
                                           (word_join (word_bytereverse (EL 1 (m b))) (word_bytereverse (EL 0 (m b)))) /\
         read (memory :> bytes128 (word_add a (word 16))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 7 (m b))) (word_bytereverse (EL 6 (m b))))
                                           (word_join (word_bytereverse (EL 5 (m b))) (word_bytereverse (EL 4 (m b)))) /\
         read (memory :> bytes128 (word_add a (word 32))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 11 (m b))) (word_bytereverse (EL 10 (m b))))
                                           (word_join (word_bytereverse (EL 9 (m b))) (word_bytereverse (EL 8 (m b)))) /\
         read (memory :> bytes128 (word_add a (word 48))) s =
          (word_join:int64->int64->int128) (word_join (word_bytereverse (EL 15 (m b))) (word_bytereverse (EL 14 (m b))))
                                           (word_join (word_bytereverse (EL 13 (m b))) (word_bytereverse (EL 12 (m b))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `!j. j < 16
        ==> read (memory :> bytes32 (word_add data (word (64 * b + 4 * j)))) s =
            word_bytereverse (EL j ((m:num->int32 list) b))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (CONJ (ASSUME `b < n`) (ASSUME `j < 16`)))]) THEN
    MATCH_MP_TAC SHA256_READ_SLICE32 THEN EXISTS_TAC `64 * n` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `b < n` THEN UNDISCH_TAC `j < 16` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NUM_MULT_CONV)) THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT);
              CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[ADD_CLAUSES]);;

(* The whole function's stack frame holds what the prologue and the loop
   write below the stack pointer. *)
let SHA256_AVX2_STACK_SUBSUMED = prove
 (`!stackpointer base:int64.
     1648 <= val stackpointer /\
     base = word_sub (word_and (word_sub stackpointer (word 592)) (word 18446744073709550592)) (word 32)
     ==> MAYCHANGE [memory :> bytes(base,576); memory :> bytes(word_sub stackpointer (word 48),48)]
         subsumed MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1648),1648)]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SHA256_AVX2_BASE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. k <= 1648 ==> val(word_sub stackpointer (word k):int64) = val stackpointer - k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `k MOD 2 EXP 64 = k` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; COND_CASES_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_SING] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUBSUMED_ASSIGNS_SUBCOMPONENTS THEN
  MATCH_MP_TAC SUBSUMED_ASSIGNS_BYTES THEN
  REWRITE_TAC[contained_modulo; DIMINDEX_64] THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th)
    then SIMP_TAC[th; ARITH_RULE `48 <= 1648`; ARITH_RULE `1648 <= 1648`] else failwith "") THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [SUBGOAL_THEN `?d. val(base:int64) = d + (val(stackpointer:int64) - 1648) /\ d + 624 <= 1648`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `val(base:int64) - (val(stackpointer:int64) - 1648)` THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `d + i:num` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[CONG_REFL] `x = y ==> (x == y) (mod n)`) THEN ARITH_TAC;
    EXISTS_TAC `1600 + i` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[CONG_REFL] `x = y ==> (x == y) (mod n)`) THEN ASM_ARITH_TAC]);;

(* The frame lies below what the prologue pushes and the return address. *)
let SHA256_AVX2_PUSH_NONOVERLAP = prove
 (`!stackpointer base:int64.
     32 <= val base /\ val base + 624 <= val stackpointer
     ==> nonoverlapping (base,576) (word_sub stackpointer (word 48),56)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_sub stackpointer (word 48):int64) + 48 = val stackpointer` MP_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[nonoverlapping; nonoverlapping_modulo; DIMINDEX_64; NOT_EXISTS_THM] THEN
  SPEC_TAC(`val(word_sub stackpointer (word 48):int64)`,`y:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  REWRITE_TAC[num_congruent; int_congruent; NOT_EXISTS_THM;
              TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  STRIP_TAC THEN X_GEN_TAC `d:int` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD;
                              GSYM INT_OF_NUM_EQ]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_POW] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_POW]) THEN
  DISJ_CASES_TAC(INT_ARITH `d:int = &0 \/ d <= -- &1 \/ &1 <= d`) THEN
  REPEAT(FIRST_X_ASSUM DISJ_CASES_TAC) THEN
  ASM_INT_ARITH_TAC);;

(* The frame is inside the function's stack region, so disjoint from what
   that region is disjoint from. *)
let SHA256_AVX2_BASE_NONOVERLAP = prove
 (`!stackpointer base:int64 x:int64 l.
     1648 <= val stackpointer /\
     val stackpointer - 1648 <= val base /\ val base + 624 <= val stackpointer /\
     nonoverlapping (word_sub stackpointer (word 1648),1656) (x,l)
     ==> nonoverlapping (base,576) (x,l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping] THEN STRIP_TAC THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`val(word_sub stackpointer (word 1648):int64)`; `1656`;
                        `val(x:int64)`; `l:num`] THEN
  ASM_REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL; DIMINDEX_64] THEN
  MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_sub stackpointer (word 1648):int64) = val stackpointer - 1648`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[contained_modulo] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?d. val(base:int64) = d + (val(stackpointer:int64) - 1648) /\ d + 624 <= 1648`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `val(base:int64) - (val(stackpointer:int64) - 1648)` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `d + i:num` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[CONG_REFL] `x = y ==> (x == y) (mod n)`) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The context, the hash state in the scalar registers, and the spec's       *)
(* state after k blocks, as the terms below state them.                      *)
(* ------------------------------------------------------------------------- *)

let sha256_els v =
  map (fun j -> mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral j), v)) (0--7);;

let sha256_ctx_at j =
  if j = 0 then `ctx:int64`
  else mk_binop `word_add:int64->int64->int64` `ctx:int64`
         (mk_comb(`word:num->int64`, mk_small_numeral (4*j)));;

let sha256_ctx_facts v =
  list_mk_conj(map2 (fun j e ->
    subst [sha256_ctx_at j,`a:int64`; e,`e:int32`] `read (memory :> bytes32 a) (s:x86state) = e`)
    (0--7) (sha256_els v));;

let sha256_scalar_regs = [`RAX`; `RBX`; `RCX`; `RDX`; `R8`; `R9`; `R10`; `R11`];;

let sha256_reg_facts v =
  list_mk_conj(map2 (fun r e ->
    subst [r,`r:(x86state,int64)component`; e,`e:int32`] `read (r:(x86state,int64)component) (s:x86state) = word_zx (e:int32)`)
    sha256_scalar_regs (sha256_els v));;

let sha256_hblocks k =
  subst [k,`k:num`] `sha256_hash_blocks (m:num->int32 list) (h:int32 list) k`;;

(* ------------------------------------------------------------------------- *)
(* The message's blocks, and the input pointer against the end.              *)
(* ------------------------------------------------------------------------- *)

let WORD_BYTEREVERSE_BYTEREVERSE_32 = prove
 (`!x:int32. word_bytereverse (word_bytereverse x) = x`,
  CONV_TAC WORD_BLAST);;

let sha256_join a mm =
  let br j = mk_comb(`word_bytereverse:int32->int32`,
                     mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral j), mm)) in
  let j64 x y = mk_binop `word_join:int32->int32->int64` x y in
  let j128 x y = mk_binop `word_join:int64->int64->int128` x y in
  map (fun k ->
    let addr = if k = 0 then a
               else mk_binop `word_add:int64->int64->int64` a
                      (mk_comb(`word:num->int64`, mk_small_numeral (16*k))) in
    subst [addr,`x:int64`;
           j128 (j64 (br (4*k+3)) (br (4*k+2))) (j64 (br (4*k+1)) (br (4*k))),`v:int128`]
      `read (memory :> bytes128 x) (s:x86state) = v`) (0--3);;

(* Any 64 bytes are some block's byte-swapped message words: block B's lane
   reads the frame when only one block is left. *)
let SHA256_AVX2_ANY_DATA =
  let w j = let x = if j = 0 then `a:int64` else
              mk_binop `word_add:int64->int64->int64` `a:int64`
                (mk_comb(`word:num->int64`, mk_small_numeral (4*j))) in
            subst [x,`x:int64`] `word_bytereverse (read (memory :> bytes32 x) (s:x86state))` in
  let witness = mk_list(map w (0--15), `:int32`) in
  prove
  (mk_forall(`s:x86state`, mk_forall(`a:int64`,
     mk_exists(`mm:int32 list`, list_mk_conj(sha256_join `a:int64` `mm:int32 list`)))),
   REPEAT GEN_TAC THEN EXISTS_TAC witness THEN
   CONV_TAC(DEPTH_CONV EL_CONV) THEN
   REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE_32;
               CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT);
               CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
   REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
   CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]);;

(* The message words as slices of the input's value, which a big step
   carries, unlike a quantified fact about the state. *)
let SHA256_AVX2_INPUT_REL = prove
 (`!(s:x86state) data n (m:num->int32 list).
     (!i j. i < n /\ j < 16
            ==> read (memory :> bytes32 (word_add data (word (64 * i + 4 * j)))) s =
                word_bytereverse (EL j (m i)))
     ==> !i j. i < n /\ j < 16
               ==> (word((read (memory :> bytes(data,64 * n)) s DIV 2 EXP (8 * (64 * i + 4 * j)))
                         MOD 2 EXP (8 * 4)):int32) = word_bytereverse (EL j (m i))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th (CONJ (ASSUME `i < n`) (ASSUME `j < 16`)))]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SHA256_READ_SLICE32 THEN EXISTS_TAC `64 * n` THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `i < n` THEN UNDISCH_TAC `j < 16` THEN ARITH_TAC);;

let SHA256_RSI_END = prove
 (`!data:int64 n i.
     val data + 64 * (n + 1) < 2 EXP 64 /\ 2 * i < n
     ==> (val (word_sub (word_add (word_add data (word (128 * i))) (word 64))
                        (word_add data (word (64 * n)))) = 0 <=> 2 * i + 1 = n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH_RULE `128 * i + 64 = 64 * (2 * i + 1)`] THEN
  MP_TAC(SPECL [`data:int64`; `n:num`; `2 * i + 1`] SHA256_AVX2_PTRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 * i < n` THEN ARITH_TAC; SIMP_TAC[]]);;

let SHA256_RSI_NEXT = prove
 (`!data:int64 n i.
     val data + 64 * (n + 1) < 2 EXP 64 /\ 2 * i + 2 <= n
     ==> (val (word_add (word_add data (word (128 * i))) (word 192)) <
          val (word_add data (word (64 * n))) <=> 2 * i + 3 < n) /\
         (val (word_sub (word_add (word_add data (word (128 * i))) (word 192))
                        (word_add data (word (64 * n)))) = 0 <=> 2 * i + 3 = n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH_RULE `128 * i + 192 = 64 * (2 * i + 3)`] THEN
  MP_TAC(SPECL [`data:int64`; `n:num`; `2 * i + 3`] SHA256_AVX2_PTRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 * i + 2 <= n` THEN ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The loop over pairs of blocks.                                            *)
(* ------------------------------------------------------------------------- *)

let sha256_endp = `word_add data (word (64 * n)):int64`;;

(* At the loop head with 2 * i blocks done. *)
let sha256_loop_inv =
  let hb = sha256_hblocks `2 * i` in
  list_mk_conj[
   `bytes_loaded s (word pc) (sha256_avx2_mc pc k256) /\
    read RIP s = word(pc + 0x80) /\ read RSP s = word_add base (word 480) /\
    read RSI s = word_add (word_add data (word (128 * i))) (word 64) /\
    read R12 s = (if 2 * i + 1 < n then word_add data (word (128 * i + 64))
                  else word_add base (word 480)) /\
    read YMM8 s = word 0xffffffffffffffff0b0a090803020100ffffffffffffffff0b0a090803020100 /\
    read YMM9 s = word 0x0b0a090803020100ffffffffffffffff0b0a090803020100ffffffffffffffff /\
    read (memory :> bytes(word k256,640)) s = num_of_bytelist sha256_avx2_k256 /\
    read (memory :> bytes(data,64 * n)) s = dv /\
    read (memory :> bytes64 (word_add base (word 544))) s = ctx /\
    read (memory :> bytes64 (word_add base (word 560))) s = word_add data (word (64 * n)) /\
    read (memory :> bytes64 (word_add base (word 568))) s = rsp0`;
   sha256_reg_facts hb;
   sha256_ctx_facts hb];;

let sha256_loop_post =
  list_mk_conj[
   `read RIP s = word(pc + 0x13ff) /\ read RBP s = word_add base (word 480) /\
    read (memory :> bytes64 (word_add base (word 568))) s = rsp0`;
   sha256_ctx_facts (sha256_hblocks `n:num`)];;

let sha256_loop_frame =
  `MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; RBP; R8; R9; R10; R11; R12; R13; R14; R15] ,,
   MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
   MAYCHANGE [memory :> bytes(base,544); memory :> bytes(ctx:int64,32)]`;;

let sha256_loop_hyps =
  `aligned 64 (word k256:int64) /\ aligned 32 (base:int64) /\
   32 <= val base /\ val base + 576 <= 2 EXP 64 /\
   nonoverlapping (base,576) (word pc:int64,0x1423) /\
   nonoverlapping (base,576) (word k256:int64,640) /\
   nonoverlapping (base,576) (data:int64,64 * n) /\
   nonoverlapping (base,576) (ctx:int64,32) /\
   nonoverlapping (ctx,32) (word pc,0x1423) /\
   nonoverlapping (ctx,32) (word k256,640) /\
   nonoverlapping (ctx,32) (data,64 * n) /\
   riprel32_within_bounds (k256 + 512) (pc + 136) /\
   riprel32_within_bounds k256 (pc + 204) /\
   val data + 64 * (n + 1) < 2 EXP 64 /\
   (!i j. i < n /\ j < 16
          ==> (word((dv DIV 2 EXP (8 * (64 * i + 4 * j))) MOD 2 EXP (8 * 4)):int32) =
              word_bytereverse (EL j ((m:num->int32 list) i)))`;;

let sha256_loop_ensures inv =
  list_mk_icomb "ensures" [`x86`; mk_abs(`s:x86state`, inv);
                           mk_abs(`s:x86state`, sha256_loop_post); sha256_loop_frame];;

let SHA256_AVX2_LOOP_GOAL =
  let tm = mk_imp(sha256_loop_hyps,
                  mk_forall(`i:num`, mk_imp(`2 * i < n`, sha256_loop_ensures sha256_loop_inv))) in
  list_mk_forall(frees tm, tm);;

let sha256_inst th l =
  INST (map (fun (v,n) -> v, mk_var(n, type_of v)) l) (SPEC_ALL th);;

(* Arithmetic on the loop counters alone, away from the state's facts. *)
let SHA256_ARITH_TAC =
  let num_ty = `:num` in
  W(fun (asl,w) ->
    let hs = filter (fun (_,th) -> let c = concl th in
               let fv = frees c in
               fv <> [] && not (is_forall c) && forall (fun v -> type_of v = num_ty) fv) asl in
    MAP_EVERY (fun (_,th) -> MP_TAC th) hs THEN ARITH_TAC);;

(* Folds a block's result into the next hash state. *)
let SHA256_FOLD_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(CONJUNCT2 sha256_hash_blocks)]);;

(* Block B's schedule words, which block A leaves on the stack, as one fact
   each, which steps carry. *)
let SHA256_SLOTS_CONV =
  EXPAND_CASES_CONV THENC REWRITE_CONV[sha256_avx2_slot] THENC DEPTH_CONV NUM_RED_CONV;;

let SHA256_SLOTS_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SHA256_SLOTS_CONV o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `sha256_avx2_slot`)) (concl th)));;

let SHA256_PRE_TAC =
  REWRITE_TAC[SHA256_AVX2_BYTES_LOADED] THEN
  TRY(CONV_TAC(ONCE_DEPTH_CONV(fun t ->
    if is_forall t && can (find_term ((=) `sha256_avx2_slot`)) t then SHA256_SLOTS_CONV t
    else failwith ""))) THEN
  ASM_REWRITE_TAC[];;

(* Block A's rounds and the context update after them, from the loop head
   with block B's message at pb, through the branch on whether B is there. *)
let SHA256_BLOCK_A_TAC pb mB =
  let thA = sha256_inst SHA256_AVX2_BLOCK_A
    [`word_add data (word (128 * i)):int64`, "pa"; pb, "pb";
     `(m:num->int32 list) (2 * i)`, "MA"; mB, "MB";
     sha256_hblocks `2 * i`, "H"] in
  REWRITE_TAC[fst SHA256_AVX2_EXEC; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`s0:x86state`; `data:int64`; `n:num`; `dv:num`; `m:num->int32 list`; `2 * i`]
          SHA256_AVX2_DATA) THEN
  ASM_REWRITE_TAC[ARITH_RULE `64 * (2 * i) = 128 * i`] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN STRIP_TAC THEN
  (fun g -> (if mB = `MB:int32 list` then
     X_CHOOSE_THEN mB STRIP_ASSUME_TAC (SPECL [`s0:x86state`; pb] SHA256_AVX2_ANY_DATA)
   else
     MP_TAC(SPECL [`s0:x86state`; `data:int64`; `n:num`; `dv:num`; `m:num->int32 list`; `2 * i + 1`]
              SHA256_AVX2_DATA) THEN
     ASM_REWRITE_TAC[ARITH_RULE `64 * (2 * i + 1) = 128 * i + 64`] THEN
     CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN STRIP_TAC) g) THEN
  MP_TAC thA THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  X86_BIGSTEP_TAC SHA256_AVX2_EXEC "s1" THENL [SHA256_PRE_TAC; ALL_TAC] THEN
  SHA256_SLOTS_TAC THEN
  X86_STEPS_TAC SHA256_AVX2_EXEC (2--3) THEN
  MP_TAC(SPECL [`data:int64`; `n:num`; `i:num`] SHA256_RSI_END) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SHA256_FOLD_TAC;;

(* Block B's rounds and the context update after them, to the loop's
   closing branch, with the branch's condition as one on i and n. *)
let SHA256_BLOCK_B_TAC =
  let thB = sha256_inst SHA256_AVX2_BLOCK_B
    [`word_add data (word (128 * i)):int64`, "pa"; sha256_endp, "endp";
     `(m:num->int32 list) (2 * i + 1)`, "MB"; sha256_hblocks `2 * i + 1`, "H"] in
  MP_TAC thB THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  X86_BIGSTEP_TAC SHA256_AVX2_EXEC "s4" THENL [SHA256_PRE_TAC; ALL_TAC] THEN
  X86_STEPS_TAC SHA256_AVX2_EXEC [5] THEN
  SHA256_FOLD_TAC THEN
  MP_TAC(SPECL [`data:int64`; `n:num`; `i:num`] SHA256_RSI_NEXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SHA256_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(2 * i + 1) + 1 = 2 * (i + 1)`]);;

let SHA256_HASH_N_TAC k =
  SUBGOAL_THEN (subst [k,`k:num`] `sha256_hash_blocks m h n = sha256_hash_blocks m h k`) SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> let c = concl th in is_eq c && rand c = `n:num`)) THEN
    (REFL_TAC ORELSE (AP_TERM_TAC THEN ARITH_TAC)); ALL_TAC];;

(* Rewriting a fact leaves the rewrite's hypotheses on it, which can clash
   with the stepper's own variable names (it names an instruction's length
   n); this restates every assumption as itself. *)
let SHA256_LAUNDER_TAC =
  POP_ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> ASSUME_TAC (ASSUME (concl th))) (rev ths));;

let SHA256_AVX2_LOOP = prove
 (SHA256_AVX2_LOOP_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_forall(`d:num`, mk_forall(`i:num`,
    mk_imp(`n - 2 * i = d`, mk_imp(`2 * i < n`, sha256_loop_ensures sha256_loop_inv)))))
   (fun th -> X_GEN_TAC `i:num` THEN MP_TAC(SPECL [`n - 2 * i`; `i:num`] th) THEN REWRITE_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `2 * i + 1 = n` THENL
   [(* One block left: block B's lane reads the frame, and the routine ends
       after block A. *)
    SUBGOAL_THEN `~(2 * i + 1 < n)` (fun th -> REWRITE_TAC[th]) THENL [SHA256_ARITH_TAC; ALL_TAC] THEN
    SHA256_BLOCK_A_TAC `word_add base (word 480):int64` `MB:int32 list` THEN
    ENSURES_FINAL_STATE_TAC THEN SHA256_HASH_N_TAC `2 * i + 1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * i + 1 < n` ASSUME_TAC THENL [SHA256_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `2 * i + 2 = n` THENL
   [(* Two blocks left: the loop ends after them. *)
    ASM_REWRITE_TAC[] THEN
    SHA256_BLOCK_A_TAC `word_add data (word (128 * i + 64)):int64` `(m:num->int32 list) (2 * i + 1)` THEN
    SHA256_BLOCK_B_TAC THEN
    SUBGOAL_THEN `~(2 * i + 3 < n) /\ ~(2 * i + 3 = n)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SHA256_ARITH_TAC; ALL_TAC] THEN
    SHA256_LAUNDER_TAC THEN X86_STEPS_TAC SHA256_AVX2_EXEC [6] THEN
    ENSURES_FINAL_STATE_TAC THEN SHA256_HASH_N_TAC `2 * (i + 1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* More: the loop runs again from the head with two more blocks done. *)
  SUBGOAL_THEN `2 * i + 3 <= n` ASSUME_TAC THENL [SHA256_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x80`
   (mk_abs(`s:x86state`, list_mk_conj(tl(tl(conjuncts(subst [`i + 1`,`i:num`] sha256_loop_inv)))))) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SHA256_BLOCK_A_TAC `word_add data (word (128 * i + 64)):int64` `(m:num->int32 list) (2 * i + 1)` THEN
    SHA256_BLOCK_B_TAC THEN
    SUBGOAL_THEN `2 * i + 3 < n \/ 2 * i + 3 = n` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SHA256_ARITH_TAC; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[ARITH_RULE `2 * (i + 1) + 1 = 2 * i + 3`; ARITH_RULE `128 * (i + 1) + 64 = 128 * i + 192`;
                ARITH_RULE `128 * (i + 1) = 128 * i + 128`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH_RULE `(128 * i + 128) + 64 = 128 * i + 192`] THEN
    ASM_CASES_TAC `2 * i + 3 = n` THEN ASM_REWRITE_TAC[LT_REFL] THEN
    SUBGOAL_THEN `2 * i + 3 < n` ASSUME_TAC THENL [SHA256_ARITH_TAC; ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 2 * (i + 1)` o
                  check (fun th -> is_forall (concl th) && free_in `d:num` (concl th))) THEN
    ANTS_TAC THENL [SHA256_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `i + 1`)] THEN
    REWRITE_TAC[] THEN
    ANTS_TAC THENL [SHA256_ARITH_TAC; REWRITE_TAC[GSYM CONJ_ASSOC; SOME_FLAGS]] THEN
    DISCH_THEN MATCH_ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The stack frame.                                                          *)
(* ------------------------------------------------------------------------- *)

let SHA256_AVX2_PUSHES = WORD_RULE
 `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
    (stackpointer:int64) (word 8)) (word 8)) (word 8)) (word 8)) (word 8)) (word 8))
    (word 544) = word_sub stackpointer (word 592)`;;

let SHA256_AVX2_FRAME_RSP = WORD_RULE
 `word_add (word_and (word_sub (stackpointer:int64) (word 592)) (word 18446744073709550592))
           (word 448) =
  word_add (word_sub (word_and (word_sub stackpointer (word 592)) (word 18446744073709550592))
                     (word 32)) (word 480)`;;

(* The frame as an offset into the function's stack region. *)
let SHA256_AVX2_BASE_OFFSET = prove
 (`!stackpointer base:int64.
     1648 <= val stackpointer /\
     val stackpointer - 1648 <= val base /\ val base + 624 <= val stackpointer
     ==> ?e. e + 576 <= 1648 /\ word_add (word_sub stackpointer (word 1648)) (word e) = base`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `val(base:int64) - (val(stackpointer:int64) - 1648)` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `base:int64` VAL_BOUND) THEN MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val(word_sub stackpointer (word 1648):int64) = val stackpointer - 1648`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(val(base:int64) - (val(stackpointer:int64) - 1648)) MOD 2 EXP 64 =
                val base - (val stackpointer - 1648)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(val(stackpointer:int64) - 1648) + (val(base:int64) - (val stackpointer - 1648)) =
                val base` SUBST1_TAC THENL
   [ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

(* Names the frame base once the prologue has aligned the stack pointer, and
   places the frame within the function's stack region. *)
let SHA256_AVX2_FRAME_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[SHA256_AVX2_PUSHES; SHA256_AVX2_FRAME_RSP]) THEN
  ABBREV_TAC `base = word_sub (word_and (word_sub stackpointer (word 592))
                                        (word 18446744073709550592)) (word 32):int64` THEN
  MP_TAC(SPECL [`stackpointer:int64`; `base:int64`] SHA256_AVX2_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`stackpointer:int64`; `base:int64`] SHA256_AVX2_PUSH_NONOVERLAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY (fun (x,l) ->
    MP_TAC(SPECL [`stackpointer:int64`; `base:int64`; x; l] SHA256_AVX2_BASE_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC)
   [`word pc:int64`,`0x1423`; `word k256:int64`,`640`; `data:int64`,`64 * n`; `ctx:int64`,`32`];;

let SHA256_AVX2_N_FACTS = prove
 (`!data:int64 n.
     0 < n /\ val data + 64 * (n + 1) < 2 EXP 64
     ==> word_sub data (word 18446744073709551552) = word_add data (word 64) /\
         word_add data (word (4 * val (word_shl (word n:int64) 4))) =
         word_add data (word (64 * n)) /\
         (val (word_sub (word_add data (word 64)) (word_add data (word (64 * n)))) = 0
          <=> ~(1 < n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_BLAST;
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(2 EXP 4 * n) MOD 2 EXP 64 = 16 * n` SUBST1_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN MATCH_MP_TAC MOD_LT THEN
      POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      ARITH_TAC];
    MP_TAC(SPECL [`data:int64`; `n:num`; `1`] SHA256_AVX2_PTRS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_ARITH_TAC]);;

(* The pushes leave their slots at nested word_sub addresses; the pops
   read them back as word_add stackpointer (word (2 EXP 64 - 8 * k)). *)
let SHA256_AVX2_PUSH_SLOTS =
  let sp = `stackpointer:int64` and w8 = `word 8:int64` in
  let rec nest k = if k = 0 then sp else mk_binop `word_sub:int64->int64->int64` (nest(k-1)) w8 in
  map (fun k ->
    let neg = mk_comb(`word:num->int64`, mk_numeral(num_of_string "18446744073709551616" -/ num_of_string(string_of_int(8*k)))) in
    let sub = mk_binop `word_sub:int64->int64->int64` sp (mk_comb(`word:num->int64`, mk_small_numeral(8*k))) in
    let th2 = WORD_BLAST(mk_eq(sub, mk_binop `word_add:int64->int64->int64` sp neg)) in
    if k = 1 then th2 else TRANS (WORD_RULE(mk_eq(nest k, sub))) th2) (1--6);;

(* The frame: every stack address the routine writes, as an offset from the
   bottom of the declared stack region. *)
let SHA256_AVX2_SUB_FRAME_TAC =
  let sp = `stackpointer:int64` and b = `word_sub stackpointer (word 1648):int64` in
  let wadd x y = mk_binop `word_add:int64->int64->int64` x y in
  let wd n = mk_comb(`word:num->int64`, n) in
  let slots = map (fun k ->
    WORD_BLAST(mk_eq(
      wadd sp (wd (mk_numeral(num_of_string "18446744073709551616" -/ num_of_string(string_of_int(8*k))))),
      wadd b (wd (mk_small_numeral(1648 - 8*k)))))) (1--6) in
  MP_TAC(SPECL [sp; `base:int64`] SHA256_AVX2_BASE_OFFSET) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th])))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE slots) THEN
  MONOTONE_MAYCHANGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The whole routine: its prologue, the loop, and its epilogue and return.   *)
(* ------------------------------------------------------------------------- *)

(* The prologue pushes six registers and then aligns its frame down to 1024
   bytes, so the frame's place depends on the stack pointer's low bits. All
   the routine writes on the stack lies in the 1648 bytes below it. *)
let SHA256_AVX2_SUBROUTINE_GOAL =
  let tm = mk_imp(
   `0 < n /\ val (data:int64) + 64 * (n + 1) < 2 EXP 64 /\
    1648 <= val (stackpointer:int64) /\ aligned 64 (word k256:int64) /\
    riprel32_within_bounds (k256 + 544) (pc + 114) /\
    riprel32_within_bounds (k256 + 576) (pc + 122) /\
    riprel32_within_bounds (k256 + 512) (pc + 136) /\
    riprel32_within_bounds k256 (pc + 204) /\
    ALL (nonoverlapping (word_sub stackpointer (word 1648),1656))
        [(word pc,0x1423); (word k256,640); (data,64 * n); (ctx:int64,32)] /\
    ALL (nonoverlapping (ctx,32)) [(word pc,0x1423); (word k256,640); (data,64 * n)]`,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj[
     `bytes_loaded s (word pc) (sha256_avx2_mc pc k256) /\
      read RIP s = word pc /\ read RSP s = stackpointer /\
      read (memory :> bytes64 stackpointer) s = returnaddress /\
      C_ARGUMENTS [ctx; data; word n] s /\
      bytes_loaded s (word k256) sha256_avx2_k256`;
     sha256_ctx_facts `h:int32 list`;
     `!i j. i < n /\ j < 16
            ==> read (memory :> bytes32 (word_add data (word (64 * i + 4 * j)))) s =
                word_bytereverse (EL j ((m:num->int32 list) i))`]);
    mk_abs(`s:x86state`, list_mk_conj[
     `read RIP s = returnaddress /\ read RSP s = word_add stackpointer (word 8)`;
     sha256_ctx_facts (sha256_hblocks `n:num`)]);
    `MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(ctx:int64,32);
                memory :> bytes(word_sub stackpointer (word 1648),1648)]`]) in
  list_mk_forall(frees tm, tm);;

let SHA256_AVX2_SUBROUTINE_CORRECT = prove
 (SHA256_AVX2_SUBROUTINE_GOAL,
  let thL = sha256_inst SHA256_AVX2_LOOP [`stackpointer:int64`, "rsp0"] in
  let fold ofs extra k =
    let sum = mk_small_numeral (ofs + extra) in
    FIRST_ASSUM(ASSUME_TAC o
      MATCH_MP (SPECL [`pc:num`; mk_small_numeral ofs; mk_small_numeral extra; `k256:num`]
                      SHA256_RIPREL_FOLD) o
      CONV_RULE(LAND_CONV(RAND_CONV(ONCE_REWRITE_CONV
        [ARITH_RULE(mk_eq(sum, mk_binop `(+):num->num->num` (mk_small_numeral ofs) (mk_small_numeral extra)))]))) o
      check ((=) (subst [k,`k:num`; mk_small_numeral ofs,`q:num`]
                    `riprel32_within_bounds (k256 + k) (pc + q)`) o concl)) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
   [`RBX`; `RBP`; `R12`; `R13`; `R14`; `R15`] THEN
  REWRITE_TAC[fst SHA256_AVX2_EXEC] THEN ENSURES_INIT_TAC "s0" THEN
  (* The input as one region, which the loop takes. *)
  ABBREV_TAC `dv = read (memory :> bytes(data,64 * n)) s0` THEN
  MP_TAC(SPECL [`s0:x86state`; `data:int64`; `n:num`; `m:num->int32 list`] SHA256_AVX2_INPUT_REL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) && free_in `s0:x86state` (concl th))) THEN
  (* The masks the prologue loads from the table, and the table as one
     region. VMOVDQA's alignment check needs the table 32-byte aligned. *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SHA256_AVX2_K256 o
    check (can (term_match [] `bytes_loaded s (word k) sha256_avx2_k256`) o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SHA256_AVX2_BYTES_LOADED]) THEN
  fold 114 430 `544` THEN fold 122 454 `576` THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  SUBGOAL_THEN `aligned 32 (word k256:int64)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ALIGNED_WORD_WEAKEN; DIVIDES_CONV `32 divides 64`]; ALL_TAC] THEN
  (* The pushes and the frame's alignment, then its stores and the loads
     before the loop. *)
  X86_STEPS_TAC SHA256_AVX2_EXEC (1--12) THEN
  SHA256_AVX2_FRAME_TAC THEN
  X86_STEPS_TAC SHA256_AVX2_EXEC (13--32) THEN
  MP_TAC(SPECL [`data:int64`; `n:num`] SHA256_AVX2_N_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; COND_SWAP])) THEN
  (* The loop, from no blocks done. *)
  MP_TAC thL THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; CONJUNCT1 sha256_hash_blocks] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  X86_BIGSTEP_TAC SHA256_AVX2_EXEC "s33" THEN
  (* The pops and the return. *)
  RULE_ASSUM_TAC(REWRITE_RULE SHA256_AVX2_PUSH_SLOTS) THEN
  X86_STEPS_TAC SHA256_AVX2_EXEC (34--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHA256_AVX2_SUB_FRAME_TAC);;
