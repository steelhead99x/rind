(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-512 block compression with AVX2, as rind's build emits it.            *)
(* ========================================================================= *)

(* rind's naked function low::x86_64::sha512::sha512_block_data_order_avx2 is
   OpenSSL's sha512_block_data_order_avx2 (crypto/sha/asm/sha512-x86_64.pl,
   the AVX2 path), which reads its round constants and byte-swap mask from
   the K512 table beside it. It hashes two blocks per pass: the message
   schedule runs in both 128-bit lanes of each YMM register, the first
   block's rounds read their round-constant-plus-schedule words as the
   schedule computes them, and the second block's rounds read the words the
   first pass left on the stack. Its result is s2n-bignum's FIPS 180-4 spec,
   sha512_hash_blocks, from s2n-bignum pull request #420, which
   rind's fork in thirdparty/s2n-bignum/ holds until it merges. The proof steps the
   instructions symbolically through both blocks of a pass, folding each
   round's registers and each message schedule lane into the spec's terms as
   they appear, so no term grows past one round. *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/sha512_spec.ml";;

(* admin/prove writes the function's object, as rind's release build emits
   it, to x86_64/sha512_block_data_order_avx2.o: its instructions as .text,
   with a relocation, and the K512 table as .rodata. The definition fails
   unless the instructions and relocation are these, and sha512_avx2_k512 is
   the table's bytes, which SHA512_AVX2_K512_FACTS checks against FIPS
   180-4's constants. *)
let sha512_avx2_mc,sha512_avx2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(fun _ -> "sha512_avx2_k512")
    "sha512_avx2_mc" "x86_64/sha512_block_data_order_avx2.o"
(fun b ADDR -> [b[
  0x48; 0x89; 0xe0;        (* MOV (% rax) (% rsp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0x20; 0x05; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 1312)) *)
  0x48; 0xc1; 0xe2; 0x04;  (* SHL (% rdx) (Imm8 (word 4)) *)
  0x48; 0x81; 0xe4; 0x00; 0xf8; 0xff; 0xff;
                           (* AND (% rsp) (Imm32 (word 4294965248)) *)
  0x48; 0x8d; 0x14; 0xd6;  (* LEA (% rdx) (%%% (rsi,3,rdx)) *)
  0x48; 0x81; 0xc4; 0x80; 0x04; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 1152)) *)
  0x48; 0x89; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rdi) *)
  0x48; 0x89; 0xb4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rsi) *)
  0x48; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rax) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0x48; 0x83; 0xee; 0x80;  (* SUB (% rsi) (Imm8 (word 128)) *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x49; 0x89; 0xf4;        (* MOV (% r12) (% rsi) *)
  0x48; 0x8b; 0x5f; 0x08;  (* MOV (% rbx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x39; 0xd6;        (* CMP (% rsi) (% rdx) *)
  0x48; 0x8b; 0x4f; 0x10;  (* MOV (% rcx) (Memop Quadword (%% (rdi,16))) *)
  0x4c; 0x0f; 0x44; 0xe4;  (* CMOVE (% r12) (% rsp) *)
  0x48; 0x8b; 0x57; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x8b; 0x47; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x8b; 0x4f; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x4c; 0x8b; 0x57; 0x30;  (* MOV (% r10) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x8b; 0x5f; 0x38;  (* MOV (% r11) (Memop Quadword (%% (rdi,56))) *)
  0xeb; 0x04;              (* JMP (Imm8 (word 4)) *)
  0x0f; 0x1f; 0x40; 0x00;  (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x80;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,18446744073709551488))) *)
  0xc5; 0xfa; 0x6f; 0x4e; 0x90;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rsi,18446744073709551504))) *)
  0xc5; 0xfa; 0x6f; 0x56; 0xa0;
                           (* VMOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,18446744073709551520))) *)
  0x48; 0x8d; 0x2d]; ADDR ("sha512_avx2_k512",(124)); b[
                           (* LEA (% rbp) (Riprel (word_sx (iword (&sha512_avx2_k512 - (&pc + &22))))) *)
  0xc5; 0xfa; 0x6f; 0x5e; 0xb0;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rsi,18446744073709551536))) *)
  0xc5; 0xfa; 0x6f; 0x66; 0xc0;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,18446744073709551552))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0xd0;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,18446744073709551568))) *)
  0xc5; 0xfa; 0x6f; 0x76; 0xe0;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,18446744073709551584))) *)
  0xc5; 0xfa; 0x6f; 0x7e; 0xf0;
                           (* VMOVDQU (%_% xmm7) (Memop Word128 (%% (rsi,18446744073709551600))) *)
  0xc5; 0x7d; 0x6f; 0x95; 0x80; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rbp,1152))) *)
  0xc4; 0xc3; 0x7d; 0x38; 0x04; 0x24; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (Memop Word128 (%% (r12,0)))
(Imm8 (word 1)) *)
  0xc4; 0xc3; 0x75; 0x38; 0x4c; 0x24; 0x10; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (r12,16)))
(Imm8 (word 1)) *)
  0xc4; 0xc2; 0x7d; 0x00; 0xc2;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm10) *)
  0xc4; 0xc3; 0x6d; 0x38; 0x54; 0x24; 0x20; 0x01;
                           (* VINSERTI128 (%_% ymm2) (%_% ymm2) (Memop Word128 (%% (r12,32)))
(Imm8 (word 1)) *)
  0xc4; 0xc2; 0x75; 0x00; 0xca;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm10) *)
  0xc4; 0xc3; 0x65; 0x38; 0x5c; 0x24; 0x30; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (r12,48)))
(Imm8 (word 1)) *)
  0xc4; 0xc2; 0x6d; 0x00; 0xd2;
                           (* VPSHUFB (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc3; 0x5d; 0x38; 0x64; 0x24; 0x40; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (r12,64)))
(Imm8 (word 1)) *)
  0xc4; 0xc2; 0x65; 0x00; 0xda;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm10) *)
  0xc4; 0xc3; 0x55; 0x38; 0x6c; 0x24; 0x50; 0x01;
                           (* VINSERTI128 (%_% ymm5) (%_% ymm5) (Memop Word128 (%% (r12,80)))
(Imm8 (word 1)) *)
  0xc4; 0xc2; 0x5d; 0x00; 0xe2;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm10) *)
  0xc4; 0xc3; 0x4d; 0x38; 0x74; 0x24; 0x60; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (Memop Word128 (%% (r12,96)))
(Imm8 (word 1)) *)
  0xc4; 0xc2; 0x55; 0x00; 0xea;
                           (* VPSHUFB (%_% ymm5) (%_% ymm5) (%_% ymm10) *)
  0xc4; 0xc3; 0x45; 0x38; 0x7c; 0x24; 0x70; 0x01;
                           (* VINSERTI128 (%_% ymm7) (%_% ymm7) (Memop Word128 (%% (r12,112)))
(Imm8 (word 1)) *)
  0xc5; 0x7d; 0xd4; 0x45; 0x80;
                           (* VPADDQ (%_% ymm8) (%_% ymm0) (Memop Word256 (%% (rbp,18446744073709551488))) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc5; 0x75; 0xd4; 0x4d; 0xa0;
                           (* VPADDQ (%_% ymm9) (%_% ymm1) (Memop Word256 (%% (rbp,18446744073709551520))) *)
  0xc4; 0xc2; 0x45; 0x00; 0xfa;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm10) *)
  0xc5; 0x6d; 0xd4; 0x55; 0xc0;
                           (* VPADDQ (%_% ymm10) (%_% ymm2) (Memop Word256 (%% (rbp,18446744073709551552))) *)
  0xc5; 0x65; 0xd4; 0x5d; 0xe0;
                           (* VPADDQ (%_% ymm11) (%_% ymm3) (Memop Word256 (%% (rbp,18446744073709551584))) *)
  0xc5; 0x7d; 0x7f; 0x04; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm8) *)
  0xc5; 0x5d; 0xd4; 0x45; 0x00;
                           (* VPADDQ (%_% ymm8) (%_% ymm4) (Memop Word256 (%% (rbp,0))) *)
  0xc5; 0x7d; 0x7f; 0x4c; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm9) *)
  0xc5; 0x55; 0xd4; 0x4d; 0x20;
                           (* VPADDQ (%_% ymm9) (%_% ymm5) (Memop Word256 (%% (rbp,32))) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rsp,64))) (%_% ymm10) *)
  0xc5; 0x4d; 0xd4; 0x55; 0x40;
                           (* VPADDQ (%_% ymm10) (%_% ymm6) (Memop Word256 (%% (rbp,64))) *)
  0xc5; 0x7d; 0x7f; 0x5c; 0x24; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rsp,96))) (%_% ymm11) *)
  0x48; 0x8b; 0xbc; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x8d; 0x64; 0x24; 0x80;
                           (* LEA (% rsp) (%% (rsp,18446744073709551488)) *)
  0x48; 0x89; 0x7c; 0x24; 0xf8;
                           (* MOV (Memop Quadword (%% (rsp,18446744073709551608))) (% rdi) *)
  0xc5; 0x45; 0xd4; 0x5d; 0x60;
                           (* VPADDQ (%_% ymm11) (%_% ymm7) (Memop Word256 (%% (rbp,96))) *)
  0xc5; 0x7d; 0x7f; 0x04; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm8) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0xc5; 0x7d; 0x7f; 0x4c; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm9) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rsp,64))) (%_% ymm10) *)
  0x48; 0x31; 0xcf;        (* XOR (% rdi) (% rcx) *)
  0xc5; 0x7d; 0x7f; 0x5c; 0x24; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rsp,96))) (%_% ymm11) *)
  0x4d; 0x89; 0xcc;        (* MOV (% r12) (% r9) *)
  0x48; 0x81; 0xc5; 0x00; 0x01; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 256)) *)
  0xeb; 0x05;              (* JMP (Imm8 (word 5)) *)
  0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%%% (rax,0,rax))) *)
  0x48; 0x8d; 0x64; 0x24; 0x80;
                           (* LEA (% rsp) (%% (rsp,18446744073709551488)) *)
  0xff; 0x74; 0x24; 0x78;  (* PUSH (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x8d; 0x64; 0x24; 0x08;
                           (* LEA (% rsp) (%% (rsp,8)) *)
  0xc4; 0x63; 0x75; 0x0f; 0xc0; 0x08;
                           (* VPALIGNR (%_% ymm8) (%_% ymm1) (%_% ymm0) (Imm8 (word 8)) *)
  0x4c; 0x03; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* ADD (% r11) (Memop Quadword (%% (rsp,256))) *)
  0x4d; 0x21; 0xc4;        (* AND (% r12) (% r8) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% r8) (Imm8 (word 41)) *)
  0xc4; 0x63; 0x55; 0x0f; 0xdc; 0x08;
                           (* VPALIGNR (%_% ymm11) (%_% ymm5) (%_% ymm4) (Imm8 (word 8)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% r8) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x04; 0x30;  (* LEA (% rax) (%%% (rax,0,r14)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd0; 0x01;
                           (* VPSRLQ (%_% ymm10) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x42; 0xb8; 0xf2; 0xe2;
                           (* ANDN (% r12) (% r8) (% r10) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% r8) (Imm8 (word 14)) *)
  0xc5; 0xa5; 0xd4; 0xc0;  (* VPADDQ (%_% ymm0) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x07;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 7)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf0; 0x38;
                           (* VPSLLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 56)) *)
  0xc4; 0x41; 0x25; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% rax) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x1c; 0x2b;  (* LEA (% r11) (%%% (r11,0,r13)) *)
  0x49; 0x31; 0xdf;        (* XOR (% r15) (% rbx) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x07;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% rax) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% rax) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x14; 0x1a;  (* LEA (% rdx) (%%% (rdx,0,r11)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x07;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xdf;        (* XOR (% rdi) (% rbx) *)
  0xc5; 0xa5; 0x73; 0xd7; 0x06;
                           (* VPSRLQ (%_% ymm11) (%_% ymm7) (Imm8 (word 6)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x1c; 0x3b;  (* LEA (% r11) (%%% (r11,0,rdi)) *)
  0x4d; 0x89; 0xc4;        (* MOV (% r12) (% r8) *)
  0xc5; 0xad; 0x73; 0xf7; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm7) (Imm8 (word 3)) *)
  0xc5; 0xbd; 0xd4; 0xc0;  (* VPADDQ (%_% ymm0) (%_% ymm8) (%_% ymm0) *)
  0x4c; 0x03; 0x94; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* ADD (% r10) (Memop Quadword (%% (rsp,264))) *)
  0x49; 0x21; 0xd4;        (* AND (% r12) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% rdx) (Imm8 (word 41)) *)
  0xc5; 0xb5; 0x73; 0xd7; 0x13;
                           (* VPSRLQ (%_% ymm9) (%_% ymm7) (Imm8 (word 19)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% rdi) (% rdx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x1c; 0x33;  (* LEA (% r11) (%%% (r11,0,r14)) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2a;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x42; 0xe8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rdx) (% r9) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% rdx) (Imm8 (word 14)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x2a;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xdf;        (* MOV (% rdi) (% r11) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% r11) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x14; 0x2a;  (* LEA (% r10) (%%% (r10,0,r13)) *)
  0x48; 0x31; 0xc7;        (* XOR (% rdi) (% rax) *)
  0xc5; 0xa5; 0xd4; 0xc0;  (* VPADDQ (%_% ymm0) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% r11) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% r11) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x0c; 0x11;  (* LEA (% rcx) (%%% (rcx,0,r10)) *)
  0xc5; 0x7d; 0xd4; 0x55; 0x80;
                           (* VPADDQ (%_% ymm10) (%_% ymm0) (Memop Word256 (%% (rbp,18446744073709551488))) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xc7;        (* XOR (% r15) (% rax) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x14; 0x3a;  (* LEA (% r10) (%%% (r10,0,r15)) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0xc5; 0x7d; 0x7f; 0x14; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm10) *)
  0xc4; 0x63; 0x6d; 0x0f; 0xc1; 0x08;
                           (* VPALIGNR (%_% ymm8) (%_% ymm2) (%_% ymm1) (Imm8 (word 8)) *)
  0x4c; 0x03; 0x8c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* ADD (% r9) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0x21; 0xcc;        (* AND (% r12) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% rcx) (Imm8 (word 41)) *)
  0xc4; 0x63; 0x4d; 0x0f; 0xdd; 0x08;
                           (* VPALIGNR (%_% ymm11) (%_% ymm6) (%_% ymm5) (Imm8 (word 8)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% r15) (% rcx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x14; 0x32;  (* LEA (% r10) (%%% (r10,0,r14)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd0; 0x01;
                           (* VPSRLQ (%_% ymm10) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x42; 0xf0; 0xf2; 0xe0;
                           (* ANDN (% r12) (% rcx) (% r8) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% rcx) (Imm8 (word 14)) *)
  0xc5; 0xa5; 0xd4; 0xc9;  (* VPADDQ (%_% ymm1) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x07;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 7)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xd7;        (* MOV (% r15) (% r10) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf0; 0x38;
                           (* VPSLLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 56)) *)
  0xc4; 0x41; 0x25; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% r10) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x0c; 0x29;  (* LEA (% r9) (%%% (r9,0,r13)) *)
  0x4d; 0x31; 0xdf;        (* XOR (% r15) (% r11) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x07;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% r10) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% r10) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x1c; 0x0b;  (* LEA (% rbx) (%%% (rbx,0,r9)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x07;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xdf;        (* XOR (% rdi) (% r11) *)
  0xc5; 0xa5; 0x73; 0xd0; 0x06;
                           (* VPSRLQ (%_% ymm11) (%_% ymm0) (Imm8 (word 6)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x0c; 0x39;  (* LEA (% r9) (%%% (r9,0,rdi)) *)
  0x49; 0x89; 0xcc;        (* MOV (% r12) (% rcx) *)
  0xc5; 0xad; 0x73; 0xf0; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm0) (Imm8 (word 3)) *)
  0xc5; 0xbd; 0xd4; 0xc9;  (* VPADDQ (%_% ymm1) (%_% ymm8) (%_% ymm1) *)
  0x4c; 0x03; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,296))) *)
  0x49; 0x21; 0xdc;        (* AND (% r12) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% rbx) (Imm8 (word 41)) *)
  0xc5; 0xb5; 0x73; 0xd0; 0x13;
                           (* VPSRLQ (%_% ymm9) (%_% ymm0) (Imm8 (word 19)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% rbx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x0c; 0x31;  (* LEA (% r9) (%%% (r9,0,r14)) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2a;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x62; 0xe0; 0xf2; 0xe2;
                           (* ANDN (% r12) (% rbx) (% rdx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% rbx) (Imm8 (word 14)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x2a;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xcf;        (* MOV (% rdi) (% r9) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% r9) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x04; 0x28;  (* LEA (% r8) (%%% (r8,0,r13)) *)
  0x4c; 0x31; 0xd7;        (* XOR (% rdi) (% r10) *)
  0xc5; 0xa5; 0xd4; 0xc9;  (* VPADDQ (%_% ymm1) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% r9) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% r9) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x04; 0x00;  (* LEA (% rax) (%%% (rax,0,r8)) *)
  0xc5; 0x75; 0xd4; 0x55; 0xa0;
                           (* VPADDQ (%_% ymm10) (%_% ymm1) (Memop Word256 (%% (rbp,18446744073709551520))) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xd7;        (* XOR (% r15) (% r10) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x04; 0x38;  (* LEA (% r8) (%%% (r8,0,r15)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm10) *)
  0xc4; 0x63; 0x65; 0x0f; 0xc2; 0x08;
                           (* VPALIGNR (%_% ymm8) (%_% ymm3) (%_% ymm2) (Imm8 (word 8)) *)
  0x48; 0x03; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* ADD (% rdx) (Memop Quadword (%% (rsp,320))) *)
  0x49; 0x21; 0xc4;        (* AND (% r12) (% rax) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% rax) (Imm8 (word 41)) *)
  0xc4; 0x63; 0x45; 0x0f; 0xde; 0x08;
                           (* VPALIGNR (%_% ymm11) (%_% ymm7) (%_% ymm6) (Imm8 (word 8)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% rax) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x04; 0x30;  (* LEA (% r8) (%%% (r8,0,r14)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd0; 0x01;
                           (* VPSRLQ (%_% ymm10) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x62; 0xf8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rax) (% rcx) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% rax) (Imm8 (word 14)) *)
  0xc5; 0xa5; 0xd4; 0xd2;  (* VPADDQ (%_% ymm2) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x07;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 7)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xc7;        (* MOV (% r15) (% r8) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf0; 0x38;
                           (* VPSLLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 56)) *)
  0xc4; 0x41; 0x25; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% r8) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x14; 0x2a;  (* LEA (% rdx) (%%% (rdx,0,r13)) *)
  0x4d; 0x31; 0xcf;        (* XOR (% r15) (% r9) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x07;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% r8) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% r8) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x1c; 0x13;  (* LEA (% r11) (%%% (r11,0,rdx)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x07;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xcf;        (* XOR (% rdi) (% r9) *)
  0xc5; 0xa5; 0x73; 0xd1; 0x06;
                           (* VPSRLQ (%_% ymm11) (%_% ymm1) (Imm8 (word 6)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x14; 0x3a;  (* LEA (% rdx) (%%% (rdx,0,rdi)) *)
  0x49; 0x89; 0xc4;        (* MOV (% r12) (% rax) *)
  0xc5; 0xad; 0x73; 0xf1; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 3)) *)
  0xc5; 0xbd; 0xd4; 0xd2;  (* VPADDQ (%_% ymm2) (%_% ymm8) (%_% ymm2) *)
  0x48; 0x03; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* ADD (% rcx) (Memop Quadword (%% (rsp,328))) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% r11) (Imm8 (word 41)) *)
  0xc5; 0xb5; 0x73; 0xd1; 0x13;
                           (* VPSRLQ (%_% ymm9) (%_% ymm1) (Imm8 (word 19)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% r11) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x14; 0x32;  (* LEA (% rdx) (%%% (rdx,0,r14)) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2a;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x62; 0xa0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r11) (% rbx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% r11) (Imm8 (word 14)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x2a;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% rdx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x0c; 0x29;  (* LEA (% rcx) (%%% (rcx,0,r13)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0xc5; 0xa5; 0xd4; 0xd2;  (* VPADDQ (%_% ymm2) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% rdx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% rdx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x14; 0x0a;  (* LEA (% r10) (%%% (r10,0,rcx)) *)
  0xc5; 0x6d; 0xd4; 0x55; 0xc0;
                           (* VPADDQ (%_% ymm10) (%_% ymm2) (Memop Word256 (%% (rbp,18446744073709551552))) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xc7;        (* XOR (% r15) (% r8) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,r15)) *)
  0x4d; 0x89; 0xdc;        (* MOV (% r12) (% r11) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rsp,64))) (%_% ymm10) *)
  0xc4; 0x63; 0x5d; 0x0f; 0xc3; 0x08;
                           (* VPALIGNR (%_% ymm8) (%_% ymm4) (%_% ymm3) (Imm8 (word 8)) *)
  0x48; 0x03; 0x9c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* ADD (% rbx) (Memop Quadword (%% (rsp,352))) *)
  0x4d; 0x21; 0xd4;        (* AND (% r12) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% r10) (Imm8 (word 41)) *)
  0xc4; 0x63; 0x7d; 0x0f; 0xdf; 0x08;
                           (* VPALIGNR (%_% ymm11) (%_% ymm0) (%_% ymm7) (Imm8 (word 8)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% r15) (% r10) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x0c; 0x31;  (* LEA (% rcx) (%%% (rcx,0,r14)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd0; 0x01;
                           (* VPSRLQ (%_% ymm10) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x62; 0xa8; 0xf2; 0xe0;
                           (* ANDN (% r12) (% r10) (% rax) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% r10) (Imm8 (word 14)) *)
  0xc5; 0xa5; 0xd4; 0xdb;  (* VPADDQ (%_% ymm3) (%_% ymm11) (%_% ymm3) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x07;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 7)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xcf;        (* MOV (% r15) (% rcx) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf0; 0x38;
                           (* VPSLLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 56)) *)
  0xc4; 0x41; 0x25; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% rcx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x1c; 0x2b;  (* LEA (% rbx) (%%% (rbx,0,r13)) *)
  0x49; 0x31; 0xd7;        (* XOR (% r15) (% rdx) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x07;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% rcx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% rcx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x0c; 0x19;  (* LEA (% r9) (%%% (r9,0,rbx)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x07;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xd7;        (* XOR (% rdi) (% rdx) *)
  0xc5; 0xa5; 0x73; 0xd2; 0x06;
                           (* VPSRLQ (%_% ymm11) (%_% ymm2) (Imm8 (word 6)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x1c; 0x3b;  (* LEA (% rbx) (%%% (rbx,0,rdi)) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0xc5; 0xad; 0x73; 0xf2; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm2) (Imm8 (word 3)) *)
  0xc5; 0xbd; 0xd4; 0xdb;  (* VPADDQ (%_% ymm3) (%_% ymm8) (%_% ymm3) *)
  0x48; 0x03; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* ADD (% rax) (Memop Quadword (%% (rsp,360))) *)
  0x4d; 0x21; 0xcc;        (* AND (% r12) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% r9) (Imm8 (word 41)) *)
  0xc5; 0xb5; 0x73; 0xd2; 0x13;
                           (* VPSRLQ (%_% ymm9) (%_% ymm2) (Imm8 (word 19)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% rdi) (% r9) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x1c; 0x33;  (* LEA (% rbx) (%%% (rbx,0,r14)) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2a;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x42; 0xb0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r9) (% r11) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% r9) (Imm8 (word 14)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x2a;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% rbx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x04; 0x28;  (* LEA (% rax) (%%% (rax,0,r13)) *)
  0x48; 0x31; 0xcf;        (* XOR (% rdi) (% rcx) *)
  0xc5; 0xa5; 0xd4; 0xdb;  (* VPADDQ (%_% ymm3) (%_% ymm11) (%_% ymm3) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% rbx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% rbx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x04; 0x00;  (* LEA (% r8) (%%% (r8,0,rax)) *)
  0xc5; 0x65; 0xd4; 0x55; 0xe0;
                           (* VPADDQ (%_% ymm10) (%_% ymm3) (Memop Word256 (%% (rbp,18446744073709551584))) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xcf;        (* XOR (% r15) (% rcx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x04; 0x38;  (* LEA (% rax) (%%% (rax,0,r15)) *)
  0x4d; 0x89; 0xcc;        (* MOV (% r12) (% r9) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rsp,96))) (%_% ymm10) *)
  0x48; 0x8d; 0x64; 0x24; 0x80;
                           (* LEA (% rsp) (%% (rsp,18446744073709551488)) *)
  0xff; 0x74; 0x24; 0x78;  (* PUSH (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x8d; 0x64; 0x24; 0x08;
                           (* LEA (% rsp) (%% (rsp,8)) *)
  0xc4; 0x63; 0x55; 0x0f; 0xc4; 0x08;
                           (* VPALIGNR (%_% ymm8) (%_% ymm5) (%_% ymm4) (Imm8 (word 8)) *)
  0x4c; 0x03; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* ADD (% r11) (Memop Quadword (%% (rsp,256))) *)
  0x4d; 0x21; 0xc4;        (* AND (% r12) (% r8) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% r8) (Imm8 (word 41)) *)
  0xc4; 0x63; 0x75; 0x0f; 0xd8; 0x08;
                           (* VPALIGNR (%_% ymm11) (%_% ymm1) (%_% ymm0) (Imm8 (word 8)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% r8) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x04; 0x30;  (* LEA (% rax) (%%% (rax,0,r14)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd0; 0x01;
                           (* VPSRLQ (%_% ymm10) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x42; 0xb8; 0xf2; 0xe2;
                           (* ANDN (% r12) (% r8) (% r10) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% r8) (Imm8 (word 14)) *)
  0xc5; 0xa5; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm11) (%_% ymm4) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x07;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 7)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf0; 0x38;
                           (* VPSLLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 56)) *)
  0xc4; 0x41; 0x25; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% rax) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x1c; 0x2b;  (* LEA (% r11) (%%% (r11,0,r13)) *)
  0x49; 0x31; 0xdf;        (* XOR (% r15) (% rbx) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x07;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% rax) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% rax) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x14; 0x1a;  (* LEA (% rdx) (%%% (rdx,0,r11)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x07;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xdf;        (* XOR (% rdi) (% rbx) *)
  0xc5; 0xa5; 0x73; 0xd3; 0x06;
                           (* VPSRLQ (%_% ymm11) (%_% ymm3) (Imm8 (word 6)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x1c; 0x3b;  (* LEA (% r11) (%%% (r11,0,rdi)) *)
  0x4d; 0x89; 0xc4;        (* MOV (% r12) (% r8) *)
  0xc5; 0xad; 0x73; 0xf3; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm3) (Imm8 (word 3)) *)
  0xc5; 0xbd; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0x4c; 0x03; 0x94; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* ADD (% r10) (Memop Quadword (%% (rsp,264))) *)
  0x49; 0x21; 0xd4;        (* AND (% r12) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% rdx) (Imm8 (word 41)) *)
  0xc5; 0xb5; 0x73; 0xd3; 0x13;
                           (* VPSRLQ (%_% ymm9) (%_% ymm3) (Imm8 (word 19)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% rdi) (% rdx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x1c; 0x33;  (* LEA (% r11) (%%% (r11,0,r14)) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2a;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x42; 0xe8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rdx) (% r9) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% rdx) (Imm8 (word 14)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x2a;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xdf;        (* MOV (% rdi) (% r11) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% r11) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x14; 0x2a;  (* LEA (% r10) (%%% (r10,0,r13)) *)
  0x48; 0x31; 0xc7;        (* XOR (% rdi) (% rax) *)
  0xc5; 0xa5; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm11) (%_% ymm4) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% r11) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% r11) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x0c; 0x11;  (* LEA (% rcx) (%%% (rcx,0,r10)) *)
  0xc5; 0x5d; 0xd4; 0x55; 0x00;
                           (* VPADDQ (%_% ymm10) (%_% ymm4) (Memop Word256 (%% (rbp,0))) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xc7;        (* XOR (% r15) (% rax) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x14; 0x3a;  (* LEA (% r10) (%%% (r10,0,r15)) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0xc5; 0x7d; 0x7f; 0x14; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm10) *)
  0xc4; 0x63; 0x4d; 0x0f; 0xc5; 0x08;
                           (* VPALIGNR (%_% ymm8) (%_% ymm6) (%_% ymm5) (Imm8 (word 8)) *)
  0x4c; 0x03; 0x8c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* ADD (% r9) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0x21; 0xcc;        (* AND (% r12) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% rcx) (Imm8 (word 41)) *)
  0xc4; 0x63; 0x6d; 0x0f; 0xd9; 0x08;
                           (* VPALIGNR (%_% ymm11) (%_% ymm2) (%_% ymm1) (Imm8 (word 8)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% r15) (% rcx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x14; 0x32;  (* LEA (% r10) (%%% (r10,0,r14)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd0; 0x01;
                           (* VPSRLQ (%_% ymm10) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x42; 0xf0; 0xf2; 0xe0;
                           (* ANDN (% r12) (% rcx) (% r8) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% rcx) (Imm8 (word 14)) *)
  0xc5; 0xa5; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm11) (%_% ymm5) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x07;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 7)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xd7;        (* MOV (% r15) (% r10) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf0; 0x38;
                           (* VPSLLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 56)) *)
  0xc4; 0x41; 0x25; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% r10) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x0c; 0x29;  (* LEA (% r9) (%%% (r9,0,r13)) *)
  0x4d; 0x31; 0xdf;        (* XOR (% r15) (% r11) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x07;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% r10) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% r10) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x1c; 0x0b;  (* LEA (% rbx) (%%% (rbx,0,r9)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x07;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xdf;        (* XOR (% rdi) (% r11) *)
  0xc5; 0xa5; 0x73; 0xd4; 0x06;
                           (* VPSRLQ (%_% ymm11) (%_% ymm4) (Imm8 (word 6)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x0c; 0x39;  (* LEA (% r9) (%%% (r9,0,rdi)) *)
  0x49; 0x89; 0xcc;        (* MOV (% r12) (% rcx) *)
  0xc5; 0xad; 0x73; 0xf4; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xbd; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0x4c; 0x03; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,296))) *)
  0x49; 0x21; 0xdc;        (* AND (% r12) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% rbx) (Imm8 (word 41)) *)
  0xc5; 0xb5; 0x73; 0xd4; 0x13;
                           (* VPSRLQ (%_% ymm9) (%_% ymm4) (Imm8 (word 19)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% rbx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x0c; 0x31;  (* LEA (% r9) (%%% (r9,0,r14)) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2a;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x62; 0xe0; 0xf2; 0xe2;
                           (* ANDN (% r12) (% rbx) (% rdx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% rbx) (Imm8 (word 14)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x2a;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xcf;        (* MOV (% rdi) (% r9) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% r9) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x04; 0x28;  (* LEA (% r8) (%%% (r8,0,r13)) *)
  0x4c; 0x31; 0xd7;        (* XOR (% rdi) (% r10) *)
  0xc5; 0xa5; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm11) (%_% ymm5) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% r9) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% r9) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x04; 0x00;  (* LEA (% rax) (%%% (rax,0,r8)) *)
  0xc5; 0x55; 0xd4; 0x55; 0x20;
                           (* VPADDQ (%_% ymm10) (%_% ymm5) (Memop Word256 (%% (rbp,32))) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xd7;        (* XOR (% r15) (% r10) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x04; 0x38;  (* LEA (% r8) (%%% (r8,0,r15)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm10) *)
  0xc4; 0x63; 0x45; 0x0f; 0xc6; 0x08;
                           (* VPALIGNR (%_% ymm8) (%_% ymm7) (%_% ymm6) (Imm8 (word 8)) *)
  0x48; 0x03; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* ADD (% rdx) (Memop Quadword (%% (rsp,320))) *)
  0x49; 0x21; 0xc4;        (* AND (% r12) (% rax) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% rax) (Imm8 (word 41)) *)
  0xc4; 0x63; 0x65; 0x0f; 0xda; 0x08;
                           (* VPALIGNR (%_% ymm11) (%_% ymm3) (%_% ymm2) (Imm8 (word 8)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% rax) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x04; 0x30;  (* LEA (% r8) (%%% (r8,0,r14)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd0; 0x01;
                           (* VPSRLQ (%_% ymm10) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x62; 0xf8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rax) (% rcx) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% rax) (Imm8 (word 14)) *)
  0xc5; 0xa5; 0xd4; 0xf6;  (* VPADDQ (%_% ymm6) (%_% ymm11) (%_% ymm6) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x07;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 7)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xc7;        (* MOV (% r15) (% r8) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf0; 0x38;
                           (* VPSLLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 56)) *)
  0xc4; 0x41; 0x25; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% r8) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x14; 0x2a;  (* LEA (% rdx) (%%% (rdx,0,r13)) *)
  0x4d; 0x31; 0xcf;        (* XOR (% r15) (% r9) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x07;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% r8) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% r8) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x1c; 0x13;  (* LEA (% r11) (%%% (r11,0,rdx)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x07;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xcf;        (* XOR (% rdi) (% r9) *)
  0xc5; 0xa5; 0x73; 0xd5; 0x06;
                           (* VPSRLQ (%_% ymm11) (%_% ymm5) (Imm8 (word 6)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x14; 0x3a;  (* LEA (% rdx) (%%% (rdx,0,rdi)) *)
  0x49; 0x89; 0xc4;        (* MOV (% r12) (% rax) *)
  0xc5; 0xad; 0x73; 0xf5; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm5) (Imm8 (word 3)) *)
  0xc5; 0xbd; 0xd4; 0xf6;  (* VPADDQ (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0x48; 0x03; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* ADD (% rcx) (Memop Quadword (%% (rsp,328))) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% r11) (Imm8 (word 41)) *)
  0xc5; 0xb5; 0x73; 0xd5; 0x13;
                           (* VPSRLQ (%_% ymm9) (%_% ymm5) (Imm8 (word 19)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% r11) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x14; 0x32;  (* LEA (% rdx) (%%% (rdx,0,r14)) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2a;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x62; 0xa0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r11) (% rbx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% r11) (Imm8 (word 14)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x2a;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% rdx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x0c; 0x29;  (* LEA (% rcx) (%%% (rcx,0,r13)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0xc5; 0xa5; 0xd4; 0xf6;  (* VPADDQ (%_% ymm6) (%_% ymm11) (%_% ymm6) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% rdx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% rdx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x14; 0x0a;  (* LEA (% r10) (%%% (r10,0,rcx)) *)
  0xc5; 0x4d; 0xd4; 0x55; 0x40;
                           (* VPADDQ (%_% ymm10) (%_% ymm6) (Memop Word256 (%% (rbp,64))) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xc7;        (* XOR (% r15) (% r8) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,r15)) *)
  0x4d; 0x89; 0xdc;        (* MOV (% r12) (% r11) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rsp,64))) (%_% ymm10) *)
  0xc4; 0x63; 0x7d; 0x0f; 0xc7; 0x08;
                           (* VPALIGNR (%_% ymm8) (%_% ymm0) (%_% ymm7) (Imm8 (word 8)) *)
  0x48; 0x03; 0x9c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* ADD (% rbx) (Memop Quadword (%% (rsp,352))) *)
  0x4d; 0x21; 0xd4;        (* AND (% r12) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% r10) (Imm8 (word 41)) *)
  0xc4; 0x63; 0x5d; 0x0f; 0xdb; 0x08;
                           (* VPALIGNR (%_% ymm11) (%_% ymm4) (%_% ymm3) (Imm8 (word 8)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% r15) (% r10) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x0c; 0x31;  (* LEA (% rcx) (%%% (rcx,0,r14)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd0; 0x01;
                           (* VPSRLQ (%_% ymm10) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x62; 0xa8; 0xf2; 0xe0;
                           (* ANDN (% r12) (% r10) (% rax) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% r10) (Imm8 (word 14)) *)
  0xc5; 0xa5; 0xd4; 0xff;  (* VPADDQ (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x07;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 7)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xcf;        (* MOV (% r15) (% rcx) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf0; 0x38;
                           (* VPSLLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 56)) *)
  0xc4; 0x41; 0x25; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% rcx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x1c; 0x2b;  (* LEA (% rbx) (%%% (rbx,0,r13)) *)
  0x49; 0x31; 0xd7;        (* XOR (% r15) (% rdx) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x07;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% rcx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% rcx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x0c; 0x19;  (* LEA (% r9) (%%% (r9,0,rbx)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x07;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xd7;        (* XOR (% rdi) (% rdx) *)
  0xc5; 0xa5; 0x73; 0xd6; 0x06;
                           (* VPSRLQ (%_% ymm11) (%_% ymm6) (Imm8 (word 6)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x1c; 0x3b;  (* LEA (% rbx) (%%% (rbx,0,rdi)) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0xc5; 0xad; 0x73; 0xf6; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xbd; 0xd4; 0xff;  (* VPADDQ (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0x48; 0x03; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* ADD (% rax) (Memop Quadword (%% (rsp,360))) *)
  0x4d; 0x21; 0xcc;        (* AND (% r12) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% r9) (Imm8 (word 41)) *)
  0xc5; 0xb5; 0x73; 0xd6; 0x13;
                           (* VPSRLQ (%_% ymm9) (%_% ymm6) (Imm8 (word 19)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% rdi) (% r9) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x1c; 0x33;  (* LEA (% rbx) (%%% (rbx,0,r14)) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2a;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x42; 0xb0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r9) (% r11) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% r9) (Imm8 (word 14)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x2a;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 42)) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0xc4; 0x41; 0x25; 0xef; 0xd9;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm9) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% rbx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x04; 0x28;  (* LEA (% rax) (%%% (rax,0,r13)) *)
  0x48; 0x31; 0xcf;        (* XOR (% rdi) (% rcx) *)
  0xc5; 0xa5; 0xd4; 0xff;  (* VPADDQ (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% rbx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% rbx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x04; 0x00;  (* LEA (% r8) (%%% (r8,0,rax)) *)
  0xc5; 0x45; 0xd4; 0x55; 0x60;
                           (* VPADDQ (%_% ymm10) (%_% ymm7) (Memop Word256 (%% (rbp,96))) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xcf;        (* XOR (% r15) (% rcx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x04; 0x38;  (* LEA (% rax) (%%% (rax,0,r15)) *)
  0x4d; 0x89; 0xcc;        (* MOV (% r12) (% r9) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rsp,96))) (%_% ymm10) *)
  0x48; 0x8d; 0xad; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rbp,256)) *)
  0x80; 0x7d; 0x87; 0x00;  (* CMP (Memop Byte (%% (rbp,18446744073709551495))) (Imm8 (word 0)) *)
  0x0f; 0x85; 0x45; 0xf5; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294964549)) *)
  0x4c; 0x03; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% r11) (Memop Quadword (%% (rsp,128))) *)
  0x4d; 0x21; 0xc4;        (* AND (% r12) (% r8) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% r8) (Imm8 (word 41)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% r8) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x04; 0x30;  (* LEA (% rax) (%%% (rax,0,r14)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0xc4; 0x42; 0xb8; 0xf2; 0xe2;
                           (* ANDN (% r12) (% r8) (% r10) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% r8) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% rax) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x1c; 0x2b;  (* LEA (% r11) (%%% (r11,0,r13)) *)
  0x49; 0x31; 0xdf;        (* XOR (% r15) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% rax) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% rax) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x14; 0x1a;  (* LEA (% rdx) (%%% (rdx,0,r11)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xdf;        (* XOR (% rdi) (% rbx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x1c; 0x3b;  (* LEA (% r11) (%%% (r11,0,rdi)) *)
  0x4d; 0x89; 0xc4;        (* MOV (% r12) (% r8) *)
  0x4c; 0x03; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* ADD (% r10) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x21; 0xd4;        (* AND (% r12) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% rdx) (Imm8 (word 41)) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% rdi) (% rdx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x1c; 0x33;  (* LEA (% r11) (%%% (r11,0,r14)) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0xc4; 0x42; 0xe8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rdx) (% r9) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% rdx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xdf;        (* MOV (% rdi) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% r11) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x14; 0x2a;  (* LEA (% r10) (%%% (r10,0,r13)) *)
  0x48; 0x31; 0xc7;        (* XOR (% rdi) (% rax) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% r11) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% r11) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x0c; 0x11;  (* LEA (% rcx) (%%% (rcx,0,r10)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xc7;        (* XOR (% r15) (% rax) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x14; 0x3a;  (* LEA (% r10) (%%% (r10,0,r15)) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x4c; 0x03; 0x8c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* ADD (% r9) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x21; 0xcc;        (* AND (% r12) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% rcx) (Imm8 (word 41)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% r15) (% rcx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x14; 0x32;  (* LEA (% r10) (%%% (r10,0,r14)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0xc4; 0x42; 0xf0; 0xf2; 0xe0;
                           (* ANDN (% r12) (% rcx) (% r8) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% rcx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xd7;        (* MOV (% r15) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% r10) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x0c; 0x29;  (* LEA (% r9) (%%% (r9,0,r13)) *)
  0x4d; 0x31; 0xdf;        (* XOR (% r15) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% r10) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% r10) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x1c; 0x0b;  (* LEA (% rbx) (%%% (rbx,0,r9)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xdf;        (* XOR (% rdi) (% r11) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x0c; 0x39;  (* LEA (% r9) (%%% (r9,0,rdi)) *)
  0x49; 0x89; 0xcc;        (* MOV (% r12) (% rcx) *)
  0x4c; 0x03; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x21; 0xdc;        (* AND (% r12) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% rbx) (Imm8 (word 41)) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% rbx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x0c; 0x31;  (* LEA (% r9) (%%% (r9,0,r14)) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0xc4; 0x62; 0xe0; 0xf2; 0xe2;
                           (* ANDN (% r12) (% rbx) (% rdx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% rbx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xcf;        (* MOV (% rdi) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% r9) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x04; 0x28;  (* LEA (% r8) (%%% (r8,0,r13)) *)
  0x4c; 0x31; 0xd7;        (* XOR (% rdi) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% r9) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% r9) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x04; 0x00;  (* LEA (% rax) (%%% (rax,0,r8)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xd7;        (* XOR (% r15) (% r10) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x04; 0x38;  (* LEA (% r8) (%%% (r8,0,r15)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x48; 0x03; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* ADD (% rdx) (Memop Quadword (%% (rsp,192))) *)
  0x49; 0x21; 0xc4;        (* AND (% r12) (% rax) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% rax) (Imm8 (word 41)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% rax) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x04; 0x30;  (* LEA (% r8) (%%% (r8,0,r14)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0xc4; 0x62; 0xf8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rax) (% rcx) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% rax) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xc7;        (* MOV (% r15) (% r8) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% r8) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x14; 0x2a;  (* LEA (% rdx) (%%% (rdx,0,r13)) *)
  0x4d; 0x31; 0xcf;        (* XOR (% r15) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% r8) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% r8) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x1c; 0x13;  (* LEA (% r11) (%%% (r11,0,rdx)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xcf;        (* XOR (% rdi) (% r9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x14; 0x3a;  (* LEA (% rdx) (%%% (rdx,0,rdi)) *)
  0x49; 0x89; 0xc4;        (* MOV (% r12) (% rax) *)
  0x48; 0x03; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* ADD (% rcx) (Memop Quadword (%% (rsp,200))) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% r11) (Imm8 (word 41)) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% r11) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x14; 0x32;  (* LEA (% rdx) (%%% (rdx,0,r14)) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0xc4; 0x62; 0xa0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r11) (% rbx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% r11) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% rdx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x0c; 0x29;  (* LEA (% rcx) (%%% (rcx,0,r13)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% rdx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% rdx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x14; 0x0a;  (* LEA (% r10) (%%% (r10,0,rcx)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xc7;        (* XOR (% r15) (% r8) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,r15)) *)
  0x4d; 0x89; 0xdc;        (* MOV (% r12) (% r11) *)
  0x48; 0x03; 0x9c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* ADD (% rbx) (Memop Quadword (%% (rsp,224))) *)
  0x4d; 0x21; 0xd4;        (* AND (% r12) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% r10) (Imm8 (word 41)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% r15) (% r10) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x0c; 0x31;  (* LEA (% rcx) (%%% (rcx,0,r14)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0xc4; 0x62; 0xa8; 0xf2; 0xe0;
                           (* ANDN (% r12) (% r10) (% rax) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% r10) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xcf;        (* MOV (% r15) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% rcx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x1c; 0x2b;  (* LEA (% rbx) (%%% (rbx,0,r13)) *)
  0x49; 0x31; 0xd7;        (* XOR (% r15) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% rcx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% rcx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x0c; 0x19;  (* LEA (% r9) (%%% (r9,0,rbx)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xd7;        (* XOR (% rdi) (% rdx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x1c; 0x3b;  (* LEA (% rbx) (%%% (rbx,0,rdi)) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0x48; 0x03; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* ADD (% rax) (Memop Quadword (%% (rsp,232))) *)
  0x4d; 0x21; 0xcc;        (* AND (% r12) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% r9) (Imm8 (word 41)) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% rdi) (% r9) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x1c; 0x33;  (* LEA (% rbx) (%%% (rbx,0,r14)) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0xc4; 0x42; 0xb0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r9) (% r11) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% r9) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% rbx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x04; 0x28;  (* LEA (% rax) (%%% (rax,0,r13)) *)
  0x48; 0x31; 0xcf;        (* XOR (% rdi) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% rbx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% rbx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x04; 0x00;  (* LEA (% r8) (%%% (r8,0,rax)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xcf;        (* XOR (% r15) (% rcx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x04; 0x38;  (* LEA (% rax) (%%% (rax,0,r15)) *)
  0x4d; 0x89; 0xcc;        (* MOV (% r12) (% r9) *)
  0x4c; 0x03; 0x1c; 0x24;  (* ADD (% r11) (Memop Quadword (%% (rsp,0))) *)
  0x4d; 0x21; 0xc4;        (* AND (% r12) (% r8) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% r8) (Imm8 (word 41)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% r8) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x04; 0x30;  (* LEA (% rax) (%%% (rax,0,r14)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0xc4; 0x42; 0xb8; 0xf2; 0xe2;
                           (* ANDN (% r12) (% r8) (% r10) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% r8) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% rax) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x1c; 0x2b;  (* LEA (% r11) (%%% (r11,0,r13)) *)
  0x49; 0x31; 0xdf;        (* XOR (% r15) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% rax) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% rax) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x14; 0x1a;  (* LEA (% rdx) (%%% (rdx,0,r11)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xdf;        (* XOR (% rdi) (% rbx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x1c; 0x3b;  (* LEA (% r11) (%%% (r11,0,rdi)) *)
  0x4d; 0x89; 0xc4;        (* MOV (% r12) (% r8) *)
  0x4c; 0x03; 0x54; 0x24; 0x08;
                           (* ADD (% r10) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x21; 0xd4;        (* AND (% r12) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% rdx) (Imm8 (word 41)) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% rdi) (% rdx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x1c; 0x33;  (* LEA (% r11) (%%% (r11,0,r14)) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0xc4; 0x42; 0xe8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rdx) (% r9) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% rdx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xdf;        (* MOV (% rdi) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% r11) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x14; 0x2a;  (* LEA (% r10) (%%% (r10,0,r13)) *)
  0x48; 0x31; 0xc7;        (* XOR (% rdi) (% rax) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% r11) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% r11) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x0c; 0x11;  (* LEA (% rcx) (%%% (rcx,0,r10)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xc7;        (* XOR (% r15) (% rax) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x14; 0x3a;  (* LEA (% r10) (%%% (r10,0,r15)) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x4c; 0x03; 0x4c; 0x24; 0x20;
                           (* ADD (% r9) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x21; 0xcc;        (* AND (% r12) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% rcx) (Imm8 (word 41)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% r15) (% rcx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x14; 0x32;  (* LEA (% r10) (%%% (r10,0,r14)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0xc4; 0x42; 0xf0; 0xf2; 0xe0;
                           (* ANDN (% r12) (% rcx) (% r8) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% rcx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xd7;        (* MOV (% r15) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% r10) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x0c; 0x29;  (* LEA (% r9) (%%% (r9,0,r13)) *)
  0x4d; 0x31; 0xdf;        (* XOR (% r15) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% r10) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% r10) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x1c; 0x0b;  (* LEA (% rbx) (%%% (rbx,0,r9)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xdf;        (* XOR (% rdi) (% r11) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x0c; 0x39;  (* LEA (% r9) (%%% (r9,0,rdi)) *)
  0x49; 0x89; 0xcc;        (* MOV (% r12) (% rcx) *)
  0x4c; 0x03; 0x44; 0x24; 0x28;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x21; 0xdc;        (* AND (% r12) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% rbx) (Imm8 (word 41)) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% rbx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x0c; 0x31;  (* LEA (% r9) (%%% (r9,0,r14)) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0xc4; 0x62; 0xe0; 0xf2; 0xe2;
                           (* ANDN (% r12) (% rbx) (% rdx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% rbx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xcf;        (* MOV (% rdi) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% r9) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x04; 0x28;  (* LEA (% r8) (%%% (r8,0,r13)) *)
  0x4c; 0x31; 0xd7;        (* XOR (% rdi) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% r9) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% r9) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x04; 0x00;  (* LEA (% rax) (%%% (rax,0,r8)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xd7;        (* XOR (% r15) (% r10) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x04; 0x38;  (* LEA (% r8) (%%% (r8,0,r15)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x48; 0x03; 0x54; 0x24; 0x40;
                           (* ADD (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x21; 0xc4;        (* AND (% r12) (% rax) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% rax) (Imm8 (word 41)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% rax) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x04; 0x30;  (* LEA (% r8) (%%% (r8,0,r14)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0xc4; 0x62; 0xf8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rax) (% rcx) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% rax) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xc7;        (* MOV (% r15) (% r8) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% r8) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x14; 0x2a;  (* LEA (% rdx) (%%% (rdx,0,r13)) *)
  0x4d; 0x31; 0xcf;        (* XOR (% r15) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% r8) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% r8) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x1c; 0x13;  (* LEA (% r11) (%%% (r11,0,rdx)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xcf;        (* XOR (% rdi) (% r9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x14; 0x3a;  (* LEA (% rdx) (%%% (rdx,0,rdi)) *)
  0x49; 0x89; 0xc4;        (* MOV (% r12) (% rax) *)
  0x48; 0x03; 0x4c; 0x24; 0x48;
                           (* ADD (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% r11) (Imm8 (word 41)) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% r11) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x14; 0x32;  (* LEA (% rdx) (%%% (rdx,0,r14)) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0xc4; 0x62; 0xa0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r11) (% rbx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% r11) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% rdx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x0c; 0x29;  (* LEA (% rcx) (%%% (rcx,0,r13)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% rdx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% rdx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x14; 0x0a;  (* LEA (% r10) (%%% (r10,0,rcx)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xc7;        (* XOR (% r15) (% r8) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,r15)) *)
  0x4d; 0x89; 0xdc;        (* MOV (% r12) (% r11) *)
  0x48; 0x03; 0x5c; 0x24; 0x60;
                           (* ADD (% rbx) (Memop Quadword (%% (rsp,96))) *)
  0x4d; 0x21; 0xd4;        (* AND (% r12) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% r10) (Imm8 (word 41)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% r15) (% r10) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x0c; 0x31;  (* LEA (% rcx) (%%% (rcx,0,r14)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0xc4; 0x62; 0xa8; 0xf2; 0xe0;
                           (* ANDN (% r12) (% r10) (% rax) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% r10) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xcf;        (* MOV (% r15) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% rcx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x1c; 0x2b;  (* LEA (% rbx) (%%% (rbx,0,r13)) *)
  0x49; 0x31; 0xd7;        (* XOR (% r15) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% rcx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% rcx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x0c; 0x19;  (* LEA (% r9) (%%% (r9,0,rbx)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xd7;        (* XOR (% rdi) (% rdx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x1c; 0x3b;  (* LEA (% rbx) (%%% (rbx,0,rdi)) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0x48; 0x03; 0x44; 0x24; 0x68;
                           (* ADD (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4d; 0x21; 0xcc;        (* AND (% r12) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% r9) (Imm8 (word 41)) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% rdi) (% r9) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x1c; 0x33;  (* LEA (% rbx) (%%% (rbx,0,r14)) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0xc4; 0x42; 0xb0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r9) (% r11) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% r9) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% rbx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x04; 0x28;  (* LEA (% rax) (%%% (rax,0,r13)) *)
  0x48; 0x31; 0xcf;        (* XOR (% rdi) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% rbx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% rbx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x04; 0x00;  (* LEA (% r8) (%%% (r8,0,rax)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xcf;        (* XOR (% r15) (% rcx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x04; 0x38;  (* LEA (% rax) (%%% (rax,0,r15)) *)
  0x4d; 0x89; 0xcc;        (* MOV (% r12) (% r9) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x05; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,1280))) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x48; 0x8d; 0xac; 0x24; 0x80; 0x04; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,1152)) *)
  0x48; 0x03; 0x07;        (* ADD (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x03; 0x5f; 0x08;  (* ADD (% rbx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x03; 0x4f; 0x10;  (* ADD (% rcx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x03; 0x57; 0x18;  (* ADD (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x03; 0x47; 0x20;  (* ADD (% r8) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x03; 0x4f; 0x28;  (* ADD (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x4c; 0x03; 0x57; 0x30;  (* ADD (% r10) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x03; 0x5f; 0x38;  (* ADD (% r11) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x89; 0x5f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rbx) *)
  0x48; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rcx) *)
  0x48; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rdx) *)
  0x4c; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r9) *)
  0x4c; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r11) *)
  0x48; 0x3b; 0xb5; 0x90; 0x00; 0x00; 0x00;
                           (* CMP (% rsi) (Memop Quadword (%% (rbp,144))) *)
  0x0f; 0x84; 0xa6; 0x03; 0x00; 0x00;
                           (* JE (Imm32 (word 934)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x31; 0xcf;        (* XOR (% rdi) (% rcx) *)
  0x4d; 0x89; 0xcc;        (* MOV (% r12) (% r9) *)
  0xeb; 0x02;              (* JMP (Imm8 (word 2)) *)
  0x66; 0x90;              (* NOP *)
  0x4c; 0x03; 0x5d; 0x10;  (* ADD (% r11) (Memop Quadword (%% (rbp,16))) *)
  0x4d; 0x21; 0xc4;        (* AND (% r12) (% r8) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% r8) (Imm8 (word 41)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% r8) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x04; 0x30;  (* LEA (% rax) (%%% (rax,0,r14)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0xc4; 0x42; 0xb8; 0xf2; 0xe2;
                           (* ANDN (% r12) (% r8) (% r10) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% r8) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x1c; 0x23;  (* LEA (% r11) (%%% (r11,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% rax) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x1c; 0x2b;  (* LEA (% r11) (%%% (r11,0,r13)) *)
  0x49; 0x31; 0xdf;        (* XOR (% r15) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% rax) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% rax) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x14; 0x1a;  (* LEA (% rdx) (%%% (rdx,0,r11)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xdf;        (* XOR (% rdi) (% rbx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x1c; 0x3b;  (* LEA (% r11) (%%% (r11,0,rdi)) *)
  0x4d; 0x89; 0xc4;        (* MOV (% r12) (% r8) *)
  0x4c; 0x03; 0x55; 0x18;  (* ADD (% r10) (Memop Quadword (%% (rbp,24))) *)
  0x49; 0x21; 0xd4;        (* AND (% r12) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% rdx) (Imm8 (word 41)) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% rdi) (% rdx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x1c; 0x33;  (* LEA (% r11) (%%% (r11,0,r14)) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0xc4; 0x42; 0xe8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rdx) (% r9) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% rdx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x14; 0x22;  (* LEA (% r10) (%%% (r10,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xdf;        (* MOV (% rdi) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% r11) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x14; 0x2a;  (* LEA (% r10) (%%% (r10,0,r13)) *)
  0x48; 0x31; 0xc7;        (* XOR (% rdi) (% rax) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% r11) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% r11) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x0c; 0x11;  (* LEA (% rcx) (%%% (rcx,0,r10)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xc7;        (* XOR (% r15) (% rax) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x14; 0x3a;  (* LEA (% r10) (%%% (r10,0,r15)) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x4c; 0x03; 0x4d; 0x30;  (* ADD (% r9) (Memop Quadword (%% (rbp,48))) *)
  0x49; 0x21; 0xcc;        (* AND (% r12) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% rcx) (Imm8 (word 41)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% r15) (% rcx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x14; 0x32;  (* LEA (% r10) (%%% (r10,0,r14)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0xc4; 0x42; 0xf0; 0xf2; 0xe0;
                           (* ANDN (% r12) (% rcx) (% r8) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% rcx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x0c; 0x21;  (* LEA (% r9) (%%% (r9,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xd7;        (* MOV (% r15) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% r10) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x0c; 0x29;  (* LEA (% r9) (%%% (r9,0,r13)) *)
  0x4d; 0x31; 0xdf;        (* XOR (% r15) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% r10) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% r10) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x1c; 0x0b;  (* LEA (% rbx) (%%% (rbx,0,r9)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xdf;        (* XOR (% rdi) (% r11) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4d; 0x8d; 0x0c; 0x39;  (* LEA (% r9) (%%% (r9,0,rdi)) *)
  0x49; 0x89; 0xcc;        (* MOV (% r12) (% rcx) *)
  0x4c; 0x03; 0x45; 0x38;  (* ADD (% r8) (Memop Quadword (%% (rbp,56))) *)
  0x49; 0x21; 0xdc;        (* AND (% r12) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% rbx) (Imm8 (word 41)) *)
  0xc4; 0xe3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% rbx) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x0c; 0x31;  (* LEA (% r9) (%%% (r9,0,r14)) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0xc4; 0x62; 0xe0; 0xf2; 0xe2;
                           (* ANDN (% r12) (% rbx) (% rdx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% rbx) (Imm8 (word 14)) *)
  0x4f; 0x8d; 0x04; 0x20;  (* LEA (% r8) (%%% (r8,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x89; 0xcf;        (* MOV (% rdi) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% r9) (Imm8 (word 39)) *)
  0x4f; 0x8d; 0x04; 0x28;  (* LEA (% r8) (%%% (r8,0,r13)) *)
  0x4c; 0x31; 0xd7;        (* XOR (% rdi) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% r9) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% r9) (Imm8 (word 28)) *)
  0x4a; 0x8d; 0x04; 0x00;  (* LEA (% rax) (%%% (rax,0,r8)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xd7;        (* XOR (% r15) (% r10) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4f; 0x8d; 0x04; 0x38;  (* LEA (% r8) (%%% (r8,0,r15)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x48; 0x03; 0x55; 0x50;  (* ADD (% rdx) (Memop Quadword (%% (rbp,80))) *)
  0x49; 0x21; 0xc4;        (* AND (% r12) (% rax) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe8; 0x29;
                           (* RORX (% r13) (% rax) (Imm8 (word 41)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf8; 0x12;
                           (* RORX (% r15) (% rax) (Imm8 (word 18)) *)
  0x4f; 0x8d; 0x04; 0x30;  (* LEA (% r8) (%%% (r8,0,r14)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0xc4; 0x62; 0xf8; 0xf2; 0xe1;
                           (* ANDN (% r12) (% rax) (% rcx) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf0; 0x0e;
                           (* RORX (% r14) (% rax) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x14; 0x22;  (* LEA (% rdx) (%%% (rdx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4d; 0x89; 0xc7;        (* MOV (% r15) (% r8) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe0; 0x27;
                           (* RORX (% r12) (% r8) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x14; 0x2a;  (* LEA (% rdx) (%%% (rdx,0,r13)) *)
  0x4d; 0x31; 0xcf;        (* XOR (% r15) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf0; 0x22;
                           (* RORX (% r14) (% r8) (Imm8 (word 34)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe8; 0x1c;
                           (* RORX (% r13) (% r8) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x1c; 0x13;  (* LEA (% r11) (%%% (r11,0,rdx)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4c; 0x31; 0xcf;        (* XOR (% rdi) (% r9) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x14; 0x3a;  (* LEA (% rdx) (%%% (rdx,0,rdi)) *)
  0x49; 0x89; 0xc4;        (* MOV (% r12) (% rax) *)
  0x48; 0x03; 0x4d; 0x58;  (* ADD (% rcx) (Memop Quadword (%% (rbp,88))) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xeb; 0x29;
                           (* RORX (% r13) (% r11) (Imm8 (word 41)) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xfb; 0x12;
                           (* RORX (% rdi) (% r11) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x14; 0x32;  (* LEA (% rdx) (%%% (rdx,0,r14)) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0xc4; 0x62; 0xa0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r11) (% rbx) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf3; 0x0e;
                           (* RORX (% r14) (% r11) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x0c; 0x21;  (* LEA (% rcx) (%%% (rcx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe2; 0x27;
                           (* RORX (% r12) (% rdx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x0c; 0x29;  (* LEA (% rcx) (%%% (rcx,0,r13)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf2; 0x22;
                           (* RORX (% r14) (% rdx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xea; 0x1c;
                           (* RORX (% r13) (% rdx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x14; 0x0a;  (* LEA (% r10) (%%% (r10,0,rcx)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x4d; 0x31; 0xc7;        (* XOR (% r15) (% r8) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,r15)) *)
  0x4d; 0x89; 0xdc;        (* MOV (% r12) (% r11) *)
  0x48; 0x03; 0x5d; 0x70;  (* ADD (% rbx) (Memop Quadword (%% (rbp,112))) *)
  0x4d; 0x21; 0xd4;        (* AND (% r12) (% r10) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xea; 0x29;
                           (* RORX (% r13) (% r10) (Imm8 (word 41)) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xfa; 0x12;
                           (* RORX (% r15) (% r10) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x0c; 0x31;  (* LEA (% rcx) (%%% (rcx,0,r14)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0xc4; 0x62; 0xa8; 0xf2; 0xe0;
                           (* ANDN (% r12) (% r10) (% rax) *)
  0x4d; 0x31; 0xfd;        (* XOR (% r13) (% r15) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf2; 0x0e;
                           (* RORX (% r14) (% r10) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x1c; 0x23;  (* LEA (% rbx) (%%% (rbx,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x49; 0x89; 0xcf;        (* MOV (% r15) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe1; 0x27;
                           (* RORX (% r12) (% rcx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x1c; 0x2b;  (* LEA (% rbx) (%%% (rbx,0,r13)) *)
  0x49; 0x31; 0xd7;        (* XOR (% r15) (% rdx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf1; 0x22;
                           (* RORX (% r14) (% rcx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe9; 0x1c;
                           (* RORX (% r13) (% rcx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x0c; 0x19;  (* LEA (% r9) (%%% (r9,0,rbx)) *)
  0x4c; 0x21; 0xff;        (* AND (% rdi) (% r15) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x48; 0x31; 0xd7;        (* XOR (% rdi) (% rdx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x48; 0x8d; 0x1c; 0x3b;  (* LEA (% rbx) (%%% (rbx,0,rdi)) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0x48; 0x03; 0x45; 0x78;  (* ADD (% rax) (Memop Quadword (%% (rbp,120))) *)
  0x4d; 0x21; 0xcc;        (* AND (% r12) (% r9) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xe9; 0x29;
                           (* RORX (% r13) (% r9) (Imm8 (word 41)) *)
  0xc4; 0xc3; 0xfb; 0xf0; 0xf9; 0x12;
                           (* RORX (% rdi) (% r9) (Imm8 (word 18)) *)
  0x4a; 0x8d; 0x1c; 0x33;  (* LEA (% rbx) (%%% (rbx,0,r14)) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0xc4; 0x42; 0xb0; 0xf2; 0xe3;
                           (* ANDN (% r12) (% r9) (% r11) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0xc4; 0x43; 0xfb; 0xf0; 0xf1; 0x0e;
                           (* RORX (% r14) (% r9) (Imm8 (word 14)) *)
  0x4a; 0x8d; 0x04; 0x20;  (* LEA (% rax) (%%% (rax,0,r12)) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xe3; 0x27;
                           (* RORX (% r12) (% rbx) (Imm8 (word 39)) *)
  0x4a; 0x8d; 0x04; 0x28;  (* LEA (% rax) (%%% (rax,0,r13)) *)
  0x48; 0x31; 0xcf;        (* XOR (% rdi) (% rcx) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xf3; 0x22;
                           (* RORX (% r14) (% rbx) (Imm8 (word 34)) *)
  0xc4; 0x63; 0xfb; 0xf0; 0xeb; 0x1c;
                           (* RORX (% r13) (% rbx) (Imm8 (word 28)) *)
  0x4d; 0x8d; 0x04; 0x00;  (* LEA (% r8) (%%% (r8,0,rax)) *)
  0x49; 0x21; 0xff;        (* AND (% r15) (% rdi) *)
  0x4d; 0x31; 0xe6;        (* XOR (% r14) (% r12) *)
  0x49; 0x31; 0xcf;        (* XOR (% r15) (% rcx) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4a; 0x8d; 0x04; 0x38;  (* LEA (% rax) (%%% (rax,0,r15)) *)
  0x4d; 0x89; 0xcc;        (* MOV (% r12) (% r9) *)
  0x48; 0x8d; 0x6d; 0x80;  (* LEA (% rbp) (%% (rbp,18446744073709551488)) *)
  0x48; 0x39; 0xe5;        (* CMP (% rbp) (% rsp) *)
  0x0f; 0x83; 0xdb; 0xfc; 0xff; 0xff;
                           (* JAE (Imm32 (word 4294966491)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x05; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,1280))) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x48; 0x8d; 0xa4; 0x24; 0x80; 0x04; 0x00; 0x00;
                           (* LEA (% rsp) (%% (rsp,1152)) *)
  0x48; 0x03; 0x07;        (* ADD (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x03; 0x5f; 0x08;  (* ADD (% rbx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x03; 0x4f; 0x10;  (* ADD (% rcx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x03; 0x57; 0x18;  (* ADD (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x03; 0x47; 0x20;  (* ADD (% r8) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x03; 0x4f; 0x28;  (* ADD (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x48; 0x8d; 0xb6; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,256)) *)
  0x4c; 0x03; 0x57; 0x30;  (* ADD (% r10) (Memop Quadword (%% (rdi,48))) *)
  0x49; 0x89; 0xf4;        (* MOV (% r12) (% rsi) *)
  0x4c; 0x03; 0x5f; 0x38;  (* ADD (% r11) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x3b; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* CMP (% rsi) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x4c; 0x0f; 0x44; 0xe4;  (* CMOVE (% r12) (% rsp) *)
  0x48; 0x89; 0x5f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rbx) *)
  0x48; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rcx) *)
  0x48; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rdx) *)
  0x4c; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r9) *)
  0x4c; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r11) *)
  0x0f; 0x86; 0xce; 0xe9; 0xff; 0xff;
                           (* JBE (Imm32 (word 4294961614)) *)
  0x48; 0x8d; 0x2c; 0x24;  (* LEA (% rbp) (%% (rsp,0)) *)
  0x48; 0x8b; 0xb5; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rbp,152))) *)
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
let sha512_avx2_k512 = last sha512_avx2_data;;
let SHA512_AVX2_EXEC = X86_MK_EXEC_RULE sha512_avx2_mc;;

(* ------------------------------------------------------------------------- *)
(* The K512 table in memory: the 80 round constants, each pair twice so one  *)
(* 256-bit load adds it to both blocks' schedule lanes, then the byte-swap   *)
(* mask. The inner loop ends on the zero top byte of the mask.               *)
(* ------------------------------------------------------------------------- *)

let SHA512_READ_BYTE7 = prove
 (`!x s d. read (memory :> bytes64 x) s = d
           ==> read (memory :> bytes8 (word_add x (word 7))) s = word_subword d (56,8)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]);;

let SHA512_AVX2_K512_FACTS =
  let kb = Array.of_list (map (fun t -> Num.int_of_num(dest_numeral(rand t)))
                              (dest_list(rand(concl sha512_avx2_k512)))) in
  let word_at n off =
    let v = ref (Num.num_of_int 0) in
    for i = n-1 downto 0 do
      v := Num.add_num (Num.mult_num !v (Num.num_of_int 256)) (Num.num_of_int kb.(off+i))
    done; !v in
  let addr off = mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` `k:num` (mk_small_numeral off)) in
  let fact comp n off =
    mk_eq(list_mk_icomb "read" [list_mk_icomb ":>" [`memory`; mk_comb(comp, addr off)]; `s:x86state`],
          mk_comb(mk_const("word",[mk_finty(Num.num_of_int(8*n)),`:N`]), mk_numeral(word_at n off))) in
  let facts = map (fun i -> fact `bytes256` 32 (32*i)) (0--40) @
              map (fun off -> fact `bytes8` 1 off) [519; 775; 1031; 1287] in
  let offset th = try Num.int_of_num(dest_numeral(rand(rand(rand(rand(rand(rator(lhand(concl th))))))))) with _ -> -1 in
  let byte th =
    CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
                RAND_CONV(GEN_REWRITE_CONV I [GSYM ADD_ASSOC] THENC RAND_CONV NUM_ADD_CONV))) THENC
              RAND_CONV WORD_REDUCE_CONV) (MATCH_MP SHA512_READ_BYTE7 th) in
  let th = prove
   (mk_forall(`s:x86state`, mk_forall(`k:num`,
      mk_imp(`bytes_loaded s (word (k + 0)) sha512_avx2_k512`, list_mk_conj facts))),
    REPEAT GEN_TAC THEN REWRITE_TAC[sha512_avx2_k512] THEN
    CONV_TAC(LAND_CONV DATA64_CONV) THEN
    DISCH_THEN(fun th ->
      let ths = CONJUNCTS th in
      MAP_EVERY ASSUME_TAC
        (ths @ map byte (filter (fun th -> mem (offset th) [512; 768; 1024; 1280]) ths))) THEN
    REWRITE_TAC[CONJUNCT1 READ_MEMORY_BYTESIZED_SPLIT;
                CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT); GSYM WORD_ADD] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV) in
  let th = SPECL [`s:x86state`; `val(kt:int64)`] th in
  GEN_ALL(REWRITE_RULE[ADD_CLAUSES; WORD_VAL; WORD_ADD; WORD_ADD_0] th);;

(* The function's lea of the table, at pc + 0x8f. *)
let SHA512_AVX2_LEA_K = prove
 (`!pc k. riprel32_within_bounds (k + 128) (pc + 150)
          ==> word (val (word (pc + 150):int64) +
                    val (word_sx (iword (&k - (&pc + &22)):int32):int64)):int64 =
              word_add (word k) (word 128)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  SUBGOAL_THEN `&k - (&pc + &22):int = &(k + 128) - (&pc + &150)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`; `150`; `0`; `k + 128`] RIP_REL_ADDR_FOLD) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The code's forms of the FIPS 180-4 functions, and one round and one       *)
(* message schedule word in the code's forms.                                *)
(* ------------------------------------------------------------------------- *)

let SHA512_SIGMA_CODE = prove
 (`(!x:int64. word_xor (word_xor (word_xor (word_xor (word_ushr x 7) (word_ushr x 1)) (word_shl x 56))
                                 (word_ushr (word_ushr x 1) 7)) (word_shl (word_shl x 56) 7) =
              sha512_msg_sigma_0 x) /\
   (!x:int64. word_xor (word_xor (word_xor (word_xor (word_ushr x 6) (word_shl x 3)) (word_ushr x 19))
                                 (word_shl (word_shl x 3) 42)) (word_ushr (word_ushr x 19) 42) =
              sha512_msg_sigma_1 x)`,
  REWRITE_TAC[sha512_msg_sigma_0; sha512_msg_sigma_1] THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;
let SHA512_CH_CODE = prove
 (`!e f g:int64. word_add (word_and f e) (word_and (word_not e) g) = sha512_choose e f g`,
  REWRITE_TAC[sha512_choose] THEN CONV_TAC WORD_BLAST);;
let SHA512_MAJ_CODE = prove
 (`!a b c:int64. word_xor (word_and (word_xor b c) (word_xor a b)) b = sha512_maj a b c`,
  REWRITE_TAC[sha512_maj] THEN CONV_TAC WORD_BLAST);;
let SHA512_SIGMA0_CODE = prove
 (`!a:int64. word_xor (word_xor (word_ror a 34) (word_ror a 39)) (word_ror a 28) = sha512_hash_sigma_0 a`,
  REWRITE_TAC[sha512_hash_sigma_0] THEN CONV_TAC WORD_BLAST);;
let SHA512_SIGMA1_CODE = prove
 (`!e:int64. word_xor (word_xor (word_ror e 41) (word_ror e 18)) (word_ror e 14) = sha512_hash_sigma_1 e`,
  REWRITE_TAC[sha512_hash_sigma_1] THEN CONV_TAC WORD_BLAST);;

let SHA512_XOR_JOIN = prove
 (`(!(a:int128) (b:int128) (c:int128) (d:int128).
      word_xor (word_join a b:int256) (word_join c d) = word_join (word_xor a c) (word_xor b d)) /\
   (!(a:int64) (b:int64) (c:int64) (d:int64).
      word_xor (word_join a b:int128) (word_join c d) = word_join (word_xor a c) (word_xor b d))`,
  CONJ_TAC THEN CONV_TAC WORD_BLAST);;
let SHA512_MSG_SCHEDULE_STEP = prove
 (`!m t. word_add (sha512_msg_sigma_1 (sha512_msg_schedule m (t + 14)))
                  (word_add (sha512_msg_sigma_0 (sha512_msg_schedule m (t + 1)))
                            (word_add (sha512_msg_schedule m (t + 9)) (sha512_msg_schedule m t))) =
         sha512_msg_schedule m (t + 16)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [sha512_msg_schedule] THEN
  REWRITE_TAC[ARITH_RULE `~(t + 16 < 16) /\ (t + 16) - 2 = t + 14 /\ (t + 16) - 7 = t + 9 /\
                          (t + 16) - 15 = t + 1 /\ (t + 16) - 16 = t`] THEN
  CONV_TAC WORD_RULE);;
let SHA512_ROUND_STEP = prove
 (`!m h t.
     let S = sha512_compress_rounds m h t and S' = sha512_compress_rounds m h (t + 1) in
     let T1 = word_add (word_add (word_add (word_add (EL 7 S)
                (word_add (sha512_msg_schedule m t) (EL t sha512_constants)))
                (word_and (EL 5 S) (EL 4 S))) (word_and (word_not (EL 4 S)) (EL 6 S)))
                (word_xor (word_xor (word_ror (EL 4 S) 41) (word_ror (EL 4 S) 18)) (word_ror (EL 4 S) 14)) in
     word_add (EL 3 S) T1 = EL 4 S' /\
     word_add T1 (word_xor (word_and (word_xor (EL 1 S) (EL 2 S)) (word_xor (EL 0 S) (EL 1 S))) (EL 1 S)) =
     word_sub (EL 0 S') (word_xor (word_xor (word_ror (EL 0 S) 34) (word_ror (EL 0 S) 39)) (word_ror (EL 0 S) 28)) /\
     EL 0 S = EL 1 S' /\ EL 1 S = EL 2 S' /\ EL 2 S = EL 3 S' /\
     EL 4 S = EL 5 S' /\ EL 5 S = EL 6 S' /\ EL 6 S = EL 7 S'`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha512_compress_rounds; sha512_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[GSYM SHA512_CH_CODE; GSYM SHA512_MAJ_CODE; GSYM SHA512_SIGMA0_CODE;
              GSYM SHA512_SIGMA1_CODE] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* YMM values as four 64-bit lanes.                                          *)
(* ------------------------------------------------------------------------- *)

let SHA512_BYTES_REVERSE = prove
 (`!x:int64.
     word_join
      (word_join (word_join (word_subword (word_bytereverse x) (0,8):byte)
                            (word_subword (word_bytereverse x) (8,8):byte):int16)
                 (word_join (word_subword (word_bytereverse x) (16,8):byte)
                            (word_subword (word_bytereverse x) (24,8):byte):int16):int32)
      (word_join (word_join (word_subword (word_bytereverse x) (32,8):byte)
                            (word_subword (word_bytereverse x) (40,8):byte):int16)
                 (word_join (word_subword (word_bytereverse x) (48,8):byte)
                            (word_subword (word_bytereverse x) (56,8):byte):int16):int32) = x`,
  CONV_TAC WORD_BLAST);;

let SHA512_VPALIGNR_LANE = prove
 (`!(a1:int64) (a0:int64) (b1:int64) (b0:int64).
     word_subword (word_ushr (word_join (word_join a1 a0:int128)
                                        (word_join b1 b0:int128):256 word) 64) (0,128):int128 =
     word_join a0 b1`,
  CONV_TAC WORD_BLAST);;

let SHA512_SUBWORD_RULES = prove
 (`(!x:int128. word_subword x (0,128) = x) /\
   (!x:int256. word_subword (word_subword x (0,128):int128) (0,64):int64 = word_subword x (0,64)) /\
   (!x:int256. word_subword (word_subword x (0,128):int128) (64,64):int64 = word_subword x (64,64)) /\
   (!x:int256. word_subword (word_subword x (128,128):int128) (0,64):int64 = word_subword x (128,64)) /\
   (!x:int256. word_subword (word_subword x (128,128):int128) (64,64):int64 = word_subword x (192,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN
  SIMP_TAC[WORD_SUBWORD_TRIVIAL; WORD_SUBWORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
           DIMINDEX_256; LE_REFL; ARITH] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]);;

let SHA512_SIMD_CONV =
  let base = TOP_DEPTH_CONV(GEN_REWRITE_CONV I [SHA512_SUBWORD_RULES; SHA512_XOR_JOIN] ORELSEC
                            WORD_SIMPLE_SUBWORD_CONV) THENC
             DEPTH_CONV WORD_NUM_RED_CONV in
  base THENC REWRITE_CONV[SHA512_BYTES_REVERSE; SHA512_VPALIGNR_LANE] THENC base;;

(* A 256-bit store as four 64-bit facts, which the rounds read. *)
let SHA512_SPLIT256 =
  let c256 = el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)
  and c128 = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT) in
  let norm = CONV_RULE(BINOP2_CONV (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                                   SHA512_SIMD_CONV) in
  fun th ->
    let th1,th2 = CONJ_PAIR(GEN_REWRITE_RULE I [c256] th) in
    let split th = let a,b = CONJ_PAIR(GEN_REWRITE_RULE I [c128] (norm th)) in
                   [norm a; norm b] in
    split th1 @ split th2;;

(* ------------------------------------------------------------------------- *)
(* Stepping: after each instruction, simplify the new state's facts.         *)
(* ------------------------------------------------------------------------- *)

let SHA512_SCALAR_RULE =
  REWRITE_RULE[MULT_CLAUSES; WORD_VAL; WORD_ADD_0;
               WORD_RULE `word_add (word_sub x y) y:int64 = x`];;

let sha512_x86state = `:x86state`;;

(* Facts already in normal form, by component and value, so a step only
   simplifies what it wrote. *)
let sha512_tidy_seen : (term * term,unit) Hashtbl.t = Hashtbl.create 4096;;

let SHA512_TIDY_TAC folds =
  let fold_conv = REWRITE_CONV folds in
  let simd_conv = SHA512_SIMD_CONV THENC fold_conv in
  let ty256 = `:int256` and kt = `kt:int64`
  and mem256 = `read (memory :> bytes256 a) s = x` in
  let is256 t = try type_of(rand t) = ty256 with _ -> false in
  let ismem256 t = can (term_match [] mem256) t in
  fun n ->
  let sv = mk_var("s"^string_of_int n,sha512_x86state) in
  let key c = (try rator(lhand c) with Failure _ -> lhand c), rand c in
  let seen th = let c = concl th in is_eq c && Hashtbl.mem sha512_tidy_seen (key c) in
  let mark th = (let c = concl th in if is_eq c then Hashtbl.replace sha512_tidy_seen (key c) ()); th in
  fun (asl,w) ->
    let ths = map snd (filter (fun (_,th) -> free_in sv (concl th) && not (seen th)) asl) in
    let tidy th =
      let th = SHA512_SCALAR_RULE th in
      let c = concl th in
      if is_eq c && is256 c then
        let th = CONV_RULE(RAND_CONV simd_conv) th in
        if ismem256 c && not (free_in kt (lhand c))
        then map (CONV_RULE(RAND_CONV fold_conv)) (SHA512_SPLIT256 th) else [th]
      else [th] in
    let ths' = map mark (List.concat (map tidy ths)) in
    (MAP_EVERY (fun th -> UNDISCH_THEN (concl th) (K ALL_TAC)) ths THEN
     MAP_EVERY ASSUME_TAC ths') (asl,w);;

(* The rewrites that fold one block's message words, schedule lanes, and
   round constants into the spec's terms. *)
let SHA512_K_EL =
  Array.init 80 (fun t ->
    (REWRITE_CONV[sha512_constants] THENC EL_CONV)
      (mk_comb(mk_comb(`EL:num->int64 list->int64`, mk_small_numeral t), `sha512_constants`)));;

let sha512_schedule_folds m =
  let small j =
    SYM(CONV_RULE(RAND_CONV(RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC REWRITE_CONV[]))
          (REWR_CONV sha512_msg_schedule (mk_comb(mk_comb(`sha512_msg_schedule`, m), mk_small_numeral j)))) in
  let step t =
    CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (SPECL [m; mk_small_numeral t] SHA512_MSG_SCHEDULE_STEP) in
  map small (0--15) @ map step (0--63);;

let sha512_round_rules m h t =
  let th = SPECL [m; h; mk_small_numeral t] SHA512_ROUND_STEP in
  let th = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV NUM_ADD_CONV THENC
                     REWRITE_CONV[SHA512_K_EL.(t)]) th in
  let ths = CONJUNCTS th in
  (fst(chop_list 2 ths), snd(chop_list 2 ths));;

(* The block and round being stepped. A round ends when it copies e into R12
   for the next; its two new values then fold to the spec's next state, and
   the six it keeps are renamed to that state's. *)
let sha512_cur_block = ref (`m:int64 list`, `h:int64 list`) and sha512_cur_round = ref 0;;

let SHA512_ROUND_TAC =
  let pat = `read R12 s = EL 4 (sha512_compress_rounds m h t)`
  and kwpat = `word_add (sha512_msg_schedule m t) k`
  and readpat = `read (memory :> bytes64 a) s`
  and s_tm = `s:x86state` and m_tm = `m:int64 list` and h_tm = `h:int64 list` and t_tm = `t:num` in
  fun n (asl,w) ->
  let m,h = !sha512_cur_block and t = !sha512_cur_round in
  let sv = mk_var("s"^string_of_int n,sha512_x86state) in
  let trig = subst [sv,s_tm; m,m_tm; h,h_tm; mk_small_numeral t,t_tm] pat in
  if t < 80 && exists (fun (_,th) -> concl th = trig) asl then
    let folds,shifts = sha512_round_rules m h t in
    let kw = subst [m,m_tm; mk_small_numeral t,t_tm] kwpat in
    let used th = can (term_match [m] (mk_eq(readpat, kw))) (concl th) in
    sha512_cur_round := t + 1;
    (RULE_ASSUM_TAC(fun th -> if free_in sv (concl th)
                              then REWRITE_RULE shifts (REWRITE_RULE folds th) else th) THEN
     REPEAT(FIRST_X_ASSUM(K ALL_TAC o check used))) (asl,w)
  else ALL_TAC (asl,w);;

(* Stack addresses as numbers: the frame never wraps, so a compare of two of
   them is a compare of their offsets. *)
let SHA512_VAL_STK = prove
 (`(!stk c. val (stk:int64) + 1344 <= 2 EXP 64 /\ c < 1344
            ==> val (word_add stk (word c)) = val stk + c) /\
   (!stk. 128 <= val (stk:int64)
          ==> val (word_add stk (word 18446744073709551520)) = val stk - 96)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THENL
   [SUBGOAL_THEN `c MOD 18446744073709551616 = c` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
    MP_TAC(ISPEC `stk:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC]);;

(* Decides a branch on the stack addresses, from the hypotheses on stk. *)
let SHA512_COND_TAC =
  let pat = `read RIP s = if p then x else y`
  and stk = `stk:int64` in
  fun (asl,w) ->
    match filter (fun (_,th) -> can (term_match [] pat) (concl th)) asl with
      [] -> ALL_TAC (asl,w)
    | (_,th)::_ ->
        let p = lhand(rator(rand(concl th))) in
        let hyps = filter (fun (_,t) -> let c = concl t in
                             free_in stk c && not (exists (fun v -> type_of v = sha512_x86state) (frees c))) asl in
        let decide = ASM_SIMP_TAC[SHA512_VAL_STK; ARITH] THEN ASM_ARITH_TAC in
        let th' = try EQT_INTRO(TAC_PROOF((hyps,p),decide))
                  with Failure _ -> EQF_INTRO(TAC_PROOF((hyps,mk_neg p),decide)) in
        RULE_ASSUM_TAC(fun t -> if concl t = concl th then REWRITE_RULE[th'] t else t) (asl,w);;

let SHA512_STEPS_TAC folds =
  let tidy = SHA512_TIDY_TAC folds in
  fun ns -> MAP_EVERY (fun n -> X86_STEPS_TAC SHA512_AVX2_EXEC [n] THEN tidy n THEN
                                SHA512_ROUND_TAC n THEN SHA512_COND_TAC) ns;;

(* Steps from state n until RIP is pc + target, leaving the last state's
   number in sha512_last_state. *)
let sha512_last_state = ref 0;;

let SHA512_RUN_TO_TAC folds =
  let steps = SHA512_STEPS_TAC folds in
  fun target ->
    let rip = mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral target)) in
    let rec run n (asl,w) =
      (steps [n] THEN
       (fun (asl,w) ->
          let sv = mk_var("s"^string_of_int n,sha512_x86state) in
          let fact = mk_eq(list_mk_icomb "read" [`RIP`; sv], rip) in
          if exists (fun (_,th) -> concl th = fact) asl then (sha512_last_state := n; ALL_TAC (asl,w))
          else run (n+1) (asl,w))) (asl,w) in
    run;;

(* Sets which block's rounds the stepping folds, when the tactic runs. *)
let SHA512_START_TAC m h : tactic =
  fun g -> sha512_cur_block := (m,h); sha512_cur_round := 0;
           Hashtbl.reset sha512_tidy_seen; ALL_TAC g;;

(* ------------------------------------------------------------------------- *)
(* Block A: from the loop head to the end of the first block's rounds.       *)
(* ------------------------------------------------------------------------- *)

(* The stack base stk sits 32 bytes below the 2048-aligned frame, so every
   stack address is stk plus a positive offset; the loop's frame pointer F
   is stk + 1184, and F + 128, 136, 144, and 152 hold the context pointer,
   the input pointer, its end, and the caller's stack pointer. *)
let sha512_at base off =
  if off = 0 then base
  else mk_comb(mk_comb(`word_add:int64->int64->int64`, base),
               mk_comb(`word:num->int64`, mk_small_numeral off));;

let sha512_read64 base off v =
  mk_eq(subst [sha512_at base off,`a:int64`] `read (memory :> bytes64 a) (s:x86state)`, v);;

(* Where block A's rounds leave block B's message word plus round constant
   for round t, which block B's rounds read back eight a pass. *)
let sha512_kw_offset t =
  1200 - 128 * (t / 8) + 32 * ((t mod 8) / 2) + 8 * (t mod 2);;

let sha512_kw_facts m =
  list_mk_conj(map (fun t ->
    sha512_read64 `stk:int64` (sha512_kw_offset t)
      (subst [m,`m:int64 list`; mk_small_numeral t,`t:num`]
         `word_add (sha512_msg_schedule m t) (EL t sha512_constants)`)) (0--79));;

let sha512_frame_facts =
  list_mk_conj(map2 (fun off v -> sha512_read64 `stk:int64` off v)
    [1312; 1320; 1328; 1336] [`ctxp:int64`; `inp:int64`; `endp:int64`; `rsp0:int64`]);;

let sha512_regs_at m h t =
  let el j = subst [mk_small_numeral j,`j:num`; m,`m:int64 list`; h,`h:int64 list`;
                    mk_small_numeral t,`t:num`]
               `EL j (sha512_compress_rounds m h t)` in
  map el (0--7);;

let sha512_reg_facts regs vals =
  list_mk_conj(map2 (fun r v -> mk_eq(list_mk_icomb "read" [r; `s:x86state`], v)) regs vals);;

let sha512_bswap_join m i =
  subst [mk_small_numeral i,`i:num`; mk_small_numeral (i+1),`j:num`; m,`m:int64 list`]
    `word_join (word_bytereverse (EL j m):int64) (word_bytereverse (EL i m):int64):int128`;;

let sha512_data_facts base m =
  list_mk_conj(map (fun j ->
    mk_eq(subst [sha512_at base (16*j),`a:int64`] `read (memory :> bytes128 a) (s:x86state)`,
          sha512_bswap_join m (2*j))) (0--7));;

let sha512_mk_goal hyps pre post frame =
  let tm = mk_imp(hyps, list_mk_icomb "ensures" [`x86`; mk_abs(`s:x86state`,pre);
                                                 mk_abs(`s:x86state`,post); frame]) in
  list_mk_forall(frees tm, tm);;

let sha512_scalar_regs = [`RAX`; `RBX`; `RCX`; `RDX`; `R8`; `R9`; `R10`; `R11`];;

let sha512_frame =
  `MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; RBP; R8; R9; R10; R11; R12; R13; R14; R15] ,,
   MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(stk,1344)]`;;

(* At the end of a block's rounds, the a register still lacks Sigma0 of the
   previous a, which R14 holds. *)
let sha512_rounds_end_facts m h =
  let r = sha512_regs_at m h 80 in
  let sig0 = mk_comb(`sha512_hash_sigma_0`, el 1 r) in
  list_mk_conj[sha512_reg_facts sha512_scalar_regs
                 (list_mk_icomb "word_sub" [el 0 r; sig0] :: tl r);
               mk_eq(`read R14 (s:x86state)`, sig0)];;

let sha512_k512_hyps =
  `nonoverlapping (word pc:int64,0x16dd) (stk:int64,1344) /\
   nonoverlapping (stk,1344) (kt:int64,1344) /\ aligned 32 stk /\ aligned 32 kt /\
   riprel32_within_bounds (k512 + 128) (pc + 150) /\ word k512 = kt`;;

let SHA512_AVX2_BLOCK_A_GOAL = sha512_mk_goal
  (mk_conj(sha512_k512_hyps, `nonoverlapping (stk:int64,1344) (dA:int64,128)`))
  (list_mk_conj[
    `bytes_loaded s (word pc) (sha512_avx2_mc pc k512) /\
     read RIP s = word(pc + 0x80) /\ read RSP s = word_add stk (word 1184) /\
     read RSI s = word_add dA (word 128) /\ read R12 s = bB /\
     bytes_loaded s kt sha512_avx2_k512`;
    sha512_frame_facts;
    sha512_reg_facts sha512_scalar_regs (sha512_regs_at `mA:int64 list` `hA:int64 list` 0);
    sha512_data_facts `dA:int64` `mA:int64 list`;
    sha512_data_facts `bB:int64` `mB:int64 list`])
  (list_mk_conj[
    `read RIP s = word(pc + 0x12b2) /\ read RSP s = word_add stk (word 32) /\
     read RSI s = word_add dA (word 128)`;
    sha512_frame_facts;
    sha512_rounds_end_facts `mA:int64 list` `hA:int64 list`;
    sha512_kw_facts `mB:int64 list`])
  sha512_frame;;

let SHA512_FINISH_TAC =
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC(GSYM SHA512_SIGMA0_CODE :: Array.to_list SHA512_K_EL) THEN
  ASM_REWRITE_TAC[];;

let SHA512_AVX2_BLOCK_A = prove
 (SHA512_AVX2_BLOCK_A_GOAL,
  let folds = SHA512_SIGMA_CODE :: sha512_schedule_folds `mA:int64 list` @
              sha512_schedule_folds `mB:int64 list` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[fst SHA512_AVX2_EXEC; SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SHA512_AVX2_K512_FACTS) THEN
  SHA512_START_TAC `mA:int64 list` `hA:int64 list` THEN
  SHA512_STEPS_TAC folds (1--4) THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `read RBP s = x`) o concl)) THEN
  ASM_SIMP_TAC[SHA512_AVX2_LEA_K] THEN DISCH_TAC THEN
  (* The last load of the message; block B's may lie in the frame. *)
  SHA512_STEPS_TAC folds (5--24) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (can (term_match [] `read (memory :> bytes128 a) s = x`) o concl))) THEN
  SHA512_RUN_TO_TAC folds 0x12b2 25 THEN
  SHA512_FINISH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Block B: its rounds, reading back the message words block A stored.       *)
(* ------------------------------------------------------------------------- *)

(* The rounds loop ends on an unsigned compare of two stack addresses, which
   is the compare of their offsets only while the frame does not wrap. *)
let sha512_stk_hyps =
  `nonoverlapping (word pc:int64,0x16dd) (stk:int64,1344) /\
   128 <= val (stk:int64) /\ val stk + 1344 <= 2 EXP 64`;;

let SHA512_AVX2_BLOCK_B_GOAL = sha512_mk_goal
  sha512_stk_hyps
  (list_mk_conj[
    `bytes_loaded s (word pc) (sha512_avx2_mc pc k512) /\
     read RIP s = word(pc + 0x1310) /\ read RSP s = word_add stk (word 32) /\
     read RBP s = word_add stk (word 1184) /\ read RSI s = rsi0`;
    sha512_frame_facts;
    sha512_reg_facts sha512_scalar_regs (sha512_regs_at `mB:int64 list` `hB:int64 list` 0);
    sha512_kw_facts `mB:int64 list`])
  (list_mk_conj[
    `read RIP s = word(pc + 0x1645) /\ read RSP s = word_add stk (word 32) /\
     read RSI s = rsi0`;
    sha512_frame_facts;
    sha512_rounds_end_facts `mB:int64 list` `hB:int64 list`])
  sha512_frame;;

let SHA512_AVX2_BLOCK_B = prove
 (SHA512_AVX2_BLOCK_B_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[fst SHA512_AVX2_EXEC; SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE(Array.to_list SHA512_K_EL)) THEN
  SHA512_START_TAC `mB:int64 list` `hB:int64 list` THEN
  SHA512_RUN_TO_TAC [SHA512_SIGMA_CODE] 0x1645 1 THEN
  SHA512_FINISH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The message in memory, and the blocks' results.                           *)
(* ------------------------------------------------------------------------- *)

(* The input as one region, with its words as the blocks' byte-swapped
   message words: stepping keeps a fact about the whole region, and this
   gives any block's words from it. *)
let sha512_input_rel =
  `!b j. b < n /\ j < 16
         ==> word(bigdigit D (16 * b + j)):int64 = word_bytereverse (EL j ((m:num->int64 list) b))`;;

let SHA512_BLOCK_DATA =
  let base = `word_add (inp:int64) (word (128 * b))` in
  prove
  (list_mk_forall([`s:x86state`; `inp:int64`; `n:num`; `D:num`; `m:num->int64 list`; `b:num`],
     mk_imp(list_mk_conj[`read (memory :> bytes(inp,128 * n)) s = D`; sha512_input_rel; `b < n`],
            sha512_data_facts base `(m:num->int64 list) b`)),
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN
    `!j. j < 16 ==> read (memory :> bytes64 (word_add inp (word (128 * b + 8 * j)))) s =
                    word_bytereverse (EL j ((m:num->int64 list) b))`
    (fun th -> MP_TAC(end_itlist CONJ
       (map (fun j -> REWRITE_RULE[ADD_CLAUSES] (CONV_RULE NUM_REDUCE_CONV
                        (SPEC (mk_small_numeral j) th))) (0--15)))) THENL
    [REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     MP_TAC(ISPECL [`16 * n`; `inp:int64`; `s:x86state`; `16 * b + j`] BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE `8 * 16 * n = 128 * n`] THEN
     ASM_SIMP_TAC[ARITH_RULE `b < n /\ j < 16 ==> 16 * b + j < 16 * n`] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[WORD_VAL; ARITH_RULE `8 * (16 * b + j) = 128 * b + 8 * j`];
     ALL_TAC] THEN
   REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)] THEN
   REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
   CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN SIMP_TAC[]);;

(* Any 128 bytes are some block's byte-swapped message words: block B's
   lane reads the frame when only one block is left. *)
let WORD_BYTEREVERSE_BYTEREVERSE_64 = prove
 (`!x:int64. word_bytereverse (word_bytereverse x) = x`,
  CONV_TAC WORD_BLAST);;

let SHA512_ANY_DATA =
  let w j = subst [sha512_at `a:int64` (8*j),`x:int64`]
              `word_bytereverse (read (memory :> bytes64 x) (s:x86state))` in
  let witness = mk_list(map w (0--15), `:int64`) in
  prove
  (mk_forall(`s:x86state`, mk_forall(`a:int64`,
     mk_exists(`mm:int64 list`, sha512_data_facts `a:int64` `mm:int64 list`))),
   REPEAT GEN_TAC THEN EXISTS_TAC witness THEN
   CONV_TAC(DEPTH_CONV EL_CONV) THEN
   REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE_64;
               CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)] THEN
   REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
   CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]);;

let SHA512_BLOCK_EL = prove
 (`!m h j. j < 8
           ==> EL j (sha512_block m h) =
               word_add (EL j (sha512_compress_rounds m h 80)) (EL j h)`,
  REWRITE_TAC[sha512_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GEN_TAC THEN GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* The input pointer and its end never wrap. *)
let SHA512_VAL_INP = prove
 (`!inp:int64 n c. val inp + 128 * (n + 1) < 2 EXP 64 /\ c <= 128 * (n + 1)
                   ==> val (word_add inp (word c)) = val inp + c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `c MOD 2 EXP 64 = c` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loop over pairs of blocks.                                            *)
(* ------------------------------------------------------------------------- *)

let sha512_hblocks k =
  subst [k,`k:num`] `sha512_hash_blocks (m:num->int64 list) (h:int64 list) k`;;

let sha512_els v =
  map (fun j -> mk_comb(mk_comb(`EL:num->int64 list->int64`, mk_small_numeral j), v)) (0--7);;

let sha512_ctx_facts v =
  list_mk_conj(map2 (fun j e -> sha512_read64 `ctxp:int64` (8*j) e) (0--7) (sha512_els v));;

let sha512_endp = `word_add inp (word (128 * n)):int64`;;

(* At the loop head with 2 * i blocks done. *)
let sha512_loop_inv =
  let hb = sha512_hblocks `2 * i` in
  list_mk_conj[
   `bytes_loaded s (word pc) (sha512_avx2_mc pc k512) /\
    read RIP s = word(pc + 0x80) /\ read RSP s = word_add stk (word 1184) /\
    read RSI s = word_add (word_add inp (word (256 * i))) (word 128) /\
    read R12 s = (if 2 * i + 1 < n then word_add inp (word (256 * i + 128))
                  else word_add stk (word 1184)) /\
    read (memory :> bytes(kt,1344)) s = kn /\
    read (memory :> bytes(inp,128 * n)) s = D`;
   subst [sha512_endp,`endp:int64`] sha512_frame_facts;
   sha512_reg_facts sha512_scalar_regs (sha512_els hb);
   sha512_ctx_facts hb];;

let sha512_loop_post =
  list_mk_conj[
   `read RIP s = word(pc + 0x16b6) /\ read RBP s = word_add stk (word 1184) /\
    read (memory :> bytes64 (word_add stk (word 1336))) s = rsp0`;
   sha512_ctx_facts (sha512_hblocks `n:num`)];;

let sha512_loop_frame =
  list_mk_icomb ",," [sha512_frame; `MAYCHANGE [memory :> bytes(ctxp:int64,64)]`];;

let sha512_loop_hyps =
  list_mk_conj[sha512_k512_hyps;
   `128 <= val (stk:int64) /\ val stk + 1344 <= 2 EXP 64`;
   `nonoverlapping (stk:int64,1344) (inp:int64,128 * n) /\
    nonoverlapping (stk,1344) (ctxp:int64,64) /\
    nonoverlapping (word pc:int64,0x16dd) (ctxp,64) /\
    nonoverlapping (ctxp,64) (kt:int64,1344) /\
    nonoverlapping (ctxp,64) (inp,128 * n) /\
    val inp + 128 * (n + 1) < 2 EXP 64 /\
    num_of_bytelist sha512_avx2_k512 = kn`;
   sha512_input_rel];;

let sha512_loop_ensures inv =
  list_mk_icomb "ensures" [`x86`; mk_abs(`s:x86state`, inv);
                           mk_abs(`s:x86state`, sha512_loop_post); sha512_loop_frame];;

let SHA512_AVX2_LOOP_GOAL =
  let tm = mk_imp(sha512_loop_hyps,
                  mk_forall(`i:num`, mk_imp(`2 * i < n`, sha512_loop_ensures sha512_loop_inv))) in
  list_mk_forall(frees tm, tm);;

let sha512_inst th l =
  INST (map (fun (v,n) -> v, mk_var(n, type_of v)) l) (SPEC_ALL th);;

let SHA512_RSI_END = prove
 (`!inp:int64 n i.
     val inp + 128 * (n + 1) < 2 EXP 64 /\ 2 * i < n
     ==> (val (word_sub (word_add (word_add inp (word (256 * i))) (word 128))
                        (word_add inp (word (128 * n)))) = 0 <=> 2 * i + 1 = n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM VAL_EQ] THEN
  MP_TAC(SPECL [`inp:int64`; `n:num`; `256 * i + 128`] SHA512_VAL_INP) THEN
  MP_TAC(SPECL [`inp:int64`; `n:num`; `128 * n`] SHA512_VAL_INP) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN ARITH_TAC);;

let SHA512_K512_LOADED = prove
 (`!s kt. bytes_loaded s kt sha512_avx2_k512 <=>
          read (memory :> bytes(kt,1344)) s = num_of_bytelist sha512_avx2_k512`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV) (AP_TERM `LENGTH:byte list->num` sha512_avx2_k512)]);;

let SHA512_RSI_NEXT = prove
 (`!inp:int64 n i.
     val inp + 128 * (n + 1) < 2 EXP 64 /\ 2 * i + 2 <= n
     ==> (val (word_add (word_add inp (word (256 * i))) (word 384)) <
          val (word_add inp (word (128 * n))) <=> 2 * i + 3 < n) /\
         (val (word_sub (word_add (word_add inp (word (256 * i))) (word 384))
                        (word_add inp (word (128 * n)))) = 0 <=> 2 * i + 3 = n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM VAL_EQ] THEN
  MP_TAC(SPECL [`inp:int64`; `n:num`; `256 * i + 384`] SHA512_VAL_INP) THEN
  MP_TAC(SPECL [`inp:int64`; `n:num`; `128 * n`] SHA512_VAL_INP) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN ARITH_TAC);;

(* Arithmetic on the loop counters alone, away from the state's facts. *)
let SHA512_ARITH_TAC =
  let num_ty = `:num` in
  W(fun (asl,w) ->
    let hs = filter (fun (_,th) -> let c = concl th in
               let fv = frees c in
               fv <> [] && not (is_forall c) && forall (fun v -> type_of v = num_ty) fv) asl in
    MAP_EVERY (fun (_,th) -> MP_TAC th) hs THEN ARITH_TAC);;

(* Rewriting a fact leaves the rewrite's hypotheses on it, which can clash
   with the stepper's own variable names (it names an instruction's length
   n); this restates every assumption as itself. *)
let SHA512_LAUNDER_TAC =
  POP_ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> ASSUME_TAC (ASSUME (concl th))) (rev ths));;

(* Folds a block's feed-forward sums to the next hash state. *)
let SHA512_FOLD_BLOCK_TAC k =
  let k1 = mk_binop `(+):num->num->num` k `1` in
  let eq j = subst [mk_small_numeral j,`j:num`; k,`k:num`; k1,`k1:num`]
   `word_add (EL j (sha512_compress_rounds ((m:num->int64 list) k) (sha512_hash_blocks m h k) 80))
             (EL j (sha512_hash_blocks m h k)) = EL j (sha512_hash_blocks m h k1)` in
  SUBGOAL_THEN (list_mk_conj (map eq (0--7))) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[sha512_hash_blocks] THEN SIMP_TAC[SHA512_BLOCK_EL; ARITH]; ALL_TAC];;

let SHA512_PRE_TAC =
  REWRITE_TAC[CONJUNCT1 sha512_compress_rounds; SHA512_K512_LOADED] THEN ASM_REWRITE_TAC[];;

(* Block A's rounds and the context update after them, from the loop head
   with block B's message at bB, to the branch on whether B is there. *)
let SHA512_BLOCK_A_TAC bB mB =
  let thA = sha512_inst SHA512_AVX2_BLOCK_A
    [`word_add inp (word (256 * i)):int64`, "dA"; bB, "bB";
     `(m:num->int64 list) (2 * i)`, "mA"; mB, "mB";
     sha512_hblocks `2 * i`, "hA"; sha512_endp, "endp"] in
  REWRITE_TAC[fst SHA512_AVX2_EXEC; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`s0:x86state`; `inp:int64`; `n:num`; `D:num`; `m:num->int64 list`; `2 * i`] SHA512_BLOCK_DATA) THEN
  ASM_REWRITE_TAC[ARITH_RULE `128 * (2 * i) = 256 * i`] THEN STRIP_TAC THEN
  (fun g -> (if mB = `mB:int64 list` then
     X_CHOOSE_THEN mB STRIP_ASSUME_TAC (SPECL [`s0:x86state`; bB] SHA512_ANY_DATA)
   else
     MP_TAC(SPECL [`s0:x86state`; `inp:int64`; `n:num`; `D:num`; `m:num->int64 list`; `2 * i + 1`] SHA512_BLOCK_DATA) THEN
     ASM_REWRITE_TAC[ARITH_RULE `128 * (2 * i + 1) = 256 * i + 128`] THEN STRIP_TAC) g) THEN
  MP_TAC thA THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  X86_BIGSTEP_TAC SHA512_AVX2_EXEC "s1" THENL [SHA512_PRE_TAC; ALL_TAC] THEN
  X86_STEPS_TAC SHA512_AVX2_EXEC (2--22) THEN RULE_ASSUM_TAC SHA512_SCALAR_RULE THEN
  MP_TAC(SPECL [`inp:int64`; `n:num`; `i:num`] SHA512_RSI_END) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SHA512_FOLD_BLOCK_TAC `2 * i`;;

(* Block B's rounds and the context update after them, to the loop's
   closing branch, with the branch's condition as one on i and n. *)
let SHA512_BLOCK_B_TAC =
  let thB = sha512_inst SHA512_AVX2_BLOCK_B
    [`(m:num->int64 list) (2 * i + 1)`, "mB"; sha512_hblocks `2 * i + 1`, "hB";
     `word_add (word_add inp (word (256 * i))) (word 128):int64`, "rsi0"; sha512_endp, "endp"] in
  MP_TAC thB THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  X86_BIGSTEP_TAC SHA512_AVX2_EXEC "s23" THENL [SHA512_PRE_TAC; ALL_TAC] THEN
  X86_STEPS_TAC SHA512_AVX2_EXEC (24--47) THEN RULE_ASSUM_TAC SHA512_SCALAR_RULE THEN
  SHA512_FOLD_BLOCK_TAC `2 * i + 1` THEN
  MP_TAC(SPECL [`inp:int64`; `n:num`; `i:num`] SHA512_RSI_NEXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SHA512_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(2 * i + 1) + 1 = 2 * (i + 1)`]);;

let SHA512_HASH_N_TAC k =
  SUBGOAL_THEN (subst [k,`k:num`] `sha512_hash_blocks m h n = sha512_hash_blocks m h k`) SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> let c = concl th in is_eq c && rand c = `n:num`)) THEN
    (REFL_TAC ORELSE (AP_TERM_TAC THEN ARITH_TAC)); ALL_TAC];;

let SHA512_AVX2_LOOP = prove
 (SHA512_AVX2_LOOP_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_forall(`d:num`, mk_forall(`i:num`,
    mk_imp(`n - 2 * i = d`, mk_imp(`2 * i < n`, sha512_loop_ensures sha512_loop_inv)))))
   (fun th -> X_GEN_TAC `i:num` THEN MP_TAC(SPECL [`n - 2 * i`; `i:num`] th) THEN REWRITE_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `2 * i + 1 = n` THENL
   [(* One block left: block B's lane reads the frame, and the routine ends
       after block A. *)
    SUBGOAL_THEN `~(2 * i + 1 < n)` (fun th -> REWRITE_TAC[th]) THENL [SHA512_ARITH_TAC; ALL_TAC] THEN
    SHA512_BLOCK_A_TAC `word_add stk (word 1184):int64` `mB:int64 list` THEN
    ENSURES_FINAL_STATE_TAC THEN SHA512_HASH_N_TAC `2 * i + 1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * i + 1 < n` ASSUME_TAC THENL [SHA512_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `2 * i + 2 = n` THENL
   [(* Two blocks left: the loop ends after them. *)
    ASM_REWRITE_TAC[] THEN
    SHA512_BLOCK_A_TAC `word_add inp (word (256 * i + 128)):int64` `(m:num->int64 list) (2 * i + 1)` THEN
    SHA512_BLOCK_B_TAC THEN
    SUBGOAL_THEN `~(2 * i + 3 < n) /\ ~(2 * i + 3 = n)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SHA512_ARITH_TAC; ALL_TAC] THEN
    SHA512_LAUNDER_TAC THEN X86_STEPS_TAC SHA512_AVX2_EXEC [48] THEN
    ENSURES_FINAL_STATE_TAC THEN SHA512_HASH_N_TAC `2 * (i + 1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* More: the loop runs again from the head with two more blocks done. *)
  SUBGOAL_THEN `2 * i + 3 <= n` ASSUME_TAC THENL [SHA512_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x80`
   (mk_abs(`s:x86state`, list_mk_conj(tl(tl(conjuncts(subst [`i + 1`,`i:num`] sha512_loop_inv)))))) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SHA512_BLOCK_A_TAC `word_add inp (word (256 * i + 128)):int64` `(m:num->int64 list) (2 * i + 1)` THEN
    SHA512_BLOCK_B_TAC THEN
    SUBGOAL_THEN `2 * i + 3 < n \/ 2 * i + 3 = n` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SHA512_ARITH_TAC; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[ARITH_RULE `2 * (i + 1) + 1 = 2 * i + 3`; ARITH_RULE `256 * (i + 1) + 128 = 256 * i + 384`;
                ARITH_RULE `256 * (i + 1) = 256 * i + 256`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH_RULE `(256 * i + 256) + 128 = 256 * i + 384`] THEN
    ASM_CASES_TAC `2 * i + 3 = n` THEN ASM_REWRITE_TAC[LT_REFL] THEN
    SUBGOAL_THEN `2 * i + 3 < n` ASSUME_TAC THENL [SHA512_ARITH_TAC; ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 2 * (i + 1)` o
                  check (fun th -> is_forall (concl th) && free_in `d:num` (concl th))) THEN
    ANTS_TAC THENL [SHA512_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `i + 1`)] THEN
    REWRITE_TAC[] THEN
    ANTS_TAC THENL [SHA512_ARITH_TAC; REWRITE_TAC[GSYM CONJ_ASSOC; SOME_FLAGS]] THEN
    DISCH_THEN MATCH_ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The stack frame.                                                          *)
(* ------------------------------------------------------------------------- *)

let SHA512_STK_MASK = prove
 (`!x:int64. word_and x (word 18446744073709549568) =
             word_sub x (word_and x (word(2 EXP 11 - 1)))`,
  CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;

let SHA512_STK_LEMMA = prove
 (`!sp0:int64.
     4096 <= val sp0
     ==> ?stk:int64.
           word_add
            (word_and
             (word_sub
              (word_sub
               (word_sub
                (word_sub
                 (word_sub (word_sub (word_sub sp0 (word 8)) (word 8)) (word 8))
                 (word 8))
                (word 8))
               (word 8))
              (word 1312))
             (word 18446744073709549568))
            (word 1152) = word_add stk (word 1184) /\
           aligned 32 stk /\ 128 <= val stk /\ val stk + 1344 <= 2 EXP 64 /\
           contained_modulo (2 EXP 64) (val stk,1344)
                            (val (word_sub sp0 (word 3440)),3440) /\
           contained_modulo (2 EXP 64) (val stk,1344)
                            (val (word_sub sp0 (word 3440)),3448) /\
           nonoverlapping (stk,1344) (word_sub sp0 (word 48),56) /\
           (?e. e + 1344 <= 3440 /\
                word_add (word_sub sp0 (word 3440)) (word e) = stk)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `word_sub
     (word_sub
      (word_sub
       (word_sub
        (word_sub (word_sub (word_sub sp0 (word 8)) (word 8)) (word 8))
        (word 8))
       (word 8))
      (word 8))
     (word 1312) = word_sub sp0 (word 1360):int64`
  SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_and (word_sub sp0 (word 1360)) (word 18446744073709549568):int64 =
    word(2048 * ((val sp0 - 1360) DIV 2048))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `word_and (word_sub sp0 (word 1360)) (word 18446744073709549568):int64 =
      word_sub (word_sub sp0 (word 1360))
               (word_and (word_sub sp0 (word 1360)) (word(2 EXP 11 - 1)))`
    SUBST1_TAC THENL [REWRITE_TAC[SHA512_STK_MASK]; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_sub sp0 (word 1360):int64) = val sp0 - 1360`
    ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VAL_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [VAL_WORD_SUB_CASES] THEN
    ASM_REWRITE_TAC[VAL_WORD_AND_MASK_WORD; MOD_LE; VAL_WORD; DIMINDEX_64] THEN
    MP_TAC(SPEC `sp0:int64` VAL_BOUND_64) THEN
    MP_TAC(SPECL [`val(sp0:int64) - 1360`; `2048`] (CONJUNCT2 DIVISION_SIMP)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o rand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `q = (val(sp0:int64) - 1360) DIV 2048` THEN
  SUBGOAL_THEN `1 <= q /\ 2048 * q <= val(sp0:int64) - 1360 /\
                val(sp0:int64) - 1360 < 2048 * q + 2048`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    MP_TAC(SPECL [`val(sp0:int64) - 1360`; `2048`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `sp0:int64` VAL_BOUND_64) THEN DISCH_TAC THEN
  EXISTS_TAC `word(2048 * q - 32):int64` THEN
  SUBGOAL_THEN `val(word(2048 * q - 32):int64) = 2048 * q - 32` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub sp0 (word 3440):int64) = val sp0 - 3440`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `32 divides 2 EXP 64` ASSUME_TAC THENL
   [CONV_TAC(RAND_CONV NUM_REDUCE_CONV THENC DIVIDES_CONV); ALL_TAC] THEN
  ASM_REWRITE_TAC[aligned; DIMINDEX_64] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `1184 = 32 + 1152`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `2048 * q - 32 = 32 * (64 * q - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    NUMBER_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN ASM_ARITH_TAC;
    REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
    SUBGOAL_THEN `val(word_sub sp0 (word 48):int64) = val sp0 - 48`
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN ASM_ARITH_TAC;
    EXISTS_TAC `2048 * q - 32 - (val(sp0:int64) - 3440)` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `(2048 * q - 32 - (val(sp0:int64) - 3440)) MOD 2 EXP 64 =
                  2048 * q - 32 - (val sp0 - 3440)` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(val(sp0:int64) - 3440) + (2048 * q - 32 - (val sp0 - 3440)) =
                  2048 * q - 32` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let SHA512_INPUT_REL = prove
 (`!s inp n m.
     (!i j. i < n /\ j < 16
            ==> read (memory :> bytes64 (word_add inp (word (128 * i + 8 * j)))) s =
                word_bytereverse (EL j ((m:num->int64 list) i)))
     ==> !b j. b < n /\ j < 16
               ==> word(bigdigit (read (memory :> bytes(inp,128 * n)) s)
                                 (16 * b + j)):int64 =
                   word_bytereverse (EL j (m b))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `128 * n = 8 * (16 * n)`; GSYM BIGNUM_FROM_MEMORY_BYTES;
              BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
  SUBGOAL_THEN `16 * b + j < 16 * n` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_VAL; ARITH_RULE `8 * (16 * b + j) = 128 * b + 8 * j`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SHA512_N_FACTS = prove
 (`!inp:int64 n.
     0 < n /\ val inp + 128 * (n + 1) < 2 EXP 64
     ==> word_sub inp (word 18446744073709551488) = word_add inp (word 128) /\
         word_add inp (word (8 * val (word_shl (word n:int64) 4))) =
         word_add inp (word (128 * n)) /\
         (val (word_sub (word_add inp (word 128)) (word_add inp (word (128 * n)))) = 0
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
    SUBGOAL_THEN
     `word_sub (word_add inp (word 128)) (word_add inp (word (128 * n))):int64 =
      word_sub (word 128) (word (128 * n))` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `(128 * n) MOD 2 EXP 64 = 128 * n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

let SHA512_SUBREGION_TAC =
  let stkv = `val(stk:int64)` and big = [`val(word_sub stackpointer (word 3440):int64)`; `3448`] in
  REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[nonoverlapping; DIMINDEX_64]) THEN
  (fun (asl,w) ->
    let (x,_),(y,_) = (dest_pair(rand(rator w))),(dest_pair(rand w)) in
    (if x = stkv then ALL_TAC
     else if y = stkv then ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM]
     else failwith "SHA512_SUBREGION_TAC") (asl,w)) THEN
  (fun (asl,w) ->
    let y,l = dest_pair(rand w) in
    (MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
     MAP_EVERY EXISTS_TAC (big @ [y; l]) THEN
     ASM_REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL]) (asl,w));;

let SHA512_STK_TAC =
  MP_TAC(SPEC `stackpointer:int64` SHA512_STK_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `stk:int64`
    (CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
                     STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `nonoverlapping (word pc:int64,0x16dd) (stk:int64,1344) /\
    nonoverlapping (stk,1344) (word k512:int64,1344) /\
    nonoverlapping (stk,1344) (inp:int64,128 * n) /\
    nonoverlapping (stk,1344) (ctxp:int64,64)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN SHA512_SUBREGION_TAC; ALL_TAC];;

(* The pushes leave their slots at nested word_sub addresses; the pops
   read them back as word_add stackpointer (word (2 EXP 64 - 8 * k)). *)
let SHA512_PUSH_SLOTS =
  let sp = `stackpointer:int64` and w8 = `word 8:int64` in
  let rec nest k = if k = 0 then sp else mk_binop `word_sub:int64->int64->int64` (nest(k-1)) w8 in
  map (fun k ->
    let neg = mk_comb(`word:num->int64`, mk_numeral(num_of_string "18446744073709551616" -/ num_of_string(string_of_int(8*k)))) in
    let sub = mk_binop `word_sub:int64->int64->int64` sp (mk_comb(`word:num->int64`, mk_small_numeral(8*k))) in
    let th2 = WORD_BLAST(mk_eq(sub, mk_binop `word_add:int64->int64->int64` sp neg)) in
    if k = 1 then th2 else TRANS (WORD_RULE(mk_eq(nest k, sub))) th2) (1--6);;

(* The frame: every stack address the routine writes, as an offset from
   the bottom of the declared stack region. *)
let SHA512_SUB_FRAME_TAC =
  let sp = `stackpointer:int64` and b = `word_sub stackpointer (word 3440):int64` in
  let wadd x y = mk_binop `word_add:int64->int64->int64` x y in
  let wd n = mk_comb(`word:num->int64`, n) in
  let slots = map (fun k ->
    WORD_BLAST(mk_eq(
      wadd sp (wd (mk_numeral(num_of_string "18446744073709551616" -/ num_of_string(string_of_int(8*k))))),
      wadd b (wd (mk_small_numeral(3440 - 8*k)))))) (1--6) in
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `stk:int64`
    then RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE slots) THEN
  MONOTONE_MAYCHANGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The whole routine: its prologue, the loop, and its epilogue and return.   *)
(* ------------------------------------------------------------------------- *)

(* The prologue pushes six registers and then aligns its frame down to 2048
   bytes, so the frame's place depends on the stack pointer's low bits. All
   the routine writes on the stack lies in the 3440 bytes below it. *)
let SHA512_AVX2_SUBROUTINE_GOAL =
  let tm = mk_imp(
   `0 < n /\ val (inp:int64) + 128 * (n + 1) < 2 EXP 64 /\
    4096 <= val (stackpointer:int64) /\ aligned 32 (word k512:int64) /\
    riprel32_within_bounds (k512 + 128) (pc + 150) /\
    ALL (nonoverlapping (word_sub stackpointer (word 3440),3448))
        [(word pc,0x16dd); (word k512,1344); (inp,128 * n); (ctxp:int64,64)] /\
    ALL (nonoverlapping (ctxp,64)) [(word pc,0x16dd); (word k512,1344); (inp,128 * n)]`,
   list_mk_icomb "ensures" [`x86`;
    mk_abs(`s:x86state`, list_mk_conj[
     `bytes_loaded s (word pc) (sha512_avx2_mc pc k512) /\
      read RIP s = word pc /\ read RSP s = stackpointer /\
      read (memory :> bytes64 stackpointer) s = returnaddress /\
      C_ARGUMENTS [ctxp; inp; word n] s /\
      bytes_loaded s (word k512) sha512_avx2_k512`;
     sha512_ctx_facts `h:int64 list`;
     `!i j. i < n /\ j < 16
            ==> read (memory :> bytes64 (word_add inp (word (128 * i + 8 * j)))) s =
                word_bytereverse (EL j ((m:num->int64 list) i))`]);
    mk_abs(`s:x86state`, list_mk_conj[
     `read RIP s = returnaddress /\ read RSP s = word_add stackpointer (word 8)`;
     sha512_ctx_facts (sha512_hblocks `n:num`)]);
    `MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(ctxp:int64,64);
                memory :> bytes(word_sub stackpointer (word 3440),3440)]`]) in
  list_mk_forall(frees tm, tm);;

let SHA512_AVX2_SUBROUTINE_CORRECT = prove
 (SHA512_AVX2_SUBROUTINE_GOAL,
  let thL = sha512_inst SHA512_AVX2_LOOP
    [`word k512:int64`, "kt"; `num_of_bytelist sha512_avx2_k512`, "kn";
     `stackpointer:int64`, "rsp0"] in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
   [`RBX`; `RBP`; `R12`; `R13`; `R14`; `R15`] THEN
  REWRITE_TAC[fst SHA512_AVX2_EXEC; SHA512_K512_LOADED] THEN ENSURES_INIT_TAC "s0" THEN
  (* The input as one region, which the loop takes. *)
  ABBREV_TAC `D = read (memory :> bytes(inp,128 * n)) s0` THEN
  MP_TAC(SPECL [`s0:x86state`; `inp:int64`; `n:num`; `m:num->int64 list`] SHA512_INPUT_REL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) && free_in `s0:x86state` (concl th))) THEN
  (* The pushes and the frame's alignment, then its first stores. *)
  X86_STEPS_TAC SHA512_AVX2_EXEC (1--12) THEN
  SHA512_STK_TAC THEN
  X86_STEPS_TAC SHA512_AVX2_EXEC (13--30) THEN
  MP_TAC(SPECL [`inp:int64`; `n:num`] SHA512_N_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; COND_SWAP])) THEN
  (* The loop, from no blocks done. *)
  MP_TAC thL THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; CONJUNCT1 sha512_hash_blocks] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  X86_BIGSTEP_TAC SHA512_AVX2_EXEC "s31" THEN
  (* The pops and the return. *)
  RULE_ASSUM_TAC(REWRITE_RULE SHA512_PUSH_SLOTS) THEN
  X86_STEPS_TAC SHA512_AVX2_EXEC (32--41) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHA512_SUB_FRAME_TAC);;
