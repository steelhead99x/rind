(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aws-lc's P-256 mixed addition with mulq on x86_64, as rind's Linux build  *)
(* emits it.                                                                 *)
(* ========================================================================= *)

(* rind's naked function low::x86_64::ecp_nistz256::ecp_nistz256_point_add_affine
   is aws-lc's ecp_nistz256_point_add_affine
   (crypto/fipsmodule/ec/asm/p256-x86_64-asm.pl, its mulq path), the mixed
   addition rind's P-256 generator multiplication runs on CPUs without BMI2
   and ADX. ECP_NISTZ256_POINT_ADD_AFFINE_SUBROUTINE_CORRECT is that, called
   in place with the System V ABI, it adds the affine point at p2 to the
   Jacobian point at p1, both in Montgomery form, as s2n-bignum's
   p256_montjmixadd states it, and also handles the two infinities the
   generator table and the accumulator start from. The proof follows the
   code's shape:
   - ECP_NISTZ256_MUL_MONTQ_CORRECT, _SQR_MONTQ_, _SUB_FROMQ_ and _SUBQ_, the
     field helpers the function carries, each from its entry to its return;
   - ECP_NISTZ256_POINT_ADD_AFFINE_BODY, 0x11 to 0x538, steps over each
     helper call with its lemma, computes in SSE registers the masks for the
     infinities, and selects the result with them in constant time;
   - ECP_NISTZ256_POINT_ADD_AFFINE_SUBROUTINE_CORRECT adds the prologue and
     the epilogue.
   The field algebra that ties the helpers' results to the group law is
   s2n-bignum's, from x86/proofs/p256_montjmixadd.ml. The bytes are the
   Linux build's: Apple's text aligns the helpers to 32 bytes but not the
   entry, so its calls can reach them at other offsets, which this does not
   cover. *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp256.ml";;

(* admin/prove writes the function's object, as rind's release build emits
   it, to x86_64/ecp_nistz256_point_add_affine.o: its section as .text, with
   the field helpers it carries, and the table it reads as .rodata. The
   definition fails unless its instructions are these. *)
let ecp_nistz256_point_add_affine_mc,
    (ecp_nistz256_point_add_affine_data::_) =
  define_assert_relocs_from_elf "ecp_nistz256_point_add_affine_mc"
  "x86_64/ecp_nistz256_point_add_affine.o"
  (fun b ADDR -> [b[
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xe8; 0x01; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 488)) *)
  0xf3; 0x0f; 0x6f; 0x06;  (* MOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,0))) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0xf3; 0x0f; 0x6f; 0x4e; 0x10;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rsi,16))) *)
  0xf3; 0x0f; 0x6f; 0x56; 0x20;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rsi,32))) *)
  0xf3; 0x0f; 0x6f; 0x5e; 0x30;
                           (* MOVDQU (%_% xmm3) (Memop Word128 (%% (rsi,48))) *)
  0xf3; 0x0f; 0x6f; 0x66; 0x40;
                           (* MOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,64))) *)
  0xf3; 0x0f; 0x6f; 0x6e; 0x50;
                           (* MOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,80))) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x4c; 0x8b; 0x76; 0x48;  (* MOV (% r14) (Memop Quadword (%% (rsi,72))) *)
  0x4c; 0x8b; 0x7e; 0x50;  (* MOV (% r15) (Memop Quadword (%% (rsi,80))) *)
  0x4c; 0x8b; 0x46; 0x58;  (* MOV (% r8) (Memop Quadword (%% (rsi,88))) *)
  0x66; 0x0f; 0x7f; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,320))) (%_% xmm0) *)
  0x66; 0x0f; 0x7f; 0x8c; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,336))) (%_% xmm1) *)
  0x66; 0x0f; 0x7f; 0x94; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,352))) (%_% xmm2) *)
  0x66; 0x0f; 0x7f; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,368))) (%_% xmm3) *)
  0x66; 0x0f; 0x7f; 0xa4; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,384))) (%_% xmm4) *)
  0x66; 0x0f; 0x7f; 0xac; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,400))) (%_% xmm5) *)
  0x66; 0x0f; 0xeb; 0xec;  (* POR (%_% xmm5) (%_% xmm4) *)
  0xf3; 0x0f; 0x6f; 0x03;  (* MOVDQU (%_% xmm0) (Memop Word128 (%% (rbx,0))) *)
  0x66; 0x0f; 0x70; 0xdd; 0xb1;
                           (* PSHUFD (%_% xmm3) (%_% xmm5) (Imm8 (word 177)) *)
  0xf3; 0x0f; 0x6f; 0x4b; 0x10;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rbx,16))) *)
  0xf3; 0x0f; 0x6f; 0x53; 0x20;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%% (rbx,32))) *)
  0x66; 0x0f; 0xeb; 0xeb;  (* POR (%_% xmm5) (%_% xmm3) *)
  0xf3; 0x0f; 0x6f; 0x5b; 0x30;
                           (* MOVDQU (%_% xmm3) (Memop Word128 (%% (rbx,48))) *)
  0x66; 0x0f; 0x7f; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,416))) (%_% xmm0) *)
  0x66; 0x0f; 0x70; 0xe5; 0x1e;
                           (* PSHUFD (%_% xmm4) (%_% xmm5) (Imm8 (word 30)) *)
  0x66; 0x0f; 0x7f; 0x8c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,432))) (%_% xmm1) *)
  0x66; 0x0f; 0xeb; 0xc8;  (* POR (%_% xmm1) (%_% xmm0) *)
  0x66; 0x48; 0x0f; 0x6e; 0xc7;
                           (* MOVQ (%_% xmm0) (% rdi) *)
  0x66; 0x0f; 0x7f; 0x94; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,448))) (%_% xmm2) *)
  0x66; 0x0f; 0x7f; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOVDQA (Memop Word128 (%% (rsp,464))) (%_% xmm3) *)
  0x66; 0x0f; 0xeb; 0xda;  (* POR (%_% xmm3) (%_% xmm2) *)
  0x66; 0x0f; 0xeb; 0xec;  (* POR (%_% xmm5) (%_% xmm4) *)
  0x66; 0x0f; 0xef; 0xe4;  (* PXOR (%_% xmm4) (%_% xmm4) *)
  0x66; 0x0f; 0xeb; 0xd9;  (* POR (%_% xmm3) (%_% xmm1) *)
  0x48; 0x8d; 0x76; 0x40;  (* LEA (% rsi) (%% (rsi,64)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0xe8; 0xb9; 0x06; 0x00; 0x00;
                           (* CALL (Imm32 (word 1721)) *)
  0x66; 0x0f; 0x76; 0xec;  (* PCMPEQD (%_% xmm5) (%_% xmm4) *)
  0x66; 0x0f; 0x70; 0xe3; 0xb1;
                           (* PSHUFD (%_% xmm4) (%_% xmm3) (Imm8 (word 177)) *)
  0x48; 0x8b; 0x03;        (* MOV (% rax) (Memop Quadword (%% (rbx,0))) *)
  0x4d; 0x89; 0xe1;        (* MOV (% r9) (% r12) *)
  0x66; 0x0f; 0xeb; 0xe3;  (* POR (%_% xmm4) (%_% xmm3) *)
  0x66; 0x0f; 0x70; 0xed; 0x00;
                           (* PSHUFD (%_% xmm5) (%_% xmm5) (Imm8 (word 0)) *)
  0x66; 0x0f; 0x70; 0xdc; 0x1e;
                           (* PSHUFD (%_% xmm3) (%_% xmm4) (Imm8 (word 30)) *)
  0x4d; 0x89; 0xea;        (* MOV (% r10) (% r13) *)
  0x66; 0x0f; 0xeb; 0xe3;  (* POR (%_% xmm4) (%_% xmm3) *)
  0x66; 0x0f; 0xef; 0xdb;  (* PXOR (%_% xmm3) (%_% xmm3) *)
  0x4d; 0x89; 0xf3;        (* MOV (% r11) (% r14) *)
  0x66; 0x0f; 0x76; 0xe3;  (* PCMPEQD (%_% xmm4) (%_% xmm3) *)
  0x66; 0x0f; 0x70; 0xe4; 0x00;
                           (* PSHUFD (%_% xmm4) (%_% xmm4) (Imm8 (word 0)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x4d; 0x89; 0xfc;        (* MOV (% r12) (% r15) *)
  0x48; 0x8d; 0x3c; 0x24;  (* LEA (% rdi) (%% (rsp,0)) *)
  0xe8; 0x34; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1076)) *)
  0x48; 0x8d; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,320)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0xe8; 0x22; 0x08; 0x00; 0x00;
                           (* CALL (Imm32 (word 2082)) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,384))) *)
  0x48; 0x8d; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,384)) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x28;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x30;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x38;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0xe8; 0xef; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 1007)) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,384))) *)
  0x48; 0x8d; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,384)) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x50;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x58;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0xe8; 0xb9; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 953)) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,448))) *)
  0x48; 0x8d; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,448)) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x28;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x30;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x38;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0xe8; 0x86; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 902)) *)
  0x48; 0x8d; 0x9c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,352)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0xe8; 0x74; 0x07; 0x00; 0x00;
                           (* CALL (Imm32 (word 1908)) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x74; 0x24; 0x48;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x50;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0xe8; 0x8e; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1422)) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x74; 0x24; 0x68;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x8d; 0x74; 0x24; 0x60;
                           (* LEA (% rsi) (%% (rsp,96)) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x70;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x8d; 0xbc; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,192)) *)
  0xe8; 0x68; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1384)) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8d; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,128)) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x50;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x58;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,160)) *)
  0xe8; 0xf2; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 754)) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0x8d; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,320)) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x8d; 0xb4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,128)) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x8d; 0x3c; 0x24;  (* LEA (% rdi) (%% (rsp,0)) *)
  0xe8; 0xb1; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 689)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x01; 0xe4;        (* ADD (% r12) (% r12) *)
  0x48; 0x8d; 0xb4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,192)) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x4d; 0x11; 0xc9;        (* ADC (% r9) (% r9) *)
  0x4c; 0x89; 0xed;        (* MOV (% rbp) (% r13) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xec; 0xff;  (* SUB (% r12) (Imm8 (word 255)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x4d; 0x19; 0xf5;        (* SBB (% r13) (% r14) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4d; 0x89; 0xca;        (* MOV (% r10) (% r9) *)
  0x4d; 0x19; 0xf9;        (* SBB (% r9) (% r15) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x42; 0xe0;  (* CMOVB (% r12) (% rax) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x0f; 0x42; 0xed;  (* CMOVB (% r13) (% rbp) *)
  0x48; 0x8b; 0x6e; 0x08;  (* MOV (% rbp) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x0f; 0x42; 0xc1;  (* CMOVB (% r8) (% rcx) *)
  0x48; 0x8b; 0x4e; 0x10;  (* MOV (% rcx) (Memop Quadword (%% (rsi,16))) *)
  0x4d; 0x0f; 0x42; 0xca;  (* CMOVB (% r9) (% r10) *)
  0x4c; 0x8b; 0x56; 0x18;  (* MOV (% r10) (Memop Quadword (%% (rsi,24))) *)
  0xe8; 0xb4; 0x06; 0x00; 0x00;
                           (* CALL (Imm32 (word 1716)) *)
  0x48; 0x8d; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,160)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,224)) *)
  0xe8; 0x3f; 0x06; 0x00; 0x00;
                           (* CALL (Imm32 (word 1599)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x6c; 0x24; 0x08;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x10;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x18;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0xe8; 0x82; 0x06; 0x00; 0x00;
                           (* CALL (Imm32 (word 1666)) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,352))) *)
  0x48; 0x8d; 0x9c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* LEA (% rbx) (%% (rsp,352)) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x8b; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,160)) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,176))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0xe8; 0xd1; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 465)) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x8d; 0x5c; 0x24; 0x60;
                           (* LEA (% rbx) (%% (rsp,96)) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x50;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x58;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0xe8; 0xa4; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 420)) *)
  0x48; 0x8d; 0x5c; 0x24; 0x20;
                           (* LEA (% rbx) (%% (rsp,32)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,256)) *)
  0xe8; 0x92; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1426)) *)
  0x66; 0x48; 0x0f; 0x7e; 0xc7;
                           (* MOVQ (% rdi) (%_% xmm0) *)
  0x66; 0x0f; 0x6f; 0xc5;  (* MOVDQA (%_% xmm0) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0xcd;  (* MOVDQA (%_% xmm1) (%_% xmm5) *)
  0x66; 0x0f; 0xdf; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* PANDN (%_% xmm0) (Memop Word128 (%% (rsp,288))) *)
  0x66; 0x0f; 0x6f; 0xd5;  (* MOVDQA (%_% xmm2) (%_% xmm5) *)
  0x66; 0x0f; 0xdf; 0x8c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* PANDN (%_% xmm1) (Memop Word128 (%% (rsp,304))) *)
  0x66; 0x0f; 0x6f; 0xdd;  (* MOVDQA (%_% xmm3) (%_% xmm5) *)
  0x66; 0x0f; 0xdb; 0x15]; ADDR ("WHOLE_READONLY_data",(124)); b[
                           (* PAND (%_% xmm2)
(Memop Word128
(Riprel (word_sx (iword (&WHOLE_READONLY_data - (&pc + &893)))))) *)
  0x66; 0x0f; 0xdb; 0x1d]; ADDR ("WHOLE_READONLY_data",(140)); b[
                           (* PAND (%_% xmm3)
(Memop Word128
(Riprel (word_sx (iword (&WHOLE_READONLY_data - (&pc + &885)))))) *)
  0x66; 0x0f; 0xeb; 0xd0;  (* POR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0xeb; 0xd9;  (* POR (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xc4;  (* MOVDQA (%_% xmm0) (%_% xmm4) *)
  0x66; 0x0f; 0x6f; 0xcc;  (* MOVDQA (%_% xmm1) (%_% xmm4) *)
  0x66; 0x0f; 0xdf; 0xc2;  (* PANDN (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x6f; 0xd4;  (* MOVDQA (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0xdf; 0xcb;  (* PANDN (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xdc;  (* MOVDQA (%_% xmm3) (%_% xmm4) *)
  0x66; 0x0f; 0xdb; 0x94; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm2) (Memop Word128 (%% (rsp,384))) *)
  0x66; 0x0f; 0xdb; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm3) (Memop Word128 (%% (rsp,400))) *)
  0x66; 0x0f; 0xeb; 0xd0;  (* POR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0xeb; 0xd9;  (* POR (%_% xmm3) (%_% xmm1) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x40;
                           (* MOVDQU (Memop Word128 (%% (rdi,64))) (%_% xmm2) *)
  0xf3; 0x0f; 0x7f; 0x5f; 0x50;
                           (* MOVDQU (Memop Word128 (%% (rdi,80))) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xc5;  (* MOVDQA (%_% xmm0) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0xcd;  (* MOVDQA (%_% xmm1) (%_% xmm5) *)
  0x66; 0x0f; 0xdf; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* PANDN (%_% xmm0) (Memop Word128 (%% (rsp,224))) *)
  0x66; 0x0f; 0x6f; 0xd5;  (* MOVDQA (%_% xmm2) (%_% xmm5) *)
  0x66; 0x0f; 0xdf; 0x8c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* PANDN (%_% xmm1) (Memop Word128 (%% (rsp,240))) *)
  0x66; 0x0f; 0x6f; 0xdd;  (* MOVDQA (%_% xmm3) (%_% xmm5) *)
  0x66; 0x0f; 0xdb; 0x94; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm2) (Memop Word128 (%% (rsp,416))) *)
  0x66; 0x0f; 0xdb; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm3) (Memop Word128 (%% (rsp,432))) *)
  0x66; 0x0f; 0xeb; 0xd0;  (* POR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0xeb; 0xd9;  (* POR (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xc4;  (* MOVDQA (%_% xmm0) (%_% xmm4) *)
  0x66; 0x0f; 0x6f; 0xcc;  (* MOVDQA (%_% xmm1) (%_% xmm4) *)
  0x66; 0x0f; 0xdf; 0xc2;  (* PANDN (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x6f; 0xd4;  (* MOVDQA (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0xdf; 0xcb;  (* PANDN (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xdc;  (* MOVDQA (%_% xmm3) (%_% xmm4) *)
  0x66; 0x0f; 0xdb; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm2) (Memop Word128 (%% (rsp,320))) *)
  0x66; 0x0f; 0xdb; 0x9c; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm3) (Memop Word128 (%% (rsp,336))) *)
  0x66; 0x0f; 0xeb; 0xd0;  (* POR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0xeb; 0xd9;  (* POR (%_% xmm3) (%_% xmm1) *)
  0xf3; 0x0f; 0x7f; 0x17;  (* MOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm2) *)
  0xf3; 0x0f; 0x7f; 0x5f; 0x10;
                           (* MOVDQU (Memop Word128 (%% (rdi,16))) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xc5;  (* MOVDQA (%_% xmm0) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0xcd;  (* MOVDQA (%_% xmm1) (%_% xmm5) *)
  0x66; 0x0f; 0xdf; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* PANDN (%_% xmm0) (Memop Word128 (%% (rsp,256))) *)
  0x66; 0x0f; 0x6f; 0xd5;  (* MOVDQA (%_% xmm2) (%_% xmm5) *)
  0x66; 0x0f; 0xdf; 0x8c; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* PANDN (%_% xmm1) (Memop Word128 (%% (rsp,272))) *)
  0x66; 0x0f; 0x6f; 0xdd;  (* MOVDQA (%_% xmm3) (%_% xmm5) *)
  0x66; 0x0f; 0xdb; 0x94; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm2) (Memop Word128 (%% (rsp,448))) *)
  0x66; 0x0f; 0xdb; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm3) (Memop Word128 (%% (rsp,464))) *)
  0x66; 0x0f; 0xeb; 0xd0;  (* POR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0xeb; 0xd9;  (* POR (%_% xmm3) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xc4;  (* MOVDQA (%_% xmm0) (%_% xmm4) *)
  0x66; 0x0f; 0x6f; 0xcc;  (* MOVDQA (%_% xmm1) (%_% xmm4) *)
  0x66; 0x0f; 0xdf; 0xc2;  (* PANDN (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x6f; 0xd4;  (* MOVDQA (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0xdf; 0xcb;  (* PANDN (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xdc;  (* MOVDQA (%_% xmm3) (%_% xmm4) *)
  0x66; 0x0f; 0xdb; 0x94; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm2) (Memop Word128 (%% (rsp,352))) *)
  0x66; 0x0f; 0xdb; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* PAND (%_% xmm3) (Memop Word128 (%% (rsp,368))) *)
  0x66; 0x0f; 0xeb; 0xd0;  (* POR (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0xeb; 0xd9;  (* POR (%_% xmm3) (%_% xmm1) *)
  0xf3; 0x0f; 0x7f; 0x57; 0x20;
                           (* MOVDQU (Memop Word128 (%% (rdi,32))) (%_% xmm2) *)
  0xf3; 0x0f; 0x7f; 0x5f; 0x30;
                           (* MOVDQU (Memop Word128 (%% (rdi,48))) (%_% xmm3) *)
  0x48; 0x8d; 0xb4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,536)) *)
  0x4c; 0x8b; 0x7e; 0xd0;  (* MOV (% r15) (Memop Quadword (%% (rsi,18446744073709551568))) *)
  0x4c; 0x8b; 0x76; 0xd8;  (* MOV (% r14) (Memop Quadword (%% (rsi,18446744073709551576))) *)
  0x4c; 0x8b; 0x6e; 0xe0;  (* MOV (% r13) (Memop Quadword (%% (rsi,18446744073709551584))) *)
  0x4c; 0x8b; 0x66; 0xe8;  (* MOV (% r12) (Memop Quadword (%% (rsi,18446744073709551592))) *)
  0x48; 0x8b; 0x5e; 0xf0;  (* MOV (% rbx) (Memop Quadword (%% (rsi,18446744073709551600))) *)
  0x48; 0x8b; 0x6e; 0xf8;  (* MOV (% rbp) (Memop Quadword (%% (rsi,18446744073709551608))) *)
  0x48; 0x8d; 0x26;        (* LEA (% rsp) (%% (rsi,0)) *)
  0xf3; 0xc3;              (* RET *)
  0x0f; 0x1f; 0x00;        (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x4c; 0x8b; 0x35]; ADDR ("WHOLE_READONLY_data",(4)); b[
                           (* MOV (% r14)
(Memop Quadword
(Riprel (word_sx (iword (&WHOLE_READONLY_data - (&pc + &1381)))))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x4c; 0x8b; 0x3d]; ADDR ("WHOLE_READONLY_data",(20)); b[
                           (* MOV (% r15)
(Memop Quadword
(Riprel (word_sx (iword (&WHOLE_READONLY_data - (&pc + &1384)))))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x4c; 0x89; 0xc5;        (* MOV (% rbp) (% r8) *)
  0x49; 0xc1; 0xe0; 0x20;  (* SHL (% r8) (Imm8 (word 32)) *)
  0x49; 0xf7; 0xe7;        (* MUL2 (% rdx,% rax) (% r15) *)
  0x48; 0xc1; 0xed; 0x20;  (* SHR (% rbp) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xc1;        (* ADD (% r9) (% r8) *)
  0x49; 0x11; 0xea;        (* ADC (% r10) (% rbp) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x48; 0x8b; 0x43; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rbx,8))) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0xf7; 0x26;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0x01; 0xca;        (* ADD (% r10) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x01; 0xcb;        (* ADD (% r11) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x01; 0xcc;        (* ADD (% r12) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xcd;        (* MOV (% rbp) (% r9) *)
  0x49; 0xc1; 0xe1; 0x20;  (* SHL (% r9) (Imm8 (word 32)) *)
  0x49; 0xf7; 0xe7;        (* MUL2 (% rdx,% rax) (% r15) *)
  0x48; 0xc1; 0xed; 0x20;  (* SHR (% rbp) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xca;        (* ADD (% r10) (% r9) *)
  0x49; 0x11; 0xeb;        (* ADC (% r11) (% rbp) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x48; 0x8b; 0x43; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rbx,16))) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0xf7; 0x26;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0x01; 0xcb;        (* ADD (% r11) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x01; 0xcc;        (* ADD (% r12) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x01; 0xcd;        (* ADD (% r13) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd5;        (* MOV (% rbp) (% r10) *)
  0x49; 0xc1; 0xe2; 0x20;  (* SHL (% r10) (Imm8 (word 32)) *)
  0x49; 0xf7; 0xe7;        (* MUL2 (% rdx,% rax) (% r15) *)
  0x48; 0xc1; 0xed; 0x20;  (* SHR (% rbp) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xd3;        (* ADD (% r11) (% r10) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x48; 0x8b; 0x43; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rbx,24))) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0xf7; 0x26;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0x01; 0xcc;        (* ADD (% r12) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x01; 0xcd;        (* ADD (% r13) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xdd;        (* MOV (% rbp) (% r11) *)
  0x49; 0xc1; 0xe3; 0x20;  (* SHL (% r11) (Imm8 (word 32)) *)
  0x49; 0xf7; 0xe7;        (* MUL2 (% rdx,% rax) (% r15) *)
  0x48; 0xc1; 0xed; 0x20;  (* SHR (% rbp) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xdc;        (* ADD (% r12) (% r11) *)
  0x49; 0x11; 0xed;        (* ADC (% r13) (% rbp) *)
  0x4c; 0x89; 0xe1;        (* MOV (% rcx) (% r12) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0xed;        (* MOV (% rbp) (% r13) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xec; 0xff;  (* SUB (% r12) (Imm8 (word 255)) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x4d; 0x19; 0xf5;        (* SBB (% r13) (% r14) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xca;        (* MOV (% rdx) (% r9) *)
  0x4d; 0x19; 0xf9;        (* SBB (% r9) (% r15) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xed;  (* CMOVB (% r13) (% rbp) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x0f; 0x42; 0xc3;  (* CMOVB (% r8) (% rbx) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x0f; 0x42; 0xca;  (* CMOVB (% r9) (% rdx) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0xf3; 0xc3;              (* RET *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x66; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x49; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% r13) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% r13) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xec;        (* ADD (% r12) (% rbp) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0xf7; 0xe7;        (* MUL2 (% rdx,% rax) (% r15) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc9;        (* ADD (% r9) (% rcx) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xcb;        (* ADD (% r11) (% rcx) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xcd;        (* ADD (% r13) (% rcx) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x35]; ADDR ("WHOLE_READONLY_data",(4)); b[
                           (* MOV (% rsi)
(Memop Quadword
(Riprel (word_sx (iword (&WHOLE_READONLY_data - (&pc + &2146)))))) *)
  0x48; 0x8b; 0x2d]; ADDR ("WHOLE_READONLY_data",(20)); b[
                           (* MOV (% rbp)
(Memop Quadword
(Riprel (word_sx (iword (&WHOLE_READONLY_data - (&pc + &2137)))))) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x49; 0xc1; 0xe0; 0x20;  (* SHL (% r8) (Imm8 (word 32)) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xc1;        (* ADD (% r9) (% r8) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x49; 0xc1; 0xe1; 0x20;  (* SHL (% r9) (Imm8 (word 32)) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xca;        (* ADD (% r10) (% r9) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x49; 0xc1; 0xe2; 0x20;  (* SHL (% r10) (Imm8 (word 32)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xd3;        (* ADD (% r11) (% r10) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x49; 0xc1; 0xe3; 0x20;  (* SHL (% r11) (Imm8 (word 32)) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xd8;        (* ADD (% r8) (% r11) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x89; 0xe0;        (* MOV (% r8) (% r12) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x89; 0xe9;        (* MOV (% r9) (% r13) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xec; 0xff;  (* SUB (% r12) (Imm8 (word 255)) *)
  0x4d; 0x89; 0xf2;        (* MOV (% r10) (% r14) *)
  0x49; 0x19; 0xf5;        (* SBB (% r13) (% rsi) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xf9;        (* MOV (% rcx) (% r15) *)
  0x49; 0x19; 0xef;        (* SBB (% r15) (% rbp) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4d; 0x0f; 0x42; 0xe0;  (* CMOVB (% r12) (% r8) *)
  0x4d; 0x0f; 0x42; 0xe9;  (* CMOVB (% r13) (% r9) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4d; 0x0f; 0x42; 0xf2;  (* CMOVB (% r14) (% r10) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x0f; 0x42; 0xf9;  (* CMOVB (% r15) (% rcx) *)
  0x4c; 0x89; 0x77; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r15) *)
  0xf3; 0xc3;              (* RET *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x90;                    (* NOP *)
  0x4c; 0x2b; 0x23;        (* SUB (% r12) (Memop Quadword (%% (rbx,0))) *)
  0x4c; 0x1b; 0x6b; 0x08;  (* SBB (% r13) (Memop Quadword (%% (rbx,8))) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x4c; 0x1b; 0x43; 0x10;  (* SBB (% r8) (Memop Quadword (%% (rbx,16))) *)
  0x4c; 0x1b; 0x4b; 0x18;  (* SBB (% r9) (Memop Quadword (%% (rbx,24))) *)
  0x4c; 0x89; 0xed;        (* MOV (% rbp) (% r13) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x49; 0x83; 0xc4; 0xff;  (* ADD (% r12) (Imm8 (word 255)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4d; 0x89; 0xca;        (* MOV (% r10) (% r9) *)
  0x4d; 0x11; 0xf9;        (* ADC (% r9) (% r15) *)
  0x4d; 0x85; 0xdb;        (* TEST (% r11) (% r11) *)
  0x4c; 0x0f; 0x44; 0xe0;  (* CMOVE (% r12) (% rax) *)
  0x4c; 0x0f; 0x44; 0xed;  (* CMOVE (% r13) (% rbp) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x0f; 0x44; 0xc1;  (* CMOVE (% r8) (% rcx) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4d; 0x0f; 0x44; 0xca;  (* CMOVE (% r9) (% r10) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0xf3; 0xc3;              (* RET *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x66; 0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x4c; 0x29; 0xe0;        (* SUB (% rax) (% r12) *)
  0x4c; 0x19; 0xed;        (* SBB (% rbp) (% r13) *)
  0x49; 0x89; 0xc4;        (* MOV (% r12) (% rax) *)
  0x4c; 0x19; 0xc1;        (* SBB (% rcx) (% r8) *)
  0x4d; 0x19; 0xca;        (* SBB (% r10) (% r9) *)
  0x49; 0x89; 0xed;        (* MOV (% r13) (% rbp) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x83; 0xc0; 0xff;  (* ADD (% rax) (Imm8 (word 255)) *)
  0x49; 0x89; 0xc8;        (* MOV (% r8) (% rcx) *)
  0x4c; 0x11; 0xf5;        (* ADC (% rbp) (% r14) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4d; 0x89; 0xd1;        (* MOV (% r9) (% r10) *)
  0x4d; 0x11; 0xfa;        (* ADC (% r10) (% r15) *)
  0x4d; 0x85; 0xdb;        (* TEST (% r11) (% r11) *)
  0x4c; 0x0f; 0x45; 0xe0;  (* CMOVNE (% r12) (% rax) *)
  0x4c; 0x0f; 0x45; 0xed;  (* CMOVNE (% r13) (% rbp) *)
  0x4c; 0x0f; 0x45; 0xc1;  (* CMOVNE (% r8) (% rcx) *)
  0x4d; 0x0f; 0x45; 0xca;  (* CMOVNE (% r9) (% r10) *)
  0xf3; 0xc3               (* RET *)
]]);;

let ECP_NISTZ256_POINT_ADD_AFFINE_EXEC =
  X86_MK_EXEC_RULE ecp_nistz256_point_add_affine_mc;;

(* ------------------------------------------------------------------------- *)
(* Rip-relative reads of the table.                                          *)
(* ------------------------------------------------------------------------- *)

let RIPREL_FOLD = prove
 (`!pc n k tgt.
     riprel32_within_bounds tgt (pc + k) /\ k <= n
     ==> word(val(word(pc + n):int64) +
              val(word_sx(iword(&tgt - (&pc + &k)):int32):int64)):int64 =
         word(tgt + (n - k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WORD32_ADD_SUB_OF_LT) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_ADD] THEN REWRITE_TAC[WORD_VAL] THEN
  SUBGOAL_THEN `word(pc + n):int64 = word_add (word(pc + k)) (word(n - k)) /\
                word(tgt + (n - k)):int64 = word_add (word tgt) (word(n - k))`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE]);;
(* Restates the table's word at tbl + (n - k) as the step at pc + n reads it,
   through a displacement relocated against pc + k. *)
let RIPREL_TAC n k =
  let off = n - k in
  let tm = subst [mk_small_numeral n,`n:num`; mk_small_numeral k,`k:num`]
    `word(val(word(pc + n):int64) +
          val(word_sx(iword(&tbl - (&pc + &k)):int32):int64)):int64` in
  SUBGOAL_THEN (mk_eq(tm, mk_comb(`word:num->int64`,
                 mk_binop `(+):num->num->num` `tbl:num` (mk_small_numeral off))))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) RIPREL_FOLD o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The field helpers, each from its entry to its return.                     *)
(* ------------------------------------------------------------------------- *)

let ECP_NISTZ256_MUL_MONTQ_CORRECT = time prove
 (`!z pa pb a0 a1 a2 a3 b0 b1 b2 b3 pc tbl stackpointer returnaddress.
     riprel32_within_bounds tbl (pc + 1381) /\
     riprel32_within_bounds tbl (pc + 1384) /\
     nonoverlapping (word pc,0x9fe) (z,32) /\
     nonoverlapping (word tbl,200) (z,32) /\
     nonoverlapping (stackpointer,8) (z,32)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (ecp_nistz256_point_add_affine_mc pc tbl) /\
               read RIP s = word(pc + 0x560) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               read (memory :> bytes64 (word(tbl + 8))) s = word 0xffffffff /\
               read (memory :> bytes64 (word(tbl + 24))) s = word 0xffffffff00000001 /\
               read RDI s = z /\ read RSI s = pa /\ read RBX s = pb /\
               read RAX s = b0 /\
               read R9 s = a0 /\ read R10 s = a1 /\ read R11 s = a2 /\ read R12 s = a3 /\
               read (memory :> bytes64 pa) s = a0 /\
               read (memory :> bytes64 (word_add pa (word 8))) s = a1 /\
               read (memory :> bytes64 (word_add pa (word 16))) s = a2 /\
               read (memory :> bytes64 (word_add pa (word 24))) s = a3 /\
               read (memory :> bytes64 pb) s = b0 /\
               read (memory :> bytes64 (word_add pb (word 8))) s = b1 /\
               read (memory :> bytes64 (word_add pb (word 16))) s = b2 /\
               read (memory :> bytes64 (word_add pb (word 24))) s = b3)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read R14 s = word 0xffffffff /\
               read R15 s = word 0xffffffff00000001 /\
               read (memory :> bytes64 z) s = read R12 s /\
               read (memory :> bytes64 (word_add z (word 8))) s = read R13 s /\
               read (memory :> bytes64 (word_add z (word 16))) s = read R8 s /\
               read (memory :> bytes64 (word_add z (word 24))) s = read R9 s /\
               (bignum_of_wordlist [a0;a1;a2;a3] * bignum_of_wordlist [b0;b1;b2;b3]
                  <= 2 EXP 256 * p_256
                ==> bignum_of_wordlist [read R12 s; read R13 s; read R8 s; read R9 s] =
                      (inverse_mod p_256 (2 EXP 256) *
                       bignum_of_wordlist [a0;a1;a2;a3] *
                       bignum_of_wordlist [b0;b1;b2;b3]) MOD p_256))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RBP; R8; R9; R10; R11;
                      R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `pa:int64`; `pb:int64`; `a0:int64`; `a1:int64`; `a2:int64`; `a3:int64`;
    `b0:int64`; `b1:int64`; `b2:int64`; `b3:int64`; `pc:num`; `tbl:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN RIPREL_TAC 1389 1381 THEN RIPREL_TAC 1408 1384 THEN
  X86_ACCSTEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (1--148) (1--148) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s142; sum_s143; sum_s145; sum_s146; sum_s148]` THEN
  ASM_CASES_TAC `bignum_of_wordlist [a0;a1;a2;a3] * bignum_of_wordlist [b0;b1;b2;b3]
                  <= 2 EXP 256 * p_256` THENL
   [ALL_TAC;
    X86_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (149--164) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\
    (2 EXP 256 * t == bignum_of_wordlist [a0;a1;a2;a3] *
                      bignum_of_wordlist [b0;b1;b2;b3]) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  X86_ACCSTEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC
   [149;151;152;154;155] (149--164) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES])) THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256 then &t:real else &t - &p_256`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s155 <=> t < p_256` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let ECP_NISTZ256_SQR_MONTQ_CORRECT = time prove
 (`!z pa a0 a1 a2 a3 pc tbl stackpointer returnaddress.
     riprel32_within_bounds tbl (pc + 2146) /\
     riprel32_within_bounds tbl (pc + 2137) /\
     nonoverlapping (word pc,0x9fe) (z,32) /\
     nonoverlapping (word tbl,200) (z,32) /\
     nonoverlapping (stackpointer,8) (z,32)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (ecp_nistz256_point_add_affine_mc pc tbl) /\
               read RIP s = word(pc + 0x7a0) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               read (memory :> bytes64 (word(tbl + 8))) s = word 0xffffffff /\
               read (memory :> bytes64 (word(tbl + 24))) s = word 0xffffffff00000001 /\
               read RDI s = z /\ read RSI s = pa /\
               read RAX s = a0 /\ read R14 s = a1 /\ read R15 s = a2 /\ read R8 s = a3 /\
               read (memory :> bytes64 pa) s = a0 /\
               read (memory :> bytes64 (word_add pa (word 8))) s = a1 /\
               read (memory :> bytes64 (word_add pa (word 16))) s = a2 /\
               read (memory :> bytes64 (word_add pa (word 24))) s = a3)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes64 z) s = read R12 s /\
               read (memory :> bytes64 (word_add z (word 8))) s = read R13 s /\
               read (memory :> bytes64 (word_add z (word 16))) s = read R14 s /\
               read (memory :> bytes64 (word_add z (word 24))) s = read R15 s /\
               (bignum_of_wordlist [a0;a1;a2;a3] EXP 2 <= 2 EXP 256 * p_256
                ==> bignum_of_wordlist [read R12 s; read R13 s; read R14 s; read R15 s] =
                      (inverse_mod p_256 (2 EXP 256) *
                       bignum_of_wordlist [a0;a1;a2;a3] EXP 2) MOD p_256))
          (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RBP; R8; R9; R10; R11;
                      R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `pa:int64`; `a0:int64`; `a1:int64`; `a2:int64`; `a3:int64`;
    `pc:num`; `tbl:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN RIPREL_TAC 2154 2146 THEN RIPREL_TAC 2161 2137 THEN
  MAP_EVERY (fun n ->
    X86_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC [n] THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n))) (1--109) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s103; sum_s104; sum_s106; sum_s107; word(bitval carry_s107)]` THEN
  ASM_CASES_TAC `bignum_of_wordlist [a0;a1;a2;a3] EXP 2 <= 2 EXP 256 * p_256` THENL
   [ALL_TAC;
    X86_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (110--125) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `2 EXP 256 * t =
    bignum_of_wordlist [a0;a1;a2;a3] EXP 2 +
    p_256 * bignum_of_wordlist [mullo_s41; sum_s68; sum_s78; sum_s88]`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_CLAUSES;
                bignum_of_wordlist; VAL_WORD_BITVAL; p_256] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\
    (2 EXP 256 * t == bignum_of_wordlist [a0;a1;a2;a3] EXP 2) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`[mullo_s41; sum_s68; sum_s78; sum_s88]:int64 list`]
        BIGNUM_OF_WORDLIST_BOUND_LENGTH) THEN
      REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `bignum_of_wordlist [a0;a1;a2;a3] EXP 2 <= 2 EXP 256 * p_256` THEN
      UNDISCH_TAC
       `2 EXP 256 * t =
        bignum_of_wordlist [a0;a1;a2;a3] EXP 2 +
        p_256 * bignum_of_wordlist [mullo_s41; sum_s68; sum_s78; sum_s88]` THEN
      SPEC_TAC(`bignum_of_wordlist [mullo_s41; sum_s68; sum_s78; sum_s88]`,`q:num`) THEN
      SPEC_TAC(`bignum_of_wordlist [a0;a1;a2;a3] EXP 2`,`aa:num`) THEN
      REWRITE_TAC[p_256] THEN ARITH_TAC;
      ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC
   [110;112;113;115;116] (110--125) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES])) THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256 then &t:real else &t - &p_256`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s116 <=> t < p_256` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; VAL_WORD_BITVAL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256; VAL_WORD_BITVAL] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let ECP_NISTZ256_SUB_FROMQ_CORRECT = time prove
 (`!z py x0 x1 x2 x3 y0 y1 y2 y3 pc tbl stackpointer returnaddress.
     nonoverlapping (word pc,0x9fe) (z,32) /\
     nonoverlapping (stackpointer,8) (z,32)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (ecp_nistz256_point_add_affine_mc pc tbl) /\
               read RIP s = word(pc + 0x960) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               read RDI s = z /\ read RBX s = py /\
               read R14 s = word 0xffffffff /\
               read R15 s = word 0xffffffff00000001 /\
               read R12 s = x0 /\ read R13 s = x1 /\ read R8 s = x2 /\ read R9 s = x3 /\
               read (memory :> bytes64 py) s = y0 /\
               read (memory :> bytes64 (word_add py (word 8))) s = y1 /\
               read (memory :> bytes64 (word_add py (word 16))) s = y2 /\
               read (memory :> bytes64 (word_add py (word 24))) s = y3)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes64 z) s = read R12 s /\
               read (memory :> bytes64 (word_add z (word 8))) s = read R13 s /\
               read (memory :> bytes64 (word_add z (word 16))) s = read R8 s /\
               read (memory :> bytes64 (word_add z (word 24))) s = read R9 s /\
               (bignum_of_wordlist [x0;x1;x2;x3] < p_256 /\
                bignum_of_wordlist [y0;y1;y2;y3] < p_256
                ==> &(bignum_of_wordlist [read R12 s; read R13 s; read R8 s; read R9 s]) =
                      (&(bignum_of_wordlist [x0;x1;x2;x3]) -
                       &(bignum_of_wordlist [y0;y1;y2;y3])) rem &p_256))
          (MAYCHANGE [RIP; RSP; RAX; RCX; RBP; R8; R9; R10; R11; R12; R13] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `py:int64`; `x0:int64`; `x1:int64`; `x2:int64`; `x3:int64`;
    `y0:int64`; `y1:int64`; `y2:int64`; `y3:int64`;
    `pc:num`; `tbl:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY ABBREV_TAC
   [`m = bignum_of_wordlist [x0;x1;x2;x3]`; `n = bignum_of_wordlist [y0;y1;y2;y3]`] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_ACCSTEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC [1;2;4;5] (1--5) THEN
  SUBGOAL_THEN `carry_s5 <=> m:num < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC [8;10;11;13] (6--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0; WORD_BITVAL_EQ_0; COND_SWAP] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `--(&(bitval(m:num < n))):int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
  REWRITE_TAC[INT_ARITH `m - n:int = --b * p + z <=> z = b * p + m - n`] THEN
  REWRITE_TAC[int_eq; int_le; int_lt] THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th; int_sub_th] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC(REAL_ARITH
  `!t:real. p < t /\
            (&0 <= a /\ a < p) /\
            (&0 <= z /\ z < t) /\
            ((&0 <= z /\ z < t) /\ (&0 <= a /\ a < t) ==> z = a)
            ==> z = a /\ &0 <= z /\ z < p`) THEN
  EXISTS_TAC `(&2:real) pow 256` THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m:num < p_256`; `n:num < p_256`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_256] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let ECP_NISTZ256_SUBQ_CORRECT = time prove
 (`!x0 x1 x2 x3 y0 y1 y2 y3 pc tbl stackpointer returnaddress.
     ensures x86
          (\s. bytes_loaded s (word pc) (ecp_nistz256_point_add_affine_mc pc tbl) /\
               read RIP s = word(pc + 0x9c0) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               read R14 s = word 0xffffffff /\
               read R15 s = word 0xffffffff00000001 /\
               read RAX s = x0 /\ read RBP s = x1 /\ read RCX s = x2 /\ read R10 s = x3 /\
               read R12 s = y0 /\ read R13 s = y1 /\ read R8 s = y2 /\ read R9 s = y3)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (bignum_of_wordlist [x0;x1;x2;x3] < p_256 /\
                bignum_of_wordlist [y0;y1;y2;y3] < p_256
                ==> &(bignum_of_wordlist [read R12 s; read R13 s; read R8 s; read R9 s]) =
                      (&(bignum_of_wordlist [x0;x1;x2;x3]) -
                       &(bignum_of_wordlist [y0;y1;y2;y3])) rem &p_256))
          (MAYCHANGE [RIP; RSP; RAX; RCX; RBP; R8; R9; R10; R11; R12; R13] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`x0:int64`; `x1:int64`; `x2:int64`; `x3:int64`;
    `y0:int64`; `y1:int64`; `y2:int64`; `y3:int64`;
    `pc:num`; `tbl:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY ABBREV_TAC
   [`m = bignum_of_wordlist [x0;x1;x2;x3]`; `n = bignum_of_wordlist [y0;y1;y2;y3]`] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_ACCSTEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC [1;2;4;5] (1--5) THEN
  SUBGOAL_THEN `carry_s5 <=> m:num < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC [8;10;11;13] (6--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `--(&(bitval(m:num < n))):int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
  REWRITE_TAC[INT_ARITH `m - n:int = --b * p + z <=> z = b * p + m - n`] THEN
  REWRITE_TAC[int_eq; int_le; int_lt] THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th; int_sub_th] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC(REAL_ARITH
  `!t:real. p < t /\
            (&0 <= a /\ a < p) /\
            (&0 <= z /\ z < t) /\
            ((&0 <= z /\ z < t) /\ (&0 <= a /\ a < t) ==> z = a)
            ==> z = a /\ &0 <= z /\ z < p`) THEN
  EXISTS_TAC `(&2:real) pow 256` THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m:num < p_256`; `n:num < p_256`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_256] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* What the coordinates mean, and the table the body reads.                  *)
(* ------------------------------------------------------------------------- *)

(* A Jacobian triple, or an affine pair, in Montgomery form, coordinates below
   p_256, representing a point of P-256, as s2n-bignum's p256_montjmixadd
   states them. *)
let represents_p256 = new_definition
 `represents_p256 P (x,y,z) <=>
        x < p_256 /\ y < p_256 /\ z < p_256 /\
        weierstrass_of_jacobian (integer_mod_ring p_256)
         (tripled (montgomery_decode (256,p_256)) (x,y,z)) = P`;;

let represents2_p256 = new_definition
 `represents2_p256 P (x,y) <=>
        x < p_256 /\ y < p_256 /\
        SOME(paired (montgomery_decode (256,p_256)) (x,y)) = P`;;

(* The table: the first 200 bytes of the object's .rodata, rind's POLY
   static. The section runs on to 208 bytes, padding that the linked binary
   may give to other data, so the theorems assume only these. *)
let nistz256_poly_bytes data =
  mk_list(fst(chop_list 200 (dest_list(rand(concl data)))),`:byte`);;

let ecp_nistz256_point_add_affine_poly = new_definition
  (mk_eq(`ecp_nistz256_point_add_affine_poly:byte list`,
         nistz256_poly_bytes ecp_nistz256_point_add_affine_data));;

let NISTZ256_POLY_DEFS = [ecp_nistz256_point_add_affine_poly];;

let NISTZ256_POLY_LENGTH = prove
 (`LENGTH ecp_nistz256_point_add_affine_poly = 200`,
  REWRITE_TAC NISTZ256_POLY_DEFS THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN
  REFL_TAC);;

let NISTZ256_POLY_LOADED = prove
 (`!s tab. bytes_loaded s tab ecp_nistz256_point_add_affine_poly <=>
           read (memory :> bytes(tab,200)) s =
           num_of_bytelist ecp_nistz256_point_add_affine_poly`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; NISTZ256_POLY_LENGTH]);;

(* The words of the table the body and the helpers read: p_256's second and
   fourth words, and the two halves of the 1 in Montgomery form. *)
let NISTZ256_POLY_TABLE_FACTS = prove
 (`!s tbl. bytes_loaded s (word tbl) ecp_nistz256_point_add_affine_poly
     ==> read (memory :> bytes64 (word(tbl + 8))) s = word 0xffffffff /\
         read (memory :> bytes64 (word(tbl + 24))) s = word 0xffffffff00000001 /\
         read (memory :> bytes128 (word(tbl + 128))) s =
           word 0xffffffff000000000000000000000001 /\
         read (memory :> bytes128 (word(tbl + 144))) s =
           word 0x00000000fffffffeffffffffffffffff`,
  REPEAT GEN_TAC THEN REWRITE_TAC NISTZ256_POLY_DEFS THEN
  ONCE_REWRITE_TAC[ARITH_RULE `tbl = tbl + 0`] THEN
  CONV_TAC(LAND_CONV DATA64_CONV) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  STRIP_TAC THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT); GSYM WORD_ADD] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The field algebra, from s2n-bignum's x86/proofs/p256_montjmixadd.ml       *)
(* (Apache-2.0 OR ISC OR MIT-0), which proves the same formulas.             *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_256 ==> x < p_256 /\ &x = &a rem &p_256`,
  REWRITE_TAC[INT_OF_NUM_REM; p_256] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_256 ==> x < p_256 /\ &x = a rem &p_256`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_256] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_256 = (&i * x rem &p_256 * y rem &p_256) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_256 = (&(NUMERAL n) * &x rem &p_256) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_256 (2 EXP 256)) *
    (&2 pow 256 * x) rem &p_256 * (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * x * y) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_256] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 256 * x) rem &p_256 + (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * (x + y)) rem &p_256 /\
   ((&2 pow 256 * x) rem &p_256 - (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * (x - y)) rem &p_256 /\
   (&(NUMERAL n) * (&2 pow 256 * x) rem &p_256) rem &p_256 =
   (&2 pow 256 * (&(NUMERAL n) * x)) rem &p_256`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_256 (2 EXP 256)) * (&2 pow 256 * x) rem &p_256) rem &p_256 =
   x rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_256
         ==> x =
             (2 EXP 256 * (inverse_mod p_256 (2 EXP 256) * x) MOD p_256) MOD
             p_256`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_affine_p256 = prove
 (`weierstrass_of_jacobian (integer_mod_ring p_256)
                           (x rem &p_256,y rem &p_256,&1 rem &p_256) =
   SOME(x rem &p_256,y rem &p_256)`,
  MP_TAC(ISPEC `integer_mod_ring p_256` RING_INV_1) THEN
  REWRITE_TAC[weierstrass_of_jacobian; ring_div; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[p_256] THEN CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[GSYM p_256; option_INJ; PAIR_EQ; INT_MUL_RID; INT_REM_REM]);;

let weierstrass_of_jacobian_p256_add = prove
 (`!P1 P2 x1 y1 z1 x2 y2 z2 x3 y3 z3.
        ~(weierstrass_of_jacobian (integer_mod_ring p_256)
           (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) =
          weierstrass_of_jacobian (integer_mod_ring p_256)
           (x2 rem &p_256,y2 rem &p_256,z2 rem &p_256)) /\
        jacobian_add_unexceptional nistp256
         (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256)
         (x2 rem &p_256,y2 rem &p_256,z2 rem &p_256) =
        (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256)
        ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) = P1 /\
            weierstrass_of_jacobian (integer_mod_ring p_256)
                (x2 rem &p_256,y2 rem &p_256,z2 rem &p_256) = P2
            ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                  (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256) =
                group_mul p256_group P1 P2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[nistp256; P256_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    W(MP_TAC o PART_MATCH (rand o rand) WEIERSTRASS_OF_JACOBIAN_EQ o
      rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P256] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_256; b_256] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the body.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The instantiation of a helper lemma's variables that makes its
   precondition's equations hold in state sname, read off the assumptions. *)
let nistz256_helper_inst lemma sname asl =
  let avs,bod = strip_forall(concl lemma) in
  let ens = if is_imp bod then rand bod else bod in
  let pre = rand(rator(rator ens)) in
  let sv,prebody = dest_abs pre in
  let s = mk_var(sname,`:x86state`) in
  let conjs = conjuncts(subst [s,sv] prebody) in
  let asms = map (concl o snd) asl in
  let norm t = try rand(concl(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV t))
               with Failure _ -> t in
  let rec loop binds =
    let step binds c =
      if not (is_eq c) then binds else
      let l,r = dest_eq c in
      if not (mem r avs) || can (rev_assoc r) binds then binds else
      let l' = norm(subst binds l) in
      if exists (fun v -> vfree_in v l') (subtract avs (map snd binds)) then binds else
      try let a = find (fun a -> is_eq a && lhs a = l') asms in (rhs a,r)::binds
      with Failure _ -> binds in
    let binds' = itlist (fun c b -> step b c) conjs binds in
    if length binds' = length binds then binds else loop binds' in
  let binds = loop [`pc:num`,`pc:num`; `tbl:num`,`tbl:num`] in
  map (fun v -> try rev_assoc v binds
                with Failure _ -> failwith ("helper_inst: no value for "^string_of_term v)) avs;;


let NISTZ256_RSP_RESTORE = WORD_RULE
  `word_add (word_sub x (word 8)) (word 8):int64 = x`;;

let NISTZ256_SUBWORD_JOIN_128 = prove
 (`(!(h:int128) (l:int128). word_subword (word_join h l:256 word) (0,128):int128 = l) /\
   (!(h:int128) (l:int128). word_subword (word_join h l:256 word) (128,128):int128 = h)`,
  CONV_TAC WORD_BLAST);;

let NISTZ256_SUBWORD_JOIN_64 = prove
 (`(!(h:int64) (l:int64). word_subword (word_join h l:int128) (0,64):int64 = l) /\
   (!(h:int64) (l:int64). word_subword (word_join h l:int128) (64,64):int64 = h)`,
  CONV_TAC WORD_BLAST);;

let NISTZ256_ZX_ZX_128 = prove
 (`!x:int64. word_zx (word_zx x:int128):int64 = x`, CONV_TAC WORD_BLAST);;

(* The SSE moves write a YMM register's low half; this reads back what they
   wrote. *)
let NISTZ256_NORM_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[NISTZ256_SUBWORD_JOIN_128; NISTZ256_ZX_ZX_128]);;

let NISTZ256_STEPS_TAC exec ns =
  MAP_EVERY (fun n -> X86_STEPS_TAC exec [n] THEN NISTZ256_NORM_TAC) ns;;

(* Steps the CALL at step n into the helper and over it, landing in s(n+1),
   and names the result registers regs name_0, name_1, ... *)
let NISTZ256_CALL_TAC exec lemma n regs name =
  let sn = "s"^string_of_int n and sn' = "s"^string_of_int(n+1) in
  let s' = mk_var(sn',`:x86state`) in
  X86_STEPS_TAC exec [n] THEN
  (fun (asl,w) ->
     let inst = nistz256_helper_inst lemma sn asl in
     MP_TAC(SPECL inst lemma) (asl,w)) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  (fun (asl,w) ->
     if is_imp(lhand w) then
       (ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC]) (asl,w)
     else ALL_TAC (asl,w)) THEN
  X86_BIGSTEP_TAC exec sn' THEN
  (fun (asl,w as g) ->
     if (try fst(dest_const(fst(strip_comb w))) = "eventually" with Failure _ -> false)
     then ALL_TAC g
     else (ASM_REWRITE_TAC[] THEN
           CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
           ASM_REWRITE_TAC[] THEN NO_TAC) g) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NISTZ256_RSP_RESTORE]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  MAP_EVERY (fun (i,r) ->
    ABBREV_TAC(mk_eq(mk_var(name^"_"^string_of_int i,`:int64`),
                     list_mk_comb(`read:(x86state,int64)component->x86state->int64`,[r;s']))))
   (zip (0--(length regs - 1)) regs);;

let NISTZ256_READ_BYTES128_SPLIT = prove
 (`!a (h:int64) (l:int64) s.
     read (memory :> bytes128 a) s = word_join h l
     ==> read (memory :> bytes64 a) s = l /\
         read (memory :> bytes64 (word_add a (word 8))) s = h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)] THEN
  DISCH_THEN(fun th ->
    MP_TAC(AP_TERM `\x:int128. word_subword x (0,64):int64` th) THEN
    MP_TAC(AP_TERM `\x:int128. word_subword x (64,64):int64` th)) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[NISTZ256_SUBWORD_JOIN_64] THEN SIMP_TAC[]);;

(* Each 128-bit stack fact joining two 64-bit words also as two 64-bit facts,
   for the helpers, which read the stack 64 bits at a time. *)
let NISTZ256_STACK_SPLIT_TAC =
  let pat = `read (memory :> bytes128 (word_add stackpointer (word n))) s =
             word_join (h:int64) (l:int64)` in
  EVERY_ASSUM (fun th ->
    if can (term_match [] pat) (concl th) then
      STRIP_ASSUME_TAC(CONV_RULE(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                         (MATCH_MP NISTZ256_READ_BYTES128_SPLIT th))
    else ALL_TAC);;

(* The 128-bit stack words at the offsets offs in state sname from the 64-bit
   words the helpers wrote there, for the SSE loads that read them. *)
let NISTZ256_STACK_MERGE_TAC sname offs (asl,w as g) =
  let s = mk_var(sname,`:x86state`) in
  let pat = `read (memory :> bytes64 a) s = (y:int64)` in
  let facts = filter (fun th -> can (term_match [] pat) (concl th) && rand(lhand(concl th)) = s)
                     (map snd asl) in
  let one k =
    let tm = subst [mk_small_numeral k, `n:num`; s, `s:x86state`]
               `read (memory :> bytes128 (word_add stackpointer (word n))) s` in
    let th = (REWR_CONV (CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)) THENC
              DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) tm in
    ASSUME_TAC(REWRITE_RULE facts th) in
  MAP_EVERY one offs g;;

(* Rewrites the mask in the low half of reg at state sname, which the code
   computes from v with PCMPEQD, PSHUFD and POR, as a select between all
   ones and zero on v = 0. *)
let NISTZ256_MASK_TAC reg sname v (asl,w as g) =
  let s = mk_var(sname,`:x86state`) in
  let l = mk_comb(mk_comb(`read:(x86state,256 word)component->x86state->256 word`, reg), s) in
  let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l) asl) in
  let e = rand(rhs(concl th)) in
  let vv = `v:int128` in
  let e' = subst [vv,v] e in
  let goal = mk_forall(vv, mk_eq(e',
     `if (v:int128) = word 0 then word 340282366920938463463374607431768211455 else word 0:int128`)) in
  let conds = setify(map (fun t -> rand(rator(rator t))) (find_terms is_cond e')) in
  let cths = map (fun c -> prove(mk_eq(c, `(v:int128) = word 0`), BITBLAST_TAC)) conds in
  let lemma = prove(goal, GEN_TAC THEN REWRITE_TAC cths THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV) in
  RULE_ASSUM_TAC(REWRITE_RULE[SPEC v lemma]) g;;

let NISTZ256_READ_BYTES128_SPLIT_GEN = prove
 (`!a (v:int128) s.
     read (memory :> bytes128 a) s = v
     ==> read (memory :> bytes64 a) s = word_subword v (0,64) /\
         read (memory :> bytes64 (word_add a (word 8))) s = word_subword v (64,64)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[NISTZ256_SUBWORD_JOIN_64]);;

let NISTZ256_SUBWORD_PUSH_64 = prove
 (`(!x y:int128. word_subword (word_or x y) (0,64):int64 =
                 word_or (word_subword x (0,64)) (word_subword y (0,64))) /\
   (!x y:int128. word_subword (word_or x y) (64,64):int64 =
                 word_or (word_subword x (64,64)) (word_subword y (64,64))) /\
   (!x y:int128. word_subword (word_and x y) (0,64):int64 =
                 word_and (word_subword x (0,64)) (word_subword y (0,64))) /\
   (!x y:int128. word_subword (word_and x y) (64,64):int64 =
                 word_and (word_subword x (64,64)) (word_subword y (64,64))) /\
   (!x:int128. word_subword (word_not x) (0,64):int64 = word_not (word_subword x (0,64))) /\
   (!x:int128. word_subword (word_not x) (64,64):int64 = word_not (word_subword x (64,64)))`,
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let NISTZ256_SUBWORD_COND_64 = prove
 (`!b (x:int128) y k. word_subword (if b then x else y) (k,64):int64 =
                      if b then word_subword x (k,64) else word_subword y (k,64)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let NISTZ256_MASK_SIMP_64 = prove
 (`(!x:int64. word_and (word 18446744073709551615) x = x) /\
   (!x:int64. word_and (word 0) x = word 0) /\
   (!x:int64. word_or (word 0) x = x) /\
   (!x:int64. word_or x (word 0) = x) /\
   word_not (word 18446744073709551615:int64) = word 0 /\
   word_not (word 0:int64) = word 18446744073709551615`,
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* Each 128-bit store to p1 as two 64-bit words, the masks pushed into each. *)
let NISTZ256_P1_SPLIT_TAC sname =
  let pat = `read (memory :> bytes128 a) s = (v:int128)` in
  let s = mk_var(sname,`:x86state`) in
  let simp = CONV_RULE(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
     REWRITE_CONV[NISTZ256_SUBWORD_PUSH_64; NISTZ256_SUBWORD_COND_64;
                  NISTZ256_SUBWORD_JOIN_64] THENC
     DEPTH_CONV WORD_NUM_RED_CONV) in
  EVERY_ASSUM (fun th ->
    let c = concl th in
    if can (term_match [] pat) c && rand(lhand c) = s && vfree_in `p1:int64` (lhand c) then
      STRIP_ASSUME_TAC(simp(MATCH_MP NISTZ256_READ_BYTES128_SPLIT_GEN th))
    else ALL_TAC);;

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

(* ------------------------------------------------------------------------- *)
(* The body, from after the prologue at 0x11 to the epilogue at 0x538.       *)
(* ------------------------------------------------------------------------- *)

(* The body's 17 helper calls each step over the helper's lemma, naming its
   result; the doubling between them is inline. The masks that select the
   result for the two infinities are computed at s52 and applied at the end,
   where the three cases split. The stack frame, at stackpointer, must be
   16-byte aligned, since the body's MOVDQA stores and loads require it,
   and so must the table, which two PANDs read. *)
let ECP_NISTZ256_POINT_ADD_AFFINE_BODY = time prove_steps
 (`!p1 p2 x1 y1 z1 x2 y2 pc tbl stackpointer.
     aligned 16 stackpointer /\
     aligned 16 (word tbl:int64) /\
     riprel32_within_bounds tbl (pc + 893) /\
     riprel32_within_bounds tbl (pc + 885) /\
     riprel32_within_bounds tbl (pc + 1381) /\
     riprel32_within_bounds tbl (pc + 1384) /\
     riprel32_within_bounds tbl (pc + 2146) /\
     riprel32_within_bounds tbl (pc + 2137) /\
     ALL (nonoverlapping (word_sub stackpointer (word 8),496))
         [(word pc,0x9fe); (word tbl,200); (p1,96); (p2,64)] /\
     ALL (nonoverlapping (p1,96)) [(word pc,0x9fe); (word tbl,200); (p2,64)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (ecp_nistz256_point_add_affine_mc pc tbl) /\
               read RIP s = word(pc + 0x11) /\
               read RSP s = stackpointer /\
               bytes_loaded s (word tbl) ecp_nistz256_point_add_affine_poly /\
               read RDI s = p1 /\ read RSI s = p1 /\ read RDX s = p2 /\
               bignum_triple_from_memory (p1,4) s = (x1,y1,z1) /\
               bignum_pair_from_memory (p2,4) s = (x2,y2))
          (\s. read RIP s = word(pc + 0x538) /\
               read RSP s = stackpointer /\
               (x1 < p_256 /\ y1 < p_256 /\ z1 < p_256 /\ x2 < p_256 /\ y2 < p_256
                ==> (x2 = 0 /\ y2 = 0
                     ==> bignum_triple_from_memory (p1,4) s = (x1,y1,z1)) /\
                    (~(x2 = 0 /\ y2 = 0) /\ z1 = 0
                     ==> bignum_triple_from_memory (p1,4) s =
                         (x2,y2,2 EXP 256 MOD p_256)) /\
                    (~(x2 = 0 /\ y2 = 0) /\ ~(z1 = 0)
                     ==> !P1 P2. represents_p256 P1 (x1,y1,z1) /\
                                 represents2_p256 P2 (x2,y2) /\ ~(P1 = P2)
                                 ==> represents_p256 (group_mul p256_group P1 P2)
                                      (bignum_triple_from_memory (p1,4) s))))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; RBP;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p1,96);
                      memory :> bytes(word_sub stackpointer (word 8),8);
                      memory :> bytes(stackpointer,488)])`,
 [
  (MAP_EVERY X_GEN_TAC
   [`p1:int64`; `p2:int64`; `x1:num`; `y1:num`; `z1:num`; `x2:num`; `y2:num`;
    `pc:num`; `tbl:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS; PAIR_EQ;
              bignum_pair_from_memory; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var("ymm"^string_of_int n,`:int256`))
                                      (parse_term("read YMM"^string_of_int n))) (0--5) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NISTZ256_POLY_TABLE_FACTS) THEN
  BIGNUM_LDIGITIZE_TAC "x1_" `read (memory :> bytes (p1,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y1_" `read (memory :> bytes (word_add p1 (word 32),8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "z1_" `read (memory :> bytes (word_add p1 (word 64),8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "x2_" `read (memory :> bytes (p2,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y2_" `read (memory :> bytes (word_add p2 (word 32),8 * 4)) s0`);
  (MEMORY_128_FROM_64_TAC "p1" 0 6 THEN MEMORY_128_FROM_64_TAC "p2" 0 4 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN STRIP_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (1--37) THEN NISTZ256_STACK_SPLIT_TAC);
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SQR_MONTQ_CORRECT 38 [`R12`;`R13`;`R14`;`R15`] "zsq" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (40--52));
  (NISTZ256_MASK_TAC `YMM5` "s52" `word_or (word_join (z1_3:int64) (z1_2:int64):int128) (word_join (z1_1:int64) (z1_0:int64))`);
  (NISTZ256_MASK_TAC `YMM4` "s52" `word_or (word_or (word_join (y2_3:int64) (y2_2:int64):int128) (word_join (y2_1:int64) (y2_0:int64)))
                                  (word_or (word_join (x2_3:int64) (x2_2:int64):int128) (word_join (x2_1:int64) (x2_0:int64)))`);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (53--55));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_MUL_MONTQ_CORRECT 56 [`R12`;`R13`;`R8`;`R9`] "u2" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (58--59));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SUB_FROMQ_CORRECT 60 [`R12`;`R13`;`R8`;`R9`] "h" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (62--69));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_MUL_MONTQ_CORRECT 70 [`R12`;`R13`;`R8`;`R9`] "s2a" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (72--79));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_MUL_MONTQ_CORRECT 80 [`R12`;`R13`;`R8`;`R9`] "resz" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (82--89));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_MUL_MONTQ_CORRECT 90 [`R12`;`R13`;`R8`;`R9`] "s2" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (92--93));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SUB_FROMQ_CORRECT 94 [`R12`;`R13`;`R8`;`R9`] "r" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (96--101));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SQR_MONTQ_CORRECT 102 [`R12`;`R13`;`R14`;`R15`] "hsq" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (104--109));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SQR_MONTQ_CORRECT 110 [`R12`;`R13`;`R14`;`R15`] "rsq" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (112--119));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_MUL_MONTQ_CORRECT 120 [`R12`;`R13`;`R8`;`R9`] "hcub" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (122--129));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_MUL_MONTQ_CORRECT 130 [`R12`;`R13`;`R8`;`R9`] "u2b" THEN NISTZ256_NORM_TAC);
  (X86_ACCSTEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC [133;135;137;138;141;143;144;146;147] (132--155));
  (SUBGOAL_THEN `bignum_of_wordlist [u2b_0;u2b_1;u2b_2;u2b_3] < p_256
   ==> bignum_of_wordlist [read R12 s155; read R13 s155; read R8 s155; read R9 s155] =
       (2 * bignum_of_wordlist [u2b_0;u2b_1;u2b_2;u2b_3]) MOD p_256` MP_TAC);
  (ASM_REWRITE_TAC[] THEN ABBREV_TAC `u = bignum_of_wordlist [u2b_0;u2b_1;u2b_2;u2b_3]` THEN DISCH_TAC);
  (SUBGOAL_THEN `carry_s147 <=> 2 * u < p_256` SUBST1_TAC);
  (MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; VAL_WORD_BITVAL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]);
  (SUBGOAL_THEN `2 * u < 2 * p_256` ASSUME_TAC THENL [UNDISCH_TAC `u < p_256` THEN ARITH_TAC; ALL_TAC]);
  (CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC [`256`; `if 2 * u < p_256 then &(2 * u):real else &(2 * u) - &p_256`] THEN
  REPEAT CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH lhand BIGNUM_OF_WORDLIST_BOUND_LENGTH o lhand o snd) THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]]);
  (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "u" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);
  (DISCH_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  MAP_EVERY (fun (n,r) -> ABBREV_TAC(mk_eq(mk_var("dbl_"^string_of_int n,`:int64`),
        list_mk_comb(`read:(x86state,int64)component->x86state->int64`,[r;`s155:x86state`]))))
   [0,`R12`; 1,`R13`; 2,`R8`; 3,`R9`]);
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SUBQ_CORRECT 156 [`R12`;`R13`;`R8`;`R9`] "rmu" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (158--159));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SUB_FROMQ_CORRECT 160 [`R12`;`R13`;`R8`;`R9`] "resx" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (162--166));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SUBQ_CORRECT 167 [`R12`;`R13`;`R8`;`R9`] "t" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (169--180));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_MUL_MONTQ_CORRECT 181 [`R12`;`R13`;`R8`;`R9`] "s2b" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (183--190));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_MUL_MONTQ_CORRECT 191 [`R12`;`R13`;`R8`;`R9`] "tr" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (193--194));
  (NISTZ256_CALL_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC ECP_NISTZ256_SUB_FROMQ_CORRECT 195 [`R12`;`R13`;`R8`;`R9`] "resy" THEN NISTZ256_NORM_TAC);
  (NISTZ256_STACK_MERGE_TAC "s196" [224;240;256;272;288;304]);
  (SUBGOAL_THEN `aligned 16 (word(tbl + 128):int64) /\ aligned 16 (word(tbl + 144):int64)`
     STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   RIPREL_TAC 1021 893 THEN RIPREL_TAC 1029 885);
  (NISTZ256_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (197--263));
  (RULE_ASSUM_TAC(REWRITE_RULE[YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (NISTZ256_P1_SPLIT_TAC "s263");
  (CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  W(fun (asl,w) -> REWRITE_TAC (filter (fun th ->
      let c = concl th in
      can (term_match [] `read (memory :> bytes64 a) s263 = (v:int64)`) c &&
      vfree_in `p1:int64` (lhand c)) (map snd asl))) THEN
  REWRITE_TAC[WORD_ADD_0]);
  (SUBGOAL_THEN `(word_or (word_join (z1_3:int64) (z1_2:int64)) (word_join (z1_1:int64) (z1_0:int64)):int128 = word 0) <=> z1 = 0`
   SUBST1_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `bignum_of_wordlist [z1_0; z1_1; z1_2; z1_3] = z1`)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN BITBLAST_TAC; ALL_TAC]);
  (SUBGOAL_THEN `(word_or (word_or (word_join (y2_3:int64) (y2_2:int64)) (word_join (y2_1:int64) (y2_0:int64)))
                         (word_or (word_join (x2_3:int64) (x2_2:int64)) (word_join (x2_1:int64) (x2_0:int64))):int128 = word 0) <=> x2 = 0 /\ y2 = 0`
   SUBST1_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `bignum_of_wordlist [x2_0; x2_1; x2_2; x2_3] = x2`);
                SYM(ASSUME `bignum_of_wordlist [y2_0; y2_1; y2_2; y2_3] = y2`)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN BITBLAST_TAC; ALL_TAC]);
  (STRIP_TAC THEN REPEAT CONJ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[NISTZ256_MASK_SIMP_64]);
  (REWRITE_TAC[bignum_of_wordlist; p_256] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);
  (DISCARD_STATE_TAC "s263" THEN DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read c s = x`] THEN
  MAP_EVERY (fun v ->
    let l = mk_list(map (fun i -> mk_var(v^"_"^string_of_int i,`:int64`)) (0--3),`:int64`) in
    let eq = mk_eq(mk_comb(`bignum_of_wordlist`,l), mk_var(v,`:num`)) in
    FIRST_X_ASSUM(fun th -> if concl th = eq then SUBST_ALL_TAC th else failwith "")) ["x1";"y1";"z1";"x2";"y2"] THEN
  MAP_EVERY (fun v ->
    let l = mk_list(map (fun i -> mk_var(v^"_"^string_of_int i,`:int64`)) (0--3),`:int64`) in
    ABBREV_TAC(mk_eq(mk_var(v,`:num`), mk_comb(`bignum_of_wordlist`,l))))
   ["zsq";"u2";"h";"s2a";"resz";"s2";"r";"hsq";"rsq";"hcub";"u2b";"dbl";"rmu";"resx";"t";"s2b";"tr";"resy"]);
  (MAP_EVERY X_GEN_TAC [`P1:(int#int)option`; `P2:(int#int)option`] THEN
  REWRITE_TAC[represents_p256; represents2_p256; tripled; paired] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_256] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_256]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]));
  (ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma)
   [`y2:num`; `x2:num`; `z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_256 (2 EXP 256) * x1`;
    `y1d = inverse_mod p_256 (2 EXP 256) * y1`;
    `z1d = inverse_mod p_256 (2 EXP 256) * z1`;
    `x2d = inverse_mod p_256 (2 EXP 256) * x2`;
    `y2d = inverse_mod p_256 (2 EXP 256) * y2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REM_DOWN_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_ADD_REM; GSYM INT_SUB_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[lemont; demont]) THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_REM_REM] THEN
  REWRITE_TAC[pumont; dismont; unmont]);
  (FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [GSYM
    weierstrass_of_affine_p256]) THEN
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p256_add THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_add_unexceptional; nistp256;
                  INTEGER_MOD_RING_CLAUSES]);
  (SUBGOAL_THEN `~(&z1d rem &p_256 = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(&z1:int = &0)` THEN ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
    REWRITE_TAC[INT_REM_EQ_0] THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[p_256] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_256] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC)
 ]);;

(* ------------------------------------------------------------------------- *)
(* The whole function, with its prologue and epilogue.                       *)
(* ------------------------------------------------------------------------- *)

let NISTZ256_SUB_SUB_NUM = prove
 (`!x:int64 a b. word_sub (word_sub x (word a)) (word b) = word_sub x (word(a + b))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* The frame's offsets below stackpointer as the epilogue's addresses state
   them, offsets above it modulo 2^64. *)
let NISTZ256_FRAME_OFFSETS = map
  (fun k -> WORD_BLAST(parse_term(
     "!x:int64. word_sub x (word " ^ string_of_int k ^ ") = word_add x (word " ^
     string_of_num(num_of_string "18446744073709551616" -/ num_of_string(string_of_int k)) ^ ")")))
  [8; 16; 24; 32; 40; 48; 536; 544];;

(* ECP_NISTZ256_POINT_ADD_AFFINE_SUBROUTINE_CORRECT: called with the System V
   ABI, in place, with p1 the Jacobian point and p2 the affine one, both in
   Montgomery form with coordinates below p_256, the function leaves at p1
   - p1 itself when p2 is (0,0), the affine encoding of infinity;
   - p2 with z the Montgomery form of 1 when p1's z is 0, the Jacobian
     infinity;
   - otherwise a Jacobian triple for the sum of the points they represent,
     unless those are equal, which these formulas cannot double.
   Its stack frame, 544 bytes below the return address, is 16-byte aligned
   whenever the caller's stack is, as the ABI requires at a call. The table,
   rind's `POLY`, is 16-byte aligned too. *)
let ECP_NISTZ256_POINT_ADD_AFFINE_SUBROUTINE_CORRECT = time prove_steps
 (`!p1 p2 x1 y1 z1 x2 y2 pc tbl stackpointer returnaddress.
     aligned 16 (word_add stackpointer (word 8)) /\
     aligned 16 (word tbl:int64) /\
     riprel32_within_bounds tbl (pc + 893) /\
     riprel32_within_bounds tbl (pc + 885) /\
     riprel32_within_bounds tbl (pc + 1381) /\
     riprel32_within_bounds tbl (pc + 1384) /\
     riprel32_within_bounds tbl (pc + 2146) /\
     riprel32_within_bounds tbl (pc + 2137) /\
     ALL (nonoverlapping (word_sub stackpointer (word 544),552))
         [(word pc,0x9fe); (word tbl,200); (p1,96); (p2,64)] /\
     ALL (nonoverlapping (p1,96)) [(word pc,0x9fe); (word tbl,200); (p2,64)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (ecp_nistz256_point_add_affine_mc pc tbl) /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               bytes_loaded s (word tbl) ecp_nistz256_point_add_affine_poly /\
               C_ARGUMENTS [p1; p1; p2] s /\
               bignum_triple_from_memory (p1,4) s = (x1,y1,z1) /\
               bignum_pair_from_memory (p2,4) s = (x2,y2))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (x1 < p_256 /\ y1 < p_256 /\ z1 < p_256 /\ x2 < p_256 /\ y2 < p_256
                ==> (x2 = 0 /\ y2 = 0
                     ==> bignum_triple_from_memory (p1,4) s = (x1,y1,z1)) /\
                    (~(x2 = 0 /\ y2 = 0) /\ z1 = 0
                     ==> bignum_triple_from_memory (p1,4) s =
                         (x2,y2,2 EXP 256 MOD p_256)) /\
                    (~(x2 = 0 /\ y2 = 0) /\ ~(z1 = 0)
                     ==> !P1 P2. represents_p256 P1 (x1,y1,z1) /\
                                 represents2_p256 P2 (x2,y2) /\ ~(P1 = P2)
                                 ==> represents_p256 (group_mul p256_group P1 P2)
                                      (bignum_triple_from_memory (p1,4) s))))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p1,96);
                      memory :> bytes(word_sub stackpointer (word 544),544)])`,
 [
  (MAP_EVERY X_GEN_TAC
    [`p1:int64`; `p2:int64`; `x1:num`; `y1:num`; `z1:num`; `x2:num`; `y2:num`;
     `pc:num`; `tbl:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
   REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS] THEN STRIP_TAC THEN
   SUBGOAL_THEN `aligned 16 (word_sub stackpointer (word 536):int64)` ASSUME_TAC THENL
    [SUBGOAL_THEN `word_sub stackpointer (word 536):int64 =
                   word_sub (word_add stackpointer (word 8)) (word 544)` SUBST1_TAC THENL
      [CONV_TAC WORD_RULE; CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]];
     ALL_TAC]);
  (REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS; PAIR_EQ;
               bignum_pair_from_memory; bignum_triple_from_memory] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
   CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
   ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
   ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
   ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
   ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
   ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
   ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
   ENSURES_INIT_TAC "s0");
  (* Steps keep reads of bytes, not bytes_loaded, so the table goes as one. *)
  (FIRST_X_ASSUM(MP_TAC o check (can (term_match []
     `bytes_loaded s (word tbl) ecp_nistz256_point_add_affine_poly`) o concl)) THEN
   REWRITE_TAC[NISTZ256_POLY_LOADED] THEN DISCH_TAC);
  (X86_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (1--7) THEN
   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV(REWR_CONV NISTZ256_SUB_SUB_NUM THENC
                                          RAND_CONV(RAND_CONV NUM_ADD_CONV)))));
  (MP_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES; NISTZ256_POLY_LOADED; SOME_FLAGS]
     (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
       (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
         (REWRITE_RULE[PAIR_EQ; bignum_pair_from_memory; bignum_triple_from_memory]
           (SPECL [`p1:int64`; `p2:int64`; `x1:num`; `y1:num`; `z1:num`;
                   `x2:num`; `y2:num`; `pc:num`; `tbl:num`;
                   `word_sub stackpointer (word 536):int64`]
                  ECP_NISTZ256_POINT_ADD_AFFINE_BODY))))) THEN
   REWRITE_TAC[NISTZ256_SUB_SUB_NUM] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
   ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC]);
  (X86_BIGSTEP_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC "s8");
  (* The epilogue reloads the saved registers relative to the frame's top. *)
  (ABBREV_TAC `x3 = read (memory :> bytes (p1,8 * 4)) s8` THEN
   ABBREV_TAC `y3 = read (memory :> bytes (word_add p1 (word 32),8 * 4)) s8` THEN
   ABBREV_TAC `z3 = read (memory :> bytes (word_add p1 (word 64),8 * 4)) s8` THEN
   X86_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC [9] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_sub (x:int64) (word 536)) (word 536) = x`]) THEN
   RULE_ASSUM_TAC(fun th ->
     if can (term_match [] `read (memory :> bytes64 (word_sub x (word k))) s = v`)
            (concl th)
     then REWRITE_RULE NISTZ256_FRAME_OFFSETS th else th) THEN
   X86_STEPS_TAC ECP_NISTZ256_POINT_ADD_AFFINE_EXEC (10--17));
  (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (RULE_ASSUM_TAC(REWRITE_RULE NISTZ256_FRAME_OFFSETS) THEN
   REWRITE_TAC NISTZ256_FRAME_OFFSETS THEN MONOTONE_MAYCHANGE_TAC)
 ]);;
