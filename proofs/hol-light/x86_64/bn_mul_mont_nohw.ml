(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Word-serial Montgomery multiplication on x86_64, as rind's build emits it. *)
(* ========================================================================= *)

(* rind's naked function low::x86_64::mont::bn_mul_mont_nohw is aws-lc's
   bn_mul_mont_nohw (crypto/fipsmodule/bn/asm/x86_64-mont.pl, its generic
   path), which rind runs for RSA's Montgomery products of any width from two
   words on CPUs without BMI2 and ADX, and for widths the 4x and 8x routines
   do not take. BN_MUL_MONT_NOHW_SUBROUTINE_CORRECT is that, called with the
   System V ABI, it writes to z the Montgomery product
   x * y / 2^(64k) mod m of the k-word x, y and m, given the word at n0p is
   -m^-1 mod 2^64, as s2n-bignum's bignum_montmul states it, and returns 1.

   The routine allocates its k + 1 word accumulator on the stack, aligned
   down to 1024 bytes and probed a page at a time, and saves the old stack
   pointer above it. The proof follows the code's shape:
   - NOHW_FIRST, the first outer iteration, 0x56 to 0x110, accumulates
     x * y[0] + q * m and shifts it down a word;
   - NOHW_OUTER, each later one, 0x110 to 0x1d0, adds x * y[i] + q * m to
     the accumulator, with q the word that zeroes its low word, so after
     iteration i, 2^(64(i+1)) * t = x * (y mod 2^(64(i+1))) + Q * m for some
     Q below 2^(64(i+1));
   - NOHW_TAIL, 0x1d0 to 0x22d, subtracts m once if that does not borrow,
     selects in constant time, and wipes the accumulator with k;
   - NOHW_BODY joins them, and BN_MUL_MONT_NOHW_SUBROUTINE_CORRECT adds the
     prologue, the probe loop, and the epilogue.
   The result is reduced only when x * y <= 2^(64k) * m, which x, y < m
   give, as they do for every caller in rind. *)

needs "x86/proofs/base.ml";;

(* admin/prove writes the function's object, as rind's release build emits
   it, to x86_64/bn_mul_mont_nohw.o: its whole section as .text, which has no
   relocations. The definition fails unless its instructions are these. *)
let bn_mul_mont_nohw_mc = define_assert_from_elf
  "bn_mul_mont_nohw_mc" "x86_64/bn_mul_mont_nohw.o"
[
  0x45; 0x89; 0xc9;        (* MOV (% r9d) (% r9d) *)
  0x48; 0x89; 0xe0;        (* MOV (% rax) (% rsp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0x89; 0xe3;        (* MOV (% r11) (% rsp) *)
  0x4e; 0x8d; 0x54; 0xcc; 0xf0;
                           (* LEA (% r10) (%%%% (rsp,3,r9,-- &16)) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0x81; 0xe2; 0x00; 0xfc; 0xff; 0xff;
                           (* AND (% r10) (Imm32 (word 4294966272)) *)
  0x4d; 0x29; 0xd3;        (* SUB (% r11) (% r10) *)
  0x49; 0x81; 0xe3; 0x00; 0xf0; 0xff; 0xff;
                           (* AND (% r11) (Imm32 (word 4294963200)) *)
  0x4b; 0x8d; 0x24; 0x1a;  (* LEA (% rsp) (%%% (r10,0,r11)) *)
  0x4c; 0x8b; 0x1c; 0x24;  (* MOV (% r11) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x39; 0xd4;        (* CMP (% rsp) (% r10) *)
  0x77; 0x04;              (* JA (Imm8 (word 4)) *)
  0xeb; 0x13;              (* JMP (Imm8 (word 19)) *)
  0x66; 0x90;              (* NOP *)
  0x48; 0x8d; 0xa4; 0x24; 0x00; 0xf0; 0xff; 0xff;
                           (* LEA (% rsp) (%% (rsp,18446744073709547520)) *)
  0x4c; 0x8b; 0x1c; 0x24;  (* MOV (% r11) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x39; 0xd4;        (* CMP (% rsp) (% r10) *)
  0x77; 0xef;              (* JA (Imm8 (word 239)) *)
  0x4a; 0x89; 0x44; 0xcc; 0x08;
                           (* MOV (Memop Quadword (%%%% (rsp,3,r9,&8))) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x4d; 0x8b; 0x00;        (* MOV (% r8) (Memop Quadword (%% (r8,0))) *)
  0x49; 0x8b; 0x1c; 0x24;  (* MOV (% rbx) (Memop Quadword (%% (r12,0))) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x4c; 0x89; 0xc5;        (* MOV (% rbp) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc2;        (* MOV (% r10) (% rax) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x0f; 0xaf; 0xea;  (* IMUL (% rbp) (% r10) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x4d; 0x8d; 0x7f; 0x01;  (* LEA (% r15) (%% (r15,1)) *)
  0xeb; 0x2a;              (* JMP (Imm8 (word 42)) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0x1f; 0x00;        (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x4a; 0x8b; 0x04; 0xfe;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r15))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x01; 0xdd;        (* ADD (% r13) (% r11) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4e; 0x89; 0x6c; 0xfc; 0xf0;
                           (* MOV (Memop Quadword (%%%% (rsp,3,r15,-- &16))) (% r13) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x4a; 0x8b; 0x04; 0xf9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r15))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x8d; 0x7f; 0x01;  (* LEA (% r15) (%% (r15,1)) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4d; 0x39; 0xcf;        (* CMP (% r15) (% r9) *)
  0x75; 0xc6;              (* JNE (Imm8 (word 198)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x01; 0xdd;        (* ADD (% r13) (% r11) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4e; 0x89; 0x6c; 0xfc; 0xf0;
                           (* MOV (Memop Quadword (%%%% (rsp,3,r15,-- &16))) (% r13) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x01; 0xdd;        (* ADD (% r13) (% r11) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4e; 0x89; 0x6c; 0xcc; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsp,3,r9,-- &8))) (% r13) *)
  0x4a; 0x89; 0x14; 0xcc;  (* MOV (Memop Quadword (%%% (rsp,3,r9))) (% rdx) *)
  0x4d; 0x8d; 0x76; 0x01;  (* LEA (% r14) (%% (r14,1)) *)
  0xeb; 0x01;              (* JMP (Imm8 (word 1)) *)
  0x90;                    (* NOP *)
  0x4b; 0x8b; 0x1c; 0xf4;  (* MOV (% rbx) (Memop Quadword (%%% (r12,3,r14))) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x4c; 0x89; 0xc5;        (* MOV (% rbp) (% r8) *)
  0x4c; 0x8b; 0x14; 0x24;  (* MOV (% r10) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x0f; 0xaf; 0xea;  (* IMUL (% rbp) (% r10) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x54; 0x24; 0x08;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x4d; 0x8d; 0x7f; 0x01;  (* LEA (% r15) (%% (r15,1)) *)
  0xeb; 0x20;              (* JMP (Imm8 (word 32)) *)
  0x66; 0x90;              (* NOP *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x4a; 0x8b; 0x04; 0xfe;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r15))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x01; 0xd5;        (* ADD (% r13) (% r10) *)
  0x4e; 0x8b; 0x14; 0xfc;  (* MOV (% r10) (Memop Quadword (%%% (rsp,3,r15))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4e; 0x89; 0x6c; 0xfc; 0xf0;
                           (* MOV (Memop Quadword (%%%% (rsp,3,r15,-- &16))) (% r13) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x4a; 0x8b; 0x04; 0xf9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r15))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x01; 0xda;        (* ADD (% r10) (% r11) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x8d; 0x7f; 0x01;  (* LEA (% r15) (%% (r15,1)) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4d; 0x39; 0xcf;        (* CMP (% r15) (% r9) *)
  0x75; 0xbe;              (* JNE (Imm8 (word 190)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x01; 0xd5;        (* ADD (% r13) (% r10) *)
  0x4e; 0x8b; 0x14; 0xfc;  (* MOV (% r10) (Memop Quadword (%%% (rsp,3,r15))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4e; 0x89; 0x6c; 0xfc; 0xf0;
                           (* MOV (Memop Quadword (%%%% (rsp,3,r15,-- &16))) (% r13) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x01; 0xdd;        (* ADD (% r13) (% r11) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4d; 0x01; 0xd5;        (* ADD (% r13) (% r10) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4e; 0x89; 0x6c; 0xcc; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsp,3,r9,-- &8))) (% r13) *)
  0x4a; 0x89; 0x14; 0xcc;  (* MOV (Memop Quadword (%%% (rsp,3,r9))) (% rdx) *)
  0x4d; 0x8d; 0x76; 0x01;  (* LEA (% r14) (%% (r14,1)) *)
  0x4d; 0x39; 0xce;        (* CMP (% r14) (% r9) *)
  0x0f; 0x82; 0x3a; 0xff; 0xff; 0xff;
                           (* JB (Imm32 (word 4294967098)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x4d; 0x89; 0xcf;        (* MOV (% r15) (% r9) *)
  0x4a; 0x1b; 0x04; 0xf1;  (* SBB (% rax) (Memop Quadword (%%% (rcx,3,r14))) *)
  0x4a; 0x89; 0x04; 0xf7;  (* MOV (Memop Quadword (%%% (rdi,3,r14))) (% rax) *)
  0x4a; 0x8b; 0x44; 0xf4; 0x08;
                           (* MOV (% rax) (Memop Quadword (%%%% (rsp,3,r14,&8))) *)
  0x4d; 0x8d; 0x76; 0x01;  (* LEA (% r14) (%% (r14,1)) *)
  0x49; 0xff; 0xcf;        (* DEC (% r15) *)
  0x75; 0xea;              (* JNE (Imm8 (word 234)) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0xc7; 0xc3; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm32 (word 4294967295)) *)
  0x48; 0x31; 0xc3;        (* XOR (% rbx) (% rax) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x4d; 0x89; 0xcf;        (* MOV (% r15) (% r9) *)
  0x4a; 0x8b; 0x0c; 0xf7;  (* MOV (% rcx) (Memop Quadword (%%% (rdi,3,r14))) *)
  0x4a; 0x8b; 0x14; 0xf4;  (* MOV (% rdx) (Memop Quadword (%%% (rsp,3,r14))) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x4e; 0x89; 0x0c; 0xf4;  (* MOV (Memop Quadword (%%% (rsp,3,r14))) (% r9) *)
  0x48; 0x09; 0xca;        (* OR (% rdx) (% rcx) *)
  0x4a; 0x89; 0x14; 0xf7;  (* MOV (Memop Quadword (%%% (rdi,3,r14))) (% rdx) *)
  0x4d; 0x8d; 0x76; 0x01;  (* LEA (% r14) (%% (r14,1)) *)
  0x49; 0x83; 0xef; 0x01;  (* SUB (% r15) (Imm8 (word 1)) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x4a; 0x8b; 0x74; 0xcc; 0x08;
                           (* MOV (% rsi) (Memop Quadword (%%%% (rsp,3,r9,&8))) *)
  0x48; 0xc7; 0xc0; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 1)) *)
  0x4c; 0x8b; 0x7e; 0xd0;  (* MOV (% r15) (Memop Quadword (%% (rsi,18446744073709551568))) *)
  0x4c; 0x8b; 0x76; 0xd8;  (* MOV (% r14) (Memop Quadword (%% (rsi,18446744073709551576))) *)
  0x4c; 0x8b; 0x6e; 0xe0;  (* MOV (% r13) (Memop Quadword (%% (rsi,18446744073709551584))) *)
  0x4c; 0x8b; 0x66; 0xe8;  (* MOV (% r12) (Memop Quadword (%% (rsi,18446744073709551592))) *)
  0x48; 0x8b; 0x6e; 0xf0;  (* MOV (% rbp) (Memop Quadword (%% (rsi,18446744073709551600))) *)
  0x48; 0x8b; 0x5e; 0xf8;  (* MOV (% rbx) (Memop Quadword (%% (rsi,18446744073709551608))) *)
  0x48; 0x8d; 0x26;        (* LEA (% rsp) (%% (rsi,0)) *)
  0xf3; 0xc3               (* RET *)
];;

let BN_MUL_MONT_NOHW_EXEC = X86_MK_EXEC_RULE bn_mul_mont_nohw_mc;;

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
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_DIGIT_READ = prove
 (`!p k s t i. bignum_from_memory(p,k) s = t /\ i < k
     ==> read (memory :> bytes64(word_add p (word(8 * i)))) s = word(bigdigit t i)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY; WORD_VAL]);;

let BIGNUM_DIGIT_READ_0 = prove
 (`!p k s t. bignum_from_memory(p,k) s = t /\ 0 < k
     ==> read (memory :> bytes64 p) s = word(bigdigit t 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:int64`; `k:num`; `s:x86state`; `t:num`; `0`] BIGNUM_DIGIT_READ) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0]);;

let BYTES_DIGIT_READ = prove
 (`!p k s t i. read (memory :> bytes(p,8 * k)) s = t /\ i < k
     ==> read (memory :> bytes64(word_add p (word(8 * i)))) s = word(bigdigit t i)`,
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_DIGIT_READ]);;

let BYTES_DIGIT_READ_0 = prove
 (`!p k s t. read (memory :> bytes(p,8 * k)) s = t /\ 0 < k
     ==> read (memory :> bytes64 p) s = word(bigdigit t 0)`,
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_DIGIT_READ_0]);;

(* Rewrites with th only where its left side matches keeping lconsts fixed. *)
let FIXED_REWRITE_TAC lconsts th =
  let pat = lhs(snd(strip_forall(concl th))) in
  CONV_TAC(DEPTH_CONV(fun tm ->
    ignore(term_match lconsts pat tm); REWR_CONV th tm));;

let BYTES_DIGIT_READ_NEXT = prove
 (`!p k s t i. read (memory :> bytes(p,8 * k)) s = t /\ i + 1 < k
     ==> read (memory :> bytes64(word_add p (word(8 * i + 8)))) s =
         word(bigdigit t (i + 1))`,
  REWRITE_TAC[ARITH_RULE `8 * i + 8 = 8 * (i + 1)`; BYTES_DIGIT_READ]);;

(* The real-valued assumption that mentions the variable v. *)
let real_mentions v th =
  let c = concl th in
  is_eq c && type_of(lhand c) = `:real` && can (find_term ((=) v)) c;;

let WORD_MASK_SELECT = prove
 (`!b x y:int64.
     word_or (word_and x (word_neg(word(bitval b))))
             (word_and y (word_not(word_neg(word(bitval b))))) =
     if b then x else y`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_BLAST);;

let VAL_MULLO = prove
 (`!(hi:int64) (lo:int64) x y.
     &2 pow 64 * &(val hi) + &(val lo):real = &x * &y ==> val lo = (x * y) MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `val(hi:int64)` THEN
  REWRITE_TAC[VAL_BOUND_64] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN ARITH_TAC);;

let NEGMODINV_DIGIT = prove
 (`!n w. (n * w + 1 == 0) (mod (2 EXP 64))
         ==> (bigdigit n 0 * w + 1 == 0) (mod (2 EXP 64))`,
  REWRITE_TAC[bigdigit; MULT_CLAUSES; EXP; DIV_1] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(NUMBER_RULE
   `(n' == n) (mod p) ==> (n * w + 1 == 0) (mod p) ==> (n' * w + 1 == 0) (mod p)`) THEN
  REWRITE_TAC[CONG_LMOD; CONG_REFL]);;

let MONT_LOW_ZERO = prove
 (`!n0 w x. (n0 * w + 1 == 0) (mod (2 EXP 64))
     ==> (x MOD 2 EXP 64 + (n0 * (w * x MOD 2 EXP 64) MOD 2 EXP 64) MOD 2 EXP 64)
         MOD 2 EXP 64 = 0`,
  REPEAT STRIP_TAC THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM DIVIDES_MOD] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONG_0_DIVIDES] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num` o MATCH_MP DIVIDES_RMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ARITH_TAC);;

let LOWDIGITS_2 = prove
 (`!a. lowdigits a 2 = bigdigit a 0 + 2 EXP 64 * bigdigit a 1`,
  REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; LOWDIGITS_CLAUSES; LOWDIGITS_1] THEN ARITH_TAC);;

let VAL_LOW_WORD_NUM = prove
 (`!h (lo:int64) z. 2 EXP 64 * h + val lo = z ==> val lo = z MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `h:num` THEN REWRITE_TAC[VAL_BOUND_64] THEN ASM_ARITH_TAC);;

(* The real-valued accumulation whose left side mentions the variable v. *)
let real_defines v th =
  let c = concl th in
  is_eq c && type_of(lhand c) = `:real` && can (find_term ((=) v)) (lhand c);;

let LOW_WORD_TAC v =
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VAL_LOW_WORD_NUM o
    REWRITE_RULE[REAL_OF_NUM_CLAUSES] o check (real_defines v));;

let WORD_INDEX_WRAP2 = prove
 (`!i. word(8 * (i + 2) + 18446744073709551600):int64 = word(8 * i)`,
  GEN_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0]);;

let WORD_INDEX_WRAP21 = prove
 (`!i. word(8 * (i + 2) + 18446744073709551608):int64 = word(8 * (i + 1))`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `8 * (i + 2) + 18446744073709551608 = 8 * (i + 1) + 18446744073709551616`] THEN
  ONCE_REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0]);;

let LOW_WORD_SIMP_TAC v =
  FIRST_ASSUM(ASSUME_TAC o SIMP_RULE[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] o
    MATCH_MP VAL_LOW_WORD_NUM o
    REWRITE_RULE[REAL_OF_NUM_CLAUSES] o check (real_defines v));;

let MUL64_BOUND = prove
 (`!x y. x < 2 EXP 64 /\ y < 2 EXP 64
         ==> x * y <= 340282366920938463426481119284349108225`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LE_TRANS `(2 EXP 64 - 1) * (2 EXP 64 - 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]);;

let WORD64_LE = prove
 (`!x:int64. val x <= 18446744073709551615`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int64` VAL_BOUND_64) THEN ARITH_TAC);;

let DIGIT_LE = prove
 (`!n i. bigdigit n i <= 18446744073709551615`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`n:num`; `i:num`] BIGDIGIT_BOUND) THEN ARITH_TAC);;

let USE_LEMMA_TAC th =
  let p,q,c = match snd(strip_comb(concl th)) with
      [_;p;q;c] -> p,q,c | _ -> failwith "USE_LEMMA_TAC" in
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c THEN CONJ_TAC THENL
   [SUBSUMED_MAYCHANGE_TAC;
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    MAP_EVERY EXISTS_TAC [p; q] THEN REWRITE_TAC[th]];;

let WORD_AND_NOT_SUB = prove
 (`!x m:int64. word_and x (word_not m) = word_sub x (word_and x m)`,
  BITBLAST_TAC);;

let VAL_ALIGN_DOWN = prove
 (`!(x:int64) j. val(word_and x (word_not(word(2 EXP j - 1)))) =
                 val x - val x MOD 2 EXP j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_AND_NOT_SUB] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[MOD_LE]);;

let VAL_ALIGN_1024 = prove
 (`!x:int64. val(word_and x (word 18446744073709550592)) = val x - val x MOD 1024`,
  GEN_TAC THEN
  SUBGOAL_THEN `word 18446744073709550592:int64 = word_not(word(2 EXP 10 - 1))` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV; REWRITE_TAC[VAL_ALIGN_DOWN] THEN CONV_TAC NUM_REDUCE_CONV]);;

let VAL_ALIGN_4096 = prove
 (`!x:int64. val(word_and x (word 18446744073709547520)) = val x - val x MOD 4096`,
  GEN_TAC THEN
  SUBGOAL_THEN `word 18446744073709547520:int64 = word_not(word(2 EXP 12 - 1))` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV; REWRITE_TAC[VAL_ALIGN_DOWN] THEN CONV_TAC NUM_REDUCE_CONV]);;

let WORD_ZX_ZX_K = prove
 (`!k. k < 2 EXP 32 ==> word_zx(word_zx(word k:int64):int32):int64 = word k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `k < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `k < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let LEA_NEG_INDEX = prove
 (`!sp0:int64 k.
     word_add (word_sub sp0 (word 48))
       (word(8 * val(word_neg(word k:int64)) + 18446744073709551600)) =
     word_sub sp0 (word(8 * k + 64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD; WORD_MUL; WORD_VAL] THEN
  SUBGOAL_THEN `word 18446744073709551600:int64 = word_neg(word 16)` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; CONV_TAC WORD_RULE]);;

let WORD_SUB_SUB_NUM = prove
 (`!x:int64 a b. word_sub (word_sub x (word a)) (word b) = word_sub x (word(a + b))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let VAL_WORD_ADD_NEG_OFFSET = prove
 (`!(sq:int64) e. e <= val sq /\ 0 < e
     ==> val(word_add sq (word(18446744073709551616 - e))) = val sq - e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  MP_TAC(ISPEC `sq:int64` VAL_BOUND_64) THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
  UNDISCH_TAC `e <= val(sq:int64)` THEN UNDISCH_TAC `0 < e` THEN
  UNDISCH_TAC `val(sq:int64) < 18446744073709551616` THEN ARITH_TAC);;

let FRAME_ALIGN = prove
 (`!(sq:int64) c. c <= val sq /\ 0 < c
     ==> word_and (word_sub sq (word c)) (word 18446744073709550592) =
         word_add sq (word(18446744073709551616 - (c + (val sq - c) MOD 1024)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_ALIGN_1024] THEN
  MP_TAC(ISPEC `sq:int64` VAL_BOUND_64) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_sub sq (word c):int64) = val sq - c` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
    SUBGOAL_THEN `val(word c:int64) = c` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_ADD_NEG_OFFSET o rand o snd) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`val(sq:int64) - c`; `1024`] MOD_LE) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`val(sq:int64) - c`; `1024`] MOD_LE) THEN ASM_ARITH_TAC);;

let PROBE_SPAN = prove
 (`!(sq:int64) e. 48 <= e /\ e <= val sq
     ==> word_and (word_sub (word_sub sq (word 48))
                            (word_add sq (word(18446744073709551616 - e))))
                  (word 18446744073709547520):int64 =
         word(4096 * ((e - 48) DIV 4096))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_ALIGN_4096] THEN
  MP_TAC(ISPEC `sq:int64` VAL_BOUND_64) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`sq:int64`; `e:num`] VAL_WORD_ADD_NEG_OFFSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `val(word_sub sq (word 48):int64) = val sq - 48` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_sub sq (word 48)) (word_add sq (word(18446744073709551616 - e))):int64) = e - 48`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(SPECL [`e - 48`; `4096`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(4096 * ((e - 48) DIV 4096)) MOD 18446744073709551616 = 4096 * ((e - 48) DIV 4096)`
  SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let WORD_SUB_AS_ADD = prove
 (`!(x:int64) c. 0 < c /\ c < 18446744073709551616
     ==> word_sub x (word c) = word_add x (word(18446744073709551616 - c))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub x y = word_add x z <=> word_add y z = word 0`] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN ASM_SIMP_TAC[ARITH_RULE `c < n ==> c + (n - c) = n`] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let WORD_SUB_NUMERAL_CONV tm =
  match tm with
    Comb(Comb(Const("word_sub",_),x),Comb(Const("word",_),n)) when is_numeral n ->
      let th = ISPECL [x; n] WORD_SUB_AS_ADD in
      let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
      CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))) th'
  | _ -> failwith "WORD_SUB_NUMERAL_CONV";;

let PROBE_STEP = prove
 (`!(tp:int64) nd i. i < nd
     ==> word_add (word_add tp (word(4096 * (nd - i)))) (word 18446744073709547520) =
         word_add tp (word(4096 * (nd - (i + 1))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4096 * (nd - i) = 4096 * (nd - (i + 1)) + 4096` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0]);;

let VAL_PROBE = prove
 (`!(tp:int64) nd j. val tp + 4096 * nd < 2 EXP 64 /\ j <= nd
     ==> val(word_add tp (word(4096 * j))) = val tp + 4096 * j /\
         val(word_sub (word_add tp (word(4096 * j))) tp) = 4096 * j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add x y) x = y`] THEN
  SUBGOAL_THEN `4096 * j < 2 EXP 64 /\ val(tp:int64) + 4096 * j < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; MOD_LT]);;

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

(* ------------------------------------------------------------------------- *)
(* The final subtraction and selection, 0x1d0 to 0x22d.                      *)
(* ------------------------------------------------------------------------- *)

let NOHW_TAIL_ARITH = prove
 (`!n t d k cb.
     n < 2 EXP (64 * k) /\ t < 2 EXP (64 * (k + 1)) /\
     &d:real = &2 pow (64 * k) * &(bitval cb) + &(lowdigits t k) - &n /\
     d < 2 EXP (64 * k) /\ t < 2 * n
     ==> word_sub (word(bigdigit t k)) (word(bitval cb)):int64 =
         word_neg(word(bitval(t < n))) /\
         (t < n ==> t MOD n = lowdigits t k) /\
         (~(t < n) ==> t MOD n = d)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `d:real = r * c + l - n <=> d + n = r * c + l`] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bigdigit t k = highdigits t k` SUBST1_TAC THENL
   [REWRITE_TAC[bigdigit; highdigits] THEN MATCH_MP_TAC MOD_LT THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `64 * k + 64 = 64 * (k + 1)`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
  MP_TAC(SPECL [`t:num`; `k:num`] LOWDIGITS_BOUND) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th))))) THEN
  SPEC_TAC(`highdigits t k`,`h:num`) THEN
  SPEC_TAC(`lowdigits t k`,`l:num`) THEN
  SPEC_TAC(`2 EXP (64 * k)`,`r:num`) THEN REPEAT GEN_TAC THEN
  BOOL_CASES_TAC `cb:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT DISCH_TAC THEN
  (SUBGOAL_THEN `h = 0 \/ h = 1` MP_TAC THENL
   [(SUBGOAL_THEN `r * h < r * 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[LT_MULT_LCANCEL] THEN ARITH_TAC;
    ALL_TAC]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  ASM_CASES_TAC `t < n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC) THEN
  TRY(MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC) THEN
  TRY(CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC);;

let NOHW_TAIL = prove_steps
 (`!z m tp k n t pc.
     2 <= k /\ k < 2 EXP 32 /\
     nonoverlapping (z,8 * k) (tp,8 * (k + 1)) /\
     ALLPAIRS nonoverlapping [(z,8 * k); (tp,8 * (k + 1))]
       [(word pc,0x256); (m,8 * k)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bn_mul_mont_nohw_mc /\
               read RIP s = word(pc + 0x1d0) /\
               read RSP s = tp /\ read R9 s = word k /\
               read RDI s = z /\ read RCX s = m /\
               bignum_from_memory (m,k) s = n /\
               bignum_from_memory (tp,k + 1) s = t /\
               ~read CF s)
          (\s. read RIP s = word(pc + 0x22d) /\
               read RSP s = tp /\ read R9 s = word k /\
               (t < 2 * n ==> bignum_from_memory (z,k) s = t MOD n))
          (MAYCHANGE [RIP; RAX; RBX; RBP; RCX; RDX; R8; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * (k + 1))] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events])`,
 [
  (MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`; `tp:int64`; `k:num`; `n:num`; `t:num`; `pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  BIGNUM_TERMRANGE_TAC `k + 1` `t:num` THEN
  VAL_INT64_TAC `k:num`);
  (ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x1e0` `pc + 0x1f4`
   `\i s. (read RSP s = tp /\ read R9 s = word k /\
           read RDI s = z /\ read RCX s = m /\
           bignum_from_memory (m,k) s = n /\
           bignum_from_memory (tp,k + 1) s = t /\
           read R14 s = word i /\ read R15 s = word(k - i) /\
           read RAX s = word(bigdigit t i) /\
           &(bignum_from_memory(z,i) s):real =
           &2 pow (64 * i) * &(bitval(read CF s)) +
           &(lowdigits t i) - &(lowdigits n i)) /\
          (read ZF s <=> i = k)`);
  (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC);
  (ASM_ARITH_TAC);
  (REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`tp:int64`; `k + 1`; `s0:x86state`; `t:num`] BYTES_DIGIT_READ_0) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < k + 1`] THEN DISCH_TAC THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUB_0; MULT_CLAUSES; GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL;
              LOWDIGITS_0; BITVAL_CLAUSES] THEN REAL_ARITH_TAC);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  FIXED_REWRITE_TAC [`i:num`; `z:int64`] (ISPECL [`i:num`; `z:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`m:int64`; `k:num`; `s0:x86state`; `n:num`; `i:num`] BYTES_DIGIT_READ) THEN
  MP_TAC(SPECL [`tp:int64`; `k + 1`; `s0:x86state`; `t:num`; `i:num`] BYTES_DIGIT_READ_NEXT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `i + 1 < k + 1 <=> i < k`] THEN
  REPEAT DISCH_TAC THEN
  X86_ACCSTEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] (1--5));
  (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`];
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (real_mentions `sum_s1:int64`)) THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
      `--a * c + s:real = x ==> s = x + a * c`)) THEN
    REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    REAL_ARITH_TAC;
    VAL_INT64_TAC `k - i:num` THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_1] THEN ASM_ARITH_TAC]);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (GHOST_INTRO_TAC `d:num` `bignum_from_memory(z,k)` THEN
  GHOST_INTRO_TAC `cb:bool` `read CF` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `d:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  SUBGOAL_THEN `lowdigits n k = n` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_SIMP_TAC[LOWDIGITS_SELF]; ALL_TAC] THEN
  ABBREV_TAC `mask:int64 = word_sub (word(bigdigit t k)) (word(bitval cb))` THEN
  ABBREV_TAC `tl = lowdigits t k` THEN
  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x20a` `pc + 0x22b`
   `\i s. (read RSP s = tp /\ read R9 s = word k /\ read RDI s = z /\
           read RAX s = mask /\ read RBX s = word_not mask /\
           read R14 s = word i /\ read R15 s = word(k - i) /\
           bignum_from_memory(word_add z (word(8 * i)),k - i) s = highdigits d i /\
           bignum_from_memory(word_add tp (word(8 * i)),k - i) s = highdigits tl i /\
           (t < 2 * n ==> bignum_from_memory(z,i) s = lowdigits (t MOD n) i)) /\
          (read ZF s <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC);
  (ASM_ARITH_TAC);
  (REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `bignum_from_memory(tp,k) s0 = tl` ASSUME_TAC THENL
   [EXPAND_TAC "tl" THEN
    UNDISCH_THEN `bignum_from_memory (tp,k + 1) s0 = t` (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY; ARITH_RULE `MIN (k + 1) k = k`];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (ASM_REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[WORD_XOR_NOT] THEN CONV_TAC WORD_BLAST);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  FIXED_REWRITE_TAC [`i:num`; `z:int64`]
    (ISPECL [`i:num`; `z:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD]);
  (CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`];
    ALL_TAC]);
  (CONJ_TAC THENL
   [ALL_TAC;
    VAL_INT64_TAC `k - i:num` THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_1] THEN
    UNDISCH_TAC `i < k` THEN ARITH_TAC]);
  (DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `t:num`; `d:num`; `k:num`; `cb:bool`] NOHW_TAIL_ARITH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ASSUME `lowdigits t k = tl`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ASSUME `word_sub (word (bigdigit t k)) (word (bitval cb)) = mask:int64`] THEN
    STRIP_TAC] THEN
  UNDISCH_THEN `mask = word_neg (word (bitval (t < n))):int64` SUBST_ALL_TAC THEN
  REWRITE_TAC[WORD_MASK_SELECT; LOWDIGITS_CLAUSES] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `t < 2 * n`)]));
  (COND_CASES_TAC THENL
   [UNDISCH_THEN `t < n ==> t MOD n = lowdigits t k`
     (fun th -> REWRITE_TAC[MP th (ASSUME `t < n`); ASSUME `lowdigits t k = tl`]);
    UNDISCH_THEN `~(t < n) ==> t MOD n = d`
     (fun th -> REWRITE_TAC[MP th (ASSUME `~(t < n)`)])] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN ARITH_TAC);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LOWDIGITS_SELF THEN TRANS_TAC LT_TRANS `n:num` THEN
  ASM_REWRITE_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC)
 ]);;

(* ------------------------------------------------------------------------- *)
(* The first outer iteration, 0x56 to 0x110.                                 *)
(* ------------------------------------------------------------------------- *)

let P1_INV = `\j s. read RSP s = tp /\ read R9 s = word k /\ read RDI s = z /\
       read RSI s = x /\ read R12 s = y /\ read RCX s = m /\
       read R8 s = w /\ read R14 s = word 0 /\ read R15 s = word j /\
       read RBX s = word(bigdigit b 0) /\ read RBP s = word q0 /\
       bignum_from_memory (x,k) s = a /\ bignum_from_memory (y,k) s = b /\
       bignum_from_memory (m,k) s = n /\
       (read ZF s <=> j = k) /\
       2 EXP 64 * val(read RDX s) + val(read RAX s) = bigdigit n (j - 1) * q0 /\
       lowdigits a j * bigdigit b 0 + lowdigits n j * q0 =
       2 EXP 64 * bignum_from_memory(tp,j - 2) s +
       2 EXP (64 * (j - 1)) *
       (val(read R13 s) + val(read R11 s) + val(read RAX s) +
        2 EXP 64 * val(read RDX s)) +
       2 EXP (64 * j) * val(read R10 s)`;;

let NOHW_FIRST = prove_steps
 (`!z x y m n0p tp k a b n w pc.
     2 <= k /\ k < 2 EXP 32 /\
     (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
     nonoverlapping (z,8 * k) (tp,8 * (k + 1)) /\
     ALLPAIRS nonoverlapping [(z,8 * k); (tp,8 * (k + 1))]
       [(word pc,0x256); (x,8 * k); (y,8 * k); (m,8 * k); (n0p,8)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bn_mul_mont_nohw_mc /\
               read RIP s = word(pc + 0x56) /\
               read RSP s = tp /\ read R9 s = word k /\
               read RDI s = z /\ read RSI s = x /\ read RDX s = y /\
               read RCX s = m /\ read R8 s = n0p /\
               read (memory :> bytes64 n0p) s = w /\
               bignum_from_memory (x,k) s = a /\
               bignum_from_memory (y,k) s = b /\
               bignum_from_memory (m,k) s = n)
          (\s. bytes_loaded s (word pc) bn_mul_mont_nohw_mc /\
               read RIP s = word(pc + 0x110) /\
               read RSP s = tp /\ read R9 s = word k /\ read RDI s = z /\
               read RSI s = x /\ read R12 s = y /\ read RCX s = m /\
               read R8 s = w /\ read R14 s = word 1 /\
               read RAX s = word(bigdigit a 0) /\
               bignum_from_memory (x,k) s = a /\ bignum_from_memory (y,k) s = b /\
               bignum_from_memory (m,k) s = n /\
               ?q. q < 2 EXP (64 * 1) /\
                   2 EXP (64 * 1) * bignum_from_memory(tp,k + 1) s =
                   q * n + a * lowdigits b 1)
          (MAYCHANGE [RIP; RAX; RBX; RBP; RCX; RDX; R8; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * (k + 1))] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events])`,
 [
  (MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`; `tp:int64`] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `a:num`; `b:num`; `n:num`; `w:int64`; `pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN
  VAL_INT64_TAC `k:num` THEN
  ABBREV_TAC `q0 = (val(w:int64) * (bigdigit a 0 * bigdigit b 0) MOD 2 EXP 64) MOD 2 EXP 64` THEN
  ENSURES_SEQUENCE_TAC `pc + 0xd8` (rand(concl(BETA_CONV(mk_comb(P1_INV,`2`))))) THEN
  CONJ_TAC);
  (REWRITE_TAC[ARITH_RULE `2 - 1 = 1 /\ 2 - 2 = 0 /\ 64 * 1 = 64 /\ 64 * 2 = 128`;
              BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (p,v) ->
    MP_TAC(SPECL [p; `k:num`; `s0:x86state`; v] BYTES_DIGIT_READ_0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC])
    [`x:int64`,`a:num`; `y:int64`,`b:num`; `m:int64`,`n:num`] THEN
  MAP_EVERY (fun (p,v) ->
    MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [p; `k:num`; `s0:x86state`; v; `1`] BYTES_DIGIT_READ)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC])
    [`x:int64`,`a:num`; `m:int64`,`n:num`] THEN
  X86_ACCSTEPS_TAC BN_MUL_MONT_NOHW_EXEC [8;13;14;16;20;21;23;26] (1--27));
  (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NEGMODINV_DIGIT) THEN
  SUBGOAL_THEN `q0 < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o SIMP_RULE[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] o
    MATCH_MP VAL_MULLO o check (real_defines `mullo_s8:int64`)) THEN
  SUBGOAL_THEN `word_mul w mullo_s8:int64 = word q0` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q0" THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC]);
  (SUBGOAL_THEN `val(sum_s14:int64) = 0` ASSUME_TAC THENL
   [LOW_WORD_TAC `sum_s14:int64` THEN LOW_WORD_TAC `mullo_s13:int64` THEN
    RULE_ASSUM_TAC(SIMP_RULE[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND;
                             ASSUME `q0 < 2 EXP 64`]) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "q0" THEN
    MATCH_MP_TAC MONT_LOW_ZERO THEN ASM_REWRITE_TAC[];
    ALL_TAC]);
  (REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
    FIRST_ASSUM(MP_TAC o check (real_defines `mulhi_s26:int64`)) THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; ASSUME `q0 < 2 EXP 64`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES];
    REWRITE_TAC[LOWDIGITS_2; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC]);
  (ENSURES_SEQUENCE_TAC `pc + 0xd8` (rand(concl(BETA_CONV(mk_comb(P1_INV,`k:num`))))) THEN
  CONJ_TAC THENL
   [ALL_TAC; ALL_TAC]);
  (ASM_CASES_TAC `k = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC ENSURES_ALREADY THEN
    CONJ_TAC THENL [MESON_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC];
    ALL_TAC]);
  (ENSURES_WHILE_AUP_TAC `2` `k:num` `pc + 0xd8` `pc + 0xd8` P1_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL [MESON_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC];
    ALL_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL [MESON_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC];
    MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL [MESON_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC]]);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS] o check (fun th -> concl th = `2 <= i`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `2 + j = j + 2`]) THEN
  REWRITE_TAC[ARITH_RULE `(2 + j) - 1 = j + 1 /\ (2 + j) - 2 = j /\
                          ((2 + j) + 1) - 1 = j + 2 /\ ((2 + j) + 1) - 2 = j + 1 /\
                          2 + j = j + 2 /\ (j + 2) + 1 = j + 3`] THEN
  FIXED_REWRITE_TAC [`j:num`; `tp:int64`] (ISPECL [`j:num`; `tp:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  GHOST_INTRO_TAC `g10:int64` `read R10` THEN
  GHOST_INTRO_TAC `g11:int64` `read R11` THEN
  GHOST_INTRO_TAC `g13:int64` `read R13` THEN
  GHOST_INTRO_TAC `gax:int64` `read RAX` THEN
  GHOST_INTRO_TAC `gdx:int64` `read RDX` THEN
  GHOST_INTRO_TAC `tl:num` `bignum_from_memory (tp,j)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (p,v) ->
    MP_TAC(SPECL [p; `k:num`; `s0:x86state`; v; `j + 2`] BYTES_DIGIT_READ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC])
    [`x:int64`,`a:num`; `m:int64`,`n:num`] THEN
  MP_TAC(SPEC `j:num` WORD_INDEX_WRAP2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word(j + 2):int64) = j + 2` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `j + 2 < k` THEN UNDISCH_TAC `k < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC BN_MUL_MONT_NOHW_EXEC [2;4;5;7;10;11;13;16] (1--17));
  (ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `q0 < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(j + 3):int64) = j + 3` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `j + 2 < k` THEN UNDISCH_TAC `k < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `(j + 2) + 1 = j + 3`;
                  VAL_WORD_SUB_EQ_0]);
  (CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (real_defines `mulhi_s16:int64`)) THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; ASSUME `q0 < 2 EXP 64`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES];
    ALL_TAC]);
  (SUBGOAL_THEN `2 EXP 64 * val(gdx:int64) + val(gax:int64) <= 340282366920938463426481119284349108225` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    TRANS_TAC LE_TRANS `(2 EXP 64 - 1) * (2 EXP 64 - 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN
      MP_TAC(SPECL [`n:num`; `j + 1`] BIGDIGIT_BOUND) THEN
      UNDISCH_TAC `q0 < 2 EXP 64` THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC]);
  (SUBGOAL_THEN
   `2 EXP 64 * val(sum_s5:int64) +
    2 EXP 128 * (val(sum_s7:int64) + val(sum_s11:int64) + val(mullo_s16:int64) +
                 2 EXP 64 * val(mulhi_s16:int64)) +
    2 EXP 192 * val(sum_s13:int64) =
    2 EXP 64 * (val(g13:int64) + val(g11:int64) + val(gax:int64) + 2 EXP 64 * val(gdx:int64)) +
    2 EXP 128 * val(g10:int64) +
    2 EXP 128 * (bigdigit a (j + 2) * bigdigit b 0 + bigdigit n (j + 2) * q0)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `2 EXP 64 * val(gdx:int64) + val(gax:int64) <= 340282366920938463426481119284349108225` THEN
    MAP_EVERY (fun t -> MP_TAC(MATCH_MP (ARITH_RULE `x < 2 EXP 64 ==> x <= 18446744073709551615`) (ISPEC t VAL_BOUND_64)))
      [`sum_s2:int64`; `sum_s4:int64`; `sum_s5:int64`; `sum_s7:int64`;
       `g13:int64`; `g11:int64`; `gax:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    BOOL_CASES_TAC `carry_s4:bool` THEN BOOL_CASES_TAC `carry_s7:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC]);
  (FIRST_X_ASSUM(MP_TAC o AP_TERM `(*) (2 EXP (64 * j))` o
    check (fun th -> can (find_term ((=) `g10:int64`)) (concl th) &&
                     can (find_term ((=) `sum_s13:int64`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o
    check (fun th -> can (find_term ((=) `tl:num`)) (concl th) &&
                     can (find_term ((=) `g10:int64`)) (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `j + 3 = (j + 2) + 1`; LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 * j + 64 /\ 64 * (j + 2) = 64 * j + 128 /\
                          64 * ((j + 2) + 1) = 64 * j + 192`; EXP_ADD] THEN
  ARITH_TAC);
  (FIRST_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS] o check (fun th -> concl th = `2 <= k`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `2 + j = j + 2`]) THEN
  REWRITE_TAC[ARITH_RULE `2 + j = j + 2`] THEN
  REWRITE_TAC[ARITH_RULE `(j + 2) - 1 = j + 1 /\ (j + 2) - 2 = j /\
                          (j + 2) + 1 = ((j + 1) + 1) + 1`] THEN
  FIXED_REWRITE_TAC [`j:num`; `tp:int64`] (ISPECL [`(j + 1) + 1`; `tp:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  FIXED_REWRITE_TAC [`j:num`; `tp:int64`] (ISPECL [`j + 1`; `tp:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  FIXED_REWRITE_TAC [`j:num`; `tp:int64`] (ISPECL [`j:num`; `tp:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  REWRITE_TAC[ARITH_RULE `(j + 1) + 1 = j + 2`] THEN
  GHOST_INTRO_TAC `g10:int64` `read R10` THEN
  GHOST_INTRO_TAC `g11:int64` `read R11` THEN
  GHOST_INTRO_TAC `g13:int64` `read R13` THEN
  GHOST_INTRO_TAC `gax:int64` `read RAX` THEN
  GHOST_INTRO_TAC `gdx:int64` `read RDX` THEN
  GHOST_INTRO_TAC `tl:num` `bignum_from_memory (tp,j)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`x:int64`; `j + 2`; `s0:x86state`; `a:num`] BYTES_DIGIT_READ_0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `j:num` WORD_INDEX_WRAP2) THEN DISCH_TAC THEN
  MP_TAC(SPEC `j:num` WORD_INDEX_WRAP21) THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word(j + 2):int64) = j + 2` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `j + 2 < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC BN_MUL_MONT_NOHW_EXEC [2;4;5;6;11;12] (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);
  (REWRITE_TAC[VAL_WORD_BITVAL; LOWDIGITS_1] THEN
  SUBGOAL_THEN `q0 < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  EXISTS_TAC `q0:num` THEN ASM_REWRITE_TAC[ARITH_RULE `64 * 1 = 64`] THEN
  SUBGOAL_THEN `2 EXP 64 * val(gdx:int64) + val(gax:int64) <= 340282366920938463426481119284349108225` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    TRANS_TAC LE_TRANS `(2 EXP 64 - 1) * (2 EXP 64 - 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN
      MP_TAC(SPECL [`n:num`; `j + 1`] BIGDIGIT_BOUND) THEN
      UNDISCH_TAC `q0 < 2 EXP 64` THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(sum_s5:int64) + 2 EXP 64 * val(sum_s11:int64) + 2 EXP 128 * bitval carry_s11 =
    val(g13:int64) + val(g11:int64) + val(gax:int64) + 2 EXP 64 * val(gdx:int64) +
    2 EXP 64 * val(g10:int64)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `2 EXP 64 * val(gdx:int64) + val(gax:int64) <= 340282366920938463426481119284349108225` THEN
    MAP_EVERY (fun t -> MP_TAC(MATCH_MP (ARITH_RULE `x < 2 EXP 64 ==> x <= 18446744073709551615`) (ISPEC t VAL_BOUND_64)))
      [`sum_s2:int64`; `sum_s4:int64`; `sum_s5:int64`; `sum_s6:int64`;
       `g13:int64`; `g11:int64`; `gax:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    BOOL_CASES_TAC `carry_s4:bool` THEN BOOL_CASES_TAC `carry_s6:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(*) (2 EXP (64 * (j + 1)))` o
    check (fun th -> can (find_term ((=) `sum_s11:int64`)) (concl th) &&
                     can (find_term ((=) `g10:int64`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o
    check (fun th -> can (find_term ((=) `tl:num`)) (concl th) &&
                     can (find_term ((=) `g10:int64`)) (concl th))) THEN
  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 * j + 64 /\ 64 * (j + 2) = 64 * j + 128`; EXP_ADD] THEN
  ARITH_TAC)
 ]);;

(* ------------------------------------------------------------------------- *)
(* Each later outer iteration, 0x110 to 0x1d0.                               *)
(* ------------------------------------------------------------------------- *)

let OUTER_GOAL = `!z x y m tp k a b n w t pc i.
     2 <= k /\ k < 2 EXP 32 /\ 1 <= i /\ i < k /\
     (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
     ALLPAIRS nonoverlapping [(tp,8 * (k + 1))]
       [(word pc,0x256); (x,8 * k); (y,8 * k); (m,8 * k)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bn_mul_mont_nohw_mc /\
               read RIP s = word(pc + 0x110) /\
               read RSP s = tp /\ read R9 s = word k /\ read RDI s = z /\
               read RSI s = x /\ read R12 s = y /\ read RCX s = m /\
               read R8 s = w /\ read R14 s = word i /\
               read RAX s = word(bigdigit a 0) /\
               bignum_from_memory (x,k) s = a /\
               bignum_from_memory (y,k) s = b /\
               bignum_from_memory (m,k) s = n /\
               bignum_from_memory (tp,k + 1) s = t)
          (\s. bytes_loaded s (word pc) bn_mul_mont_nohw_mc /\
               read RIP s = word(pc + 0x1d0) /\
               read RSP s = tp /\ read R9 s = word k /\ read RDI s = z /\
               read RSI s = x /\ read R12 s = y /\ read RCX s = m /\
               read R8 s = w /\ read R14 s = word(i + 1) /\
               read RAX s = word(bigdigit a 0) /\
               bignum_from_memory (x,k) s = a /\
               bignum_from_memory (y,k) s = b /\
               bignum_from_memory (m,k) s = n /\
               (?q. q < 2 EXP 64 /\
                    2 EXP 64 * bignum_from_memory (tp,k + 1) s =
                    t + a * bigdigit b i + q * n) /\
               (read CF s <=> i + 1 < k))
          (MAYCHANGE [RIP; RAX; RBX; RBP; RCX; RDX; R8; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * (k + 1))] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events])`;;

let INNER_INV = `\j s. read RSP s = tp /\ read R9 s = word k /\ read RDI s = z /\
     read RSI s = x /\ read R12 s = y /\ read RCX s = m /\
     read R8 s = w /\ read R14 s = word i /\ read R15 s = word j /\
     read RBX s = word(bigdigit b i) /\ read RBP s = word qi /\
     bignum_from_memory (x,k) s = a /\ bignum_from_memory (y,k) s = b /\
     bignum_from_memory (m,k) s = n /\
     bignum_from_memory (word_add tp (word(8 * j)),(k + 1) - j) s = highdigits t j /\
     (read ZF s <=> j = k) /\
     2 EXP 64 * val(read RDX s) + val(read RAX s) = bigdigit n (j - 1) * qi /\
     lowdigits t j + lowdigits a j * bigdigit b i + lowdigits n j * qi =
     2 EXP 64 * bignum_from_memory(tp,j - 2) s +
     2 EXP (64 * (j - 1)) *
     (val(read R13 s) + val(read R10 s) + val(read RAX s) +
      2 EXP 64 * val(read RDX s)) +
     2 EXP (64 * j) * val(read R11 s)`;;

let NOHW_OUTER = prove_steps
 (OUTER_GOAL,
 [
  (MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `tp:int64`] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `a:num`; `b:num`; `n:num`; `w:int64`; `t:num`; `pc:num`; `i:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN
  BIGNUM_TERMRANGE_TAC `k + 1` `t:num` THEN
  ABBREV_TAC `qi = (val(w:int64) * ((bigdigit t 0 + bigdigit a 0 * bigdigit b i) MOD 2 EXP 64)) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `k < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `i < k` THEN UNDISCH_TAC `k < 2 EXP 32` THEN ARITH_TAC; ALL_TAC]);
  (ENSURES_SEQUENCE_TAC `pc + 0x190` (rand(concl(BETA_CONV(mk_comb(INNER_INV,`2`))))) THEN
  CONJ_TAC);
  (REWRITE_TAC[ARITH_RULE `2 - 1 = 1 /\ 2 - 2 = 0 /\ 64 * 1 = 64 /\ 64 * 2 = 128 /\ 8 * 2 = 16`;
              BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (p,v) ->
    MP_TAC(SPECL [p; `k:num`; `s0:x86state`; v] BYTES_DIGIT_READ_0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC])
    [`m:int64`,`n:num`] THEN
  MP_TAC(SPECL [`tp:int64`; `k + 1`; `s0:x86state`; `t:num`] BYTES_DIGIT_READ_0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] THEN
  MAP_EVERY (fun (p,v) ->
    MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [p; `k:num`; `s0:x86state`; v; `1`] BYTES_DIGIT_READ)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC])
    [`x:int64`,`a:num`; `m:int64`,`n:num`] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`tp:int64`; `k + 1`; `s0:x86state`; `t:num`; `1`] BYTES_DIGIT_READ)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`y:int64`; `k:num`; `s0:x86state`; `b:num`; `i:num`] BYTES_DIGIT_READ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  X86_ACCSTEPS_TAC BN_MUL_MONT_NOHW_EXEC [5;6;8;11;12;14;19;20;22;23;25;27] (1--28));
  (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NEGMODINV_DIGIT) THEN
  SUBGOAL_THEN `qi < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "qi" THEN REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  LOW_WORD_SIMP_TAC `sum_s6:int64` THEN
  FIRST_ASSUM(ASSUME_TAC o SIMP_RULE[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] o
    MATCH_MP VAL_MULLO o check (real_defines `mullo_s5:int64`)) THEN
  SUBGOAL_THEN `word_mul w sum_s6:int64 = word qi` SUBST_ALL_TAC THENL
   [EXPAND_TAC "qi" THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[MOD_MOD_REFL] THEN EXPAND_TAC "qi" THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[];
    ALL_TAC]);
  (SUBGOAL_THEN `val(sum_s12:int64) = 0` ASSUME_TAC THENL
   [LOW_WORD_TAC `sum_s12:int64` THEN LOW_WORD_TAC `mullo_s11:int64` THEN
    RULE_ASSUM_TAC(SIMP_RULE[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND;
                             ASSUME `qi < 2 EXP 64`]) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "qi" THEN
    SUBGOAL_THEN `(bigdigit t 0 + (bigdigit a 0 * bigdigit b i) MOD 2 EXP 64) MOD 2 EXP 64 = (bigdigit t 0 + bigdigit a 0 * bigdigit b i) MOD 2 EXP 64` SUBST1_TAC THENL
     [CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
      MATCH_MP_TAC MONT_LOW_ZERO THEN ASM_REWRITE_TAC[]];
    ALL_TAC]);
  (REWRITE_TAC[] THEN REPEAT CONJ_TAC);
  (REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; highdigits] THEN
  REWRITE_TAC[ARITH_RULE `16 = 8 * 2`] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV] THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]);
  (REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);
  (FIRST_ASSUM(MP_TAC o check (real_defines `mulhi_s27:int64`)) THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; ASSUME `qi < 2 EXP 64`] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES]);
  (SUBGOAL_THEN
   `val(sum_s14:int64) + val(sum_s23:int64) + val(mullo_s27:int64) +
    2 EXP 64 * val(mulhi_s27:int64) + 2 EXP 64 * val(sum_s25:int64) =
    val(sum_s8:int64) + val(sum_s14:int64) + bigdigit t 1 + bigdigit a 1 * bigdigit b i +
    bigdigit n 1 * qi /\
    2 EXP 64 * (val(sum_s8:int64) + val(sum_s14:int64)) =
    bigdigit t 0 + bigdigit a 0 * bigdigit b i + bigdigit n 0 * qi`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LOWDIGITS_2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC]);
  (MAP_EVERY (fun t -> MP_TAC(MATCH_MP (ARITH_RULE `x < 2 EXP 64 ==> x <= 18446744073709551615`) (ISPEC t VAL_BOUND_64)))
      [`sum_s8:int64`; `sum_s22:int64`; `sum_s20:int64`; `mulhi_s19:int64`] THEN
  MP_TAC(SPECL [`t:num`; `1`] BIGDIGIT_BOUND) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  BOOL_CASES_TAC `carry_s25:bool` THEN BOOL_CASES_TAC `carry_s22:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);
  (ENSURES_SEQUENCE_TAC `pc + 0x190` (rand(concl(BETA_CONV(mk_comb(INNER_INV,`k:num`))))) THEN
  CONJ_TAC THENL [ALL_TAC; ALL_TAC]);
  (ASM_CASES_TAC `k = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC ENSURES_ALREADY THEN
    CONJ_TAC THENL [MESON_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC];
    ALL_TAC]);
  (ENSURES_WHILE_AUP_TAC `2` `k:num` `pc + 0x190` `pc + 0x190` INNER_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL [MESON_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC];
    ALL_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL [MESON_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC];
    MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL [MESON_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC]]);
  (X_GEN_TAC `i':num` THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS] o check (fun th -> concl th = `2 <= i'`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `2 + j = j + 2`]) THEN
  REWRITE_TAC[ARITH_RULE `(2 + j) - 1 = j + 1 /\ (2 + j) - 2 = j /\
                          ((2 + j) + 1) - 1 = j + 2 /\ ((2 + j) + 1) - 2 = j + 1 /\
                          2 + j = j + 2 /\ (j + 2) + 1 = j + 3`] THEN
  FIXED_REWRITE_TAC [`j:num`; `tp:int64`] (ISPECL [`j:num`; `tp:int64`] BIGNUM_FROM_MEMORY_STEP));
  (MP_TAC(ISPECL [`tp:int64`; `(k + 1) - (j + 2)`; `t:num`; `j + 2`; `j + 2`] BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS) THEN
  SUBGOAL_THEN `~((k + 1) - (j + 2) = 0) /\ (k + 1) - (j + 2) - 1 = (k + 1) - (j + 3) /\ (j + 2) + 1 = j + 3`
   (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `j + 2 < k` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]));
  (GHOST_INTRO_TAC `g10:int64` `read R10` THEN
  GHOST_INTRO_TAC `g11:int64` `read R11` THEN
  GHOST_INTRO_TAC `g13:int64` `read R13` THEN
  GHOST_INTRO_TAC `gax:int64` `read RAX` THEN
  GHOST_INTRO_TAC `gdx:int64` `read RDX` THEN
  GHOST_INTRO_TAC `tl:num` `bignum_from_memory (tp,j)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (p,v) ->
    MP_TAC(SPECL [p; `k:num`; `s0:x86state`; v; `j + 2`] BYTES_DIGIT_READ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC])
    [`x:int64`,`a:num`; `m:int64`,`n:num`] THEN
  MP_TAC(SPEC `j:num` WORD_INDEX_WRAP2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word(j + 2):int64) = j + 2` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `j + 2 < k` THEN UNDISCH_TAC `k < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC BN_MUL_MONT_NOHW_EXEC [2;4;5;7;10;11;13;14;16;18] (1--19));
  (ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `qi < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "qi" THEN REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(j + 3):int64) = j + 3` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `j + 2 < k` THEN UNDISCH_TAC `k < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `(j + 2) + 1 = j + 3`;
                  VAL_WORD_SUB_EQ_0]);
  (CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (real_defines `mulhi_s18:int64`)) THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; ASSUME `qi < 2 EXP 64`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES];
    ALL_TAC]);
  (SUBGOAL_THEN
   `val(sum_s5:int64) +
    2 EXP 64 * (val(sum_s7:int64) + val(sum_s14:int64) + val(mullo_s18:int64) +
                2 EXP 64 * val(mulhi_s18:int64)) +
    2 EXP 128 * val(sum_s16:int64) =
    (val(g13:int64) + val(g10:int64) + val(gax:int64) + 2 EXP 64 * val(gdx:int64)) +
    2 EXP 64 * val(g11:int64) +
    2 EXP 64 * (bigdigit t (j + 2) + bigdigit a (j + 2) * bigdigit b i +
                bigdigit n (j + 2) * qi)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`bigdigit a (j + 2)`; `bigdigit b i`] MUL64_BOUND) THEN
    REWRITE_TAC[BIGDIGIT_BOUND] THEN
    SUBGOAL_THEN `2 EXP 64 * val(gdx:int64) + val(gax:int64) <= 340282366920938463426481119284349108225` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MUL64_BOUND THEN ASM_REWRITE_TAC[BIGDIGIT_BOUND];
      ALL_TAC] THEN
    MAP_EVERY (fun t -> MP_TAC(ISPEC t WORD64_LE))
      [`sum_s2:int64`; `sum_s4:int64`; `sum_s5:int64`; `sum_s7:int64`;
       `sum_s11:int64`; `sum_s13:int64`; `sum_s14:int64`;
       `g13:int64`; `g10:int64`; `g11:int64`; `gax:int64`] THEN
    MP_TAC(SPECL [`t:num`; `j + 2`] DIGIT_LE) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    BOOL_CASES_TAC `carry_s4:bool` THEN BOOL_CASES_TAC `carry_s7:bool` THEN
    BOOL_CASES_TAC `carry_s13:bool` THEN BOOL_CASES_TAC `carry_s16:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC]);
  (FIRST_X_ASSUM(MP_TAC o AP_TERM `(*) (2 EXP (64 * (j + 1)))` o
    check (fun th -> can (find_term ((=) `g11:int64`)) (concl th) &&
                     can (find_term ((=) `sum_s16:int64`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o
    check (fun th -> can (find_term ((=) `tl:num`)) (concl th) &&
                     can (find_term ((=) `g11:int64`)) (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `j + 3 = (j + 2) + 1`; LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 * j + 64 /\ 64 * (j + 2) = 64 * j + 128 /\
                          64 * ((j + 2) + 1) = 64 * j + 192`; EXP_ADD] THEN
  ARITH_TAC);
  (FIRST_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS] o check (fun th -> concl th = `2 <= k`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `2 + j = j + 2`]) THEN
  REWRITE_TAC[ARITH_RULE `2 + j = j + 2`] THEN
  REWRITE_TAC[ARITH_RULE `((j + 2) + 1) - (j + 2) = 1`] THEN
  MP_TAC(ISPECL [`tp:int64`; `1`; `t:num`; `j + 2`; `j + 2`] BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS) THEN
  REWRITE_TAC[ARITH_RULE `~(1 = 0) /\ 1 - 1 = 0`; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  REWRITE_TAC[ARITH_RULE `(0 = x) <=> (x = 0)`] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `(j + 2) - 1 = j + 1 /\ (j + 2) - 2 = j /\
                          (j + 2) + 1 = ((j + 1) + 1) + 1`] THEN
  FIXED_REWRITE_TAC [`j:num`; `tp:int64`] (ISPECL [`(j + 1) + 1`; `tp:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  FIXED_REWRITE_TAC [`j:num`; `tp:int64`] (ISPECL [`j + 1`; `tp:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  FIXED_REWRITE_TAC [`j:num`; `tp:int64`] (ISPECL [`j:num`; `tp:int64`] BIGNUM_FROM_MEMORY_STEP) THEN
  REWRITE_TAC[ARITH_RULE `(j + 1) + 1 = j + 2`] THEN
  GHOST_INTRO_TAC `g10:int64` `read R10` THEN
  GHOST_INTRO_TAC `g11:int64` `read R11` THEN
  GHOST_INTRO_TAC `g13:int64` `read R13` THEN
  GHOST_INTRO_TAC `gax:int64` `read RAX` THEN
  GHOST_INTRO_TAC `gdx:int64` `read RDX` THEN
  GHOST_INTRO_TAC `tl:num` `bignum_from_memory (tp,j)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`x:int64`; `j + 2`; `s0:x86state`; `a:num`] BYTES_DIGIT_READ_0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `j:num` WORD_INDEX_WRAP2) THEN DISCH_TAC THEN
  MP_TAC(SPEC `j:num` WORD_INDEX_WRAP21) THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word(j + 2):int64) = j + 2` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `j + 2 < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC BN_MUL_MONT_NOHW_EXEC [2;4;5;7;11;12;13;14] (1--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (SUBGOAL_THEN `word_add (word i) (word 1):int64 = word(i + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(i + 1):int64) = i + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `i < j + 2` THEN UNDISCH_TAC `j + 2 < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `qi < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "qi" THEN REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  EXISTS_TAC `qi:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `val(sum_s5:int64) + 2 EXP 64 * val(sum_s13:int64) + 2 EXP 128 * val(sum_s14:int64) =
    val(g13:int64) + val(g10:int64) + val(gax:int64) + 2 EXP 64 * val(gdx:int64) +
    2 EXP 64 * val(g11:int64) + 2 EXP 64 * bigdigit t (j + 2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP 64 * val(gdx:int64) + val(gax:int64) <= 340282366920938463426481119284349108225` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MUL64_BOUND THEN ASM_REWRITE_TAC[BIGDIGIT_BOUND];
      ALL_TAC] THEN
    MAP_EVERY (fun t -> MP_TAC(ISPEC t WORD64_LE))
      [`sum_s2:int64`; `sum_s4:int64`; `sum_s5:int64`; `sum_s7:int64`;
       `sum_s11:int64`; `sum_s12:int64`; `sum_s13:int64`;
       `g13:int64`; `g10:int64`; `g11:int64`; `gax:int64`] THEN
    MP_TAC(SPECL [`t:num`; `j + 2`] DIGIT_LE) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    BOOL_CASES_TAC `carry_s4:bool` THEN BOOL_CASES_TAC `carry_s7:bool` THEN
    BOOL_CASES_TAC `carry_s12:bool` THEN BOOL_CASES_TAC `carry_s14:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(*) (2 EXP (64 * (j + 1)))` o
    check (fun th -> can (find_term ((=) `sum_s14:int64`)) (concl th) &&
                     can (find_term ((=) `g11:int64`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o
    check (fun th -> can (find_term ((=) `tl:num`)) (concl th) &&
                     can (find_term ((=) `g11:int64`)) (concl th))) THEN
  SUBGOAL_THEN `t = lowdigits t (j + 2) + 2 EXP (64 * (j + 2)) * bigdigit t (j + 2)` MP_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM LOWDIGITS_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 * j + 64 /\ 64 * (j + 2) = 64 * j + 128`; EXP_ADD] THEN
  ARITH_TAC)
 ]);;

(* ------------------------------------------------------------------------- *)
(* The body, 0x56 to 0x22d.                                                  *)
(* ------------------------------------------------------------------------- *)

let BODY_GOAL = `!z x y m n0p tp k a b n w pc.
     2 <= k /\ k < 2 EXP 32 /\
     (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
     nonoverlapping (z,8 * k) (tp,8 * (k + 1)) /\
     ALLPAIRS nonoverlapping [(z,8 * k); (tp,8 * (k + 1))]
       [(word pc,0x256); (x,8 * k); (y,8 * k); (m,8 * k); (n0p,8)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bn_mul_mont_nohw_mc /\
               read RIP s = word(pc + 0x56) /\
               read RSP s = tp /\ read R9 s = word k /\
               read RDI s = z /\ read RSI s = x /\ read RDX s = y /\
               read RCX s = m /\ read R8 s = n0p /\
               read (memory :> bytes64 n0p) s = w /\
               bignum_from_memory (x,k) s = a /\
               bignum_from_memory (y,k) s = b /\
               bignum_from_memory (m,k) s = n)
          (\s. read RIP s = word(pc + 0x22d) /\
               read RSP s = tp /\ read R9 s = word k /\
               (a * b <= 2 EXP (64 * k) * n
                ==> bignum_from_memory (z,k) s =
                    (inverse_mod n (2 EXP (64 * k)) * a * b) MOD n))
          (MAYCHANGE [RIP; RAX; RBX; RBP; RCX; RDX; R8; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * k); memory :> bytes(tp,8 * (k + 1))] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;

let OUTER_INV = `\i s. (read RSP s = tp /\ read R9 s = word k /\ read RDI s = z /\
         read RSI s = x /\ read R12 s = y /\ read RCX s = m /\
         read R8 s = w /\ read R14 s = word i /\
         read RAX s = word(bigdigit a 0) /\
         bignum_from_memory (x,k) s = a /\ bignum_from_memory (y,k) s = b /\
         bignum_from_memory (m,k) s = n /\
         ?q. q < 2 EXP (64 * i) /\
             2 EXP (64 * i) * bignum_from_memory(tp,k + 1) s =
             q * n + a * lowdigits b i) /\
        (read CF s <=> i < k)`;;

let NOHW_BODY = prove_steps
 (BODY_GOAL,
 [
  (MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`; `tp:int64`] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `a:num`; `b:num`; `n:num`; `w:int64`; `pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN STRIP_TAC THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`]);
  (ENSURES_WHILE_PAUP_TAC `1` `k:num` `pc + 0x110` `pc + 0x1d0` OUTER_INV);
  (REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `2 <= k` THEN ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC]);
  (MP_TAC(SPECL [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`; `tp:int64`;
                `k:num`; `a:num`; `b:num`; `n:num`; `w:int64`; `pc:num`] NOHW_FIRST) THEN
  ASM_REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN USE_LEMMA_TAC);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `t:num` `bignum_from_memory (tp,k + 1)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `tp:int64`;
                `k:num`; `a:num`; `b:num`; `n:num`; `w:int64`; `t:num`; `pc:num`; `i:num`] NOHW_OUTER) THEN
  ASM_REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN USE_LEMMA_TAC);
  (X_GEN_TAC `s:x86state` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `q + 2 EXP (64 * i) * q'` THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
    MATCH_MP_TAC(ARITH_RULE `q < e /\ e * (q' + 1) <= e * 2 EXP 64 ==> q + e * q' < e * 2 EXP 64`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `q' < 2 EXP 64` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o AP_TERM `(*) (2 EXP (64 * i))` o
      check (fun th -> is_eq(concl th) && can (find_term ((=) `t:num`)) (concl th) &&
                       can (find_term ((=) `q':num`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o
      check (fun th -> is_eq(concl th) && can (find_term ((=) `t:num`)) (concl th) &&
                       can (find_term ((=) `lowdigits b i`)) (concl th))) THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
    ARITH_TAC]);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `t:num` `bignum_from_memory (tp,k + 1)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);
  (GHOST_INTRO_TAC `t:num` `bignum_from_memory (tp,k + 1)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`z:int64`; `m:int64`; `tp:int64`; `k:num`; `n:num`; `t:num`; `pc:num`] NOHW_TAIL) THEN
  ASM_REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN USE_LEMMA_TAC);
  (CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN REWRITE_TAC[LT_REFL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC]);
  (SUBGOAL_THEN `a * b <= 2 EXP (64 * k) * n ==> t < 2 * n /\ t MOD n = (inverse_mod n (2 EXP (64 * k)) * a * b) MOD n`
   MP_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `2 EXP (64 * k) * t = q * n + a * lowdigits b k` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `2 EXP (64 * k) * t < 2 EXP (64 * k) * (2 * n)` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(ARITH_RULE `q * n < r * n /\ x <= r * n ==> q * n + x < r * (2 * n)`) THEN
        ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP NEGMODINV_ODD) THEN
        ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH];
        REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
      MATCH_MP_TAC MONT_REDUCE_CONG THEN EXISTS_TAC `q:num` THEN
      ASM_REWRITE_TAC[COPRIME_REXP] THEN DISJ1_TAC THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN REWRITE_TAC[COPRIME_2] THEN
      MATCH_MP_TAC NEGMODINV_ODD THEN EXISTS_TAC `val(w:int64)` THEN ASM_REWRITE_TAC[]];
    MESON_TAC[]])
 ]);;

(* ------------------------------------------------------------------------- *)
(* The whole function, with its prologue, probes and epilogue.               *)
(* ------------------------------------------------------------------------- *)

let SUB_GOAL = `!z x y m n0p a b n w k pc stackpointer returnaddress.
     2 <= k /\ k < 2 EXP 32 /\
     (n * val(w:int64) + 1 == 0) (mod (2 EXP 64)) /\
     8 * k + 1088 <= val(stackpointer:int64) /\
     ALLPAIRS nonoverlapping
       [(z,8 * k); (word_sub stackpointer (word(8 * k + 1088)),8 * k + 1096)]
       [(word pc,0x256); (x,8 * k); (y,8 * k); (m,8 * k); (n0p,8)] /\
     nonoverlapping (z,8 * k)
       (word_sub stackpointer (word(8 * k + 1088)),8 * k + 1096)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bn_mul_mont_nohw_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [z; x; y; m; n0p; word k] s /\
               read (memory :> bytes64 n0p) s = w /\
               bignum_from_memory (x,k) s = a /\
               bignum_from_memory (y,k) s = b /\
               bignum_from_memory (m,k) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read RAX s = word 1 /\
               (a * b <= 2 EXP (64 * k) * n
                ==> bignum_from_memory (z,k) s =
                    (inverse_mod n (2 EXP (64 * k)) * a * b) MOD n))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * k);
                      memory :> bytes(word_sub stackpointer (word(8 * k + 1088)),
                                      8 * k + 1088)] ,,
           MAYCHANGE [events])`;;

(* The state at 0x33, after the frame is allocated, and at 0x51, after the
   probe loop: the arguments, the return address, and the callee-saved
   registers pushed below it. *)
let SAVED_S = "read RAX s = stackpointer /\\ read R9 s = word k /\\
     read RDI s = z /\\ read RSI s = x /\\ read RDX s = y /\\
     read RCX s = m /\\ read R8 s = n0p /\\
     read (memory :> bytes64 n0p) s = w /\\
     bignum_from_memory (x,k) s = a /\\ bignum_from_memory (y,k) s = b /\\
     bignum_from_memory (m,k) s = n /\\
     read (memory :> bytes64 stackpointer) s = returnaddress /\\
     read (memory :> bytes64 (word_sub stackpointer (word 8))) s = rbx_init /\\
     read (memory :> bytes64 (word_sub stackpointer (word 16))) s = rbp_init /\\
     read (memory :> bytes64 (word_sub stackpointer (word 24))) s = r12_init /\\
     read (memory :> bytes64 (word_sub stackpointer (word 32))) s = r13_init /\\
     read (memory :> bytes64 (word_sub stackpointer (word 40))) s = r14_init /\\
     read (memory :> bytes64 (word_sub stackpointer (word 48))) s = r15_init";;
let P33 = parse_term ("\\s. read RSP s = word_add tp d /\\ read R10 s = tp /\\ " ^ SAVED_S);;
let P51 = parse_term ("\\s. read RSP s = tp /\\ " ^ SAVED_S);;

let TP_EQ_TAC ttac =
  FIRST_ASSUM(ttac o SYM o check (fun th -> rhs(concl th) = `tp:int64` &&
    can (term_match [] `word_add (stackpointer:int64) w`) (lhs(concl th))));;

let PROBE_INV = parse_term ("\\i s. (read RSP s = word_add tp (word(4096 * (nd - i))):int64 /\\
     read R10 s = tp /\\ " ^ SAVED_S ^ ") /\\ (~read CF s /\\ (read ZF s <=> i = nd))");;

let PROBE_FIN_TAC j =
  MP_TAC(SPECL [`tp:int64`; `nd:num`; j] VAL_PROBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(a + b < a:num)`; MULT_EQ_0; ARITH_EQ];;

let TP_EQ_X_TAC ttac =
  FIRST_X_ASSUM(ttac o SYM o check (fun th -> rhs(concl th) = `tp:int64` &&
    can (term_match [] `word_add (stackpointer:int64) w`) (lhs(concl th))));;

let BN_MUL_MONT_NOHW_SUBROUTINE_CORRECT = prove_steps
 (SUB_GOAL,
 [
  (MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `n:num`; `w:int64`; `k:num`; `pc:num`;
                       `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS] THEN STRIP_TAC THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ABBREV_TAC `tp = word_and (word_sub stackpointer (word(8 * k + 64))) (word 18446744073709550592):int64` THEN
  ABBREV_TAC `d = word_and (word_sub (word_sub stackpointer (word 48)) tp) (word 18446744073709547520):int64`);
  (ENSURES_SEQUENCE_TAC `pc + 0x33` P33);
  (CONJ_TAC);
  (REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WORD_ZX_ZX_K (ASSUME `k < 2 EXP 32`)]) THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (2--8) THEN
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[WORD_SUB_SUB_NUM] THENC DEPTH_CONV NUM_ADD_CONV)) THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (9--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LEA_NEG_INDEX; WORD_NEG_NEG]) THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (13--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; WORD_VAL]);
  (SUBGOAL_THEN `word_sub stackpointer (word(8 * k + 1088)):int64 =
                word_add stackpointer (word(18446744073709551616 - (8 * k + 1088)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC WORD_SUB_AS_ADD THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (maychange_term o concl)) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_SUB_NUMERAL_CONV) THEN DISCH_TAC THEN
  MONOTONE_MAYCHANGE_TAC);
  (ABBREV_TAC `delta = 8 * k + 64 + (val(stackpointer:int64) - (8 * k + 64)) MOD 1024` THEN
  SUBGOAL_THEN `8 * k + 64 <= delta /\ delta <= 8 * k + 1087` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN
    MP_TAC(SPECL [`val(stackpointer:int64) - (8 * k + 64)`; `1024`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add stackpointer (word(18446744073709551616 - delta)) = tp:int64` ASSUME_TAC THENL
   [EXPAND_TAC "tp" THEN CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhand o rand) FRAME_ALIGN o lhs o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "delta" THEN REWRITE_TAC[ADD_ASSOC];
    ALL_TAC] THEN
  ABBREV_TAC `nd = (delta - 48) DIV 4096`);
  (SUBGOAL_THEN `d:int64 = word(4096 * nd)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN EXPAND_TAC "nd" THEN TP_EQ_TAC SUBST1_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PROBE_SPAN o lhs o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4096 * nd + 48 <= delta` ASSUME_TAC THENL
   [EXPAND_TAC "nd" THEN MP_TAC(SPECL [`delta - 48`; `4096`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(tp:int64) + 4096 * nd < 2 EXP 64` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(tp:int64) = val(stackpointer:int64) - delta` SUBST1_TAC THENL
     [TP_EQ_TAC SUBST1_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_ADD_NEG_OFFSET o lhs o snd) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;
      MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC];
    ALL_TAC]);
  (ENSURES_SEQUENCE_TAC `pc + 0x51` P51 THEN CONJ_TAC);
  (ASM_CASES_TAC `nd = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (1--4);
    ALL_TAC]);
  (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (ENSURES_WHILE_PAUP_TAC `0` `nd:num` `pc + 0x40` `pc + 0x4f` PROBE_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC]);
  (REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SUB_0]);
  (PROBE_FIN_TAC `nd:num`);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP PROBE_STEP (ASSUME `i < nd`)]) THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PROBE_FIN_TAC `nd - (i + 1)`);
  (UNDISCH_TAC `i < nd` THEN ARITH_TAC);
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(i:num = nd)` ASSUME_TAC THENL
   [UNDISCH_TAC `i < nd` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (REWRITE_TAC[SUB_REFL; MULT_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);
  (TP_EQ_X_TAC SUBST_ALL_TAC THEN
  SUBGOAL_THEN `word_sub stackpointer (word(8 * k + 1088)):int64 =
                word_add stackpointer (word(18446744073709551616 - (8 * k + 1088)))`
   SUBST_ALL_TAC THENL
   [MATCH_MP_TAC WORD_SUB_AS_ADD THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_SUB_NUMERAL_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_SUB_NUMERAL_CONV)) THEN
  VAL_INT64_TAC `k:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC [1]);
  (SUBGOAL_THEN `nonoverlapping_modulo (2 EXP 64) (val(stackpointer:int64),8)
                 (val(word_add stackpointer (word(18446744073709551616 - delta)):int64),8 * (k + 1))`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`stackpointer:int64`; `0`; `8`; `18446744073709551616 - delta`; `8 * (k + 1)`]
      NONOVERLAPPING_MODULO_OFFSET_BOTH) THEN
    REWRITE_TAC[WORD_ADD_0; DIMINDEX_64] THEN DISCH_THEN MATCH_MP_TAC THEN
    DISJ1_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC]);
  (MP_TAC(SPECL [`z:int64`; `x:int64`; `y:int64`; `m:int64`; `n0p:int64`;
                `word_add stackpointer (word (18446744073709551616 - delta)):int64`;
                `k:num`; `a:num`; `b:num`; `n:num`; `w:int64`; `pc:num`] NOHW_BODY) THEN
  ASM_REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES]);
  (ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC]);
  (SUBGOAL_THEN `nonoverlapping_modulo (2 EXP 64) (val(stackpointer:int64),8) (val(z:int64),8 * k)`
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     `contained_modulo (2 EXP 64)
        (val(word_add stackpointer (word 18446744073709551616):int64),8)
        (val(word_add stackpointer (word(18446744073709551616 - (8 * k + 1088))):int64),
         8 * k + 1096)`
    MP_TAC THENL [CONTAINED_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCH_TAC THEN MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
    MAP_EVERY EXISTS_TAC
     [`val(word_add stackpointer (word(18446744073709551616 - (8 * k + 1088))):int64)`;
      `8 * k + 1096`; `val(z:int64)`; `8 * k`] THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    ASM_REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL];
    ALL_TAC]);
  (REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SOME_FLAGS] THEN X86_BIGSTEP_TAC BN_MUL_MONT_NOHW_EXEC "s2");
  (X86_STEPS_TAC BN_MUL_MONT_NOHW_EXEC (3--12));
  (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[])
 ]);;
