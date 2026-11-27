(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 16-byte constant-time compare, as rind's build emits it.                  *)
(* ========================================================================= *)

(* The A32 routine `ct_compare_16` in rind's low::arm::cpu, which reads each
   16-byte block at R0 and R1 as four words, at any alignment, and returns
   in R0 the OR of their XORs: zero exactly when the blocks are equal. Its
   loads and its return are the same whatever the blocks hold. Its theorems
   hold for a caller in A32 or T32, whose return address has bit 0 set, so
   they cover every armv7 target. *)

needs "aarch32/proofs/base.ml";;
needs "aarch32/proofs/consttime.ml";;

(* admin/prove writes the routine's bytes, as rind's release build for
   armv7-unknown-linux-gnueabihf emits them, to armv7/ct_compare_16.bin, and
   the definition fails unless they are these. The routine is A32 on every
   target. *)
let ct_compare_16_mc = define_assert_word_list "ct_compare_16_mc"
  (term_of_bytes (load_file "armv7/ct_compare_16.bin"))
[
  0xe5902000;       (* ldr r2, [r0] *)
  0xe5913000;       (* ldr r3, [r1] *)
  0xe022c003;       (* eor r12, r2, r3 *)
  0xe5902004;       (* ldr r2, [r0, #4] *)
  0xe5913004;       (* ldr r3, [r1, #4] *)
  0xe0222003;       (* eor r2, r2, r3 *)
  0xe18cc002;       (* orr r12, r12, r2 *)
  0xe5902008;       (* ldr r2, [r0, #8] *)
  0xe5913008;       (* ldr r3, [r1, #8] *)
  0xe0222003;       (* eor r2, r2, r3 *)
  0xe18cc002;       (* orr r12, r12, r2 *)
  0xe590200c;       (* ldr r2, [r0, #12] *)
  0xe591300c;       (* ldr r3, [r1, #12] *)
  0xe0222003;       (* eor r2, r2, r3 *)
  0xe18c0002;       (* orr r0, r12, r2 *)
  0xe12fff1e        (* bx lr *)
];;

let CT_COMPARE_16_EXEC = AARCH32_MK_EXEC_RULE ct_compare_16_mc;;

(* The word at offset i of a 16-byte string is its value's digits from
   byte i. *)
let CT_COMPARE_16_LOAD = prove
 (`!(a:int32) x i s.
        read (bytes(a,16)) s = x /\ i <= 12
        ==> read (bytes32 (word_add a (word i))) s = word(x DIV 2 EXP (8 * i))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_BYTES_DIV] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM WORD_MOD_SIZE] THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 32 = 2 EXP (8 * 4)`; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `i <= 12 ==> MIN (16 - i) 4 = 4`] THEN
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read]);;

(* Two numbers agree below bit k + 32 exactly when they agree below bit k
   and in the word from it. *)
let CT_COMPARE_16_STEP = prove
 (`!x y k.
        x MOD 2 EXP (k + 32) = y MOD 2 EXP (k + 32) <=>
        x MOD 2 EXP k = y MOD 2 EXP k /\
        (word(x DIV 2 EXP k):int32) = word(y DIV 2 EXP k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_32] THEN
  SIMP_TAC[LEXICOGRAPHIC_EQ; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  CONV_TAC TAUT);;

(* Two 16-byte strings are equal exactly when their four words are. *)
let CT_COMPARE_16_EQ = prove
 (`!x y. x < 2 EXP 128 /\ y < 2 EXP 128
         ==> (x = y <=>
              (word x:int32) = word y /\
              (word(x DIV 2 EXP 32):int32) = word(y DIV 2 EXP 32) /\
              (word(x DIV 2 EXP 64):int32) = word(y DIV 2 EXP 64) /\
              (word(x DIV 2 EXP 96):int32) = word(y DIV 2 EXP 96))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `0`] CT_COMPARE_16_STEP) THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `32`] CT_COMPARE_16_STEP) THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `64`] CT_COMPARE_16_STEP) THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `96`] CT_COMPARE_16_STEP) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_SIMP_TAC[MOD_LT; EXP; MOD_1; DIV_1] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC TAUT);;

(* From entry to return: R0 is the OR of the four words' XORs. *)
let CT_COMPARE_16_CORRECT = prove
 (`!a b x y pc returnaddress.
        aarch32_bx_target returnaddress /\
        aarch32_nowrap a 16 /\ aarch32_nowrap b 16
        ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) ct_compare_16_mc /\
               read PC s = word pc /\
               read LR s = returnaddress /\
               C_ARGUMENTS [a; b] s /\
               read (memory :> bytes(a,16)) s = x /\
               read (memory :> bytes(b,16)) s = y)
          (\s. read PC s = returnaddress /\
               (C_RETURN s = word 0 <=> x = y))
          MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; fst CT_COMPARE_16_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `x < 2 EXP 128 /\ y < 2 EXP 128` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `128 = 8 * 16`;
                READ_BYTES_BOUND];
    ALL_TAC] THEN
  MAP_EVERY (fun (p,v,i) ->
      MP_TAC(SPECL [p; v; i; `read memory s0`] CT_COMPARE_16_LOAD))
   [`a:int32`,`x:num`,`0`; `a:int32`,`x:num`,`4`;
    `a:int32`,`x:num`,`8`; `a:int32`,`x:num`,`12`;
    `b:int32`,`y:num`,`0`; `b:int32`,`y:num`,`4`;
    `b:int32`,`y:num`,`8`; `b:int32`,`y:num`,`12`] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; DIV_1] THEN
  REPEAT(DISCH_THEN ASSUME_TAC) THEN
  AARCH32_STEPS_TAC CT_COMPARE_16_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[CT_COMPARE_16_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0; CONJ_ACI]);;

(* The trace, its eight loads and the return, is a function of R0, R1, and
   the return address alone, and every load lands inside the two blocks. *)
let CT_COMPARE_16_SAFE = prove
 (`exists f_events.
       forall e a b pc returnaddress.
           aarch32_bx_target returnaddress /\
           aarch32_nowrap a 16 /\ aarch32_nowrap b 16
           ==> ensures aarch32
           (\s. aligned_bytes_loaded s (word pc) ct_compare_16_mc /\
                read PC s = word pc /\
                read LR s = returnaddress /\
                C_ARGUMENTS [a; b] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a b pc returnaddress /\
                    memaccess_inbounds e2 [a,16; b,16] [])
           (\s s'. true)`,
  REWRITE_TAC[C_ARGUMENTS; fst CT_COMPARE_16_EXEC] THEN
  META_EXISTS_TAC THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  AARCH32_STEPS_TAC CT_COMPARE_16_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
