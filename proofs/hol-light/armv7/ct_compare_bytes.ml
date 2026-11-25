(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time byte compare, as rind's build emits it.                     *)
(* ========================================================================= *)

(* The asm! block in rind's low::arm::cpu::ct_compare_bytes, which ORs
   together the XOR of each pair of bytes at R0 and R1, R2 of them, into R3,
   zero on entry. R3 ends below 256, and zero exactly when the bytes are
   equal. Its loads and branches depend only on R0, R1, and R2. *)

needs "aarch32/proofs/base.ml";;
needs "aarch32/proofs/consttime.ml";;

(* admin/prove writes the block's bytes, as rind's release build for
   armv7-unknown-linux-gnueabihf emits them, to armv7/ct_compare_bytes.bin, and the
   definition fails unless they are these. A target that builds Thumb-2 by
   default, as Android's does, emits other bytes, which this does not cover. *)
let ct_compare_bytes_mc = define_assert_word_list "ct_compare_bytes_mc"
  (term_of_bytes (load_file "armv7/ct_compare_bytes.bin"))
[
  0xe2522001;       (* aarch32_SUBS R2 R2 (rvalue (word 1)) *)
  0x3a000004;       (* aarch32_B (word 3) (word 24) *)
  0xe4d0c001;       (* aarch32_LDRB (word 14) R12 R0 (rvalue (word 1)) F T *)
  0xe4d1e001;       (* aarch32_LDRB (word 14) LR R1 (rvalue (word 1)) F T *)
  0xe02cc00e;       (* aarch32_EOR R12 R12 LR *)
  0xe183300c;       (* aarch32_ORR R3 R3 R12 *)
  0xeafffff8        (* aarch32_B (word 14) (word 4294967272) *)
];;

let CT_COMPARE_BYTES_EXEC = AARCH32_MK_EXEC_RULE ct_compare_bytes_mc;;

(* SUBS #1 of a word below 2^32 borrows exactly when it is zero. *)
let CT_COMPARE_BYTES_SUB1 = prove
 (`!m. ~(m = 0) /\ m < 2 EXP 32
       ==> word_sub (word m) (word 1):int32 = word(m - 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE
   `word_sub x (word 1):int32 = word y <=> x = word(y + 1)`] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let CT_COMPARE_BYTES_CARRY = prove
 (`!m. m < 2 EXP 32
       ==> (&m - &1:int = &(val(word_sub (word m) (word 1):int32)) <=>
            ~(m = 0))`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[]
  THENL
   [CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    ASM_SIMP_TAC[CT_COMPARE_BYTES_SUB1; VAL_WORD_EQ; DIMINDEX_32;
                 ARITH_RULE `m < n ==> m - 1 < n`; GSYM INT_OF_NUM_SUB;
                 ARITH_RULE `~(m = 0) ==> 1 <= m`]]);;

(* Two strings of i + 1 bytes are equal exactly when their first i bytes
   and their last bytes are. *)
let CT_COMPARE_BYTES_STEP = prove
 (`!x y i.
        x MOD 2 EXP (8 * (i + 1)) = y MOD 2 EXP (8 * (i + 1)) <=>
        x MOD 2 EXP (8 * i) = y MOD 2 EXP (8 * i) /\
        (word(x DIV 2 EXP (8 * i)):byte) = word(y DIV 2 EXP (8 * i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; EXP_ADD; MOD_MULT_MOD] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[LEXICOGRAPHIC_EQ; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  CONV_TAC TAUT);;

(* A word below 256 is its low byte. *)
let CT_COMPARE_BYTES_VAL = prove
 (`!z:int32. val z < 256 <=> z = word_zx(word_zx z:byte)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; MOD_LT_EQ; ARITH_RULE `x < 256 ==> x < 4294967296`;
           ARITH_EQ] THEN
  MESON_TAC[MOD_EQ_SELF; ARITH_EQ]);;

(* The byte at offset i of a string is its value's digit i. *)
let CT_COMPARE_BYTES_LOAD = prove
 (`!(a:int32) n i x s.
        read (bytes(a,n)) s = x /\ i < n
        ==> read (bytes8 (word_add a (word i))) s = word(x DIV 2 EXP (8 * i))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_BYTES_DIV] THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 2 EXP (8 * 1)`; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < n ==> MIN (n - i) 1 = 1`] THEN
  REWRITE_TAC[READ_BYTES_BYTES8; WORD_VAL; WORD_MOD_SIZE]);;

(* The loop runs from the load at pc + 0x8, after the SUBS and BLO that
   test R2, through the BLO that leaves at pc + 0x1c once R2 runs out. That
   last SUBS wraps R2 to 2^32 - 1, so the invariant states R2 as a word
   difference. *)
let CT_COMPARE_BYTES_CORRECT = prove
 (`!a b n x y pc.
        ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) ct_compare_bytes_mc /\
               read PC s = word pc /\
               read R0 s = a /\ read R1 s = b /\ read R2 s = n /\
               read R3 s = word 0 /\
               read (memory :> bytes(a,val n)) s = x /\
               read (memory :> bytes(b,val n)) s = y)
          (\s. read PC s = word (pc + 0x1c) /\
               val(read R3 s) < 256 /\
               (read R3 s = word 0 <=> x = y))
          (MAYCHANGE [PC; R0; R1; R2; R3; R12; LR] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int32`; `b:int32`] THEN
  W32_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; fst CT_COMPARE_BYTES_EXEC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN
    AARCH32_STEPS_TAC CT_COMPARE_BYTES_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    REWRITE_TAC[VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `n:num` `pc + 0x8` `pc + 0x1c`
   `\i s. read R0 s = word_add a (word i) /\
          read R1 s = word_add b (word i) /\
          read R2 s = word_sub (word n) (word(i + 1)) /\
          val(read R3 s) < 256 /\
          read (memory :> bytes(a,n)) s = x /\
          read (memory :> bytes(b,n)) s = y /\
          (read R3 s = word 0 <=>
           x MOD 2 EXP (8 * i) = y MOD 2 EXP (8 * i))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    AARCH32_STEPS_TAC CT_COMPARE_BYTES_EXEC (1--2) THEN
    MP_TAC(SPEC `n:num` CT_COMPARE_BYTES_CARRY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; WORD_ADD_0; ADD_CLAUSES; MULT_CLAUSES; EXP;
                MOD_1] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    BINOP_TAC THEN MATCH_MP_TAC MOD_LT THEN
    ASM_MESON_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE]] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `acc:int32` `read R3` THEN
  SUBGOAL_THEN `word_sub (word n) (word(i + 1)):int32 = word(n - (i + 1))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < n ==> i + 1 <= n`]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`a:int32`; `n:num`; `i:num`; `x:num`; `read memory s0`]
    CT_COMPARE_BYTES_LOAD) THEN
  MP_TAC(SPECL [`b:int32`; `n:num`; `i:num`; `y:num`; `read memory s0`]
    CT_COMPARE_BYTES_LOAD) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN ASSUME_TAC) THEN
  VAL_INT32_TAC `n - (i + 1)` THEN
  AARCH32_STEPS_TAC CT_COMPARE_BYTES_EXEC (1--7) THEN
  MP_TAC(SPEC `n - (i + 1)` CT_COMPARE_BYTES_CARRY) THEN
  ANTS_TAC THENL [UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n - (i + 1) = 0 <=> ~(i + 1 < n)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `word(n - (i + 1)):int32 = word_sub (word n) (word(i + 1))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < n ==> i + 1 <= n`]; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `?c:byte. acc:int32 = word_zx c`
   (X_CHOOSE_THEN `c:byte` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `word_zx(acc:int32):byte` THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT; ARITH_RULE
      `x < 256 ==> x < 4294967296`];
    ALL_TAC] THEN
  REWRITE_TAC[CT_COMPARE_BYTES_STEP] THEN
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && free_in `c:byte` (concl th)
    then REWRITE_TAC[GSYM th] else failwith "not IH") THEN
  MAP_EVERY SPEC_TAC
   [`word(x DIV 2 EXP (8 * i)):byte`,`u:byte`;
    `word(y DIV 2 EXP (8 * i)):byte`,`v:byte`] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CT_COMPARE_BYTES_VAL] THEN
  CONJ_TAC THEN BITBLAST_TAC);;

(* The trace, its loads and branches, is a function of R0, R1, and R2 alone,
   and every load lands inside the two strings. *)
let CT_COMPARE_BYTES_SAFE = prove
 (`exists f_events.
       forall e a b n pc.
           ensures aarch32
           (\s. aligned_bytes_loaded s (word pc) ct_compare_bytes_mc /\
                read PC s = word pc /\
                read R0 s = a /\ read R1 s = b /\ read R2 s = n /\
                read events s = e)
           (\s. read PC s = word (pc + 0x1c) /\
                exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a b n pc /\
                    memaccess_inbounds e2 [a,val n; b,val n] [])
           (\s s'. true)`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int32) (b:int32) (n:int32) (pc:num).
      if val n = 0 then f_ev_zero a b n pc
      else APPEND (f_ev_post a b n pc)
             (APPEND (ENUMERATEL (val n) (f_ev_loop a b n pc))
                     (f_ev_entry a b n pc))
      :(aarch32_uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int32`; `b:int32`] THEN
  W32_GEN_TAC `n:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[fst CT_COMPARE_BYTES_EXEC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    AARCH32_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false CT_COMPARE_BYTES_EXEC (1--2) THEN
    ASM_REWRITE_TAC[WORD_SUB_0; VAL_WORD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `n:num` `pc + 0x8` `pc + 0x1c`
   `\i s. read R0 s = word_add a (word i) /\
          read R1 s = word_add b (word i) /\
          read R2 s = word_sub (word n) (word(i + 1))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    AARCH32_STEPS_TAC CT_COMPARE_BYTES_EXEC (1--2) THEN
    MP_TAC(SPEC `n:num` CT_COMPARE_BYTES_CARRY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_SUB_0; WORD_ADD_0; ADD_CLAUSES; VAL_WORD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC;
    REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word n) (word(i + 1)):int32 = word(n - (i + 1))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < n ==> i + 1 <= n`]; ALL_TAC] THEN
  VAL_INT32_TAC `n - (i + 1)` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  AARCH32_STEPS_TAC CT_COMPARE_BYTES_EXEC (1--7) THEN
  MP_TAC(SPEC `n - (i + 1)` CT_COMPARE_BYTES_CARRY) THEN
  ANTS_TAC THENL [UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `n - (i + 1) = 0 <=> ~(i + 1 < n)`] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `word(n - (i + 1)):int32 = word_sub (word n) (word(i + 1))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < n ==> i + 1 <= n`]; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
