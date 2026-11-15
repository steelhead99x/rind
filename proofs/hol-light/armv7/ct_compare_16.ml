(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 16-byte constant-time compare, as rind's build emits it.                  *)
(* ========================================================================= *)

(* The asm! block in rind's low::arm::cpu::ct_compare_16, whose four 32-bit
   words of each block arrive in R0-R3 and R4, R5, R8, R12: R0 ends zero
   exactly when the blocks are equal. The block has no branch or memory
   access, so its trace is empty whatever the inputs. *)

needs "aarch32/proofs/base.ml";;

(* admin/prove writes the block's bytes, as rind's release build for
   armv7-unknown-linux-gnueabihf emits them, to armv7/ct_compare_16.bin, and the
   definition fails unless they are these. A target that builds Thumb-2 by
   default, as Android's does, emits other bytes, which this does not cover. *)
let ct_compare_16_mc = define_assert_word_list "ct_compare_16_mc"
  (term_of_bytes (load_file "armv7/ct_compare_16.bin"))
[
  0xe0200004;       (* aarch32_EOR R0 R0 R4 *)
  0xe0211005;       (* aarch32_EOR R1 R1 R5 *)
  0xe0222008;       (* aarch32_EOR R2 R2 R8 *)
  0xe023300c;       (* aarch32_EOR R3 R3 R12 *)
  0xe1800001;       (* aarch32_ORR R0 R0 R1 *)
  0xe1822003;       (* aarch32_ORR R2 R2 R3 *)
  0xe1800002        (* aarch32_ORR R0 R0 R2 *)
];;

let CT_COMPARE_16_EXEC = AARCH32_MK_EXEC_RULE ct_compare_16_mc;;

let CT_COMPARE_16_CORRECT = prove
 (`!a0 a1 a2 a3 b0 b1 b2 b3 pc.
        ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) ct_compare_16_mc /\
               read PC s = word pc /\
               read R0 s = a0 /\ read R1 s = a1 /\
               read R2 s = a2 /\ read R3 s = a3 /\
               read R4 s = b0 /\ read R5 s = b1 /\
               read R8 s = b2 /\ read R12 s = b3)
          (\s. read PC s = word (pc + 0x1c) /\
               (read R0 s = word 0 <=>
                a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3))
          (MAYCHANGE [PC; R0; R1; R2; R3] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a0:int32`; `a1:int32`; `a2:int32`; `a3:int32`;
    `b0:int32`; `b1:int32`; `b2:int32`; `b3:int32`; `pc:num`] THEN
  REWRITE_TAC[fst CT_COMPARE_16_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  AARCH32_STEPS_TAC CT_COMPARE_16_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0; CONJ_ACI]);;

let CT_COMPARE_16_SAFE = prove
 (`exists f_events.
       forall e a0 a1 a2 a3 b0 b1 b2 b3 pc.
           ensures aarch32
           (\s. aligned_bytes_loaded s (word pc) ct_compare_16_mc /\
                read PC s = word pc /\
                read R0 s = a0 /\ read R1 s = a1 /\
                read R2 s = a2 /\ read R3 s = a3 /\
                read R4 s = b0 /\ read R5 s = b1 /\
                read R8 s = b2 /\ read R12 s = b3 /\
                read events s = e)
           (\s. read PC s = word (pc + 0x1c) /\
                exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pc /\
                    memaccess_inbounds e2 [] [])
           (\s s'. true)`,
  EXISTS_TAC `\pc:num. []:aarch32_uarch_event list` THEN
  MAP_EVERY X_GEN_TAC
   [`e:aarch32_uarch_event list`;
    `a0:int32`; `a1:int32`; `a2:int32`; `a3:int32`;
    `b0:int32`; `b1:int32`; `b2:int32`; `b3:int32`; `pc:num`] THEN
  REWRITE_TAC[fst CT_COMPARE_16_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  AARCH32_STEPS_TAC CT_COMPARE_16_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `[]:aarch32_uarch_event list` THEN
  REWRITE_TAC[APPEND; memaccess_inbounds_def; ALL]);;
