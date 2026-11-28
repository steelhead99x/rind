(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aws-lc's gcm_init_neon, as rind's build emits it.                        *)
(* ========================================================================= *)

(* The A32 routine `gcm_init_neon` in rind's low::arm::ghash_armv4, which
   armv7 runs for GHASH without the crypto extension. Its theorems hold for
   a caller in A32 or T32, so they cover every armv7 target. *)

needs "aarch32/proofs/base.ml";;
needs "common/polyval_ghash.ml";;

(* admin/prove writes the routine's bytes, as rind's release build for
   armv7-unknown-linux-gnueabihf emits them, to armv7/gcm_init_neon.bin, and
   the definition fails unless they are these. The routine is A32 on every
   target. *)
let gcm_init_neon_mc = define_assert_word_list "gcm_init_neon_mc"
  (term_of_bytes (load_file "armv7/gcm_init_neon.bin"))
[
  0xf42177cd; (* vld1.64 {d7}, [r1]! *)
  0xf3c60e51; (* vmov.i8 q8, #0xe1 *)
  0xf42167cf; (* vld1.64 {d6}, [r1] *)
  0xf2f915b1; (* vshl.i64 d17, d17, #0x39 *)
  0xf3c100b0; (* vshr.u64 d16, d16, #0x3f *)
  0xf3ff2c47; (* vdup.8 q9, d7[7] *)
  0xf3c1a096; (* vshr.u64 d26, d6, #0x3f *)
  0xf2c92072; (* vshr.s8 q9, q9, #0x7 *)
  0xf28165d6; (* vshl.i64 q3, q3, #0x1 *)
  0xf24001f2; (* vand q8, q8, q9 *)
  0xf227713a; (* vorr d7, d7, d26 *)
  0xf3066170; (* veor q3, q3, q8 *)
  0xec806b04; (* vstmia r0, {d6, d7} *)
  0xe12fff1e; (* bx lr *)
];;

let GCM_INIT_NEON_EXEC = AARCH32_MK_EXEC_RULE gcm_init_neon_mc;;

(* rind passes H as two words, its first eight bytes as a big-endian number
   and then its last eight, so word_join hi lo is H's big-endian value. The
   routine stores ghash_twist of it, H times x modulo POLYVAL's polynomial
   x^128 + x^127 + x^126 + x^121 + 1, as s2n-bignum states it, the only
   entry of Htable that gcm_ghash_neon reads. *)
let GCM_INIT_NEON_CORRECT = prove
 (`!htable hp hi lo pc.
     aarch32_nowrap hp 16 /\ aligned 16 htable /\ aarch32_nowrap htable 16 /\
     nonoverlapping (word pc,0x38) (htable,16)
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) gcm_init_neon_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes64 hp) s = hi /\
               read (memory :> bytes64 (word_add hp (word 8))) s = lo)
          (\s. read PC s = word (pc + 0x34) /\
               read (memory :> bytes128 htable) s =
               ghash_twist (word_join hi lo))
          (MAYCHANGE [PC; R1] ,, MAYCHANGE [Q3; Q8; Q9; Q13] ,,
           MAYCHANGE [memory :> bytes128 htable] ,, MAYCHANGE [events])`,
  REWRITE_TAC[C_ARGUMENTS; fst GCM_INIT_NEON_EXEC; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (v,c) -> GHOST_INTRO_TAC v c)
   [`q3:int128`,`read Q3`; `q8:int128`,`read Q8`;
    `q9:int128`,`read Q9`; `q13:int128`,`read Q13`] THEN
  ENSURES_INIT_TAC "s0" THEN
  AARCH32_STEPS_TAC GCM_INIT_NEON_EXEC (1--13) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ghash_twist; POLYVAL_TWIST_CONST] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN BITBLAST_TAC);;

let GCM_INIT_NEON_SUBROUTINE_CORRECT = prove
 (`!htable hp hi lo pc returnaddress.
     aarch32_nowrap hp 16 /\ aligned 16 htable /\ aarch32_nowrap htable 16 /\
     nonoverlapping (word pc,0x38) (htable,16) /\
     aarch32_bx_target returnaddress
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) gcm_init_neon_mc /\
               read PC s = word pc /\
               read LR s = returnaddress /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes64 hp) s = hi /\
               read (memory :> bytes64 (word_add hp (word 8))) s = lo)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes128 htable) s =
               ghash_twist (word_join hi lo))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes128 htable])`,
  REWRITE_TAC[fst GCM_INIT_NEON_EXEC] THEN
  AARCH32_ADD_RETURN_NOSTACK_TAC GCM_INIT_NEON_EXEC
    (REWRITE_RULE[fst GCM_INIT_NEON_EXEC] GCM_INIT_NEON_CORRECT));;
