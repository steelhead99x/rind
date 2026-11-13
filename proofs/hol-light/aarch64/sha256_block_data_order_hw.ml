(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 block compression with the Armv8 crypto extension, as rind's      *)
(* build emits it.                                                           *)
(* ========================================================================= *)

(* rind's naked function low::aarch64::sha256::sha256_block_data_order_hw is
   aws-lc's sha256_block_data_order_hw (crypto/fipsmodule/sha/asm/
   sha256-armv8.pl, the ARMv8 path), which reads its round constants from the
   K256 table beside it. Its result is s2n-bignum's FIPS 180-4 spec,
   sha256_hash_blocks, from s2n-bignum pull request #415, which
   rind's fork of s2n-bignum holds until it merges. The proof steps the
   loop body's 115 instructions symbolically, rewriting each SHA256H/SHA256H2
   pair to four rounds and each SHA256SU0/SHA256SU1 pair to four message
   schedule words, so no case split on the data is needed. *)

needs "arm/proofs/base.ml";;
needs "x86/proofs/utils/sha256_spec.ml";;

(* admin/prove writes the function's object, as rind's release build emits
   it, to aarch64/sha256_block_data_order_hw.o: its instructions as .text,
   with relocations, and the K256 table as .rodata. The definition fails
   unless the instructions and relocations are these, and sha256_hw_k256 is
   the table's bytes, which SHA256_HW_K256_QUADS checks against FIPS 180-4's
   constants. *)
let sha256_hw_mc,sha256_hw_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(fun _ -> "sha256_hw_k256")
    "sha256_hw_mc" "aarch64/sha256_block_data_order_hw.o"
(fun w BL ADR ADRP ADD_rri64 -> [
  w 0xa9bf7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0x4c40a800;         (* arm_LDP Q0 Q1 X0 No_Offset *)
  ADRP (mk_var("sha256_hw_k256",`:num`),0,12,3);
  ADD_rri64 (mk_var("sha256_hw_k256",`:num`),0,3,3);
  w 0x4cdf2024;         (* arm_LDP4 Q4 Q5 Q6 Q7 X1 (Postimmediate_Offset (word 64)) *)
  w 0xd1000442;         (* arm_SUB X2 X2 (rvalue (word 1)) *)
  w 0x4cdf7870;         (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e200884;         (* arm_REV32_VEC Q4 Q4 8 *)
  w 0x6e2008a5;         (* arm_REV32_VEC Q5 Q5 8 *)
  w 0x6e2008c6;         (* arm_REV32_VEC Q6 Q6 8 *)
  w 0x6e2008e7;         (* arm_REV32_VEC Q7 Q7 8 *)
  w 0x4ea01c12;         (* arm_MOV_VEC Q18 Q0 128 *)
  w 0x4ea11c33;         (* arm_MOV_VEC Q19 Q1 128 *)
  w 0x4cdf7871;         (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea48610;         (* arm_ADD_VEC Q16 Q16 Q4 32 128 *)
  w 0x5e2828a4;         (* arm_SHA256SU0 Q4 Q5 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e104020;         (* arm_SHA256H Q0 Q1 Q16 *)
  w 0x5e105041;         (* arm_SHA256H2 Q1 Q2 Q16 *)
  w 0x5e0760c4;         (* arm_SHA256SU1 Q4 Q6 Q7 *)
  w 0x4cdf7870;         (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea58631;         (* arm_ADD_VEC Q17 Q17 Q5 32 128 *)
  w 0x5e2828c5;         (* arm_SHA256SU0 Q5 Q6 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e114020;         (* arm_SHA256H Q0 Q1 Q17 *)
  w 0x5e115041;         (* arm_SHA256H2 Q1 Q2 Q17 *)
  w 0x5e0460e5;         (* arm_SHA256SU1 Q5 Q7 Q4 *)
  w 0x4cdf7871;         (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea68610;         (* arm_ADD_VEC Q16 Q16 Q6 32 128 *)
  w 0x5e2828e6;         (* arm_SHA256SU0 Q6 Q7 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e104020;         (* arm_SHA256H Q0 Q1 Q16 *)
  w 0x5e105041;         (* arm_SHA256H2 Q1 Q2 Q16 *)
  w 0x5e056086;         (* arm_SHA256SU1 Q6 Q4 Q5 *)
  w 0x4cdf7870;         (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea78631;         (* arm_ADD_VEC Q17 Q17 Q7 32 128 *)
  w 0x5e282887;         (* arm_SHA256SU0 Q7 Q4 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e114020;         (* arm_SHA256H Q0 Q1 Q17 *)
  w 0x5e115041;         (* arm_SHA256H2 Q1 Q2 Q17 *)
  w 0x5e0660a7;         (* arm_SHA256SU1 Q7 Q5 Q6 *)
  w 0x4cdf7871;         (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea48610;         (* arm_ADD_VEC Q16 Q16 Q4 32 128 *)
  w 0x5e2828a4;         (* arm_SHA256SU0 Q4 Q5 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e104020;         (* arm_SHA256H Q0 Q1 Q16 *)
  w 0x5e105041;         (* arm_SHA256H2 Q1 Q2 Q16 *)
  w 0x5e0760c4;         (* arm_SHA256SU1 Q4 Q6 Q7 *)
  w 0x4cdf7870;         (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea58631;         (* arm_ADD_VEC Q17 Q17 Q5 32 128 *)
  w 0x5e2828c5;         (* arm_SHA256SU0 Q5 Q6 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e114020;         (* arm_SHA256H Q0 Q1 Q17 *)
  w 0x5e115041;         (* arm_SHA256H2 Q1 Q2 Q17 *)
  w 0x5e0460e5;         (* arm_SHA256SU1 Q5 Q7 Q4 *)
  w 0x4cdf7871;         (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea68610;         (* arm_ADD_VEC Q16 Q16 Q6 32 128 *)
  w 0x5e2828e6;         (* arm_SHA256SU0 Q6 Q7 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e104020;         (* arm_SHA256H Q0 Q1 Q16 *)
  w 0x5e105041;         (* arm_SHA256H2 Q1 Q2 Q16 *)
  w 0x5e056086;         (* arm_SHA256SU1 Q6 Q4 Q5 *)
  w 0x4cdf7870;         (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea78631;         (* arm_ADD_VEC Q17 Q17 Q7 32 128 *)
  w 0x5e282887;         (* arm_SHA256SU0 Q7 Q4 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e114020;         (* arm_SHA256H Q0 Q1 Q17 *)
  w 0x5e115041;         (* arm_SHA256H2 Q1 Q2 Q17 *)
  w 0x5e0660a7;         (* arm_SHA256SU1 Q7 Q5 Q6 *)
  w 0x4cdf7871;         (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea48610;         (* arm_ADD_VEC Q16 Q16 Q4 32 128 *)
  w 0x5e2828a4;         (* arm_SHA256SU0 Q4 Q5 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e104020;         (* arm_SHA256H Q0 Q1 Q16 *)
  w 0x5e105041;         (* arm_SHA256H2 Q1 Q2 Q16 *)
  w 0x5e0760c4;         (* arm_SHA256SU1 Q4 Q6 Q7 *)
  w 0x4cdf7870;         (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea58631;         (* arm_ADD_VEC Q17 Q17 Q5 32 128 *)
  w 0x5e2828c5;         (* arm_SHA256SU0 Q5 Q6 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e114020;         (* arm_SHA256H Q0 Q1 Q17 *)
  w 0x5e115041;         (* arm_SHA256H2 Q1 Q2 Q17 *)
  w 0x5e0460e5;         (* arm_SHA256SU1 Q5 Q7 Q4 *)
  w 0x4cdf7871;         (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea68610;         (* arm_ADD_VEC Q16 Q16 Q6 32 128 *)
  w 0x5e2828e6;         (* arm_SHA256SU0 Q6 Q7 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e104020;         (* arm_SHA256H Q0 Q1 Q16 *)
  w 0x5e105041;         (* arm_SHA256H2 Q1 Q2 Q16 *)
  w 0x5e056086;         (* arm_SHA256SU1 Q6 Q4 Q5 *)
  w 0x4cdf7870;         (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea78631;         (* arm_ADD_VEC Q17 Q17 Q7 32 128 *)
  w 0x5e282887;         (* arm_SHA256SU0 Q7 Q4 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e114020;         (* arm_SHA256H Q0 Q1 Q17 *)
  w 0x5e115041;         (* arm_SHA256H2 Q1 Q2 Q17 *)
  w 0x5e0660a7;         (* arm_SHA256SU1 Q7 Q5 Q6 *)
  w 0x4cdf7871;         (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea48610;         (* arm_ADD_VEC Q16 Q16 Q4 32 128 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e104020;         (* arm_SHA256H Q0 Q1 Q16 *)
  w 0x5e105041;         (* arm_SHA256H2 Q1 Q2 Q16 *)
  w 0x4cdf7870;         (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ea58631;         (* arm_ADD_VEC Q17 Q17 Q5 32 128 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e114020;         (* arm_SHA256H Q0 Q1 Q17 *)
  w 0x5e115041;         (* arm_SHA256H2 Q1 Q2 Q17 *)
  w 0x4c407871;         (* arm_LDR Q17 X3 No_Offset *)
  w 0x4ea68610;         (* arm_ADD_VEC Q16 Q16 Q6 32 128 *)
  w 0xd103c063;         (* arm_SUB X3 X3 (rvalue (word 240)) *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e104020;         (* arm_SHA256H Q0 Q1 Q16 *)
  w 0x5e105041;         (* arm_SHA256H2 Q1 Q2 Q16 *)
  w 0x4ea78631;         (* arm_ADD_VEC Q17 Q17 Q7 32 128 *)
  w 0x4ea01c02;         (* arm_MOV_VEC Q2 Q0 128 *)
  w 0x5e114020;         (* arm_SHA256H Q0 Q1 Q17 *)
  w 0x5e115041;         (* arm_SHA256H2 Q1 Q2 Q17 *)
  w 0x4eb28400;         (* arm_ADD_VEC Q0 Q0 Q18 32 128 *)
  w 0x4eb38421;         (* arm_ADD_VEC Q1 Q1 Q19 32 128 *)
  w 0xb5fff1a2;         (* arm_CBNZ X2 (word 2096692) *)
  w 0x4c00a800;         (* arm_STP Q0 Q1 X0 No_Offset *)
  w 0xf84107fd;         (* arm_LDR X29 SP (Postimmediate_Offset (word 16)) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;
let sha256_hw_k256 = last sha256_hw_data;;
let SHA256_HW_EXEC = ARM_MK_EXEC_RULE sha256_hw_mc;;

(* ------------------------------------------------------------------------- *)
(* The SHA256H/SHA256H2 instructions as four rounds of the spec.             *)
(* ------------------------------------------------------------------------- *)

let sha256_quad = new_definition
 `sha256_quad (a:int32) (b:int32) (c:int32) (d:int32) : int128 =
    word_join (word_join d c:int64) (word_join b a:int64)`;;

let SHA256_QUAD_SUBWORDS = prove
 (`!a b c d:int32.
     word_subword (sha256_quad a b c d) (0,32) = a /\
     word_subword (sha256_quad a b c d) (32,32) = b /\
     word_subword (sha256_quad a b c d) (64,32) = c /\
     word_subword (sha256_quad a b c d) (96,32) = d`,
  REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST);;

let SHA256_ROL_LEMMA = prove
 (`!a b c d e f g h p q:int32.
     word_rol (word_join
        ((word_join:int32->96 word->int128) p (word_subword (sha256_quad a b c d) (0,96)))
        ((word_join:int32->96 word->int128) q (word_subword (sha256_quad e f g h) (0,96))) :256 word) 32 =
     word_join (sha256_quad q a b c) (sha256_quad p e f g)`,
  REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST);;

let SHA256HASH_LOOP_ROUND = prove
 (`!i a b c d e f g h k w W.
     elem W i 32 = word_add k w
     ==> sha256hash_loop i (sha256_quad a b c d) (sha256_quad e f g h) W =
         let l = sha256_round [a;b;c;d;e;f;g;h] k w in
         word_join (sha256_quad (EL 0 l) (EL 1 l) (EL 2 l) (EL 3 l))
                   (sha256_quad (EL 4 l) (EL 5 l) (EL 6 l) (EL 7 l))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha256hash_loop; sha256_round] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA256_QUAD_SUBWORDS; SHA256_ROL_LEMMA] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[WORD_ADD_AC]);;

let sha256_abcd = new_definition
 `sha256_abcd (l:int32 list) = sha256_quad (EL 0 l) (EL 1 l) (EL 2 l) (EL 3 l)`;;
let sha256_efgh = new_definition
 `sha256_efgh (l:int32 list) = sha256_quad (EL 4 l) (EL 5 l) (EL 6 l) (EL 7 l)`;;

let SHA256_ROUND_ELS = prove
 (`!l k w. sha256_round l k w =
           sha256_round [EL 0 l; EL 1 l; EL 2 l; EL 3 l; EL 4 l; EL 5 l; EL 6 l; EL 7 l] k w`,
  REWRITE_TAC[sha256_round] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let SHA256HASH_LOOP_STATE = prove
 (`!i l k w W.
     elem W i 32 = word_add k w
     ==> sha256hash_loop i (sha256_abcd l) (sha256_efgh l) W =
         word_join (sha256_abcd (sha256_round l k w)) (sha256_efgh (sha256_round l k w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sha256_abcd; sha256_efgh] THEN
  ASM_SIMP_TAC[SHA256HASH_LOOP_ROUND] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SHA256_ROUND_ELS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;

let SHA256_JOIN128_SUBWORDS = prove
 (`!x y:int128. word_subword ((word_join:int128->int128->256 word) x y) (128,128) = x /\
                word_subword ((word_join:int128->int128->256 word) x y) (0,128) = y`,
  CONV_TAC WORD_BLAST);;

let SHA256_ELEM_QUAD = prove
 (`!a b c d:int32. elem (sha256_quad a b c d) 0 32 = a /\ elem (sha256_quad a b c d) 1 32 = b /\
                   elem (sha256_quad a b c d) 2 32 = c /\ elem (sha256_quad a b c d) 3 32 = d`,
  REWRITE_TAC[elem] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[SHA256_QUAD_SUBWORDS]);;

let SHA256HASH_LOOP_QUAD = prove
 (`!k0 w0 k1 w1 k2 w2 k3 w3.
     let W = sha256_quad (word_add k0 w0) (word_add k1 w1) (word_add k2 w2) (word_add k3 w3) in
     (!l. sha256hash_loop 0 (sha256_abcd l) (sha256_efgh l) W =
          word_join (sha256_abcd (sha256_round l k0 w0)) (sha256_efgh (sha256_round l k0 w0))) /\
     (!l. sha256hash_loop 1 (sha256_abcd l) (sha256_efgh l) W =
          word_join (sha256_abcd (sha256_round l k1 w1)) (sha256_efgh (sha256_round l k1 w1))) /\
     (!l. sha256hash_loop 2 (sha256_abcd l) (sha256_efgh l) W =
          word_join (sha256_abcd (sha256_round l k2 w2)) (sha256_efgh (sha256_round l k2 w2))) /\
     (!l. sha256hash_loop 3 (sha256_abcd l) (sha256_efgh l) W =
          word_join (sha256_abcd (sha256_round l k3 w3)) (sha256_efgh (sha256_round l k3 w3)))`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC SHA256HASH_LOOP_STATE THEN
  REWRITE_TAC[SHA256_ELEM_QUAD]);;

let SHA256H_4ROUNDS = prove
 (`!l k0 k1 k2 k3 w0 w1 w2 w3.
     let W = sha256_quad (word_add k0 w0) (word_add k1 w1) (word_add k2 w2) (word_add k3 w3) in
     let l4 = sha256_round (sha256_round (sha256_round (sha256_round l k0 w0) k1 w1) k2 w2) k3 w3 in
     sha256h (sha256_abcd l) (sha256_efgh l) W = sha256_abcd l4 /\
     sha256h2 (sha256_efgh l) (sha256_abcd l) W = sha256_efgh l4`,
  REPEAT GEN_TAC THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (SPECL [`k0:int32`; `w0:int32`; `k1:int32`; `w1:int32`;
            `k2:int32`; `w2:int32`; `k3:int32`; `w3:int32`] SHA256HASH_LOOP_QUAD)) THEN
  STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha256h; sha256h2; sha256hash] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[SHA256_JOIN128_SUBWORDS]);;
(* ------------------------------------------------------------------------- *)
(* The SHA256SU0/SHA256SU1 instructions as the message schedule.             *)
(* ------------------------------------------------------------------------- *)

let SHA256_QUAD_NESTED = prove
 (`!a b c d:int32.
     sha256_quad a b c d =
     (word_join:int32->96 word->int128) d
       ((word_join:int32->64 word->96 word) c ((word_join:int32->int32->int64) b a))`,
  REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST);;

let SHA256SU_SCHEDULE = prove
 (`!w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15:int32.
     let x16 = word_add (word_add (sha_msg_sigma_1 w14) w9) (word_add (sha_msg_sigma_0 w1) w0) in
     let x17 = word_add (word_add (sha_msg_sigma_1 w15) w10) (word_add (sha_msg_sigma_0 w2) w1) in
     let x18 = word_add (word_add (sha_msg_sigma_1 x16) w11) (word_add (sha_msg_sigma_0 w3) w2) in
     let x19 = word_add (word_add (sha_msg_sigma_1 x17) w12) (word_add (sha_msg_sigma_0 w4) w3) in
     sha256su1 (sha256su0 (sha256_quad w0 w1 w2 w3) (sha256_quad w4 w5 w6 w7))
               (sha256_quad w8 w9 w10 w11) (sha256_quad w12 w13 w14 w15) =
     sha256_quad x16 x17 x18 x19`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha256su0; sha256su1; sha256su0_loop; sha256su1_loop0; sha256su1_loop1; elem] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[SHA256_QUAD_NESTED] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[sha_msg_sigma_0; sha_msg_sigma_1] THEN
  REWRITE_TAC[WORD_ADD_AC]);;
(* ------------------------------------------------------------------------- *)
(* Four rounds and four schedule words at a time, for the loop body.         *)
(* ------------------------------------------------------------------------- *)

let SHA256_REVERSE_BYTEREVERSE = prove
 (`!x:int32. word_reversefields 8 (word_bytereverse x) = x`,
  CONV_TAC WORD_BLAST);;

let SHA256_ROUNDS_STEP = prove
 (`!m hs n.
     sha256h (sha256_abcd (sha256_compress_rounds m hs n)) (sha256_efgh (sha256_compress_rounds m hs n))
       (sha256_quad (word_add (EL n sha256_constants) (sha256_msg_schedule m n))
                    (word_add (EL (n+1) sha256_constants) (sha256_msg_schedule m (n+1)))
                    (word_add (EL (n+2) sha256_constants) (sha256_msg_schedule m (n+2)))
                    (word_add (EL (n+3) sha256_constants) (sha256_msg_schedule m (n+3)))) =
     sha256_abcd (sha256_compress_rounds m hs (n+4)) /\
     sha256h2 (sha256_efgh (sha256_compress_rounds m hs n)) (sha256_abcd (sha256_compress_rounds m hs n))
       (sha256_quad (word_add (EL n sha256_constants) (sha256_msg_schedule m n))
                    (word_add (EL (n+1) sha256_constants) (sha256_msg_schedule m (n+1)))
                    (word_add (EL (n+2) sha256_constants) (sha256_msg_schedule m (n+2)))
                    (word_add (EL (n+3) sha256_constants) (sha256_msg_schedule m (n+3)))) =
     sha256_efgh (sha256_compress_rounds m hs (n+4))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 4 = (((n + 1) + 1) + 1) + 1`] THEN
  REWRITE_TAC[sha256_compress_rounds] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV) (ISPEC `sha256_compress_rounds m hs n` SHA256H_4ROUNDS)) THEN
  SIMP_TAC[]);;

let SHA256_MSG_SCHEDULE_REC = prove
 (`!m t. sha256_msg_schedule m (t + 16) =
         word_add (word_add (sha_msg_sigma_1 (sha256_msg_schedule m (t + 14)))
                            (sha256_msg_schedule m (t + 9)))
                  (word_add (sha_msg_sigma_0 (sha256_msg_schedule m (t + 1)))
                            (sha256_msg_schedule m t))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [sha256_msg_schedule] THEN
  REWRITE_TAC[ARITH_RULE `~(t + 16 < 16) /\ (t + 16) - 2 = t + 14 /\ (t + 16) - 7 = t + 9 /\
                          (t + 16) - 15 = t + 1 /\ (t + 16) - 16 = t`]);;

let SHA256_SCHED_STEP = prove
 (`!m n.
     sha256su1
       (sha256su0
         (sha256_quad (sha256_msg_schedule m n) (sha256_msg_schedule m (n+1))
                      (sha256_msg_schedule m (n+2)) (sha256_msg_schedule m (n+3)))
         (sha256_quad (sha256_msg_schedule m (n+4)) (sha256_msg_schedule m (n+5))
                      (sha256_msg_schedule m (n+6)) (sha256_msg_schedule m (n+7))))
       (sha256_quad (sha256_msg_schedule m (n+8)) (sha256_msg_schedule m (n+9))
                    (sha256_msg_schedule m (n+10)) (sha256_msg_schedule m (n+11)))
       (sha256_quad (sha256_msg_schedule m (n+12)) (sha256_msg_schedule m (n+13))
                    (sha256_msg_schedule m (n+14)) (sha256_msg_schedule m (n+15))) =
     sha256_quad (sha256_msg_schedule m (n+16)) (sha256_msg_schedule m (n+17))
                 (sha256_msg_schedule m (n+18)) (sha256_msg_schedule m (n+19))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SHA256SU_SCHEDULE |> SPEC_ALL |> CONV_RULE(TOP_DEPTH_CONV let_CONV)] THEN
  let inst k = CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (REWRITE_RULE[GSYM ADD_ASSOC] (SPECL [`m:int32 list`; mk_comb(mk_comb(`(+)`,`n:num`),mk_small_numeral k)] SHA256_MSG_SCHEDULE_REC)) in
  REWRITE_TAC(GSYM(SPECL [`m:int32 list`; `n:num`] SHA256_MSG_SCHEDULE_REC) ::
              map (fun k -> GSYM(inst k)) [1;2;3]) THEN
  ALL_TAC);;
let SHA256_ROUNDS_AT n =
  let th = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (SPECL [`m:int32 list`; `hs:int32 list`; mk_small_numeral n] SHA256_ROUNDS_STEP) in
  if n = 0 then REWRITE_RULE[CONJUNCT1 sha256_compress_rounds] th else th;;
let SHA256_SCHED_AT n =
  CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (SPECL [`m:int32 list`; mk_small_numeral n] SHA256_SCHED_STEP);;
let SHA256_BODY_THS =
  map SHA256_ROUNDS_AT (0--15 |> map (( * ) 4)) @ map SHA256_SCHED_AT (0--11 |> map (( * ) 4));;

let SHA256_SIMP_QREG_TAC =
  let is_qread th =
    let c = concl th in
    is_eq c && (let l = lhs c in
      try let r,_ = dest_comb l in let rd,comp = dest_comb r in
          name_of rd = "read" && is_const comp && String.sub (name_of comp) 0 1 = "Q"
      with _ -> false) in
  let rule = REWRITE_RULE SHA256_BODY_THS o REWRITE_RULE[GSYM sha256_quad] o
             CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) o
             REWRITE_RULE[SHA256_QUAD_SUBWORDS; SHA256_REVERSE_BYTEREVERSE] in
  RULE_ASSUM_TAC(fun th -> if is_qread th then rule th else th);;

let SHA256_STEPS_TAC ns =
  MAP_EVERY (fun n -> ARM_STEPS_TAC SHA256_HW_EXEC [n] THEN SHA256_SIMP_QREG_TAC) ns;;

(* ------------------------------------------------------------------------- *)
(* The round constants and the message words in memory.                      *)
(* ------------------------------------------------------------------------- *)

let quad_of f i = list_mk_comb(`sha256_quad`, map (fun k -> f (i+k)) [0;1;2;3]);;
let kconst t = mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral t), `sha256_constants`);;

let SHA256_HW_K256_QUADS =
  let at j = mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` `k:num` (mk_small_numeral (16*j))) in
  let kfacts = list_mk_conj(map (fun j -> mk_eq(subst [at j,`a:int64`] `read (memory :> bytes128 a) s`, quad_of kconst (4*j))) (0--15)) in
  prove
  (mk_forall(`s:armstate`, mk_forall(`k:num`, mk_imp(`bytes_loaded s (word (k + 0)) sha256_hw_k256`, kfacts))),
   REPEAT GEN_TAC THEN REWRITE_TAC[sha256_hw_k256] THEN
   CONV_TAC(LAND_CONV DATA64_CONV) THEN STRIP_TAC THEN
   REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT); GSYM WORD_ADD] THEN
   REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
   ASM_REWRITE_TAC[sha256_quad; sha256_constants] THEN
   CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC WORD_REDUCE_CONV);;
let SHA256_READ_QUAD = prove
 (`!a s. read (memory :> bytes128 a) s =
         sha256_quad (read (memory :> bytes32 a) s)
                     (read (memory :> bytes32 (word_add a (word 4))) s)
                     (read (memory :> bytes32 (word_add a (word 8))) s)
                     (read (memory :> bytes32 (word_add a (word 12))) s)`,
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT);
              CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
  REWRITE_TAC[sha256_quad; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]);;

let sha256_hw_inputs = new_definition
 `sha256_hw_inputs (k256:num) (data:int64) (n:num) (m:num->int32 list) (M:int64->byte) <=>
    read (bytelist (word k256,LENGTH sha256_hw_k256)) M = sha256_hw_k256 /\
    !i j. i < n /\ j < 16
          ==> read (bytes32 (word_add data (word (64 * i + 4 * j)))) M =
              word_bytereverse (EL j (m i))`;;

let SHA256_MEM0_TAC =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("memory",_)),_)),Var("mem0",_)) ->
        RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th
    | _ -> failwith "SHA256_MEM0_TAC");;
let SHA256_MSCH_SMALL =
  map (fun t -> CONV_RULE(RAND_CONV(RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC REWRITE_CONV[]))
                  (REWR_CONV sha256_msg_schedule (mk_comb(`sha256_msg_schedule mm`, mk_small_numeral t))))
      (0--15);;

let SHA256_DATA_TAC =
  let dq q = let a = if q = 0 then `word_add (data:int64) (word (64 * i))`
                     else mk_comb(mk_comb(`word_add:int64->int64->int64`, `word_add (data:int64) (word (64 * i))`),
                                  mk_comb(`word:num->int64`, mk_small_numeral (16*q))) in
             mk_eq(subst [a,`a:int64`] `read (memory :> bytes128 (a:int64)) (s0:armstate)`,
                   quad_of (fun t -> mk_comb(`word_bytereverse:int32->int32`,
                     mk_comb(`sha256_msg_schedule (m(i:num))`, mk_small_numeral t))) (4*q)) in
  let goal = list_mk_conj(map dq (0--3)) in
  SUBGOAL_THEN goal STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [sha256_hw_inputs]) THEN
    DISCH_THEN(fun th -> MP_TAC(end_itlist CONJ (map (fun j -> SPECL [`i:num`; mk_small_numeral j] th) (0--15)))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    STRIP_TAC THEN
    REWRITE_TAC(SHA256_READ_QUAD :: READ_COMPONENT_COMPOSE :: SHA256_MSCH_SMALL) THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let SHA256_K256_TAC =
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [sha256_hw_inputs]) THEN
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("memory",_)),_)),Var("mem0",_)) ->
        REWRITE_TAC[SYM th; GSYM READ_COMPONENT_COMPOSE]
    | _ -> failwith "") THEN
  REWRITE_TAC[GSYM bytes_loaded] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `k256 = k256 + 0`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SHA256_HW_K256_QUADS) THEN
  REWRITE_TAC[ADD_CLAUSES; WORD_ADD; WORD_ADD_0] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness of the loop, from after the prologue to before the epilogue.  *)
(* ------------------------------------------------------------------------- *)

let SHA256_ABBREV_D_TAC =
  ABBREV_TAC `d = word_add data (word (64 * i)):int64` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th);;
let SHA256_QUAD_INJ = prove
 (`!a b c d x y z w:int32.
     sha256_quad a b c d = sha256_quad x y z w <=> a = x /\ b = y /\ c = z /\ d = w`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun p -> MP_TAC(AP_TERM (subst [p,`p:num#num`] `\q:int128. (word_subword q p:int32)`) th)) [`0,32`; `32,32`; `64,32`; `96,32`]) THEN
  REWRITE_TAC[SHA256_QUAD_SUBWORDS] THEN SIMP_TAC[]);;

let SHA256_READ_QUAD_SPLIT = prove
 (`!a s x0 x1 x2 x3.
     read (memory :> bytes128 a) s = sha256_quad x0 x1 x2 x3
     ==> read (memory :> bytes32 a) s = x0 /\
         read (memory :> bytes32 (word_add a (word 4))) s = x1 /\
         read (memory :> bytes32 (word_add a (word 8))) s = x2 /\
         read (memory :> bytes32 (word_add a (word 12))) s = x3`,
  REWRITE_TAC[SHA256_READ_QUAD; SHA256_QUAD_INJ]);;

let SHA256_HW_CORRECT = prove
 (`!pc k256 state data n h0 h1 h2 h3 h4 h5 h6 h7 m.
     0 < n /\ n < 2 EXP 64 /\
     nonoverlapping (word pc,0x1f0) (state,32) /\
     adrp_within_bounds (word k256) (word (pc + 12))
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) (sha256_hw_mc pc k256) /\
               read PC s = word(pc + 0x8) /\
               C_ARGUMENTS [state; data; word n] s /\
               bytes_loaded s (word k256) sha256_hw_k256 /\
               read (memory :> bytes32 state) s = h0 /\
               read (memory :> bytes32 (word_add state (word 4))) s = h1 /\
               read (memory :> bytes32 (word_add state (word 8))) s = h2 /\
               read (memory :> bytes32 (word_add state (word 12))) s = h3 /\
               read (memory :> bytes32 (word_add state (word 16))) s = h4 /\
               read (memory :> bytes32 (word_add state (word 20))) s = h5 /\
               read (memory :> bytes32 (word_add state (word 24))) s = h6 /\
               read (memory :> bytes32 (word_add state (word 28))) s = h7 /\
               (!i j. i < n /\ j < 16
                      ==> read (memory :> bytes32 (word_add data (word (64 * i + 4 * j)))) s =
                          word_bytereverse (EL j (m i))))
          (\s. read PC s = word(pc + 0x1e8) /\
               let h' = sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n in
               read (memory :> bytes32 state) s = EL 0 h' /\
               read (memory :> bytes32 (word_add state (word 4))) s = EL 1 h' /\
               read (memory :> bytes32 (word_add state (word 8))) s = EL 2 h' /\
               read (memory :> bytes32 (word_add state (word 12))) s = EL 3 h' /\
               read (memory :> bytes32 (word_add state (word 16))) s = EL 4 h' /\
               read (memory :> bytes32 (word_add state (word 20))) s = EL 5 h' /\
               read (memory :> bytes32 (word_add state (word 24))) s = EL 6 h' /\
               read (memory :> bytes32 (word_add state (word 28))) s = EL 7 h')
          (MAYCHANGE [PC; X1; X2; X3] ,,
           MAYCHANGE [Q0; Q1; Q2; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19] ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(state,32)])`,
  MAP_EVERY X_GEN_TAC [`pc:num`; `k256:num`; `state:int64`; `data:int64`; `n:num`;
    `h0:int32`; `h1:int32`; `h2:int32`; `h3:int32`; `h4:int32`; `h5:int32`; `h6:int32`; `h7:int32`;
    `m:num->int32 list`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; fst SHA256_HW_EXEC; bytes_loaded] THEN
  STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `n:num` `pc + 0x14` `pc + 0x1e0`
   `\i s. read X0 s = state /\
          read X1 s = word_add data (word (64 * i)) /\
          read X2 s = word (n - i) /\
          read X3 s = word k256 /\
          read Q0 s = sha256_abcd (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i) /\
          read Q1 s = sha256_efgh (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i) /\
          sha256_hw_inputs k256 data n m (read memory s)` THEN
  REPEAT CONJ_TAC THENL
   [(* n > 0 *)
    ASM_ARITH_TAC;
    GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `sha256_hw_inputs k256 data n m mem0` ASSUME_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[sha256_hw_inputs; GSYM READ_COMPONENT_COMPOSE]; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 state) s0 = sha256_quad h0 h1 h2 h3 /\
    read (memory :> bytes128 (word_add state (word 16))) s0 = sha256_quad h4 h5 h6 h7`
    STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[SHA256_READ_QUAD; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
    ARM_STEPS_TAC SHA256_HW_EXEC (1--3) THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[sha256_hash_blocks; sha256_abcd; sha256_efgh; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
    ENSURES_INIT_TAC "s0" THEN SHA256_MEM0_TAC THEN
    SHA256_DATA_TAC THEN SHA256_K256_TAC THEN SHA256_ABBREV_D_TAC THEN
    SHA256_STEPS_TAC (1--115) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; sha256_hash_blocks] THEN REWRITE_TAC[ADD1] THEN
    REWRITE_TAC[sha256_block; sha256_abcd; sha256_efgh; SHA256_QUAD_SUBWORDS] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC[WORD_ADD];
    EXPAND_TAC "d" THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; LEFT_ADD_DISTRIB; MULT_CLAUSES];
    REWRITE_TAC[WORD_SUB] THEN ASM_SIMP_TAC[ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`] THEN REWRITE_TAC[WORD_ADD] THEN
    CONV_TAC WORD_RULE];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
    ENSURES_INIT_TAC "s0" THEN SHA256_MEM0_TAC THEN
    ARM_STEPS_TAC SHA256_HW_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (word (n - i):int64) = n - i` SUBST1_TAC THENL
    [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> ~(n - i = 0)`]];
    REWRITE_TAC[SUB_REFL] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SHA256_HW_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP SHA256_READ_QUAD_SPLIT o
    REWRITE_RULE[sha256_abcd; sha256_efgh] o
    check (can (term_match [] `read (memory :> bytes128 a) s = x`) o concl))) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the whole function, with its frame and return.             *)
(* ------------------------------------------------------------------------- *)

let SHA256_HW_BYTES_LOADED = prove
 (`bytes_loaded s tab sha256_hw_k256 <=>
   read (memory :> bytes(tab,320)) s = num_of_bytelist sha256_hw_k256`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV) (AP_TERM `LENGTH:byte list->num` sha256_hw_k256)]);;

let SHA256_HW_SUBROUTINE_CORRECT = prove
 (`!pc k256 state data n h0 h1 h2 h3 h4 h5 h6 h7 m stackpointer returnaddress.
     0 < n /\ n < 2 EXP 64 /\
     aligned 16 stackpointer /\
     adrp_within_bounds (word k256) (word (pc + 12)) /\
     ALLPAIRS nonoverlapping
       [(state,32); (word_sub stackpointer (word 16),16)]
       [(word pc,0x1f0); (data,64 * n); (word k256,320)] /\
     nonoverlapping (state,32) (word_sub stackpointer (word 16),16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) (sha256_hw_mc pc k256) /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [state; data; word n] s /\
               bytes_loaded s (word k256) sha256_hw_k256 /\
               read (memory :> bytes32 state) s = h0 /\
               read (memory :> bytes32 (word_add state (word 4))) s = h1 /\
               read (memory :> bytes32 (word_add state (word 8))) s = h2 /\
               read (memory :> bytes32 (word_add state (word 12))) s = h3 /\
               read (memory :> bytes32 (word_add state (word 16))) s = h4 /\
               read (memory :> bytes32 (word_add state (word 20))) s = h5 /\
               read (memory :> bytes32 (word_add state (word 24))) s = h6 /\
               read (memory :> bytes32 (word_add state (word 28))) s = h7 /\
               (!i j. i < n /\ j < 16
                      ==> read (memory :> bytes32 (word_add data (word (64 * i + 4 * j)))) s =
                          word_bytereverse (EL j (m i))))
          (\s. read PC s = returnaddress /\
               let h' = sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n in
               read (memory :> bytes32 state) s = EL 0 h' /\
               read (memory :> bytes32 (word_add state (word 4))) s = EL 1 h' /\
               read (memory :> bytes32 (word_add state (word 8))) s = EL 2 h' /\
               read (memory :> bytes32 (word_add state (word 12))) s = EL 3 h' /\
               read (memory :> bytes32 (word_add state (word 16))) s = EL 4 h' /\
               read (memory :> bytes32 (word_add state (word 20))) s = EL 5 h' /\
               read (memory :> bytes32 (word_add state (word 24))) s = EL 6 h' /\
               read (memory :> bytes32 (word_add state (word 28))) s = EL 7 h')
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(state,32);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  REWRITE_TAC[SHA256_HW_BYTES_LOADED; fst SHA256_HW_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(2,1) SHA256_HW_EXEC
    (REWRITE_RULE[SHA256_HW_BYTES_LOADED; fst SHA256_HW_EXEC] SHA256_HW_CORRECT)
    `[X29; X30]` 16);;
