(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 block compression with the SHA extensions on x86_64, as rind's    *)
(* build emits it.                                                           *)
(* ========================================================================= *)

(* The asm! block in rind's low::x86_64::sha256::sha256_compress_blocks_shaext,
   whose state's address arrives in rdi, its n blocks' in rsi, n in rdx, and
   K's in rcx. SHA256_COMPRESS_BLOCKS_SHAEXT_CORRECT is that it stores to the
   state s2n-bignum's FIPS 180-4 spec, sha256_hash_blocks, of the blocks from
   the state, for every n, none included. The rounds are
   SHA256_SHAEXT_ROUNDS_CORRECT's. *)

needs "x86_64/sha256_shaext_rounds.ml";;

(* admin/prove writes the block's bytes, as rind's release build emits them,
   to x86_64/sha256_compress_blocks_shaext.bin, and the definition fails
   unless they are these, the rounds at 0x52. *)
let sha256_compress_blocks_shaext_mc =
  define_assert_word_list "sha256_compress_blocks_shaext_mc"
  (term_of_bytes (load_file "x86_64/sha256_compress_blocks_shaext.bin"))
 ([
  0xf3; 0x0f; 0x6f; 0x07;  (* MOVDQU (%_% xmm0) (Memop Word128 (%% (rdi,0))) *)
  0xf3; 0x0f; 0x6f; 0x4f; 0x10;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,16))) *)
  0x66; 0x0f; 0x70; 0xc0; 0xb1;
                           (* PSHUFD (%_% xmm0) (%_% xmm0) (Imm8 (word 177)) *)
  0x66; 0x44; 0x0f; 0x70; 0xd1; 0x1b;
                           (* PSHUFD (%_% xmm10) (%_% xmm1) (Imm8 (word 27)) *)
  0x66; 0x44; 0x0f; 0x6f; 0xd8;
                           (* MOVDQA (%_% xmm11) (%_% xmm0) *)
  0x66; 0x45; 0x0f; 0x3a; 0x0f; 0xda; 0x08;
                           (* PALIGNR (%_% xmm11) (%_% xmm10) (Imm8 (word 8)) *)
  0x66; 0x44; 0x0f; 0x3a; 0x0e; 0xd0; 0xf0;
                           (* PBLENDW (%_% xmm10) (%_% xmm0) (Imm8 (word 240)) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x0f; 0x84; 0x1f; 0x03; 0x00; 0x00;
                           (* JE (Imm32 (word 799)) *)
  0x66; 0x0f; 0x6f; 0xa1; 0x00; 0x01; 0x00; 0x00;
                           (* MOVDQA (%_% xmm4) (Memop Word128 (%% (rcx,256))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x36;
                           (* MOVDQU (%_% xmm14) (Memop Word128 (%% (rsi,0))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x7e; 0x10;
                           (* MOVDQU (%_% xmm15) (Memop Word128 (%% (rsi,16))) *)
  0xf3; 0x0f; 0x6f; 0x4e; 0x20;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rsi,32))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x66; 0x30;
                           (* MOVDQU (%_% xmm12) (Memop Word128 (%% (rsi,48))) *)
  0x48; 0x83; 0xc6; 0x40   (* ADD (% rsi) (Imm8 (word 64)) *)
] @ sha256_shaext_rounds @
  [
  0x48; 0x83; 0xea; 0x01;  (* SUB (% rdx) (Imm8 (word 1)) *)
  0x0f; 0x85; 0xe9; 0xfc; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966505)) *)
  0x66; 0x41; 0x0f; 0x70; 0xc3; 0x1b;
                           (* PSHUFD (%_% xmm0) (%_% xmm11) (Imm8 (word 27)) *)
  0x66; 0x41; 0x0f; 0x70; 0xca; 0xb1;
                           (* PSHUFD (%_% xmm1) (%_% xmm10) (Imm8 (word 177)) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x3a; 0x0e; 0xd1; 0xf0;
                           (* PBLENDW (%_% xmm2) (%_% xmm1) (Imm8 (word 240)) *)
  0x66; 0x0f; 0x3a; 0x0f; 0xc8; 0x08;
                           (* PALIGNR (%_% xmm1) (%_% xmm0) (Imm8 (word 8)) *)
  0xf3; 0x0f; 0x7f; 0x17;  (* MOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm2) *)
  0xf3; 0x0f; 0x7f; 0x4f; 0x10
                           (* MOVDQU (Memop Word128 (%% (rdi,16))) (%_% xmm1) *)
]);;

let SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC =
  X86_MK_EXEC_RULE sha256_compress_blocks_shaext_mc;;

let SHA256_COMPRESS_BLOCKS_SHAEXT_ROUNDS_LOADED =
  BYTES_LOADED_SUBPROGRAM_RULE sha256_compress_blocks_shaext_mc
    sha256_shaext_rounds_mc 0x52;;

(* The two stores to state, as eight words. *)
let SHA256_SHAEXT_STORED_TAC =
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP SHA256_READ_QUAD_SPLIT o
    check (can (term_match [] `read (memory :> bytes128 a) s = sha256_quad x0 x1 x2 x3`) o
           concl))) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN SIMP_TAC[];;

(* The loop runs from 0x38 to 0x349 for each block: four loads, the rounds,
   and the count's decrement, whose flag closes it. *)
let SHA256_COMPRESS_BLOCKS_SHAEXT_CORRECT = prove
 (`!pc state data n k h0 h1 h2 h3 h4 h5 h6 h7 m.
     n < 2 EXP 64 /\ aligned 16 (word k:int64) /\
     nonoverlapping (word pc,884) (state,32)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) sha256_compress_blocks_shaext_mc /\
               read RIP s = word pc /\
               read RDI s = state /\ read RSI s = data /\ read RDX s = word n /\
               read RCX s = word k /\ bytes_loaded s (word k) sha256_shaext_k /\
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
          (\s. read RIP s = word (pc + 884) /\
               let h' = sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n in
               read (memory :> bytes32 state) s = EL 0 h' /\
               read (memory :> bytes32 (word_add state (word 4))) s = EL 1 h' /\
               read (memory :> bytes32 (word_add state (word 8))) s = EL 2 h' /\
               read (memory :> bytes32 (word_add state (word 12))) s = EL 3 h' /\
               read (memory :> bytes32 (word_add state (word 16))) s = EL 4 h' /\
               read (memory :> bytes32 (word_add state (word 20))) s = EL 5 h' /\
               read (memory :> bytes32 (word_add state (word 24))) s = EL 6 h' /\
               read (memory :> bytes32 (word_add state (word 28))) s = EL 7 h')
          (MAYCHANGE [RIP; RSI; RDX] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM10; ZMM11; ZMM12; ZMM13;
                      ZMM14; ZMM15] ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(state,32)])`,
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `state:int64`; `data:int64`; `n:num`; `k:num`;
    `h0:int32`; `h1:int32`; `h2:int32`; `h3:int32`;
    `h4:int32`; `h5:int32`; `h6:int32`; `h7:int32`; `m:num->int32 list`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS;
              fst SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [(* No block: the state goes back as it came. *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[CONJUNCT1 sha256_hash_blocks] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
    SHA256_SHAEXT_YMM_INIT_TAC THEN SHA256_SHAEXT_STATE_TAC THEN
    SHA256_SHAEXT_STEPS_TAC SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC (1--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SHA256_SHAEXT_STORED_TAC;
    ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `n:num` `pc + 0x38` `pc + 0x349`
   `\i s. (read RDI s = state /\ read RSI s = word_add data (word (64 * i)) /\
           read RDX s = word (n - i) /\ read RCX s = word k /\
           read XMM4 s = word 16018520953223639909183530438118932995 /\
           read XMM11 s = sha256_abef (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i) /\
           read XMM10 s = sha256_cdgh (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i) /\
           sha256_shaext_blocks_in k data n m (read memory s)) /\
          (read ZF s <=> i = n)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* The state's loads, and the mask's. *)
    VAL_INT64_TAC `n:num` THEN
    GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
    SHA256_SHAEXT_YMM_INIT_TAC THEN SHA256_SHAEXT_MEM0_TAC THEN
    SHA256_SHAEXT_INPUTS_TAC [sha256_shaext_blocks_in]
      `sha256_shaext_blocks_in k data n m mem0` THEN
    SHA256_SHAEXT_K_TAC THEN SHA256_SHAEXT_STATE_TAC THEN
    SHA256_SHAEXT_STEPS_TAC SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHA256_SHAEXT_LOADED_STATE_TAC;

    (* A block. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
    SHA256_SHAEXT_YMM_INIT_TAC THEN SHA256_SHAEXT_MEM0_TAC THEN
    SHA256_SHAEXT_BLOCK_TAC `i:num` THEN
    SHA256_SHAEXT_STEPS_TAC SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC (1--5) THEN
    SHA256_SHAEXT_K_LOADED_TAC "s5" THEN
    MP_TAC(SPECL [`pc + 0x52`; `k:num`; `(m:num->int32 list) i`;
                  `sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i`]
                 SHA256_SHAEXT_ROUNDS_CORRECT) THEN
    X86_BIGSTEP_TAC SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC "s6" THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_ACCEPT_TAC o
                    MATCH_MP SHA256_COMPRESS_BLOCKS_SHAEXT_ROUNDS_LOADED);
        REWRITE_TAC[READ_XMM_YMM] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV)) THEN
    SHA256_SHAEXT_STEPS_TAC SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC [7] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_XMM_YMM; sha256_hash_blocks] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
    SUBGOAL_THEN `n - i = (n - (i + 1)) + 1` SUBST1_TAC THENL
     [UNDISCH_TAC `i < n` THEN ARITH_TAC; REWRITE_TAC[WORD_SUB_ADD]] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64;
                 ARITH_RULE `n < 2 EXP 64 ==> n - (i + 1) < 2 EXP 64`] THEN
    UNDISCH_TAC `i < n` THEN ARITH_TAC;

    (* The back edge. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
    ENSURES_INIT_TAC "s0" THEN SHA256_SHAEXT_MEM0_TAC THEN
    X86_STEPS_TAC SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (* The state's stores. *)
    REWRITE_TAC[sha256_abef; sha256_cdgh] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    SHA256_SHAEXT_YMM_INIT_TAC THEN
    SHA256_SHAEXT_STEPS_TAC SHA256_COMPRESS_BLOCKS_SHAEXT_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SHA256_SHAEXT_STORED_TAC]);;
