(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256's last blocks and digest with the SHA extensions on x86_64, as    *)
(* rind's build emits them.                                                  *)
(* ========================================================================= *)

(* The asm! block in rind's low::x86_64::sha256::sha256_finish_shaext, whose
   state's address arrives in rsi, the message's n whole blocks' in rdx, n in
   rax, and K's in rcx. Rust builds the padded block's end in registers: r9
   is how many whole 16-byte lanes of the message follow the blocks, or 4
   when there are three and the length needs a block of its own, r10 and r11
   the lane after them, and r8 the length's last lane word.
   SHA256_FINISH_SHAEXT_CORRECT is that it leaves in xmm2 and xmm1 the
   digest's 32 bytes, as s2n-bignum's FIPS 180-4 spec, sha256_hash_blocks,
   computes it over the blocks and then the padded block or two:
   sha256_shaext_finish_blocks. *)

needs "x86_64/sha256_shaext_rounds.ml";;

(* admin/prove writes the block's bytes, as rind's release build emits them,
   to x86_64/sha256_finish_shaext.bin, and the definition fails unless they
   are these, the rounds at 0x6a. *)
let sha256_finish_shaext_mc =
  define_assert_word_list "sha256_finish_shaext_mc"
  (term_of_bytes (load_file "x86_64/sha256_finish_shaext.bin"))
 ([
  0xf3; 0x0f; 0x6f; 0x06;  (* MOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,0))) *)
  0xf3; 0x0f; 0x6f; 0x4e; 0x10;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rsi,16))) *)
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
  0x66; 0x0f; 0x6f; 0xa1; 0x00; 0x01; 0x00; 0x00;
                           (* MOVDQA (%_% xmm4) (Memop Word128 (%% (rcx,256))) *)
  0x48; 0x83; 0xe8; 0x01;  (* SUB (% rax) (Imm8 (word 1)) *)
  0x0f; 0x83; 0xa0; 0x03; 0x00; 0x00;
                           (* JAE (Imm32 (word 928)) *)
  0x49; 0x83; 0xf9; 0x01;  (* CMP (% r9) (Imm8 (word 1)) *)
  0x0f; 0x83; 0x3b; 0x03; 0x00; 0x00;
                           (* JAE (Imm32 (word 827)) *)
  0x66; 0x4d; 0x0f; 0x6e; 0xf2;
                           (* MOVQ (%_% xmm14) (% r10) *)
  0x66; 0x49; 0x0f; 0x6e; 0xc3;
                           (* MOVQ (%_% xmm0) (% r11) *)
  0x66; 0x44; 0x0f; 0x6c; 0xf0;
                           (* PUNPCKLQDQ (%_% xmm14) (%_% xmm0) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x66; 0x4d; 0x0f; 0x6e; 0xfb;
                           (* MOVQ (%_% xmm15) (% r11) *)
  0x66; 0x49; 0x0f; 0x6e; 0xcb;
                           (* MOVQ (%_% xmm1) (% r11) *)
  0x66; 0x4d; 0x0f; 0x6e; 0xe0;
                           (* MOVQ (%_% xmm12) (% r8) *)
  0x66; 0x45; 0x0f; 0x70; 0xe4; 0x4e
                           (* PSHUFD (%_% xmm12) (%_% xmm12) (Imm8 (word 78)) *)
] @ sha256_shaext_rounds @
  [
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x0f; 0x89; 0xc9; 0xfc; 0xff; 0xff;
                           (* JNS (Imm32 (word 4294966473)) *)
  0x49; 0x83; 0xf9; 0x04;  (* CMP (% r9) (Imm8 (word 4)) *)
  0x0f; 0x85; 0x88; 0x00; 0x00; 0x00;
                           (* JNE (Imm32 (word 136)) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0xe9; 0xbb; 0xfc; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294966459)) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x32;
                           (* MOVDQU (%_% xmm14) (Memop Word128 (%% (rdx,0))) *)
  0x74; 0x25;              (* JE (Imm8 (word 37)) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x7a; 0x10;
                           (* MOVDQU (%_% xmm15) (Memop Word128 (%% (rdx,16))) *)
  0x49; 0x83; 0xf9; 0x02;  (* CMP (% r9) (Imm8 (word 2)) *)
  0x74; 0x35;              (* JE (Imm8 (word 53)) *)
  0xf3; 0x0f; 0x6f; 0x4a; 0x20;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rdx,32))) *)
  0x66; 0x4d; 0x0f; 0x6e; 0xe2;
                           (* MOVQ (%_% xmm12) (% r10) *)
  0x66; 0x49; 0x0f; 0x6e; 0xc3;
                           (* MOVQ (%_% xmm0) (% r11) *)
  0x66; 0x44; 0x0f; 0x6c; 0xe0;
                           (* PUNPCKLQDQ (%_% xmm12) (%_% xmm0) *)
  0xe9; 0xc0; 0xfc; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294966464)) *)
  0x66; 0x4d; 0x0f; 0x6e; 0xfa;
                           (* MOVQ (%_% xmm15) (% r10) *)
  0x66; 0x49; 0x0f; 0x6e; 0xc3;
                           (* MOVQ (%_% xmm0) (% r11) *)
  0x66; 0x44; 0x0f; 0x6c; 0xf8;
                           (* PUNPCKLQDQ (%_% xmm15) (%_% xmm0) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x66; 0x49; 0x0f; 0x6e; 0xcb;
                           (* MOVQ (%_% xmm1) (% r11) *)
  0xe9; 0x99; 0xfc; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294966425)) *)
  0x66; 0x49; 0x0f; 0x6e; 0xca;
                           (* MOVQ (%_% xmm1) (% r10) *)
  0x66; 0x49; 0x0f; 0x6e; 0xc3;
                           (* MOVQ (%_% xmm0) (% r11) *)
  0x66; 0x0f; 0x6c; 0xc8;  (* PUNPCKLQDQ (%_% xmm1) (%_% xmm0) *)
  0xe9; 0x86; 0xfc; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294966406)) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x32;
                           (* MOVDQU (%_% xmm14) (Memop Word128 (%% (rdx,0))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x7a; 0x10;
                           (* MOVDQU (%_% xmm15) (Memop Word128 (%% (rdx,16))) *)
  0xf3; 0x0f; 0x6f; 0x4a; 0x20;
                           (* MOVDQU (%_% xmm1) (Memop Word128 (%% (rdx,32))) *)
  0xf3; 0x44; 0x0f; 0x6f; 0x62; 0x30;
                           (* MOVDQU (%_% xmm12) (Memop Word128 (%% (rdx,48))) *)
  0x48; 0x83; 0xc2; 0x40;  (* ADD (% rdx) (Imm8 (word 64)) *)
  0xe9; 0x72; 0xfc; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294966386)) *)
  0x66; 0x41; 0x0f; 0x70; 0xc3; 0x1b;
                           (* PSHUFD (%_% xmm0) (%_% xmm11) (Imm8 (word 27)) *)
  0x66; 0x41; 0x0f; 0x70; 0xca; 0xb1;
                           (* PSHUFD (%_% xmm1) (%_% xmm10) (Imm8 (word 177)) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x3a; 0x0e; 0xd1; 0xf0;
                           (* PBLENDW (%_% xmm2) (%_% xmm1) (Imm8 (word 240)) *)
  0x66; 0x0f; 0x3a; 0x0f; 0xc8; 0x08;
                           (* PALIGNR (%_% xmm1) (%_% xmm0) (Imm8 (word 8)) *)
  0x66; 0x0f; 0x38; 0x00; 0xd4;
                           (* PSHUFB (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0x38; 0x00; 0xcc
                           (* PSHUFB (%_% xmm1) (%_% xmm4) *)
]);;

let SHA256_FINISH_SHAEXT_EXEC = X86_MK_EXEC_RULE sha256_finish_shaext_mc;;

let SHA256_FINISH_SHAEXT_ROUNDS_LOADED =
  BYTES_LOADED_SUBPROGRAM_RULE sha256_finish_shaext_mc sha256_shaext_rounds_mc 0x6a;;

(* ------------------------------------------------------------------------- *)
(* The padded blocks.                                                        *)
(* ------------------------------------------------------------------------- *)

(* The words of a lane held as two little-endian registers. *)
let sha256_shaext_lane = new_definition
 `sha256_shaext_lane (x:int64) (y:int64) : int32 list =
    [word_bytereverse (word_subword x (0,32)); word_bytereverse (word_subword x (32,32));
     word_bytereverse (word_subword y (0,32)); word_bytereverse (word_subword y (32,32))]`;;

(* The padded block: r of t's lanes, at most three, the lane x and y hold,
   zeros, and l as the last lane's top word unless that lane is x and y. *)
let sha256_shaext_padded = new_definition
 `sha256_shaext_padded r (t:int32 list) x y (l:int64) : int32 list =
    if r = 0 then
      APPEND (sha256_shaext_lane x y)
       (APPEND (sha256_shaext_lane (word 0) (word 0))
         (APPEND (sha256_shaext_lane (word 0) (word 0))
                 (sha256_shaext_lane (word 0) l)))
    else if r = 1 then
      APPEND [EL 0 t; EL 1 t; EL 2 t; EL 3 t]
       (APPEND (sha256_shaext_lane x y)
         (APPEND (sha256_shaext_lane (word 0) (word 0))
                 (sha256_shaext_lane (word 0) l)))
    else if r = 2 then
      APPEND [EL 0 t; EL 1 t; EL 2 t; EL 3 t; EL 4 t; EL 5 t; EL 6 t; EL 7 t]
       (APPEND (sha256_shaext_lane x y) (sha256_shaext_lane (word 0) l))
    else
      APPEND [EL 0 t; EL 1 t; EL 2 t; EL 3 t; EL 4 t; EL 5 t; EL 6 t; EL 7 t;
              EL 8 t; EL 9 t; EL 10 t; EL 11 t]
       (sha256_shaext_lane x y)`;;

(* The blocks the finish compresses: the message's n, the padded one, whose
   lanes from memory are block n's first words, and, when r is 4, one of
   zeros and the length. *)
let sha256_shaext_finish_blocks = new_definition
 `sha256_shaext_finish_blocks m n r x y l i =
    if i < n then m i
    else if i = n then sha256_shaext_padded r (m n) x y l
    else sha256_shaext_padded 0 (m n) (word 0) (word 0) l`;;

let SHA256_HASH_BLOCKS_PREFIX = prove
 (`!m m' h n. (!i. i < n ==> m' i = m i)
              ==> sha256_hash_blocks m' h n = sha256_hash_blocks m h n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sha256_hash_blocks; ADD1] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `n < n + 1`] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < n ==> i < n + 1`]);;

let SHA256_SHAEXT_FINISH_BLOCKS = prove
 (`!m n r x y l h.
     sha256_hash_blocks (sha256_shaext_finish_blocks m n r x y l) h
                        (if r = 4 then n + 2 else n + 1) =
     if r = 4
     then sha256_block (sha256_shaext_padded 0 (m n) (word 0) (word 0) l)
            (sha256_block (sha256_shaext_padded r (m n) x y l)
                          (sha256_hash_blocks m h n))
     else sha256_block (sha256_shaext_padded r (m n) x y l)
                       (sha256_hash_blocks m h n)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `sha256_hash_blocks (sha256_shaext_finish_blocks m n r x y l) h n =
    sha256_hash_blocks m h n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SHA256_HASH_BLOCKS_PREFIX THEN
    SIMP_TAC[sha256_shaext_finish_blocks];
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = (n + 1) + 1`; sha256_hash_blocks] THEN
  ASM_REWRITE_TAC[sha256_shaext_finish_blocks; LT_REFL;
                  ARITH_RULE `~(n + 1 < n) /\ ~(n + 1 = n)`]);;

(* ------------------------------------------------------------------------- *)
(* The padded block, from 0x39 through the rounds.                           *)
(* ------------------------------------------------------------------------- *)

(* The memory M holds from data's block n the first w words of m n, each
   big-endian. *)
let sha256_shaext_tail_in = new_definition
 `sha256_shaext_tail_in (data:int64) n w (m:num->int32 list) (M:int64->byte) <=>
    !j. j < w
        ==> read (bytes32 (word_add data (word (64 * n + 4 * j)))) M =
            word_bytereverse (EL j (m n))`;;

let SHA256_MIN_CONV tm =
  match tm with
    Comb(Comb(Const("MIN",_),a),b) when is_numeral a && is_numeral b ->
      (REWR_CONV MIN THENC NUM_REDUCE_CONV) tm
  | _ -> failwith "SHA256_MIN_CONV";;

(* The padded block's first w words at s0, as its loads read them, from
   sha256_shaext_tail_in data n w m mem0. *)
let SHA256_FINISH_SHAEXT_TAIL_TAC w =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `sha256_shaext_tail_in data n w m mem0`) (concl th) then
      let th' = REWRITE_RULE[sha256_shaext_tail_in] th in
      MAP_EVERY (fun j -> MP_TAC(SPEC (mk_small_numeral j) th')) (0--(w-1))
    else failwith "SHA256_FINISH_SHAEXT_TAIL_TAC") THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY (SHA256_SHAEXT_LANE_TAC `n:num`) (0--(w / 4 - 1));;

(* With r lanes, steps to the rounds at 0x6a, and runs them. *)
let SHA256_FINISH_SHAEXT_PAD_TAC r nsteps =
  let pad = vsubst [mk_small_numeral r, `r:num`]
     `sha256_shaext_padded r ((m:num->int32 list) n) x y l` in
  SHA256_FINISH_SHAEXT_TAIL_TAC (4 * min r 3) THEN
  SHA256_SHAEXT_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (1--nsteps) THEN
  SHA256_SHAEXT_K_LOADED_TAC ("s" ^ string_of_int nsteps) THEN
  MP_TAC(SPECL [`pc + 0x6a`; `k:num`; pad; `h:int32 list`]
               SHA256_SHAEXT_ROUNDS_CORRECT) THEN
  X86_BIGSTEP_TAC SHA256_FINISH_SHAEXT_EXEC ("s" ^ string_of_int (nsteps + 1)) THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP SHA256_FINISH_SHAEXT_ROUNDS_LOADED);
      REWRITE_TAC[READ_XMM_YMM] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[sha256_shaext_padded; sha256_shaext_lane; APPEND; ARITH_EQ] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN
      REWRITE_TAC[SHA256_BYTEREVERSE_BYTEREVERSE] THEN
      REPEAT CONJ_TAC THEN REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* With r = 4, the block is r = 3's: its length takes the next. *)
let SHA256_FINISH_SHAEXT_PAD = prove
 (`!pc data n k r l x y m h.
     r <= 4
     ==> ensures x86
      (\s. bytes_loaded s (word pc) sha256_finish_shaext_mc /\
           read RIP s = word (pc + 0x39) /\
           read RDX s = word_add data (word (64 * n)) /\
           read RCX s = word k /\
           read R8 s = l /\ read R9 s = word r /\ read R10 s = x /\ read R11 s = y /\
           read XMM4 s = word 16018520953223639909183530438118932995 /\
           read XMM11 s = sha256_abef h /\ read XMM10 s = sha256_cdgh h /\
           sha256_shaext_blocks_in k data n m (read memory s) /\
           sha256_shaext_tail_in data n (4 * MIN r 3) m (read memory s))
      (\s. read RIP s = word (pc + 0x35d) /\
           read XMM11 s =
           sha256_abef (sha256_block (sha256_shaext_padded r (m n) x y l) h) /\
           read XMM10 s =
           sha256_cdgh (sha256_block (sha256_shaext_padded r (m n) x y l) h))
      (MAYCHANGE [RIP; R11] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                  ZMM15] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `data:int64`; `n:num`; `k:num`; `r:num`; `l:int64`; `x:int64`;
    `y:int64`; `m:num->int32 list`; `h:int32 list`] THEN
  REWRITE_TAC[SOME_FLAGS; fst SHA256_FINISH_SHAEXT_EXEC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SHA256_MIN_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
  SHA256_SHAEXT_YMM_INIT_TAC THEN SHA256_SHAEXT_MEM0_TAC THENL
   [SHA256_FINISH_SHAEXT_PAD_TAC 0 10;
    SHA256_FINISH_SHAEXT_PAD_TAC 1 12;
    SHA256_FINISH_SHAEXT_PAD_TAC 2 13;
    SHA256_FINISH_SHAEXT_PAD_TAC 3 12;
    SHA256_FINISH_SHAEXT_PAD_TAC 4 12]);;

(* ------------------------------------------------------------------------- *)
(* The digest, from 0x3f8 to the end.                                        *)
(* ------------------------------------------------------------------------- *)

let SHA256_FINISH_SHAEXT_UNLOAD = prove
 (`!pc h.
     ensures x86
      (\s. bytes_loaded s (word pc) sha256_finish_shaext_mc /\
           read RIP s = word (pc + 0x3f8) /\
           read XMM4 s = word 16018520953223639909183530438118932995 /\
           read XMM11 s = sha256_abef h /\ read XMM10 s = sha256_cdgh h)
      (\s. read RIP s = word (pc + 0x41e) /\
           read XMM2 s = sha256_quad (word_bytereverse (EL 0 h)) (word_bytereverse (EL 1 h))
                                     (word_bytereverse (EL 2 h)) (word_bytereverse (EL 3 h)) /\
           read XMM1 s = sha256_quad (word_bytereverse (EL 4 h)) (word_bytereverse (EL 5 h))
                                     (word_bytereverse (EL 6 h)) (word_bytereverse (EL 7 h)))
      (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`pc:num`; `h:int32 list`] THEN
  REWRITE_TAC[fst SHA256_FINISH_SHAEXT_EXEC; sha256_abef; sha256_cdgh] THEN
  SHA256_SHAEXT_YMM_INIT_TAC THEN
  SHA256_SHAEXT_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_XMM_YMM] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The padded blocks and the digest, from 0x2f once rax has counted down.    *)
(* ------------------------------------------------------------------------- *)

let SHA256_FINISH_SHAEXT_PAD_BIGSTEP_TAC r x y h sname =
  let rtm = mk_small_numeral r in
  let th = MP (SPECL [`pc:num`; `data:int64`; `n:num`; `k:num`; rtm; `l:int64`; x; y;
                      `m:num->int32 list`; h] SHA256_FINISH_SHAEXT_PAD)
              (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<=):num->num->bool` rtm `4`))) in
  MP_TAC(REWRITE_RULE[SOME_FLAGS]
    (CONV_RULE(ONCE_DEPTH_CONV SHA256_MIN_CONV THENC
               ONCE_DEPTH_CONV NUM_MULT_CONV) th)) THEN
  X86_BIGSTEP_TAC SHA256_FINISH_SHAEXT_EXEC sname THEN
  TRY(ASM_REWRITE_TAC[] THEN REWRITE_TAC[sha256_shaext_tail_in; LT] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV));;

let SHA256_FINISH_SHAEXT_UNLOAD_BIGSTEP_TAC h sname =
  MP_TAC(SPECL [`pc:num`; h] SHA256_FINISH_SHAEXT_UNLOAD) THEN
  X86_BIGSTEP_TAC SHA256_FINISH_SHAEXT_EXEC sname THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV));;

let sha256_finish_shaext_block r x y h =
  vsubst [mk_small_numeral r, `r:num`; x, `x:int64`; y, `y:int64`; h, `h:int32 list`]
    `sha256_block (sha256_shaext_padded r ((m:num->int32 list) n) x y l) h`;;

(* rax's borrow takes the padded block, and test and jns fall through after
   it; with r = 4, r9, r10, and r11 are cleared for the length's block. *)
let SHA256_FINISH_SHAEXT_TAIL_CASE_TAC r =
  if r < 4 then
    X86_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (1--2) THEN
    SHA256_FINISH_SHAEXT_PAD_BIGSTEP_TAC r `x:int64` `y:int64` `h:int32 list` "s3" THEN
    X86_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (4--7) THEN
    SHA256_FINISH_SHAEXT_UNLOAD_BIGSTEP_TAC
      (sha256_finish_shaext_block r `x:int64` `y:int64` `h:int32 list`) "s8" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]
  else
    let h1 = sha256_finish_shaext_block 4 `x:int64` `y:int64` `h:int32 list` in
    X86_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (1--2) THEN
    SHA256_FINISH_SHAEXT_PAD_BIGSTEP_TAC 4 `x:int64` `y:int64` `h:int32 list` "s3" THEN
    X86_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (4--11) THEN
    SHA256_FINISH_SHAEXT_PAD_BIGSTEP_TAC 0 `word 0:int64` `word 0:int64` h1 "s12" THEN
    X86_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (13--16) THEN
    SHA256_FINISH_SHAEXT_UNLOAD_BIGSTEP_TAC
      (sha256_finish_shaext_block 0 `word 0:int64` `word 0:int64` h1) "s17" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let SHA256_FINISH_SHAEXT_TAIL = prove
 (`!pc data n k r l x y m h.
     r <= 4
     ==> ensures x86
      (\s. bytes_loaded s (word pc) sha256_finish_shaext_mc /\
           read RIP s = word (pc + 0x2f) /\
           read RAX s = word 0 /\
           read RDX s = word_add data (word (64 * n)) /\
           read RCX s = word k /\
           read R8 s = l /\ read R9 s = word r /\ read R10 s = x /\ read R11 s = y /\
           read XMM4 s = word 16018520953223639909183530438118932995 /\
           read XMM11 s = sha256_abef h /\ read XMM10 s = sha256_cdgh h /\
           sha256_shaext_blocks_in k data n m (read memory s) /\
           sha256_shaext_tail_in data n (4 * MIN r 3) m (read memory s))
      (\s. read RIP s = word (pc + 0x41e) /\
           let h' = if r = 4
                    then sha256_block (sha256_shaext_padded 0 (m n) (word 0) (word 0) l)
                           (sha256_block (sha256_shaext_padded r (m n) x y l) h)
                    else sha256_block (sha256_shaext_padded r (m n) x y l) h in
           read XMM2 s = sha256_quad (word_bytereverse (EL 0 h')) (word_bytereverse (EL 1 h'))
                                     (word_bytereverse (EL 2 h')) (word_bytereverse (EL 3 h')) /\
           read XMM1 s = sha256_quad (word_bytereverse (EL 4 h')) (word_bytereverse (EL 5 h'))
                                     (word_bytereverse (EL 6 h')) (word_bytereverse (EL 7 h')))
      (MAYCHANGE [RIP; RAX; R9; R10; R11] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                  ZMM15] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `data:int64`; `n:num`; `k:num`; `r:num`; `l:int64`; `x:int64`;
    `y:int64`; `m:num->int32 list`; `h:int32 list`] THEN
  REWRITE_TAC[SOME_FLAGS; fst SHA256_FINISH_SHAEXT_EXEC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SHA256_MIN_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[ARITH_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
  ENSURES_INIT_TAC "s0" THEN SHA256_SHAEXT_MEM0_TAC THENL
   (map SHA256_FINISH_SHAEXT_TAIL_CASE_TAC (0--4)));;

(* ------------------------------------------------------------------------- *)
(* The block.                                                                *)
(* ------------------------------------------------------------------------- *)

(* The count's borrow and sign, before each block and after. *)
let SHA256_FINISH_SHAEXT_COUNT = prove
 (`!n i. n < 2 EXP 63 /\ i < n
         ==> word_sub (word (n - i)) (word 1):int64 = word (n - (i + 1)) /\
             (val (word (n - i):int64) < 1 <=> F) /\
             (ival (word (n - (i + 1)):int64) < &0 <=> F)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `n - i = (n - (i + 1)) + 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[WORD_SUB_ADD]];
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_RULE
     `n < 2 EXP 63 ==> n - i < 2 EXP 64`] THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM MSB_IVAL; MSB_VAL; DIMINDEX_64] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_RULE
     `n < 2 EXP 63 ==> n - (i + 1) < 2 EXP 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

(* The state's loads and the mask's, from the start to 0x2f with the blocks
   still to run numbered from ntm. *)
let SHA256_FINISH_SHAEXT_PROLOGUE_TAC ntm =
  GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
  SHA256_SHAEXT_YMM_INIT_TAC THEN SHA256_SHAEXT_MEM0_TAC THEN
  SHA256_SHAEXT_INPUTS_TAC [sha256_shaext_blocks_in; sha256_shaext_tail_in]
   (vsubst [ntm, `n:num`]
     `sha256_shaext_blocks_in k data n m mem0 /\
      sha256_shaext_tail_in data n (4 * MIN r 3) m mem0`) THEN
  SHA256_SHAEXT_K_TAC THEN SHA256_SHAEXT_STATE_TAC THEN
  SHA256_SHAEXT_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHA256_SHAEXT_LOADED_STATE_TAC;;

(* The loop runs at 0x2f for each of the message's blocks: the count's
   decrement, four loads, the rounds, and the count's test. Its exit is the
   padded blocks', SHA256_FINISH_SHAEXT_TAIL. *)
let SHA256_FINISH_SHAEXT_CORRECT = prove
 (`!pc state data n k r l x y h0 h1 h2 h3 h4 h5 h6 h7 m.
     n < 2 EXP 63 /\ r <= 4 /\ aligned 16 (word k:int64)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) sha256_finish_shaext_mc /\
               read RIP s = word pc /\
               read RSI s = state /\ read RDX s = data /\ read RAX s = word n /\
               read RCX s = word k /\ bytes_loaded s (word k) sha256_shaext_k /\
               read R8 s = l /\ read R9 s = word r /\ read R10 s = x /\ read R11 s = y /\
               read (memory :> bytes32 state) s = h0 /\
               read (memory :> bytes32 (word_add state (word 4))) s = h1 /\
               read (memory :> bytes32 (word_add state (word 8))) s = h2 /\
               read (memory :> bytes32 (word_add state (word 12))) s = h3 /\
               read (memory :> bytes32 (word_add state (word 16))) s = h4 /\
               read (memory :> bytes32 (word_add state (word 20))) s = h5 /\
               read (memory :> bytes32 (word_add state (word 24))) s = h6 /\
               read (memory :> bytes32 (word_add state (word 28))) s = h7 /\
               (!i j. i < n /\ j < 16 \/ i = n /\ j < 4 * MIN r 3
                      ==> read (memory :> bytes32 (word_add data (word (64 * i + 4 * j)))) s =
                          word_bytereverse (EL j (m i))))
          (\s. read RIP s = word (pc + 1054) /\
               let h' = sha256_hash_blocks (sha256_shaext_finish_blocks m n r x y l)
                          [h0;h1;h2;h3;h4;h5;h6;h7] (if r = 4 then n + 2 else n + 1) in
               read XMM2 s = sha256_quad (word_bytereverse (EL 0 h')) (word_bytereverse (EL 1 h'))
                                         (word_bytereverse (EL 2 h')) (word_bytereverse (EL 3 h')) /\
               read XMM1 s = sha256_quad (word_bytereverse (EL 4 h')) (word_bytereverse (EL 5 h'))
                                         (word_bytereverse (EL 6 h')) (word_bytereverse (EL 7 h')))
          (MAYCHANGE [RIP; RAX; RDX; R9; R10; R11] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM10; ZMM11; ZMM12; ZMM13;
                      ZMM14; ZMM15] ,,
           MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `state:int64`; `data:int64`; `n:num`; `k:num`; `r:num`; `l:int64`;
    `x:int64`; `y:int64`; `h0:int32`; `h1:int32`; `h2:int32`; `h3:int32`;
    `h4:int32`; `h5:int32`; `h6:int32`; `h7:int32`; `m:num->int32 list`] THEN
  REWRITE_TAC[SOME_FLAGS; fst SHA256_FINISH_SHAEXT_EXEC; SHA256_SHAEXT_FINISH_BLOCKS] THEN
  STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2f`
   `\s. read RAX s = word 0 /\
        read RDX s = word_add data (word (64 * n)) /\
        read RCX s = word k /\
        read R8 s = l /\ read R9 s = word r /\ read R10 s = x /\ read R11 s = y /\
        read XMM4 s = word 16018520953223639909183530438118932995 /\
        read XMM11 s = sha256_abef (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n) /\
        read XMM10 s = sha256_cdgh (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n) /\
        sha256_shaext_blocks_in k data n m (read memory s) /\
        sha256_shaext_tail_in data n (4 * MIN r 3) m (read memory s)` THEN
  CONJ_TAC THENL
   [(* The message's blocks. *)
    ASM_CASES_TAC `n = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN SHA256_FINISH_SHAEXT_PROLOGUE_TAC `0`;
      ALL_TAC] THEN
    ENSURES_WHILE_UP_TAC `n:num` `pc + 0x2f` `pc + 0x2f`
     `\i s. read RAX s = word (n - i) /\
            read RDX s = word_add data (word (64 * i)) /\
            read RCX s = word k /\
            read R8 s = l /\ read R9 s = word r /\ read R10 s = x /\ read R11 s = y /\
            read XMM4 s = word 16018520953223639909183530438118932995 /\
            read XMM11 s = sha256_abef (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i) /\
            read XMM10 s = sha256_cdgh (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i) /\
            sha256_shaext_blocks_in k data n m (read memory s) /\
            sha256_shaext_tail_in data n (4 * MIN r 3) m (read memory s)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SHA256_FINISH_SHAEXT_PROLOGUE_TAC `n:num`;

      (* A block. *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
      SHA256_SHAEXT_YMM_INIT_TAC THEN SHA256_SHAEXT_MEM0_TAC THEN
      SHA256_SHAEXT_BLOCK_TAC `i:num` THEN
      MP_TAC(SPECL [`n:num`; `i:num`] SHA256_FINISH_SHAEXT_COUNT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun cth ->
        X86_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC [1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[cth]) THEN
        SHA256_SHAEXT_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC (2--8) THEN
        SHA256_SHAEXT_K_LOADED_TAC "s8" THEN
        MP_TAC(SPECL [`pc + 0x6a`; `k:num`; `(m:num->int32 list) i`;
                      `sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i`]
                     SHA256_SHAEXT_ROUNDS_CORRECT) THEN
        X86_BIGSTEP_TAC SHA256_FINISH_SHAEXT_EXEC "s9" THENL
         [CONJ_TAC THENL
           [FIRST_ASSUM(MATCH_ACCEPT_TAC o
                        MATCH_MP SHA256_FINISH_SHAEXT_ROUNDS_LOADED);
            REWRITE_TAC[READ_XMM_YMM] THEN ASM_REWRITE_TAC[] THEN
            CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV)) THEN
        X86_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC [10] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[cth]) THEN
        X86_STEPS_TAC SHA256_FINISH_SHAEXT_EXEC [11]) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[READ_XMM_YMM; sha256_hash_blocks] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; LEFT_ADD_DISTRIB; MULT_CLAUSES];

      (* The back edge, which is no step. *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

      (* The exit, with the count at zero. *)
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (* The padded blocks and the digest. *)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP
     (SPECL [`pc:num`; `data:int64`; `n:num`; `k:num`; `r:num`; `l:int64`; `x:int64`;
             `y:int64`; `m:num->int32 list`;
             `sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n`]
      SHA256_FINISH_SHAEXT_TAIL)) THEN
    CONV_TAC(LAND_CONV(REWRITE_CONV[SOME_FLAGS] THENC TOP_DEPTH_CONV let_CONV)) THEN
    X86_BIGSTEP_TAC SHA256_FINISH_SHAEXT_EXEC "s1" THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[]]);;
