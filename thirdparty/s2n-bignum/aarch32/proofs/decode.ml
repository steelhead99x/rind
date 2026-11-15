(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Partial A32 instruction decoding.                                         *)
(* ========================================================================= *)

(* Encodings follow the ARMv7-A manual (DDI 0406), A5.1 "ARM instruction set
   encoding" and its subsections, as DDI 0487's F4 restates them for AArch32.

   Every encoding the model does not cover, or the manual calls
   UNPREDICTABLE, decodes to NONE, so no theorem holds of code containing it:
   R15 as an operand or destination, the unconditional space (cond = 1111),
   non-zero should-be-zero fields, LDRT and STRT, and writeback to the
   transfer register. *)

(* An instruction under `cond`: plain for AL, guarded otherwise. *)

let aarch32_conditional = new_definition
 `aarch32_conditional (cond:4 word) (i:aarch32state->aarch32state->bool) =
    if cond = word 15 then NONE
    else if cond = word 14 then SOME i
    else SOME (aarch32_cond cond i)`;;

(* DecodeImmShift and Shift_C for an immediate shift of Rm: its value, and
   which bit of Rm is the carry out. LSL #0 leaves Rm and C as they are. *)

let aarch32_shifted = new_definition
 `aarch32_shifted (ty:2 word) (imm5:5 word) Rm =
    if ty = word 0 then
      if imm5 = word 0 then Rm else aarch32_LSL Rm (val imm5)
    else if ty = word 1 then
      aarch32_LSR Rm (if imm5 = word 0 then 32 else val imm5)
    else if ty = word 2 then
      aarch32_ASR Rm (if imm5 = word 0 then 32 else val imm5)
    else if imm5 = word 0 then aarch32_RRX Rm
    else aarch32_ROR Rm (val imm5)`;;

let aarch32_shifted_carry = new_definition
 `aarch32_shifted_carry (ty:2 word) (imm5:5 word) Rm =
    if ty = word 0 then
      if imm5 = word 0 then CF else aarch32_BIT Rm (32 - val imm5)
    else if ty = word 1 \/ ty = word 2 then
      aarch32_BIT Rm (if imm5 = word 0 then 31 else val imm5 - 1)
    else if imm5 = word 0 then aarch32_BIT Rm 0
    else aarch32_BIT Rm (val imm5 - 1)`;;

(* A32ExpandImm_C: an 8-bit value rotated right by twice the rotation. The
   carry out is C when the rotation is zero, else the result's top bit. *)

let aarch32_expand_imm = new_definition
 `aarch32_expand_imm (rot:4 word) (imm8:byte) : int32 =
    word_ror (word_zx imm8) (2 * val rot)`;;

let aarch32_expand_imm_carry = new_definition
 `aarch32_expand_imm_carry (rot:4 word) (imm8:byte) =
    if rot = word 0 then CF
    else rvalue (bit 31 (aarch32_expand_imm rot imm8))`;;

(* "Data-processing and miscellaneous instructions": the sixteen opcodes,
   each given its second operand and that operand's carry out. The compare
   and test opcodes without S are other instructions, which decode to NONE,
   as do non-zero should-be-zero register fields. *)

let aarch32_dp = new_definition
 `aarch32_dp (cond:4 word) (opc:4 word) S (d:4 word) (n:4 word) Rm Rc =
    if d = word 15 \/ n = word 15 then NONE else
    if opc = word 0 then
      aarch32_conditional cond
       (if S then aarch32_ANDS (aarch32_reg d) (aarch32_reg n) Rm Rc
        else aarch32_AND (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 1 then
      aarch32_conditional cond
       (if S then aarch32_EORS (aarch32_reg d) (aarch32_reg n) Rm Rc
        else aarch32_EOR (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 2 then
      aarch32_conditional cond
       ((if S then aarch32_SUBS else aarch32_SUB)
        (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 3 then
      aarch32_conditional cond
       ((if S then aarch32_RSBS else aarch32_RSB)
        (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 4 then
      aarch32_conditional cond
       ((if S then aarch32_ADDS else aarch32_ADD)
        (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 5 then
      aarch32_conditional cond
       ((if S then aarch32_ADCS else aarch32_ADC)
        (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 6 then
      aarch32_conditional cond
       ((if S then aarch32_SBCS else aarch32_SBC)
        (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 7 then
      aarch32_conditional cond
       ((if S then aarch32_RSCS else aarch32_RSC)
        (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 8 then
      (if S /\ d = word 0
       then aarch32_conditional cond (aarch32_TST (aarch32_reg n) Rm Rc)
       else NONE) else
    if opc = word 9 then
      (if S /\ d = word 0
       then aarch32_conditional cond (aarch32_TEQ (aarch32_reg n) Rm Rc)
       else NONE) else
    if opc = word 10 then
      (if S /\ d = word 0
       then aarch32_conditional cond (aarch32_CMP (aarch32_reg n) Rm)
       else NONE) else
    if opc = word 11 then
      (if S /\ d = word 0
       then aarch32_conditional cond (aarch32_CMN (aarch32_reg n) Rm)
       else NONE) else
    if opc = word 12 then
      aarch32_conditional cond
       (if S then aarch32_ORRS (aarch32_reg d) (aarch32_reg n) Rm Rc
        else aarch32_ORR (aarch32_reg d) (aarch32_reg n) Rm) else
    if opc = word 13 then
      (if n = word 0
       then aarch32_conditional cond
             (if S then aarch32_MOVS (aarch32_reg d) Rm Rc
              else aarch32_MOV (aarch32_reg d) Rm)
       else NONE) else
    if opc = word 14 then
      aarch32_conditional cond
       (if S then aarch32_BICS (aarch32_reg d) (aarch32_reg n) Rm Rc
        else aarch32_BIC (aarch32_reg d) (aarch32_reg n) Rm)
    else
      (if n = word 0
       then aarch32_conditional cond
             (if S then aarch32_MVNS (aarch32_reg d) Rm Rc
              else aarch32_MVN (aarch32_reg d) Rm)
       else NONE)`;;

(* "Load/store word and unsigned byte", immediate offset: offset (P = 1,
   W = 0), pre-indexed (P = 1, W = 1), and post-indexed (P = 0, W = 0).
   P = 0 with W = 1 is LDRT or STRT, which decodes to NONE. *)

let aarch32_ldst = new_definition
 `aarch32_ldst (cond:4 word) P U B W L (n:4 word) (t:4 word) (imm:int32) =
    if n = word 15 \/ t = word 15 \/ (~P /\ W) \/ ((~P \/ W) /\ n = t)
    then NONE else
    aarch32_conditional cond
     ((if L then if B then aarch32_LDRB else aarch32_LDR
       else if B then aarch32_STRB else aarch32_STR)
      (aarch32_reg t) (aarch32_reg n)
      (if U then imm else word_neg imm) P (~P \/ W))`;;

(* B's offset from its own address: the sign-extended imm24:00 plus A32's
   PC bias of 8. *)

let aarch32_branch_offset = new_definition
 `aarch32_branch_offset (imm24:24 word) : int32 =
    word_add (word_sx (word_join imm24 (word 0:2 word):26 word)) (word 8)`;;

(* The immediate data-processing space, where the compare and test opcodes
   without S hold MOVW (opc = 8) and MOVT (opc = 10), whose 16-bit
   immediate is the Rn field above rot:imm8. *)

let aarch32_dp_imm = new_definition
 `aarch32_dp_imm (cond:4 word) (opc:4 word) S (d:4 word) (n:4 word)
                 (rot:4 word) (imm8:byte) =
    if ~S /\ (opc = word 8 \/ opc = word 10) then
      if d = word 15 then NONE
      else aarch32_conditional cond
            ((if opc = word 8 then aarch32_MOVW else aarch32_MOVT)
             (aarch32_reg d)
             (word_join n (word_join rot imm8:12 word)))
    else
      aarch32_dp cond opc S d n
       (rvalue (aarch32_expand_imm rot imm8))
       (aarch32_expand_imm_carry rot imm8)`;;

(* Instruction words are decoded with `bitmatch`, most-significant field
   first. The clauses do not overlap:

     DP register   [cond:4; 000; opc:4; S; Rn:4; Rd:4; imm5:5; type:2; 0; Rm:4]
     DP immediate  [cond:4; 001; opc:4; S; Rn:4; Rd:4; rot:4; imm8:8]
     B             [cond:4; 1010; imm24:24]
     LDR(B), STR(B) immediate
                   [cond:4; 010; P; U; B; W; L; Rn:4; Rt:4; imm12:12] *)

let decode = new_definition
 `decode (w:int32) =
    bitmatch w with
    | [cond:4; 0b000:3; opc:4; S; Rn:4; Rd:4; imm5:5; ty:2; 0b0:1; Rm:4] ->
        if Rm = word 15 then NONE
        else aarch32_dp cond opc S Rd Rn
              (aarch32_shifted ty imm5 (aarch32_reg Rm))
              (aarch32_shifted_carry ty imm5 (aarch32_reg Rm))
    | [cond:4; 0b001:3; opc:4; S; Rn:4; Rd:4; rot:4; imm8:8] ->
        aarch32_dp_imm cond opc S Rd Rn rot imm8
    | [cond:4; 0b1010:4; imm24:24] ->
        if cond = word 15 then NONE
        else SOME (aarch32_B cond (aarch32_branch_offset imm24))
    | [cond:4; 0b010:3; P; U; B; W; L; Rn:4; Rt:4; imm12:12] ->
        aarch32_ldst cond P U B W L Rn Rt (word_zx imm12)
    | _ -> NONE`;;

open Compute;;

(* Prove the result of decoding one concrete 32-bit instruction word. The
   input must have the form `decode (word n)`, and the conversion fails when
   the encoding is unsupported. For example, applying `PURE_DECODE_CONV` to

     `decode (word 0xe0200002)`

   proves that 0xe0200002 decodes to `SOME (aarch32_EOR R0 R0 R2)`. *)

let PURE_DECODE_CONV =
  let decode_rw =
    let rw = bool_compset() in
    set_skip rw `COND:bool->A->A->A` (Some 1);
    set_skip rw `_MATCH:A->(A->B->bool)->B` (Some 1);
    set_skip rw `_BITMATCH:(N)word->(num->B->bool)->B` (Some 1);
    word_compute_add_convs rw;
    num_compute_add_convs rw;
    add_conv (`_MATCH:A->(A->B->bool)->B`, 2, MATCH_CONV) rw;
    add_thms [aarch32_reg; aarch32_conditional; aarch32_shifted;
              aarch32_shifted_carry; aarch32_expand_imm;
              aarch32_expand_imm_carry; aarch32_dp; aarch32_dp_imm; aarch32_ldst;
              aarch32_branch_offset] rw;
    (let Some (conceal_th, opaque_const, opaque_arity, _, opaque_conv) =
        conceal_bitmatch (concl decode) in
     add_thms [GEN_REWRITE_RULE I [conceal_th] decode] rw;
     add_conv (opaque_const, opaque_arity, opaque_conv) rw);
    rw in
  let base_conv = WEAK_CBV_CONV decode_rw in
  fun t ->
    try
      let th = base_conv t in
      let c = concl th in
      let r,_ = dest_comb (rhs c) in
      if is_const r && name_of r = "SOME" then th else failwith ""
    with Failure _ -> failwith ("PURE_DECODE_CONV: " ^ string_of_term t);;

let DECODE_CONV = PURE_DECODE_CONV;;

(* One encoding per instruction form, checked as this file loads, with
   operand shapes the manual's special cases distinguish: each shift type
   and the amounts that encode 32 and RRX, a rotated immediate, conditions,
   backward branches, and each indexing mode. *)

let AARCH32_DECODE_TESTS =
  let cases =
   [`decode (word 0xe0200002)`,                (* eor r0, r0, r2 *)
      `SOME (aarch32_EOR R0 R0 R2)`;
    `decode (word 0xe1800001)`,                (* orr r0, r0, r1 *)
      `SOME (aarch32_ORR R0 R0 R1)`;
    `decode (word 0xe2511001)`,                (* subs r1, r1, #1 *)
      `SOME (aarch32_SUBS R1 R1 (rvalue (word 1)))`;
    `decode (word 0xe0910182)`,                (* adds r0, r1, r2, lsl #3 *)
      `SOME (aarch32_ADDS R0 R1 (aarch32_LSL R2 3))`;
    `decode (word 0xe0310022)`,                (* eors r0, r1, r2, lsr #32 *)
      `SOME (aarch32_EORS R0 R1 (aarch32_LSR R2 32) (aarch32_BIT R2 31))`;
    `decode (word 0xe1b00062)`,                (* rrxs r0, r2 *)
      `SOME (aarch32_MOVS R0 (aarch32_RRX R2) (aarch32_BIT R2 0))`;
    `decode (word 0xe1a00ee2)`,                (* ror r0, r2, #29 *)
      `SOME (aarch32_MOV R0 (aarch32_ROR R2 29))`;
    `decode (word 0xe3c004ff)`,                (* bic r0, r0, #0xff000000 *)
      `SOME (aarch32_BIC R0 R0 (rvalue (word 0xff000000)))`;
    `decode (word 0xe3500000)`,                (* cmp r0, #0 *)
      `SOME (aarch32_CMP R0 (rvalue (word 0)))`;
    `decode (word 0x31a01003)`,                (* movlo r1, r3 *)
      `SOME (aarch32_cond (word 3) (aarch32_MOV R1 R3))`;
    `decode (word 0x3afffffe)`,                (* blo . *)
      `SOME (aarch32_B (word 3) (word 0))`;
    `decode (word 0xeafffff9)`,                (* b .-20 *)
      `SOME (aarch32_B (word 14) (word 0xffffffec))`;
    `decode (word 0xe4d0c001)`,                (* ldrb r12, [r0], #1 *)
      `SOME (aarch32_LDRB R12 R0 (word 1) F T)`;
    `decode (word 0xe5b2e004)`,                (* ldr lr, [r2, #4]! *)
      `SOME (aarch32_LDR LR R2 (word 4) T T)`;
    `decode (word 0xe5013008)`,                (* str r3, [r1, #-8] *)
      `SOME (aarch32_STR R3 R1 (word 0xfffffff8) T F)`;
    `decode (word 0xe30a1bcd)`,                (* movw r1, #0xabcd *)
      `SOME (aarch32_MOVW R1 (word 0xabcd))`;
    `decode (word 0xe3411234)`,                (* movt r1, #0x1234 *)
      `SOME (aarch32_MOVT R1 (word 0x1234))`] in
  end_itlist CONJ
   (map
     (fun tm,expected ->
        let th = DECODE_CONV tm in
        if rhs(concl th) = expected then th
        else
          failwith
           ("AARCH32_DECODE_TESTS: expected " ^
            string_of_term expected ^ " but got " ^
            string_of_term(rhs(concl th))))
     cases);;

(* Encodings that must decode to NONE: R15 as an operand, the unconditional
   space, LDRT, writeback to the transfer register, and a should-be-zero
   field that is not. *)

let AARCH32_DECODE_REFUSALS =
  let refuse tm =
    (try ignore (DECODE_CONV tm);
         failwith ("AARCH32_DECODE_REFUSALS: decoded " ^ string_of_term tm)
     with Failure s when String.length s >= 16 &&
                         String.sub s 0 16 = "PURE_DECODE_CONV" -> ()) in
  List.iter refuse
   [`decode (word 0xe08ff000)`;                (* add pc, pc, r0 *)
    `decode (word 0xe08f0001)`;                (* add r0, pc, r1 *)
    `decode (word 0xf0200002)`;                (* cond = 1111 *)
    `decode (word 0xe4f0c001)`;                (* ldrbt r12, [r0], #1 *)
    `decode (word 0xe4d00001)`;                (* ldrb r0, [r0], #1 *)
    `decode (word 0xe1a10002)`];;              (* mov r0, r2, Rn = 1 *)

loadt "common/decode32.ml";;

(* `decode32` is the shared four-byte fetch relation; A32 instructions are
   little-endian words at four-byte-aligned addresses. *)

let aarch32_decode = new_definition
 `aarch32_decode s pc inst <=> decode32 decode s pc inst`;;

let AARCH32_DECODE_CONS = prove
 (`!s pc l i inst l'.
      aligned_bytes_loaded s (word pc) l ==>
      read_int32 l = SOME (i,l') ==>
      decode i = SOME inst ==>
      aarch32_decode s (word pc) inst /\
      aligned_bytes_loaded s (word (pc + 4)) l'`,
  REWRITE_TAC[aarch32_decode] THEN MATCH_ACCEPT_TAC DECODE32_CONS);;

let aarch32_decode_unique = prove
 (`!s pc x y. aarch32_decode s pc x ==> aarch32_decode s pc y ==> x = y`,
  REWRITE_TAC[aarch32_decode] THEN MESON_TAC[decode32_unique]);;

(* Turn a concrete byte-list definition into one decode theorem per
   instruction, at byte offsets 0, 4, 8, and so on:

     !s pc. aligned_bytes_loaded s (word pc) code
            ==> aarch32_decode s (word (pc + n)) instruction *)

let AARCH32_DECODES_THM =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + 4 = pc' ==>
     aligned_bytes_loaded s (word pc) l ==>
     read_int32 l = SOME (a,l') ==> decode a = SOME i ==>
     aarch32_decode s (word pc) i' /\
     aligned_bytes_loaded s (word pc') l'`,
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC AARCH32_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + 4 = p ==> (pc + n) + 4 = pc + p`
  and r32,dec,n4 = `read_int32`,`decode`,`4`
  and ei,ei' =
    `i:aarch32state->aarch32state->bool`,
    `i':aarch32state->aarch32state->bool`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and ea,en,ep,epc,epc' =
    `a:int32`,`n:num`,`p:num`,`pc:num`,`pc':num` in
  let rec go th: (thm*term) list =
    let pc,l = (rand o rand F_F I) (dest_comb (concl th)) in
    let th1 = READ_WORD_CONV (mk_comb (r32,l)) in
    let a,l' = dest_pair (rand (rhs (concl th1))) in
    let th2 = DECODE_CONV (mk_comb (dec,a)) in
    let i = rand (rhs (concl th2)) in
    let ith = REFL i in
    let th4,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl,a),n4)) in
      PROVE_HYP th (INST [pc,epc; a,en; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl,pc),n4)),`0` in
    let pc' = rhs (concl th4) in
    let th' = itlist PROVE_HYP [ith; th4; th; th1; th2]
      (INST [i,ei; i,ei'; pc,epc; pc',epc'; l,el; a,ea; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> [CONJUNCT1 th',pcofs]
    | _ ->
        let dth,bth = CONJ_PAIR th' in
        (dth,pcofs)::go bth in
  fun th ->
    let decodes:(thm*term) list =
      (go o
       (fun dth -> EQ_MP dth (ASSUME (lhs (concl dth)))) o
       AP_TERM `aligned_bytes_loaded s (word pc)`) th in
    map
      (fun th,pcofs ->
        ((GENL [`s:aarch32state`; `pc:num`] o DISCH_ALL) th,pcofs))
      decodes;;

(* The code-length theorem and the decode theorem for each instruction at
   its byte offset. *)

let AARCH32_MK_EXEC_RULE th0:thm * thm option array =
  GEN_MK_EXEC_RULE
    [LENGTH_BYTELIST_OF_NUM; LENGTH; LENGTH_APPEND]
    AARCH32_DECODES_THM th0;;

(* Define the checked byte list only after `assert_word_list` has confirmed
   that the supplied 32-bit words are exactly its little-endian contents. *)

let define_assert_word_list name tm ls =
  define_word_list name (assert_word_list tm ls);;
