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
   UNPREDICTABLE, decodes to NONE, so a proof cannot step at an offset
   holding it, though it may step through the code's other words:
   R15 as a destination other than a load's, or as an operand where the
   manual forbids it, the unconditional space (cond = 1111) but for DMB,
   non-zero should-be-zero fields, LDRT and STRT, and writeback to a
   transferred register. *)

(* An instruction under `cond`: plain for AL, guarded otherwise. *)

let aarch32_conditional = new_definition
 `aarch32_conditional (cond:4 word) (i:aarch32state->aarch32state->bool) =
    if cond = word 15 then NONE
    else if cond = word 14 then SOME i
    else SOME (aarch32_cond cond i)`;;

(* A branch under `cond`, which records its fall-through when not taken. A
   load or store, which records an access either way, takes `cond` itself,
   and the unconditional space, cond = 1111, holds none of them. *)

let aarch32_conditional_branch = new_definition
 `aarch32_conditional_branch (cond:4 word)
                             (i:aarch32state->aarch32state->bool) =
    if cond = word 15 then NONE
    else if cond = word 14 then SOME i
    else SOME (aarch32_cond_branch cond i)`;;

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

(* Shift_C for a register shifted by the low byte of the register Rs. *)

let aarch32_shifted_reg = new_definition
 `aarch32_shifted_reg (ty:2 word) Rm Rs =
    if ty = word 0 then aarch32_LSL_R Rm Rs
    else if ty = word 1 then aarch32_LSR_R Rm Rs
    else if ty = word 2 then aarch32_ASR_R Rm Rs
    else aarch32_ROR_R Rm Rs`;;

let aarch32_shifted_reg_carry = new_definition
 `aarch32_shifted_reg_carry (ty:2 word) Rm Rs =
    if ty = word 0 then aarch32_LSL_RC Rm Rs
    else if ty = word 1 then aarch32_LSR_RC Rm Rs
    else if ty = word 2 then aarch32_ASR_RC Rm Rs
    else aarch32_ROR_RC Rm Rs`;;

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
   each given its first operand `Rn`, its second operand, and that operand's
   carry out. The compare and test opcodes without S are other instructions,
   which decode to NONE, as do non-zero should-be-zero register fields. *)

let aarch32_dp = new_definition
 `aarch32_dp (cond:4 word) (opc:4 word) S (d:4 word) (n:4 word) Rn Rm Rc =
    if d = word 15 then NONE else
    if opc = word 0 then
      aarch32_conditional cond
       (if S then aarch32_ANDS (aarch32_reg d) Rn Rm Rc
        else aarch32_AND (aarch32_reg d) Rn Rm) else
    if opc = word 1 then
      aarch32_conditional cond
       (if S then aarch32_EORS (aarch32_reg d) Rn Rm Rc
        else aarch32_EOR (aarch32_reg d) Rn Rm) else
    if opc = word 2 then
      aarch32_conditional cond
       ((if S then aarch32_SUBS else aarch32_SUB)
        (aarch32_reg d) Rn Rm) else
    if opc = word 3 then
      aarch32_conditional cond
       ((if S then aarch32_RSBS else aarch32_RSB)
        (aarch32_reg d) Rn Rm) else
    if opc = word 4 then
      aarch32_conditional cond
       ((if S then aarch32_ADDS else aarch32_ADD)
        (aarch32_reg d) Rn Rm) else
    if opc = word 5 then
      aarch32_conditional cond
       ((if S then aarch32_ADCS else aarch32_ADC)
        (aarch32_reg d) Rn Rm) else
    if opc = word 6 then
      aarch32_conditional cond
       ((if S then aarch32_SBCS else aarch32_SBC)
        (aarch32_reg d) Rn Rm) else
    if opc = word 7 then
      aarch32_conditional cond
       ((if S then aarch32_RSCS else aarch32_RSC)
        (aarch32_reg d) Rn Rm) else
    if opc = word 8 then
      (if S /\ d = word 0
       then aarch32_conditional cond (aarch32_TST Rn Rm Rc)
       else NONE) else
    if opc = word 9 then
      (if S /\ d = word 0
       then aarch32_conditional cond (aarch32_TEQ Rn Rm Rc)
       else NONE) else
    if opc = word 10 then
      (if S /\ d = word 0
       then aarch32_conditional cond (aarch32_CMP Rn Rm)
       else NONE) else
    if opc = word 11 then
      (if S /\ d = word 0
       then aarch32_conditional cond (aarch32_CMN Rn Rm)
       else NONE) else
    if opc = word 12 then
      aarch32_conditional cond
       (if S then aarch32_ORRS (aarch32_reg d) Rn Rm Rc
        else aarch32_ORR (aarch32_reg d) Rn Rm) else
    if opc = word 13 then
      (if n = word 0
       then aarch32_conditional cond
             (if S then aarch32_MOVS (aarch32_reg d) Rm Rc
              else aarch32_MOV (aarch32_reg d) Rm)
       else NONE) else
    if opc = word 14 then
      aarch32_conditional cond
       (if S then aarch32_BICS (aarch32_reg d) Rn Rm Rc
        else aarch32_BIC (aarch32_reg d) Rn Rm)
    else
      (if n = word 0
       then aarch32_conditional cond
             (if S then aarch32_MVNS (aarch32_reg d) Rm Rc
              else aarch32_MVN (aarch32_reg d) Rm)
       else NONE)`;;

(* A register-shifted register operand, where the manual forbids R15 in
   every field. The compare opcode TEQ without S holds BX here: every
   register field but Rm ones, and no shift. *)

let aarch32_dp_rsr = new_definition
 `aarch32_dp_rsr (cond:4 word) (opc:4 word) S (d:4 word) (n:4 word)
                 (s:4 word) (ty:2 word) (m:4 word) =
    if m = word 15 then NONE else
    if ~S /\ opc = word 9 then
      if d = word 15 /\ n = word 15 /\ s = word 15 /\ ty = word 0
      then aarch32_conditional_branch cond (aarch32_BX (aarch32_reg m))
      else NONE
    else if n = word 15 \/ s = word 15 then NONE
    else aarch32_dp cond opc S d n (aarch32_reg n)
          (aarch32_shifted_reg ty (aarch32_reg m) (aarch32_reg s))
          (aarch32_shifted_reg_carry ty (aarch32_reg m) (aarch32_reg s))`;;

(* "Load/store word and unsigned byte", with the offset operand `Roff`:
   offset (P = 1, W = 0), pre-indexed (P = 1, W = 1), and post-indexed
   (P = 0, W = 0). P = 0 with W = 1 is LDRT or STRT, which decodes to NONE.
   Rn may be R15 for a word load without writeback, a literal load, and Rt
   for a word load from another base, a branch. *)

let aarch32_ldst = new_definition
 `aarch32_ldst (cond:4 word) P B W L (n:4 word) (t:4 word) Roff =
    if cond = word 15 \/ (~P /\ W) \/
       ((~P \/ W) /\ (n = t \/ n = word 15)) \/
       (n = word 15 /\ (~L \/ B \/ t = word 15))
    then NONE else
    if t = word 15 then
      if L /\ ~B
      then SOME (aarch32_LDR_PC cond (aarch32_reg n) Roff P (~P \/ W))
      else NONE
    else
    SOME ((if L then if B then aarch32_LDRB else aarch32_LDR
           else if B then aarch32_STRB else aarch32_STR)
          cond (aarch32_reg t) (aarch32_src n) Roff P (~P \/ W))`;;

(* The immediate-offset form, whose encodings with cond = 1111 hold DMB,
   under any option: the model's one unconditional instruction. *)

let aarch32_ldst_imm = new_definition
 `aarch32_ldst_imm (cond:4 word) P U B W L (n:4 word) (t:4 word)
                   (imm12:12 word) =
    if cond = word 15 then
      if P /\ ~U /\ B /\ W /\ L /\ n = word 15 /\ t = word 15 /\
         word_subword imm12 (4,8) = (word 5:byte)
      then SOME aarch32_DMB
      else NONE
    else
    aarch32_ldst cond P B W L n t
     (rvalue (if U then word_zx imm12 else word_neg (word_zx imm12)))`;;

(* The same with a register offset, shifted by an immediate and added or
   subtracted. R15 is not the offset nor, here, the base or the target. *)

let aarch32_ldst_reg = new_definition
 `aarch32_ldst_reg (cond:4 word) P U B W L (n:4 word) (t:4 word)
                   (imm5:5 word) (ty:2 word) (m:4 word) =
    if m = word 15 \/ n = word 15 \/ t = word 15 then NONE else
    aarch32_ldst cond P B W L n t
     (if U then aarch32_shifted ty imm5 (aarch32_reg m)
      else aarch32_NEG (aarch32_shifted ty imm5 (aarch32_reg m)))`;;

(* LDRD and STRD with an immediate offset: Rt even, Rt2 the register after
   it, neither R15, and a base that is not R15. *)

let aarch32_ldstd = new_definition
 `aarch32_ldstd (cond:4 word) P U W St (n:4 word) (t:4 word) (imm:int32) =
    if cond = word 15 \/ bit 0 t \/ t = word 14 \/ n = word 15 \/
       (~P /\ W) \/ ((~P \/ W) /\ (n = t \/ n = word_add t (word 1)))
    then NONE else
    SOME ((if St then aarch32_STRD else aarch32_LDRD)
          cond (aarch32_reg t) (aarch32_reg (word_add t (word 1)))
          (aarch32_reg n) (rvalue (if U then imm else word_neg imm))
          P (~P \/ W))`;;

(* MUL, and UMULL (A = 0) and UMLAL (A = 1), without S. *)

let aarch32_mul = new_definition
 `aarch32_mul (cond:4 word) S (d:4 word) (n:4 word) (m:4 word) =
    if S \/ d = word 15 \/ n = word 15 \/ m = word 15 then NONE else
    aarch32_conditional cond
     (aarch32_MUL (aarch32_reg d) (aarch32_reg n) (aarch32_reg m))`;;

let aarch32_mull = new_definition
 `aarch32_mull (cond:4 word) A S (hi:4 word) (lo:4 word) (n:4 word)
               (m:4 word) =
    if S \/ hi = word 15 \/ lo = word 15 \/ n = word 15 \/ m = word 15 \/
       hi = lo
    then NONE else
    aarch32_conditional cond
     ((if A then aarch32_UMLAL else aarch32_UMULL)
      (aarch32_reg lo) (aarch32_reg hi) (aarch32_reg n) (aarch32_reg m))`;;

(* The registers of an LDM or STM list, R0 to R12 and LR, in ascending
   order. *)

let aarch32_reglist = new_definition
 `aarch32_reglist (l:16 word) =
    APPEND (if bit 0 l then [R0] else [])
    (APPEND (if bit 1 l then [R1] else [])
    (APPEND (if bit 2 l then [R2] else [])
    (APPEND (if bit 3 l then [R3] else [])
    (APPEND (if bit 4 l then [R4] else [])
    (APPEND (if bit 5 l then [R5] else [])
    (APPEND (if bit 6 l then [R6] else [])
    (APPEND (if bit 7 l then [R7] else [])
    (APPEND (if bit 8 l then [R8] else [])
    (APPEND (if bit 9 l then [R9] else [])
    (APPEND (if bit 10 l then [R10] else [])
    (APPEND (if bit 11 l then [R11] else [])
    (APPEND (if bit 12 l then [R12] else [])
            (if bit 14 l then [LR] else [])))))))))))))`;;

(* LDM and STM in each addressing mode: increment or decrement (U), before
   or after (P). The lowest address is Rn, plus 4 before an increment, or
   less the length, plus 4 after a decrement. NONE for an empty list, R15 as
   the base, writeback to a base in the list, SP in the list, which the
   manual deprecates, the user-register forms (bit 22), and STM of R15. LDM
   of R15 is a branch. *)

let aarch32_ldstm_lowest = new_definition
 `aarch32_ldstm_lowest P U (l:16 word) : int32 =
    if U then if P then word 4 else word 0
    else word_sub (if P then word 0 else word 4) (word(4 * word_popcount l))`;;

let aarch32_ldstm_writeback = new_definition
 `aarch32_ldstm_writeback U (l:16 word) : int32 =
    if U then word(4 * word_popcount l)
    else word_neg(word(4 * word_popcount l))`;;

let aarch32_ldstm = new_definition
 `aarch32_ldstm (cond:4 word) P U W L (n:4 word) (l:16 word) =
    if cond = word 15 \/ l = word 0 \/ n = word 15 \/ (W /\ bit (val n) l) \/
       bit 13 l \/ (~L /\ bit 15 l)
    then NONE else
    SOME
     (if L then
        if bit 15 l then
          aarch32_LDM_PC cond (aarch32_reglist l) (aarch32_reg n)
           (aarch32_ldstm_lowest P U l)
           (if U then word(4 * word_popcount l - (if P then 0 else 4))
            else if P then word_neg(word 4) else word 0)
           (4 * word_popcount l) (aarch32_ldstm_writeback U l) W
        else
          aarch32_LDM cond (aarch32_reglist l) (aarch32_reg n)
           (aarch32_ldstm_lowest P U l)
           (4 * word_popcount l) (aarch32_ldstm_writeback U l) W
      else
        aarch32_STM cond (aarch32_reglist l) (aarch32_reg n)
         (aarch32_ldstm_lowest P U l)
         (4 * word_popcount l) (aarch32_ldstm_writeback U l) W)`;;

(* B's and BL's offset from its own address: the sign-extended imm24:00 plus
   A32's PC bias of 8. *)

let aarch32_branch_offset = new_definition
 `aarch32_branch_offset (imm24:24 word) : int32 =
    word_add (word_sx (word_join imm24 (word 0:2 word):26 word)) (word 8)`;;

(* The immediate data-processing space, where the compare and test opcodes
   without S hold MOVW (opc = 8) and MOVT (opc = 10), whose 16-bit
   immediate is the Rn field above rot:imm8, and the hints (opc = 9), of
   which only NOP decodes. Rn may be R15, as ADR's is. *)

let aarch32_dp_imm = new_definition
 `aarch32_dp_imm (cond:4 word) (opc:4 word) S (d:4 word) (n:4 word)
                 (rot:4 word) (imm8:byte) =
    if ~S /\ (opc = word 8 \/ opc = word 10) then
      if d = word 15 then NONE
      else aarch32_conditional cond
            ((if opc = word 8 then aarch32_MOVW else aarch32_MOVT)
             (aarch32_reg d)
             (word_join n (word_join rot imm8:12 word)))
    else if ~S /\ opc = word 9 then
      if n = word 0 /\ d = word 15 /\ rot = word 0 /\ imm8 = word 0
      then aarch32_conditional cond aarch32_NOP
      else NONE
    else
      aarch32_dp cond opc S d n (aarch32_src n)
       (rvalue (aarch32_expand_imm rot imm8))
       (aarch32_expand_imm_carry rot imm8)`;;

(* Instruction words are decoded with `bitmatch`, most-significant field
   first. The clauses do not overlap, which the conversion below needs:

     MUL           [cond:4; 0000000; S; Rd:4; 0000; Rm:4; 1001; Rn:4]
     UMULL, UMLAL  [cond:4; 000010; A; S; RdHi:4; RdLo:4; Rm:4; 1001; Rn:4]
     LDRD, STRD immediate
                   [cond:4; 000; P; U; 1; W; 0; Rn:4; Rt:4; imm4H:4; 11; St; 1;
                    imm4L:4]
     DP register   [cond:4; 000; opc:4; S; Rn:4; Rd:4; imm5:5; type:2; 0; Rm:4]
     DP register-shifted register, BX
                   [cond:4; 000; opc:4; S; Rn:4; Rd:4; Rs:4; 0; type:2; 1; Rm:4]
     DP immediate, NOP
                   [cond:4; 001; opc:4; S; Rn:4; Rd:4; rot:4; imm8:8]
     LDR(B), STR(B) immediate, DMB
                   [cond:4; 010; P; U; B; W; L; Rn:4; Rt:4; imm12:12]
     LDR(B), STR(B) register
                   [cond:4; 011; P; U; B; W; L; Rn:4; Rt:4; imm5:5; type:2; 0;
                    Rm:4]
     REV           [cond:4; 0110 1011 1111; Rd:4; 1111 0011; Rm:4]
     LDM, STM      [cond:4; 100; P; U; 0; W; L; Rn:4; register_list:16]
     B, BL         [cond:4; 101; L; imm24:24] *)

let decode = new_definition
 `decode (w:int32) =
    bitmatch w with
    | [cond:4; 0b0000000:7; S; Rd:4; 0b0000:4; Rm:4; 0b1001:4; Rn:4] ->
        aarch32_mul cond S Rd Rn Rm
    | [cond:4; 0b000010:6; A; S; RdHi:4; RdLo:4; Rm:4; 0b1001:4; Rn:4] ->
        aarch32_mull cond A S RdHi RdLo Rn Rm
    | [cond:4; 0b000:3; P; U; 0b1:1; W; 0b0:1; Rn:4; Rt:4; imm4H:4; 0b11:2;
       St; 0b1:1; imm4L:4] ->
        aarch32_ldstd cond P U W St Rn Rt
         (word_zx (word_join imm4H imm4L:byte))
    | [cond:4; 0b000:3; opc:4; S; Rn:4; Rd:4; imm5:5; ty:2; 0b0:1; Rm:4] ->
        aarch32_dp cond opc S Rd Rn (aarch32_src Rn)
         (aarch32_shifted ty imm5 (aarch32_src Rm))
         (aarch32_shifted_carry ty imm5 (aarch32_src Rm))
    | [cond:4; 0b000:3; opc:4; S; Rn:4; Rd:4; Rs:4; 0b0:1; ty:2; 0b1:1; Rm:4] ->
        aarch32_dp_rsr cond opc S Rd Rn Rs ty Rm
    | [cond:4; 0b001:3; opc:4; S; Rn:4; Rd:4; rot:4; imm8:8] ->
        aarch32_dp_imm cond opc S Rd Rn rot imm8
    | [cond:4; 0b010:3; P; U; B; W; L; Rn:4; Rt:4; imm12:12] ->
        aarch32_ldst_imm cond P U B W L Rn Rt imm12
    | [cond:4; 0b011:3; P; U; B; W; L; Rn:4; Rt:4; imm5:5; ty:2; 0b0:1; Rm:4] ->
        aarch32_ldst_reg cond P U B W L Rn Rt imm5 ty Rm
    | [cond:4; 0b011010111111:12; Rd:4; 0b11110011:8; Rm:4] ->
        if Rd = word 15 \/ Rm = word 15 then NONE
        else aarch32_conditional cond
              (aarch32_REV (aarch32_reg Rd) (aarch32_reg Rm))
    | [cond:4; 0b100:3; P; U; 0b0:1; W; L; Rn:4; list:16] ->
        aarch32_ldstm cond P U W L Rn list
    | [cond:4; 0b101:3; L; imm24:24] ->
        if cond = word 15 then NONE
        else if L
        then aarch32_conditional_branch cond
              (aarch32_BL (aarch32_branch_offset imm24))
        else SOME (aarch32_B cond (aarch32_branch_offset imm24))
    | _ -> NONE`;;

open Compute;;

(* Whether a decode theorem says the encoding is unsupported. *)

let is_decode_none th =
  match rhs (concl th) with Const("NONE",_) -> true | _ -> false;;

(* Prove the result of decoding one concrete 32-bit instruction word. The
   input must have the form `decode (word n)`. For example, applying
   `DECODE_OPTION_CONV` to

     `decode (word 0xe0200002)`

   proves that 0xe0200002 decodes to `SOME (aarch32_EOR R0 R0 R2)`, and an
   unsupported encoding's theorem says it decodes to `NONE`. It fails only
   when the evaluation reaches neither, which is a fault in the decoder or
   in this conversion, not a refusal. *)

let DECODE_OPTION_CONV =
  let decode_rw =
    let rw = bool_compset() in
    set_skip rw `COND:bool->A->A->A` (Some 1);
    set_skip rw `_MATCH:A->(A->B->bool)->B` (Some 1);
    set_skip rw `_BITMATCH:(N)word->(num->B->bool)->B` (Some 1);
    word_compute_add_convs rw;
    num_compute_add_convs rw;
    add_conv (`_MATCH:A->(A->B->bool)->B`, 2, MATCH_CONV) rw;
    add_thms [aarch32_reg; aarch32_src; aarch32_conditional;
              aarch32_conditional_branch; aarch32_shifted;
              aarch32_shifted_carry; aarch32_shifted_reg;
              aarch32_shifted_reg_carry; aarch32_expand_imm;
              aarch32_expand_imm_carry; aarch32_dp; aarch32_dp_rsr;
              aarch32_dp_imm; aarch32_ldst; aarch32_ldst_imm; aarch32_ldst_reg; aarch32_ldstd;
              aarch32_mul; aarch32_mull; aarch32_reglist; aarch32_ldstm;
              aarch32_ldstm_lowest; aarch32_ldstm_writeback;
              aarch32_branch_offset; APPEND] rw;
    (let Some (conceal_th, opaque_const, opaque_arity, _, opaque_conv) =
        conceal_bitmatch (concl decode) in
     add_thms [GEN_REWRITE_RULE I [conceal_th] decode] rw;
     add_conv (opaque_const, opaque_arity, opaque_conv) rw);
    rw in
  let base_conv = WEAK_CBV_CONV decode_rw
  (* The decision tree above has no leaf for a word that matches no clause,
     so it leaves one unevaluated: the clauses in order reach the default. *)
  and default_conv = REWR_CONV decode THENC BITMATCH_SEQ_CONV in
  let is_result r =
    match r with
    | Const("NONE",_) | Comb(Const("SOME",_),_) -> true
    | _ -> false in
  fun t ->
    let th = base_conv t in
    if is_result (rhs (concl th)) then th else
    let th' = try default_conv t with Failure _ -> th in
    if is_decode_none th' then th' else
    failwith ("DECODE_OPTION_CONV: " ^ string_of_term t ^
              " evaluates to " ^ string_of_term (rhs (concl th)));;

(* `DECODE_OPTION_CONV` for an encoding that must be supported. *)

let DECODE_CONV t =
  let th = DECODE_OPTION_CONV t in
  if is_decode_none th
  then failwith ("DECODE_CONV: unsupported " ^ string_of_term t) else th;;

(* One encoding per instruction form, checked as this file loads, with
   operand shapes the manual's special cases distinguish: each shift type
   and the amounts that encode 32 and RRX, a rotated immediate, conditions,
   backward branches, each indexing mode, R15 as an operand, and each LDM
   and STM addressing mode. *)

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
    `decode (word 0xe1a02632)`,                (* lsr r2, r2, r6 *)
      `SOME (aarch32_MOV R2 (aarch32_LSR_R R2 R6))`;
    `decode (word 0xe0910352)`,                (* adds r0, r1, r2, asr r3 *)
      `SOME (aarch32_ADDS R0 R1 (aarch32_ASR_R R2 R3))`;
    `decode (word 0xe1b00311)`,                (* lsls r0, r1, r3 *)
      `SOME (aarch32_MOVS R0 (aarch32_LSL_R R1 R3) (aarch32_LSL_RC R1 R3))`;
    `decode (word 0xe3c004ff)`,                (* bic r0, r0, #0xff000000 *)
      `SOME (aarch32_BIC R0 R0 (rvalue (word 0xff000000)))`;
    `decode (word 0xe3500000)`,                (* cmp r0, #0 *)
      `SOME (aarch32_CMP R0 (rvalue (word 0)))`;
    `decode (word 0x31a01003)`,                (* movlo r1, r3 *)
      `SOME (aarch32_cond (word 3) (aarch32_MOV R1 R3))`;
    `decode (word 0xe24f3078)`,                (* sub r3, pc, #120 *)
      `SOME (aarch32_SUB R3 aarch32_R15 (rvalue (word 120)))`;
    `decode (word 0xe08fe00e)`,                (* add lr, pc, lr *)
      `SOME (aarch32_ADD LR aarch32_R15 LR)`;
    `decode (word 0xe1a0000f)`,                (* mov r0, pc *)
      `SOME (aarch32_MOV R0 aarch32_R15)`;
    `decode (word 0x3afffffe)`,                (* blo . *)
      `SOME (aarch32_B (word 3) (word 0))`;
    `decode (word 0xeafffff9)`,                (* b .-20 *)
      `SOME (aarch32_B (word 14) (word 0xffffffec))`;
    `decode (word 0xebfffffe)`,                (* bl . *)
      `SOME (aarch32_BL (word 0))`;
    `decode (word 0x1b000001)`,                (* blne .+12 *)
      `SOME (aarch32_cond_branch (word 1) (aarch32_BL (word 12)))`;
    `decode (word 0xe12fff1e)`,                (* bx lr *)
      `SOME (aarch32_BX LR)`;
    `decode (word 0x112fff1e)`,                (* bxne lr *)
      `SOME (aarch32_cond_branch (word 1) (aarch32_BX LR))`;
    `decode (word 0xe4d0c001)`,                (* ldrb r12, [r0], #1 *)
      `SOME (aarch32_LDRB (word 14) R12 R0 (rvalue (word 1)) F T)`;
    `decode (word 0xe5b2e004)`,                (* ldr lr, [r2, #4]! *)
      `SOME (aarch32_LDR (word 14) LR R2 (rvalue (word 4)) T T)`;
    `decode (word 0xe5013008)`,                (* str r3, [r1, #-8] *)
      `SOME (aarch32_STR (word 14) R3 R1 (rvalue (word 0xfffffff8)) T F)`;
    `decode (word 0x249c8010)`,                (* ldrhs r8, [r12], #16 *)
      `SOME (aarch32_LDR (word 2) R8 R12 (rvalue (word 16)) F T)`;
    `decode (word 0xe59f84ec)`,                (* ldr r8, [pc, #0x4ec] *)
      `SOME (aarch32_LDR (word 14) R8 aarch32_R15 (rvalue (word 0x4ec)) T F)`;
    `decode (word 0xe59df1b8)`,                (* ldr pc, [sp, #0x1b8] *)
      `SOME (aarch32_LDR_PC (word 14) SP (rvalue (word 0x1b8)) T F)`;
    `decode (word 0x159df1b8)`,                (* ldrne pc, [sp, #0x1b8] *)
      `SOME (aarch32_LDR_PC (word 1) SP (rvalue (word 0x1b8)) T F)`;
    `decode (word 0xe7d12002)`,                (* ldrb r2, [r1, r2] *)
      `SOME (aarch32_LDRB (word 14) R2 R1 R2 T F)`;
    `decode (word 0xe7203102)`,                (* str r3, [r0, -r2, lsl #2]! *)
      `SOME (aarch32_STR (word 14) R3 R0 (aarch32_NEG (aarch32_LSL R2 2)) T T)`;
    `decode (word 0xe1cd40d0)`,                (* ldrd r4, r5, [sp] *)
      `SOME (aarch32_LDRD (word 14) R4 R5 SP (rvalue (word 0)) T F)`;
    `decode (word 0x11cd40f0)`,                (* strdne r4, r5, [sp] *)
      `SOME (aarch32_STRD (word 1) R4 R5 SP (rvalue (word 0)) T F)`;
    `decode (word 0xe16041f8)`,                (* strd r4, r5, [r0, #-24]! *)
      `SOME (aarch32_STRD (word 14) R4 R5 R0 (rvalue (word 0xffffffe8)) T T)`;
    `decode (word 0xe92d4010)`,                (* push {r4, lr} *)
      `SOME (aarch32_STM (word 14) [R4; LR] SP (word 0xfffffff8) 8
              (word 0xfffffff8) T)`;
    `decode (word 0xe8bd8010)`,                (* pop {r4, pc} *)
      `SOME (aarch32_LDM_PC (word 14) [R4] SP (word 0) (word 4) 8 (word 8)
              T)`;
    `decode (word 0x18bd8010)`,                (* popne {r4, pc} *)
      `SOME (aarch32_LDM_PC (word 1) [R4] SP (word 0) (word 4) 8 (word 8)
              T)`;
    `decode (word 0x18bd0010)`,                (* popne {r4} *)
      `SOME (aarch32_LDM (word 1) [R4] SP (word 0) 4 (word 4) T)`;
    `decode (word 0x092d4010)`,                (* pusheq {r4, lr} *)
      `SOME (aarch32_STM (word 0) [R4; LR] SP (word 0xfffffff8) 8
              (word 0xfffffff8) T)`;
    `decode (word 0xe89c0030)`,                (* ldm r12, {r4, r5} *)
      `SOME (aarch32_LDM (word 14) [R4; R5] R12 (word 0) 8 (word 8) F)`;
    `decode (word 0xe9800006)`,                (* stmib r0, {r1, r2} *)
      `SOME (aarch32_STM (word 14) [R1; R2] R0 (word 4) 8 (word 8) F)`;
    `decode (word 0xe8300006)`,                (* ldmda r0!, {r1, r2} *)
      `SOME (aarch32_LDM (word 14) [R1; R2] R0 (word 0xfffffffc) 8
              (word 0xfffffff8) T)`;
    `decode (word 0xe008089a)`,                (* mul r8, r10, r8 *)
      `SOME (aarch32_MUL R8 R10 R8)`;
    `decode (word 0xe08ba295)`,                (* umull r10, r11, r5, r2 *)
      `SOME (aarch32_UMULL R10 R11 R5 R2)`;
    `decode (word 0xe0aca896)`,                (* umlal r10, r12, r6, r8 *)
      `SOME (aarch32_UMLAL R10 R12 R6 R8)`;
    `decode (word 0xe6bf8f38)`,                (* rev r8, r8 *)
      `SOME (aarch32_REV R8 R8)`;
    `decode (word 0xe320f000)`,                (* nop *)
      `SOME aarch32_NOP`;
    `decode (word 0xf57ff05f)`,                (* dmb sy *)
      `SOME aarch32_DMB`;
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

(* Encodings that must decode to NONE: R15 as a destination, or as an operand
   the manual forbids, the unconditional space, LDRT, writeback to a
   transferred register, a should-be-zero field that is not, and the
   neighbors of the encodings above. *)

let AARCH32_DECODE_REFUSALS =
  let refuse tm =
    if not (is_decode_none (DECODE_OPTION_CONV tm)) then
      failwith ("AARCH32_DECODE_REFUSALS: decoded " ^ string_of_term tm) in
  List.iter refuse
   [`decode (word 0xe08ff000)`;                (* add pc, pc, r0 *)
    `decode (word 0xe1a0f00e)`;                (* mov pc, lr *)
    `decode (word 0xe1a0021f)`;                (* lsl r0, pc, r2 *)
    `decode (word 0xf0200002)`;                (* cond = 1111 *)
    `decode (word 0xf7910002)`;                (* ldr r0, [r1, r2], cond = 1111 *)
    `decode (word 0xf1cd40d0)`;                (* ldrd r4, r5, [sp], cond = 1111 *)
    `decode (word 0xf8bd0010)`;                (* pop {r4}, cond = 1111 *)
    `decode (word 0xe4f0c001)`;                (* ldrbt r12, [r0], #1 *)
    `decode (word 0xe4d00001)`;                (* ldrb r0, [r0], #1 *)
    `decode (word 0xe1a10002)`;                (* mov r0, r2, Rn = 1 *)
    `decode (word 0xe58f0000)`;                (* str r0, [pc] *)
    `decode (word 0xe5df0000)`;                (* ldrb r0, [pc] *)
    `decode (word 0xe59ff000)`;                (* ldr pc, [pc] *)
    `decode (word 0xe790f001)`;                (* ldr pc, [r0, r1] *)
    `decode (word 0xe5d0f000)`;                (* ldrb pc, [r0] *)
    `decode (word 0xe79f0001)`;                (* ldr r0, [pc, r1] *)
    `decode (word 0xe12fff3e)`;                (* blx lr *)
    `decode (word 0xe12fff1f)`;                (* bx pc *)
    `decode (word 0xfa000000)`;                (* blx . *)
    `decode (word 0xe8bd0000)`;                (* pop {} *)
    `decode (word 0xe8bd2010)`;                (* pop {r4, sp} *)
    `decode (word 0xe8902010)`;                (* ldm r0, {r4, sp} *)
    `decode (word 0xe8a00011)`;                (* stm r0!, {r0, r4} *)
    `decode (word 0xe92d8010)`;                (* push {r4, pc} *)
    `decode (word 0xe8fd8010)`;                (* ldm sp!, {r4, pc}^ *)
    `decode (word 0xe89f0030)`;                (* ldm pc, {r4, r5} *)
    `decode (word 0xe1c150f0)`;                (* strd r5, r6, [r1] *)
    `decode (word 0xe1cde0d0)`;                (* ldrd lr, pc, [sp] *)
    `decode (word 0xe0100291)`;                (* muls r0, r1, r2 *)
    `decode (word 0xe0200291)`;                (* mla r0, r1, r2, r0 *)
    `decode (word 0xe0800291)`;                (* umull r0, r0, r1, r2 *)
    `decode (word 0xe0c10392)`;                (* smull r0, r1, r2, r3 *)
    `decode (word 0xe6ff0f31)`;                (* rbit r0, r1 *)
    `decode (word 0xe320f001)`;                (* yield *)
    `decode (word 0xf57ff04f)`];;              (* dsb sy *)

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
            ==> aarch32_decode s (word (pc + n)) instruction

   A word that does not decode gets none, rather than failing, since A32
   routines keep literal pools and tables among their instructions. A proof
   that steps to one fails there. *)

let AARCH32_DECODES_THM =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + 4 = pc' ==>
     aligned_bytes_loaded s (word pc) l ==>
     read_int32 l = SOME (a,l') ==> decode a = SOME i ==>
     aarch32_decode s (word pc) i' /\
     aligned_bytes_loaded s (word pc') l'`,
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC AARCH32_DECODE_CONS)
  and sth = (UNDISCH_ALL o prove)
   (`pc + 4 = pc' ==>
     aligned_bytes_loaded s (word pc:int32) l ==>
     read_int32 l = SOME (a:int32,l') ==>
     aligned_bytes_loaded s (word pc':int32) l'`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[read_int32; read_word_eq_some; aligned_bytes_loaded_word] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC DIVIDES_ADD THEN ASM_REWRITE_TAC[DIVIDES_REFL];
      UNDISCH_TAC `bytes_loaded s (word pc:int32) l` THEN
      ASM_REWRITE_TAC[bytes_loaded_append; GSYM WORD_ADD] THEN SIMP_TAC[]])
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
    let th4,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl,a),n4)) in
      PROVE_HYP th (INST [pc,epc; a,en; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl,pc),n4)),`0` in
    let pc' = rhs (concl th4) in
    let rest bth =
      match l' with
      | Const("NIL",_) -> []
      | _ -> go (bth ()) in
    let th2 = DECODE_OPTION_CONV (mk_comb (dec,a)) in
    if is_decode_none th2 then
      rest (fun () ->
        itlist PROVE_HYP [th4; th; th1]
          (INST [pc,epc; pc',epc'; l,el; a,ea; l',el'] sth))
    else
      let i = rand (rhs (concl th2)) in
      let th' = itlist PROVE_HYP [REFL i; th4; th; th1; th2]
        (INST [i,ei; i,ei'; pc,epc; pc',epc'; l,el; a,ea; l',el'] pth) in
      (CONJUNCT1 th',pcofs)::rest (fun () -> CONJUNCT2 th') in
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
