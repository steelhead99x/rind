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

(* ------------------------------------------------------------------------- *)
(* Advanced SIMD and the crypto extension, DDI 0406's A7.4 to A7.8 and the   *)
(* crypto extension's encodings in DDI 0487's F5. A register field is its    *)
(* high bit, D, N, or M, over four more, which `aarch32_vnum` puts together; *)
(* a Q register's number is its D registers', so an odd one is UNDEFINED.    *)
(* The model decodes the forms armv7's assembly runs and their neighbors at  *)
(* little cost: the integer, bitwise, shift, permute, and long-multiply      *)
(* operations below at every element size the manual allows, but VMULL and  *)
(* VMLAL of integers and their by-scalar forms at 32 bits only, VMOV and     *)
(* VDUP between core and SIMD registers, VLD1 and VST1 of every form, and    *)
(* VLDM, VSTM, VLDR, and VSTR of D registers from a base other than PC.      *)
(* ------------------------------------------------------------------------- *)

let aarch32_vnum = new_definition
 `aarch32_vnum D (v:4 word) = if D then val v + 16 else val v`;;

let aarch32_dreg = new_definition
 `aarch32_dreg n =
    if n = 0 then D0 else if n = 1 then D1 else if n = 2 then D2 else
    if n = 3 then D3 else if n = 4 then D4 else if n = 5 then D5 else
    if n = 6 then D6 else if n = 7 then D7 else if n = 8 then D8 else
    if n = 9 then D9 else if n = 10 then D10 else if n = 11 then D11 else
    if n = 12 then D12 else if n = 13 then D13 else if n = 14 then D14 else
    if n = 15 then D15 else if n = 16 then D16 else if n = 17 then D17 else
    if n = 18 then D18 else if n = 19 then D19 else if n = 20 then D20 else
    if n = 21 then D21 else if n = 22 then D22 else if n = 23 then D23 else
    if n = 24 then D24 else if n = 25 then D25 else if n = 26 then D26 else
    if n = 27 then D27 else if n = 28 then D28 else if n = 29 then D29 else
    if n = 30 then D30 else D31`;;

let aarch32_qreg = new_definition
 `aarch32_qreg n =
    if n = 0 then Q0 else if n = 2 then Q1 else if n = 4 then Q2 else
    if n = 6 then Q3 else if n = 8 then Q4 else if n = 10 then Q5 else
    if n = 12 then Q6 else if n = 14 then Q7 else if n = 16 then Q8 else
    if n = 18 then Q9 else if n = 20 then Q10 else if n = 22 then Q11 else
    if n = 24 then Q12 else if n = 26 then Q13 else if n = 28 then Q14 else
    Q15`;;

(* `k` D registers from Dd up, for a list. *)

let aarch32_dregs = define
 `aarch32_dregs d k =
    if k = 0 then []
    else CONS (aarch32_dreg d) (aarch32_dregs (d + 1) (k - 1))`;;

(* An operation over the whole register, given at the D and Q widths. *)

let aarch32_vwhole1 = new_definition
 `aarch32_vwhole1 Q (fd:int64->int64) (fq:int128->int128) d m =
    if Q then
      if ODD d \/ ODD m then NONE
      else SOME (aarch32_VUNARY fq (aarch32_qreg d) (aarch32_qreg m))
    else SOME (aarch32_VUNARY fd (aarch32_dreg d) (aarch32_dreg m))`;;

let aarch32_vwhole2 = new_definition
 `aarch32_vwhole2 Q (fd:int64->int64->int64) (fq:int128->int128->int128)
                  d n m =
    if Q then
      if ODD d \/ ODD n \/ ODD m then NONE
      else SOME (aarch32_VBINARY fq (aarch32_qreg d) (aarch32_qreg n)
                                 (aarch32_qreg m))
    else SOME (aarch32_VBINARY fd (aarch32_dreg d) (aarch32_dreg n)
                               (aarch32_dreg m))`;;

let aarch32_vwhole3 = new_definition
 `aarch32_vwhole3 Q (fd:int64->int64->int64->int64)
                  (fq:int128->int128->int128->int128) d n m =
    if Q then
      if ODD d \/ ODD n \/ ODD m then NONE
      else SOME (aarch32_VTERNARY fq (aarch32_qreg d) (aarch32_qreg n)
                                  (aarch32_qreg m))
    else SOME (aarch32_VTERNARY fd (aarch32_dreg d) (aarch32_dreg n)
                                (aarch32_dreg m))`;;

let aarch32_vmove = new_definition
 `aarch32_vmove Q d m =
    if Q then
      if ODD d \/ ODD m then NONE
      else SOME (aarch32_VMOV (aarch32_qreg d) (aarch32_qreg m))
    else SOME (aarch32_VMOV (aarch32_dreg d) (aarch32_dreg m))`;;

(* A lane operation, given at each lane width: 8, 16, 32, and 64 bits for
   `sz` 0 to 3. Over a D register, a 64-bit one applies whole. *)

let aarch32_vlanes1 = new_definition
 `aarch32_vlanes1 Q sz (f8:byte->byte) (f16:int16->int16) (f32:int32->int32)
                  (f64:int64->int64) d m =
    if Q then
      if ODD d \/ ODD m then NONE else
      SOME (if sz = 0 then aarch32_VUNARY (usimd16 f8) (aarch32_qreg d)
                             (aarch32_qreg m)
            else if sz = 1 then aarch32_VUNARY (usimd8 f16) (aarch32_qreg d)
                                  (aarch32_qreg m)
            else if sz = 2 then aarch32_VUNARY (usimd4 f32) (aarch32_qreg d)
                                  (aarch32_qreg m)
            else aarch32_VUNARY (usimd2 f64) (aarch32_qreg d) (aarch32_qreg m))
    else
      SOME (if sz = 0 then aarch32_VUNARY (usimd8 f8) (aarch32_dreg d)
                             (aarch32_dreg m)
            else if sz = 1 then aarch32_VUNARY (usimd4 f16) (aarch32_dreg d)
                                  (aarch32_dreg m)
            else if sz = 2 then aarch32_VUNARY (usimd2 f32) (aarch32_dreg d)
                                  (aarch32_dreg m)
            else aarch32_VUNARY f64 (aarch32_dreg d) (aarch32_dreg m))`;;

let aarch32_vlanes2 = new_definition
 `aarch32_vlanes2 Q sz (f8:byte->byte->byte) (f16:int16->int16->int16)
                  (f32:int32->int32->int32) (f64:int64->int64->int64) d n m =
    if Q then
      if ODD d \/ ODD n \/ ODD m then NONE else
      SOME (if sz = 0 then aarch32_VBINARY (simd16 f8) (aarch32_qreg d)
                             (aarch32_qreg n) (aarch32_qreg m)
            else if sz = 1 then aarch32_VBINARY (simd8 f16) (aarch32_qreg d)
                                  (aarch32_qreg n) (aarch32_qreg m)
            else if sz = 2 then aarch32_VBINARY (simd4 f32) (aarch32_qreg d)
                                  (aarch32_qreg n) (aarch32_qreg m)
            else aarch32_VBINARY (simd2 f64) (aarch32_qreg d) (aarch32_qreg n)
                   (aarch32_qreg m))
    else
      SOME (if sz = 0 then aarch32_VBINARY (simd8 f8) (aarch32_dreg d)
                             (aarch32_dreg n) (aarch32_dreg m)
            else if sz = 1 then aarch32_VBINARY (simd4 f16) (aarch32_dreg d)
                                  (aarch32_dreg n) (aarch32_dreg m)
            else if sz = 2 then aarch32_VBINARY (simd2 f32) (aarch32_dreg d)
                                  (aarch32_dreg n) (aarch32_dreg m)
            else aarch32_VBINARY f64 (aarch32_dreg d) (aarch32_dreg n)
                   (aarch32_dreg m))`;;

(* A lane operation that reads the destination's lane too. *)

let aarch32_vlanes_update = new_definition
 `aarch32_vlanes_update Q sz (f8:byte->byte->byte) (f16:int16->int16->int16)
                        (f32:int32->int32->int32) (f64:int64->int64->int64)
                        d m =
    if Q then
      if ODD d \/ ODD m then NONE else
      SOME (if sz = 0 then aarch32_VUPDATE (simd16 f8) (aarch32_qreg d)
                             (aarch32_qreg m)
            else if sz = 1 then aarch32_VUPDATE (simd8 f16) (aarch32_qreg d)
                                  (aarch32_qreg m)
            else if sz = 2 then aarch32_VUPDATE (simd4 f32) (aarch32_qreg d)
                                  (aarch32_qreg m)
            else aarch32_VUPDATE (simd2 f64) (aarch32_qreg d) (aarch32_qreg m))
    else
      SOME (if sz = 0 then aarch32_VUPDATE (simd8 f8) (aarch32_dreg d)
                             (aarch32_dreg m)
            else if sz = 1 then aarch32_VUPDATE (simd4 f16) (aarch32_dreg d)
                                  (aarch32_dreg m)
            else if sz = 2 then aarch32_VUPDATE (simd2 f32) (aarch32_dreg d)
                                  (aarch32_dreg m)
            else aarch32_VUPDATE f64 (aarch32_dreg d) (aarch32_dreg m))`;;

(* A crypto-extension operation, which takes only Q registers. *)

let aarch32_vcrypto1 = new_definition
 `aarch32_vcrypto1 (f:int128->int128) d m =
    if ODD d \/ ODD m then NONE
    else SOME (aarch32_VUNARY f (aarch32_qreg d) (aarch32_qreg m))`;;

let aarch32_vcrypto2 = new_definition
 `aarch32_vcrypto2 (f:int128->int128->int128) d m =
    if ODD d \/ ODD m then NONE
    else SOME (aarch32_VUPDATE f (aarch32_qreg d) (aarch32_qreg m))`;;

let aarch32_vcrypto3 = new_definition
 `aarch32_vcrypto3 (f:int128->int128->int128->int128) d n m =
    if ODD d \/ ODD n \/ ODD m then NONE
    else SOME (aarch32_VTERNARY f (aarch32_qreg d) (aarch32_qreg n)
                                (aarch32_qreg m))`;;

(* "Three registers of the same length", with the crypto extension's SHA-1
   and SHA-256 operations. VSHL by register shifts Vm by Vn's lanes. *)

let aarch32_simd_3same = new_definition
 `aarch32_simd_3same U (size:2 word) (opc:4 word) o1 Q d n m =
    if opc = word 1 /\ o1 then
      if ~U /\ size = word 0 then aarch32_vwhole2 Q word_and word_and d n m
      else if ~U /\ size = word 1 then
        aarch32_vwhole2 Q aarch32_bic aarch32_bic d n m
      else if ~U /\ size = word 2 then
        (if n = m then aarch32_vmove Q d m
         else aarch32_vwhole2 Q word_or word_or d n m)
      else if U /\ size = word 0 then aarch32_vwhole2 Q word_xor word_xor d n m
      else if U /\ size = word 1 then
        aarch32_vwhole3 Q aarch32_bsl aarch32_bsl d n m
      else NONE
    else if opc = word 8 then
      if ~o1 then
        (if U then aarch32_vlanes2 Q (val size) word_sub word_sub word_sub
                     word_sub d n m
         else aarch32_vlanes2 Q (val size) word_add word_add word_add word_add
                d n m)
      else if ~U /\ ~(size = word 3) then
        aarch32_vlanes2 Q (val size) aarch32_tst aarch32_tst aarch32_tst
          aarch32_tst d n m
      else NONE
    else if opc = word 9 /\ o1 /\ ~U /\ ~(size = word 3) then
      aarch32_vlanes2 Q (val size) word_mul word_mul word_mul word_mul d n m
    else if opc = word 4 /\ ~o1 then
      (if U then aarch32_vlanes2 Q (val size) aarch32_ushl aarch32_ushl
                   aarch32_ushl aarch32_ushl d m n
       else aarch32_vlanes2 Q (val size) aarch32_sshl aarch32_sshl
              aarch32_sshl aarch32_sshl d m n)
    else if opc = word 12 /\ ~o1 /\ Q then
      if ~U then
        aarch32_vcrypto3 (if size = word 0 then sha1c
                          else if size = word 1 then sha1p
                          else if size = word 2 then sha1m else sha1su0) d n m
      else if size = word 3 then NONE
      else aarch32_vcrypto3 (if size = word 0 then sha256h
                             else if size = word 1 then sha256h2
                             else sha256su1) d n m
    else NONE`;;

(* AdvSIMDExpandImm: the 64-bit value of `op`, `cmode`, and `imm8`. With op
   set and cmode 1110, each bit of imm8 fills a byte; with op clear and cmode
   1111, it is VMOV.F32's single-precision value, twice. *)

let aarch32_byte_mask = new_definition
 `aarch32_byte_mask (imm8:byte) : int64 =
    word((if bit 0 imm8 then 0xff else 0) +
         (if bit 1 imm8 then 0xff00 else 0) +
         (if bit 2 imm8 then 0xff0000 else 0) +
         (if bit 3 imm8 then 0xff000000 else 0) +
         (if bit 4 imm8 then 0xff00000000 else 0) +
         (if bit 5 imm8 then 0xff0000000000 else 0) +
         (if bit 6 imm8 then 0xff000000000000 else 0) +
         (if bit 7 imm8 then 0xff00000000000000 else 0))`;;

let aarch32_vfp_imm32 = new_definition
 `aarch32_vfp_imm32 (imm8:byte) : int32 =
    word((if bit 7 imm8 then 0x80000000 else 0) +
         (if bit 6 imm8 then 0x3e000000 else 0x40000000) +
         val(word_and imm8 (word 63)) * 0x80000)`;;

let aarch32_expand_simd_imm = new_definition
 `aarch32_expand_simd_imm op (cmode:4 word) (imm8:byte) : int64 =
    if cmode = word 0 \/ cmode = word 1 then word_duplicate (word_zx imm8:int32)
    else if cmode = word 2 \/ cmode = word 3 then
      word_duplicate (word_shl (word_zx imm8:int32) 8)
    else if cmode = word 4 \/ cmode = word 5 then
      word_duplicate (word_shl (word_zx imm8:int32) 16)
    else if cmode = word 6 \/ cmode = word 7 then
      word_duplicate (word_shl (word_zx imm8:int32) 24)
    else if cmode = word 8 \/ cmode = word 9 then
      word_duplicate (word_zx imm8:int16)
    else if cmode = word 10 \/ cmode = word 11 then
      word_duplicate (word_shl (word_zx imm8:int16) 8)
    else if cmode = word 12 then
      word_duplicate (word_add (word_shl (word_zx imm8:int32) 8) (word 0xff))
    else if cmode = word 13 then
      word_duplicate (word_add (word_shl (word_zx imm8:int32) 16)
                               (word 0xffff))
    else if cmode = word 14 then
      if op then aarch32_byte_mask imm8 else word_duplicate imm8
    else word_duplicate (aarch32_vfp_imm32 imm8)`;;

(* VMOV (k = 0), VMVN (1), VORR (2), and VBIC (3) of an immediate. *)

let aarch32_vimm = new_definition
 `aarch32_vimm Q d k (imm:int64) =
    if Q then
      if ODD d then NONE
      else if k = 0 then
        SOME (aarch32_VMOV (aarch32_qreg d)
               (rvalue (word_duplicate imm:int128)))
      else if k = 1 then
        SOME (aarch32_VMOV (aarch32_qreg d)
               (rvalue (word_not (word_duplicate imm:int128))))
      else if k = 2 then
        SOME (aarch32_VUPDATE word_or (aarch32_qreg d)
               (rvalue (word_duplicate imm:int128)))
      else
        SOME (aarch32_VUPDATE aarch32_bic (aarch32_qreg d)
               (rvalue (word_duplicate imm:int128)))
    else if k = 0 then SOME (aarch32_VMOV (aarch32_dreg d) (rvalue imm))
    else if k = 1 then
      SOME (aarch32_VMOV (aarch32_dreg d) (rvalue (word_not imm)))
    else if k = 2 then
      SOME (aarch32_VUPDATE word_or (aarch32_dreg d) (rvalue imm))
    else SOME (aarch32_VUPDATE aarch32_bic (aarch32_dreg d) (rvalue imm))`;;

(* "One register and a modified immediate". A zero imm8 is UNPREDICTABLE
   where the manual tests it, and op set with cmode 1111 UNDEFINED. *)

let aarch32_simd_modimm = new_definition
 `aarch32_simd_modimm (cmode:4 word) Q op d (imm8:byte) =
    if (op /\ cmode = word 15) \/
       (imm8 = word 0 /\
        ~(cmode = word 0 \/ cmode = word 1 \/ cmode = word 8 \/
          cmode = word 9 \/ cmode = word 14 \/ cmode = word 15))
    then NONE else
    aarch32_vimm Q d
     (if ~(bit 3 cmode /\ bit 2 cmode) /\ bit 0 cmode then
        if op then 3 else 2
      else if op /\ ~(cmode = word 14) then 1 else 0)
     (aarch32_expand_simd_imm op cmode imm8)`;;

(* A narrowing or widening shift: a Q register's lanes to a D register's,
   or the reverse, at the narrow width `esize`. *)

let aarch32_vnarrow = new_definition
 `aarch32_vnarrow esize (f8:int16->byte) (f16:int32->int16)
                  (f32:int64->int32) d m =
    if ODD m then NONE
    else if esize = 8 then
      SOME (aarch32_VUNARY (usimd8 f8) (aarch32_dreg d) (aarch32_qreg m))
    else if esize = 16 then
      SOME (aarch32_VUNARY (usimd4 f16) (aarch32_dreg d) (aarch32_qreg m))
    else SOME (aarch32_VUNARY (usimd2 f32) (aarch32_dreg d) (aarch32_qreg m))`;;

let aarch32_vwiden = new_definition
 `aarch32_vwiden esize (f8:byte->int16) (f16:int16->int32)
                 (f32:int32->int64) d m =
    if ODD d then NONE
    else if esize = 8 then
      SOME (aarch32_VUNARY (usimd8 f8) (aarch32_qreg d) (aarch32_dreg m))
    else if esize = 16 then
      SOME (aarch32_VUNARY (usimd4 f16) (aarch32_qreg d) (aarch32_dreg m))
    else SOME (aarch32_VUNARY (usimd2 f32) (aarch32_qreg d) (aarch32_dreg m))`;;

(* "Two registers and a shift amount", at lane width `esize`, 8 * 2^sz, from
   L:imm6, where right shifts take 1 to esize places and left ones 0 to
   esize - 1. *)

let aarch32_shift_size = new_definition
 `aarch32_shift_size L (imm6:6 word) =
    if L then 3 else if bit 5 imm6 then 2 else if bit 4 imm6 then 1 else 0`;;

let aarch32_simd_shift_lanes = new_definition
 `aarch32_simd_shift_lanes U (opc:4 word) L Q d m sz esize imm =
    if opc = word 0 then
      (if U then
         aarch32_vlanes1 Q sz
           (aarch32_ushr ((if L then 64 else 2 * esize) - imm))
           (aarch32_ushr ((if L then 64 else 2 * esize) - imm))
           (aarch32_ushr ((if L then 64 else 2 * esize) - imm))
           (aarch32_ushr ((if L then 64 else 2 * esize) - imm)) d m
       else
         aarch32_vlanes1 Q sz
           (aarch32_sshr ((if L then 64 else 2 * esize) - imm))
           (aarch32_sshr ((if L then 64 else 2 * esize) - imm))
           (aarch32_sshr ((if L then 64 else 2 * esize) - imm))
           (aarch32_sshr ((if L then 64 else 2 * esize) - imm)) d m)
    else if opc = word 4 /\ U then
      aarch32_vlanes_update Q sz
        (aarch32_sri ((if L then 64 else 2 * esize) - imm))
        (aarch32_sri ((if L then 64 else 2 * esize) - imm))
        (aarch32_sri ((if L then 64 else 2 * esize) - imm))
        (aarch32_sri ((if L then 64 else 2 * esize) - imm)) d m
    else if opc = word 5 then
      (if U then
         aarch32_vlanes_update Q sz
           (aarch32_sli (if L then imm else imm - esize))
           (aarch32_sli (if L then imm else imm - esize))
           (aarch32_sli (if L then imm else imm - esize))
           (aarch32_sli (if L then imm else imm - esize)) d m
       else
         aarch32_vlanes1 Q sz
           (aarch32_shl (if L then imm else imm - esize))
           (aarch32_shl (if L then imm else imm - esize))
           (aarch32_shl (if L then imm else imm - esize))
           (aarch32_shl (if L then imm else imm - esize)) d m)
    else if opc = word 8 /\ ~U /\ ~L /\ ~Q then
      aarch32_vnarrow esize (aarch32_shrn (2 * esize - imm))
        (aarch32_shrn (2 * esize - imm)) (aarch32_shrn (2 * esize - imm)) d m
    else if opc = word 10 /\ ~L /\ ~Q then
      (if U then
         aarch32_vwiden esize (aarch32_ushll (imm - esize))
           (aarch32_ushll (imm - esize)) (aarch32_ushll (imm - esize)) d m
       else
         aarch32_vwiden esize (aarch32_sshll (imm - esize))
           (aarch32_sshll (imm - esize)) (aarch32_sshll (imm - esize)) d m)
    else NONE`;;

(* Bit 23 set and bit 4 set: a shift, or with L:imm6<5:3> zero a modified
   immediate, whose i, imm3, cmode, op, and imm4 are the U, imm6<2:0>, opc,
   M, and Vm fields. *)

let aarch32_simd_shift = new_definition
 `aarch32_simd_shift U (imm6:6 word) (opc:4 word) L Q M d (vm:4 word) =
    if ~L /\ word_subword imm6 (3,3) = (word 0:3 word) then
      aarch32_simd_modimm opc Q M d
       (word_join (word_join (word(bitval U):1 word)
                             (word_subword imm6 (0,3):3 word):4 word) vm)
    else
      aarch32_simd_shift_lanes U opc L Q d (aarch32_vnum M vm)
       (aarch32_shift_size L imm6) (8 * 2 EXP aarch32_shift_size L imm6)
       (val imm6)`;;

(* VREV64, VREV32, and VREV16, which reverse `esize`-bit lanes in each
   container of `c` bits. *)

let aarch32_simd_rev = new_definition
 `aarch32_simd_rev c esize Q d m =
    if c <= esize then NONE
    else if Q then
      if ODD d \/ ODD m then NONE
      else if c = 64 then
        SOME (aarch32_VUNARY (usimd2 (word_reversefields esize))
               (aarch32_qreg d) (aarch32_qreg m))
      else if c = 32 then
        SOME (aarch32_VUNARY (usimd4 (word_reversefields esize))
               (aarch32_qreg d) (aarch32_qreg m))
      else
        SOME (aarch32_VUNARY (usimd8 (word_reversefields esize))
               (aarch32_qreg d) (aarch32_qreg m))
    else if c = 64 then
      SOME (aarch32_VUNARY (word_reversefields esize)
             (aarch32_dreg d) (aarch32_dreg m))
    else if c = 32 then
      SOME (aarch32_VUNARY (usimd2 (word_reversefields esize))
             (aarch32_dreg d) (aarch32_dreg m))
    else
      SOME (aarch32_VUNARY (usimd4 (word_reversefields esize))
             (aarch32_dreg d) (aarch32_dreg m))`;;

(* VTRN at lane width `esize`, per container of two lanes, and VZIP. *)

let aarch32_simd_trn = new_definition
 `aarch32_simd_trn esize Q d m =
    if d = m \/ esize = 64 then NONE
    else if Q then
      if ODD d \/ ODD m then NONE
      else if esize = 8 then
        SOME (aarch32_VTRN (simd8 aarch32_trn1) (simd8 aarch32_trn2)
               (aarch32_qreg d) (aarch32_qreg m))
      else if esize = 16 then
        SOME (aarch32_VTRN (simd4 aarch32_trn1) (simd4 aarch32_trn2)
               (aarch32_qreg d) (aarch32_qreg m))
      else
        SOME (aarch32_VTRN (simd2 aarch32_trn1) (simd2 aarch32_trn2)
               (aarch32_qreg d) (aarch32_qreg m))
    else if esize = 8 then
      SOME (aarch32_VTRN (simd4 aarch32_trn1) (simd4 aarch32_trn2)
             (aarch32_dreg d) (aarch32_dreg m))
    else if esize = 16 then
      SOME (aarch32_VTRN (simd2 aarch32_trn1) (simd2 aarch32_trn2)
             (aarch32_dreg d) (aarch32_dreg m))
    else
      SOME (aarch32_VTRN aarch32_trn1 aarch32_trn2
             (aarch32_dreg d) (aarch32_dreg m))`;;

let aarch32_simd_zip = new_definition
 `aarch32_simd_zip esize Q d m =
    if d = m \/ esize = 64 then NONE
    else if Q then
      if ODD d \/ ODD m then NONE
      else if esize = 8 then
        SOME (aarch32_VZIP (aarch32_simd16 aarch32_pair)
               (aarch32_qreg d) (aarch32_qreg m))
      else if esize = 16 then
        SOME (aarch32_VZIP (aarch32_simd8 aarch32_pair)
               (aarch32_qreg d) (aarch32_qreg m))
      else
        SOME (aarch32_VZIP (aarch32_simd4 aarch32_pair)
               (aarch32_qreg d) (aarch32_qreg m))
    else if esize = 8 then
      SOME (aarch32_VZIP (aarch32_simd8 aarch32_pair)
             (aarch32_dreg d) (aarch32_dreg m))
    else if esize = 16 then
      SOME (aarch32_VZIP (aarch32_simd4 aarch32_pair)
             (aarch32_dreg d) (aarch32_dreg m))
    else NONE`;;

(* "Two registers, miscellaneous", A = bits 17:16 and B = bits 10:6, the
   latter split here as `b` (bits 10:8), N (bit 7), and Q (bit 6). *)

let aarch32_simd_misc = new_definition
 `aarch32_simd_misc (size:2 word) (a:2 word) (b:3 word) N Q d m =
    if a = word 0 then
      if b = word 0 then
        aarch32_simd_rev (if N then 32 else 64) (8 * 2 EXP val size) Q d m
      else if b = word 1 /\ ~N then
        aarch32_simd_rev 16 (8 * 2 EXP val size) Q d m
      else if b = word 5 /\ N /\ size = word 0 then
        aarch32_vwhole1 Q word_not word_not d m
      else if b = word 3 /\ size = word 0 then
        if N then aarch32_vcrypto1 (if Q then aesimc else aesmc) d m
        else aarch32_vcrypto2 (if Q then aesd else aese) d m
      else NONE
    else if a = word 1 then
      if b = word 2 /\ N /\ Q /\ size = word 2 then aarch32_vcrypto1 sha1h d m
      else NONE
    else if a = word 2 then
      if b = word 0 /\ ~N /\ size = word 0 then
        (if d = m then NONE
         else if Q then
           (if ODD d \/ ODD m then NONE
            else SOME (aarch32_VSWP (aarch32_qreg d) (aarch32_qreg m)))
         else SOME (aarch32_VSWP (aarch32_dreg d) (aarch32_dreg m)))
      else if b = word 0 /\ N then
        aarch32_simd_trn (8 * 2 EXP val size) Q d m
      else if b = word 1 /\ N then
        aarch32_simd_zip (8 * 2 EXP val size) Q d m
      else if b = word 3 /\ N /\ size = word 2 then
        aarch32_vcrypto2 (if Q then sha256su0 else sha1su1) d m
      else NONE
    else NONE`;;

(* VEXT, by `k` bytes. *)

let aarch32_simd_ext = new_definition
 `aarch32_simd_ext Q k d n m =
    if Q then
      if ODD d \/ ODD n \/ ODD m then NONE
      else SOME (aarch32_VBINARY (aarch32_ext k) (aarch32_qreg d)
                                 (aarch32_qreg n) (aarch32_qreg m))
    else if 8 <= k then NONE
    else SOME (aarch32_VBINARY (aarch32_ext k) (aarch32_dreg d)
                               (aarch32_dreg n) (aarch32_dreg m))`;;

(* VTBL with a list of `len` registers from Dn, which must not run past
   D31. *)

let aarch32_simd_tbl = new_definition
 `aarch32_simd_tbl len d n m =
    if 32 < n + len then NONE
    else SOME (aarch32_VTBL (aarch32_dreg d) (aarch32_dreg n)
                (if 2 <= len then aarch32_dreg (n + 1) else rvalue (word 0))
                (if 3 <= len then aarch32_dreg (n + 2) else rvalue (word 0))
                (if 4 <= len then aarch32_dreg (n + 3) else rvalue (word 0))
                len (aarch32_dreg m))`;;

(* VDUP of a scalar, whose size and index imm4 gives. *)

let aarch32_simd_dup = new_definition
 `aarch32_simd_dup Q (imm4:4 word) d m =
    if Q /\ ODD d then NONE
    else if bit 0 imm4 then
      SOME (if Q then aarch32_VUNARY (aarch32_dup8 (val imm4 DIV 2))
                        (aarch32_qreg d) (aarch32_dreg m)
            else aarch32_VUNARY (aarch32_dup8 (val imm4 DIV 2))
                   (aarch32_dreg d) (aarch32_dreg m))
    else if bit 1 imm4 then
      SOME (if Q then aarch32_VUNARY (aarch32_dup16 (val imm4 DIV 4))
                        (aarch32_qreg d) (aarch32_dreg m)
            else aarch32_VUNARY (aarch32_dup16 (val imm4 DIV 4))
                   (aarch32_dreg d) (aarch32_dreg m))
    else if bit 2 imm4 then
      SOME (if Q then aarch32_VUNARY (aarch32_dup32 (val imm4 DIV 8))
                        (aarch32_qreg d) (aarch32_dreg m)
            else aarch32_VUNARY (aarch32_dup32 (val imm4 DIV 8))
                   (aarch32_dreg d) (aarch32_dreg m))
    else NONE`;;

(* "Three registers of different lengths" and "two registers and a scalar":
   VMLAL (opc 1000) and VMULL (1100) of 32-bit lanes, signed or unsigned,
   VMULL.P8 and VMULL.P64 (1110), and by a scalar, Dm[x] for D0 to D15,
   VMLAL (0010) and VMULL (1010). *)

let aarch32_simd_long = new_definition
 `aarch32_simd_long U (size:2 word) (opc:4 word) d n m =
    if ODD d then NONE
    else if opc = word 8 /\ size = word 2 then
      SOME (aarch32_VTERNARY (if U then aarch32_umlal else aarch32_smlal)
             (aarch32_qreg d) (aarch32_dreg n) (aarch32_dreg m))
    else if opc = word 12 /\ size = word 2 then
      SOME (aarch32_VBINARY (if U then aarch32_umull else aarch32_smull)
             (aarch32_qreg d) (aarch32_dreg n) (aarch32_dreg m))
    else if opc = word 14 /\ ~U /\ size = word 0 then
      SOME (aarch32_VBINARY aarch32_pmull8
             (aarch32_qreg d) (aarch32_dreg n) (aarch32_dreg m))
    else if opc = word 14 /\ ~U /\ size = word 2 then
      SOME (aarch32_VBINARY (word_pmul:int64->int64->int128)
             (aarch32_qreg d) (aarch32_dreg n) (aarch32_dreg m))
    else NONE`;;

let aarch32_simd_scalar = new_definition
 `aarch32_simd_scalar U (size:2 word) (opc:4 word) d n M (vm:4 word) =
    if ODD d \/ ~(size = word 2) then NONE
    else if opc = word 2 then
      SOME (aarch32_VTERNARY
             ((if U then aarch32_umlal_lane else aarch32_smlal_lane)
              (bitval M))
             (aarch32_qreg d) (aarch32_dreg n) (aarch32_dreg (val vm)))
    else if opc = word 10 then
      SOME (aarch32_VBINARY
             ((if U then aarch32_umull_lane else aarch32_smull_lane)
              (bitval M))
             (aarch32_qreg d) (aarch32_dreg n) (aarch32_dreg (val vm)))
    else NONE`;;

(* Bit 23 set and bit 4 clear: by size 11, VEXT, VTBL, VDUP of a scalar, and
   the miscellaneous group; by any other, the long and scalar forms. *)

let aarch32_simd_other = new_definition
 `aarch32_simd_other U (size:2 word) (vn:4 word) (opc:4 word) N B6 M
                     (vm:4 word) d =
    if size = word 3 then
      if ~U then
        aarch32_simd_ext B6 (val opc) d (aarch32_vnum N vn) (aarch32_vnum M vm)
      else if bit 3 opc /\ ~bit 2 opc then
        (if B6 then NONE
         else aarch32_simd_tbl (val opc MOD 4 + 1) d (aarch32_vnum N vn)
                (aarch32_vnum M vm))
      else if opc = word 12 /\ ~N then
        aarch32_simd_dup B6 vn d (aarch32_vnum M vm)
      else if bit 3 opc then NONE
      else aarch32_simd_misc (word_subword vn (2,2)) (word_subword vn (0,2))
             (word_subword opc (0,3)) N B6 d (aarch32_vnum M vm)
    else if B6 then
      aarch32_simd_scalar U size opc d (aarch32_vnum N vn) M vm
    else aarch32_simd_long U size opc d (aarch32_vnum N vn)
           (aarch32_vnum M vm)`;;

(* VLD1 and VST1: the offset operand for writeback, Rm, or for Rm = 13 the
   length, or for Rm = 15, no writeback, zero; and an alignment qualifier's
   byte count. *)

let aarch32_vld_offset = new_definition
 `aarch32_vld_offset (m:4 word) len =
    if m = word 13 then rvalue (word len)
    else if m = word 15 then rvalue (word 0)
    else aarch32_reg m`;;

let aarch32_vld_align = new_definition
 `aarch32_vld_align (align:2 word) =
    if align = word 0 then 1 else 4 * 2 EXP val align`;;

(* Multiple single elements: 1 to 4 registers, by `type`, or none for the
   other structure loads and stores. *)

let aarch32_vld1_regs = new_definition
 `aarch32_vld1_regs (ty:4 word) =
    if ty = word 7 then 1 else if ty = word 10 then 2
    else if ty = word 6 then 3 else if ty = word 2 then 4 else 0`;;

let aarch32_vld1_multiple = new_definition
 `aarch32_vld1_multiple L d (n:4 word) regs (align:2 word) (m:4 word) =
    if regs = 0 \/ 32 < d + regs \/ ((regs = 1 \/ regs = 3) /\ bit 1 align) \/
       (regs = 2 /\ align = word 3)
    then NONE
    else SOME ((if L then aarch32_VLD1 else aarch32_VST1)
               (aarch32_dregs d regs) (aarch32_reg n)
               (aarch32_vld_offset m (8 * regs)) (8 * regs)
               (aarch32_vld_align align) (~(m = word 15)))`;;

(* A single element to or from one lane, of size `sz` with index_align
   `ia`. *)

let aarch32_vld1_lane = new_definition
 `aarch32_vld1_lane L d (n:4 word) sz (ia:4 word) (m:4 word) =
    if sz = 0 then
      if bit 0 ia then NONE
      else SOME ((if L then aarch32_VLD1_LANE else aarch32_VST1_LANE)
                 (aarch32_dreg d) bytes8 (8 * (val ia DIV 2)) 8 1
                 (aarch32_reg n) (aarch32_vld_offset m 1) 1 (~(m = word 15)))
    else if sz = 1 then
      if bit 1 ia then NONE
      else SOME ((if L then aarch32_VLD1_LANE else aarch32_VST1_LANE)
                 (aarch32_dreg d) bytes16 (16 * (val ia DIV 4)) 16 2
                 (aarch32_reg n) (aarch32_vld_offset m 2)
                 (if bit 0 ia then 2 else 1) (~(m = word 15)))
    else
      if bit 2 ia \/ ~(bit 0 ia <=> bit 1 ia) then NONE
      else SOME ((if L then aarch32_VLD1_LANE else aarch32_VST1_LANE)
                 (aarch32_dreg d) bytes32 (32 * (val ia DIV 8)) 32 4
                 (aarch32_reg n) (aarch32_vld_offset m 4)
                 (if bit 0 ia then 4 else 1) (~(m = word 15)))`;;

(* A single element to all lanes of one register or, with `two`, two. *)

let aarch32_vld1_all = new_definition
 `aarch32_vld1_all d (n:4 word) (size:2 word) two a (m:4 word) =
    if size = word 3 \/ (size = word 0 /\ a) \/
       32 < d + (if two then 2 else 1)
    then NONE
    else if size = word 0 then
      SOME (aarch32_VLD1_ALL (aarch32_dregs d (if two then 2 else 1)) bytes8 1
             (aarch32_reg n) (aarch32_vld_offset m 1) 1 (~(m = word 15)))
    else if size = word 1 then
      SOME (aarch32_VLD1_ALL (aarch32_dregs d (if two then 2 else 1)) bytes16 2
             (aarch32_reg n) (aarch32_vld_offset m 2) (if a then 2 else 1)
             (~(m = word 15)))
    else
      SOME (aarch32_VLD1_ALL (aarch32_dregs d (if two then 2 else 1)) bytes32 4
             (aarch32_reg n) (aarch32_vld_offset m 4) (if a then 4 else 1)
             (~(m = word 15)))`;;

(* "Advanced SIMD element or structure load/store": VLD1 and VST1 alone, of
   multiple elements (A clear), one lane, or all lanes (B = 1100). The
   fields after B are bits 7:6 and 5:4, a lane's index_align together. PC
   is no base. *)

let aarch32_simd_ldst = new_definition
 `aarch32_simd_ldst A L d (n:4 word) (b:4 word) (size:2 word) (align:2 word)
                    (m:4 word) =
    if n = word 15 then NONE
    else if ~A then aarch32_vld1_multiple L d n (aarch32_vld1_regs b) align m
    else if b = word 12 then
      (if L then aarch32_vld1_all d n size (bit 1 align) (bit 0 align) m
       else NONE)
    else if word_subword b (0,2) = (word 0:2 word) /\
            ~(word_subword b (2,2) = (word 3:2 word)) then
      aarch32_vld1_lane L d n (val b DIV 4) (word_join size align:4 word) m
    else NONE`;;

(* The unconditional space's Advanced SIMD instructions, 1111 001x for data
   processing and 1111 0100 for VLD1 and VST1, which `decode` passes here.
   The clauses cover both spaces without overlap:

     three registers of the same length
                   [1111001; U; 0; D; size:2; Vn:4; Vd:4; opc:4; N; Q; M; o1;
                    Vm:4]
     a shift or a modified immediate
                   [1111001; U; 1; D; imm6:6; Vd:4; opc:4; L; Q; M; 1; Vm:4]
     the rest      [1111001; U; 1; D; size:2; Vn:4; Vd:4; opc:4; N; B6; M; 0;
                    Vm:4]
     element and structure loads and stores
                   [11110100; A; D; L; 0; Rn:4; Vd:4; B:4; size:2; align:2;
                    Rm:4] *)

let decode_simd = new_definition
 `decode_simd (w:int32) =
    bitmatch w with
    | [0b1111001:7; U; 0b0:1; D; size:2; Vn:4; Vd:4; opc:4; N; Q; M; o1;
       Vm:4] ->
        aarch32_simd_3same U size opc o1 Q (aarch32_vnum D Vd)
         (aarch32_vnum N Vn) (aarch32_vnum M Vm)
    | [0b1111001:7; U; 0b1:1; D; imm6:6; Vd:4; opc:4; L; Q; M; 0b1:1; Vm:4] ->
        aarch32_simd_shift U imm6 opc L Q M (aarch32_vnum D Vd) Vm
    | [0b1111001:7; U; 0b1:1; D; size:2; Vn:4; Vd:4; opc:4; N; B6; M; 0b0:1;
       Vm:4] ->
        aarch32_simd_other U size Vn opc N B6 M Vm (aarch32_vnum D Vd)
    | [0b11110100:8; A; D; L; 0b0:1; Rn:4; Vd:4; B:4; size:2; align:2;
       Rm:4] ->
        aarch32_simd_ldst A L (aarch32_vnum D Vd) Rn B size align Rm
    | [0b11110100:8; x:3; 0b1:1; y:20] -> NONE
    | _ -> NONE`;;

(* VLDM, VSTM, VLDR, and VSTR of D registers, VPUSH and VPOP among them:
   increment after (P clear, U set), decrement before with writeback (P and
   W set, U clear), or one register at an offset (P set, W clear). An odd
   imm8 is FLDMX, a list past D31 or of more than 16 registers UNPREDICTABLE,
   and P = U the 64-bit core transfers or UNDEFINED. PC is no base. *)

let aarch32_vldstm = new_definition
 `aarch32_vldstm (cond:4 word) P U W L d (n:4 word) (imm8:byte) =
    if cond = word 15 \/ n = word 15 then NONE
    else if P /\ ~W then
      SOME ((if L then aarch32_VLDM else aarch32_VSTM) cond [aarch32_dreg d]
            (aarch32_reg n)
            (if U then word(4 * val imm8) else word_neg(word(4 * val imm8)))
            8 (word 0) F)
    else if (P <=> U) \/ bit 0 imm8 \/ imm8 = word 0 \/ 32 < val imm8 \/
            32 < d + val imm8 DIV 2
    then NONE
    else SOME ((if L then aarch32_VLDM else aarch32_VSTM) cond
               (aarch32_dregs d (val imm8 DIV 2)) (aarch32_reg n)
               (if U then word 0 else word_neg(word(4 * val imm8)))
               (4 * val imm8)
               (if U then word(4 * val imm8) else word_neg(word(4 * val imm8)))
               W)`;;

(* VMOV from a core register to a D register's lane (bit 23 clear), with
   opc1:opc2 giving its size and index, and VDUP from a core register (bit 23
   set), with B:E its size. Rt is not PC. *)

let aarch32_vmov_core = new_definition
 `aarch32_vmov_core (cond:4 word) b23 b22 b21 d (t:4 word) b6 b5 =
    if t = word 15 then NONE
    else if b23 then
      if b6 \/ (b22 /\ b5) \/ (b21 /\ ODD d) then NONE
      else aarch32_conditional cond
            (if b21 then
               (if b22 then aarch32_VUNARY (aarch32_dup8 0) (aarch32_qreg d)
                              (aarch32_reg t)
                else if b5 then aarch32_VUNARY (aarch32_dup16 0)
                                  (aarch32_qreg d) (aarch32_reg t)
                else aarch32_VUNARY (aarch32_dup32 0) (aarch32_qreg d)
                       (aarch32_reg t))
             else if b22 then aarch32_VUNARY (aarch32_dup8 0) (aarch32_dreg d)
                                (aarch32_reg t)
             else if b5 then aarch32_VUNARY (aarch32_dup16 0) (aarch32_dreg d)
                               (aarch32_reg t)
             else aarch32_VUNARY (aarch32_dup32 0) (aarch32_dreg d)
                    (aarch32_reg t))
    else if b22 then
      aarch32_conditional cond
       (aarch32_VUPDATE
         (aarch32_ins (8 * (4 * bitval b21 + 2 * bitval b6 + bitval b5)) 8)
         (aarch32_dreg d) (aarch32_reg t))
    else if b5 then
      aarch32_conditional cond
       (aarch32_VUPDATE (aarch32_ins (16 * (2 * bitval b21 + bitval b6)) 16)
         (aarch32_dreg d) (aarch32_reg t))
    else if b6 then NONE
    else
      aarch32_conditional cond
       (aarch32_VUPDATE (aarch32_ins (32 * bitval b21) 32)
         (aarch32_dreg d) (aarch32_reg t))`;;

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
     DP immediate, NOP, and for cond = 1111 Advanced SIMD data processing
                   [cond:4; 001; opc:4; S; Rn:4; Rd:4; rot:4; imm8:8]
     LDR(B), STR(B) immediate, DMB, and for cond = 1111 with P clear VLD1
     and VST1      [cond:4; 010; P; U; B; W; L; Rn:4; Rt:4; imm12:12]
     LDR(B), STR(B) register
                   [cond:4; 011; P; U; B; W; L; Rn:4; Rt:4; imm5:5; type:2; 0;
                    Rm:4]
     REV           [cond:4; 0110 1011 1111; Rd:4; 1111 0011; Rm:4]
     LDM, STM      [cond:4; 100; P; U; 0; W; L; Rn:4; register_list:16]
     B, BL         [cond:4; 101; L; imm24:24]
     VLDM, VSTM, VLDR, VSTR
                   [cond:4; 110; P; U; D; W; L; Rn:4; Vd:4; 1011; imm8:8]
     VMOV to a lane, VDUP from a core register
                   [cond:4; 1110; b23; b22; b21; 0; Vd:4; Rt:4; 1011; D; b6;
                    b5; 1; 0000] *)

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
        if cond = word 15 then decode_simd w
        else aarch32_dp_imm cond opc S Rd Rn rot imm8
    | [cond:4; 0b010:3; P; U; B; W; L; Rn:4; Rt:4; imm12:12] ->
        if cond = word 15 /\ ~P then decode_simd w
        else aarch32_ldst_imm cond P U B W L Rn Rt imm12
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
    | [cond:4; 0b110:3; P; U; D; W; L; Rn:4; Vd:4; 0b1011:4; imm8:8] ->
        aarch32_vldstm cond P U W L (aarch32_vnum D Vd) Rn imm8
    | [cond:4; 0b1110:4; b23; b22; b21; 0b0:1; Vd:4; Rt:4; 0b1011:4; D; b6;
       b5; 0b1:1; 0b0000:4] ->
        aarch32_vmov_core cond b23 b22 b21 (aarch32_vnum D Vd) Rt b6 b5
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
              aarch32_branch_offset; APPEND; BITVAL_CLAUSES;
              aarch32_vnum; aarch32_dreg; aarch32_qreg; aarch32_dregs;
              aarch32_vwhole1; aarch32_vwhole2; aarch32_vwhole3;
              aarch32_vmove; aarch32_vlanes1; aarch32_vlanes2;
              aarch32_vlanes_update; aarch32_vcrypto1; aarch32_vcrypto2;
              aarch32_vcrypto3; aarch32_simd_3same; aarch32_byte_mask;
              aarch32_vfp_imm32; aarch32_expand_simd_imm; aarch32_vimm;
              aarch32_simd_modimm; aarch32_vnarrow; aarch32_vwiden;
              aarch32_shift_size; aarch32_simd_shift_lanes;
              aarch32_simd_shift; aarch32_simd_rev; aarch32_simd_trn;
              aarch32_simd_zip; aarch32_simd_misc; aarch32_simd_ext;
              aarch32_simd_tbl; aarch32_simd_dup; aarch32_simd_long;
              aarch32_simd_scalar; aarch32_simd_other; aarch32_vld_offset;
              aarch32_vld_align; aarch32_vld1_regs; aarch32_vld1_multiple;
              aarch32_vld1_lane; aarch32_vld1_all; aarch32_simd_ldst;
              aarch32_vldstm; aarch32_vmov_core] rw;
    List.iter (fun def ->
      let Some (conceal_th, opaque_const, opaque_arity, _, opaque_conv) =
        conceal_bitmatch (concl def) in
      add_thms [GEN_REWRITE_RULE I [conceal_th] def] rw;
      add_conv (opaque_const, opaque_arity, opaque_conv) rw)
     [decode; decode_simd];
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
   backward branches, each indexing mode, R15 as an operand, each LDM and STM
   addressing mode, and Advanced SIMD's D and Q forms and writebacks. *)

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
      `SOME (aarch32_MOVT R1 (word 0x1234))`;
    `decode (word 0xf3000139)`,                (* veor d0, d0, d25 *)
      `SOME (aarch32_VBINARY word_xor D0 D0 D25)`;
    `decode (word 0xf2202150)`,                (* vorr q1, q0, q0 *)
      `SOME (aarch32_VMOV Q1 Q0)`;
    `decode (word 0xf350d1b1)`,                (* vbsl d29, d16, d17 *)
      `SOME (aarch32_VTERNARY aarch32_bsl D29 D16 D17)`;
    `decode (word 0xf2200829)`,                (* vadd.i32 d0, d0, d25 *)
      `SOME (aarch32_VBINARY (simd2 word_add) D0 D0 D25)`;
    `decode (word 0xf3300846)`,                (* vsub.i64 q0, q0, q3 *)
      `SOME (aarch32_VBINARY (simd2 word_sub) Q0 Q0 Q3)`;
    `decode (word 0xf362444a)`,                (* vshl.u32 q10, q5, q1 *)
      `SOME (aarch32_VBINARY (simd4 aarch32_ushl) Q10 Q5 Q1)`;
    `decode (word 0xf2020c68)`,                (* sha1c q0, q1, q12 *)
      `SOME (aarch32_VTERNARY sha1c Q0 Q1 Q12)`;
    `decode (word 0xf3020c68)`,                (* sha256h q0, q1, q12 *)
      `SOME (aarch32_VTERNARY sha256h Q0 Q1 Q12)`;
    `decode (word 0xf2800050)`,                (* vmov.i32 q0, #0 *)
      `SOME (aarch32_VMOV Q0 (rvalue (word 0)))`;
    `decode (word 0xf2806751)`,                (* vorr.i32 q3, #0x1000000 *)
      `SOME (aarch32_VUPDATE word_or Q3
              (rvalue (word 0x01000000010000000100000001000000)))`;
    `decode (word 0xf3a20078)`,                (* vshr.u32 q0, q12, #30 *)
      `SOME (aarch32_VUNARY (usimd4 (aarch32_ushr 30)) Q0 Q12)`;
    `decode (word 0xf38184fa)`,                (* vsri.64 q4, q13, #63 *)
      `SOME (aarch32_VUPDATE (simd2 (aarch32_sri 63)) Q4 Q13)`;
    `decode (word 0xf2e65836)`,                (* vshrn.i64 d21, q11, #26 *)
      `SOME (aarch32_VUNARY (usimd2 (aarch32_shrn 26)) D21 Q11)`;
    `decode (word 0xf3acea1f)`,                (* vshll.u32 q7, d15, #12 *)
      `SOME (aarch32_VUNARY (usimd2 (aarch32_ushll 12)) Q7 D15)`;
    `decode (word 0xf3b000c0)`,                (* vrev32.8 q0, q0 *)
      `SOME (aarch32_VUNARY (usimd4 (word_reversefields 8)) Q0 Q0)`;
    `decode (word 0xf3b00304)`,                (* aese.8 q0, q2 *)
      `SOME (aarch32_VUPDATE aese Q0 Q2)`;
    `decode (word 0xf3b00380)`,                (* aesmc.8 q0, q0 *)
      `SOME (aarch32_VUNARY aesmc Q0 Q0)`;
    `decode (word 0xf3b942c0)`,                (* sha1h.32 q2, q0 *)
      `SOME (aarch32_VUNARY sha1h Q2 Q0)`;
    `decode (word 0xf3ba838e)`,                (* sha1su1.32 q4, q7 *)
      `SOME (aarch32_VUPDATE sha1su1 Q4 Q7)`;
    `decode (word 0xf3b22027)`,                (* vswp d2, d23 *)
      `SOME (aarch32_VSWP D2 D23)`;
    `decode (word 0xf3ba0081)`,                (* vtrn.32 d0, d1 *)
      `SOME (aarch32_VTRN aarch32_trn1 aarch32_trn2 D0 D1)`;
    `decode (word 0xf3b6c18d)`,                (* vzip.16 d12, d13 *)
      `SOME (aarch32_VZIP (aarch32_simd4 aarch32_pair) D12 D13)`;
    `decode (word 0xf2b00140)`,                (* vext.8 q0, q0, q0, #1 *)
      `SOME (aarch32_VBINARY (aarch32_ext 1) Q0 Q0 Q0)`;
    `decode (word 0xf3b009a8)`,                (* vtbl.8 d0, {d16, d17}, d24 *)
      `SOME (aarch32_VTBL D0 D16 D17 (rvalue (word 0)) (rvalue (word 0)) 2
              D24)`;
    `decode (word 0xf3a64c83)`,                (* vmull.u32 q2, d22, d3 *)
      `SOME (aarch32_VBINARY aarch32_umull Q2 D22 D3)`;
    `decode (word 0xf3acc2c0)`,                (* vmlal.u32 q6, d28, d0[0] *)
      `SOME (aarch32_VTERNARY (aarch32_umlal_lane 0) Q6 D28 D0)`;
    `decode (word 0xf28a0e80)`,                (* vmull.p8 q0, d26, d0 *)
      `SOME (aarch32_VBINARY aarch32_pmull8 Q0 D26 D0)`;
    `decode (word 0xf2a90ea9)`,                (* vmull.p64 q0, d25, d25 *)
      `SOME (aarch32_VBINARY word_pmul Q0 D25 D25)`;
    `decode (word 0xeea02b90)`,                (* vdup.32 q8, r2 *)
      `SOME (aarch32_VUNARY (aarch32_dup32 0) Q8 R2)`;
    `decode (word 0xee2d9b10)`,                (* vmov.32 d13[1], r9 *)
      `SOME (aarch32_VUPDATE (aarch32_ins 32 32) D13 R9)`;
    `decode (word 0xf420020d)`,                (* vld1.8 {d0-d3}, [r0]! *)
      `SOME (aarch32_VLD1 [D0; D1; D2; D3] R0 (rvalue (word 32)) 32 1 T)`;
    `decode (word 0xf4200701)`,                (* vld1.8 {d0}, [r0], r1 *)
      `SOME (aarch32_VLD1 [D0] R0 R1 8 1 T)`;
    `decode (word 0xf40007cf)`,                (* vst1.64 {d0}, [r0] *)
      `SOME (aarch32_VST1 [D0] R0 (rvalue (word 0)) 8 1 F)`;
    `decode (word 0xf4a0280f)`,                (* vld1.32 {d2[0]}, [r0] *)
      `SOME (aarch32_VLD1_LANE D2 bytes32 0 32 4 R0 (rvalue (word 0)) 1 F)`;
    `decode (word 0xf4a00c0f)`,                (* vld1.8 {d0[]}, [r0] *)
      `SOME (aarch32_VLD1_ALL [D0] bytes8 1 R0 (rvalue (word 0)) 1 F)`;
    `decode (word 0xf4e30cbd)`,       (* vld1.32 {d16[], d17[]}, [r3:32]! *)
      `SOME (aarch32_VLD1_ALL [D16; D17] bytes32 4 R3 (rvalue (word 4)) 4 T)`;
    `decode (word 0xec990b04)`,                (* vldmia r9, {d0, d1} *)
      `SOME (aarch32_VLDM (word 14) [D0; D1] R9 (word 0) 16 (word 16) F)`;
    `decode (word 0x1c900b02)`,                (* vldmiane r0, {d0} *)
      `SOME (aarch32_VLDM (word 1) [D0] R0 (word 0) 8 (word 8) F)`;
    `decode (word 0xed2d8b08)`,                (* vpush {d8-d11} *)
      `SOME (aarch32_VSTM (word 14) [D8; D9; D10; D11] SP (word 0xffffffe0) 32
              (word 0xffffffe0) T)`;
    `decode (word 0xecbd8b08)`,                (* vpop {d8-d11} *)
      `SOME (aarch32_VLDM (word 14) [D8; D9; D10; D11] SP (word 0) 32
              (word 32) T)`;
    `decode (word 0xedcd8b10)`,                (* vstr d24, [sp, #64] *)
      `SOME (aarch32_VSTM (word 14) [D24] SP (word 64) 8 (word 0) F)`] in
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
   transferred register, a should-be-zero field that is not, the neighbors of
   the encodings above, an odd Q register, the UNPREDICTABLE operands and
   immediates of Advanced SIMD, and its forms rind's assembly does not run. *)

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
    `decode (word 0xf57ff04f)`;                (* dsb sy *)
    `decode (word 0xf2201840)`;                (* vadd.i32 q1, q0, q0, Vd odd *)
    `decode (word 0xf3000d50)`;                (* vmul.f32 q0, q0, q0 *)
    `decode (word 0xf2800350)`;                (* vorr.i32 q0, #0 *)
    `decode (word 0xf2800f30)`;                (* op = 1, cmode = 1111 *)
    `decode (word 0xf3ba0181)`;                (* vzip.32 d0, d1 *)
    `decode (word 0xf3ba0080)`;                (* vtrn.32 d0, d0 *)
    `decode (word 0xf3b20000)`;                (* vswp d0, d0 *)
    `decode (word 0xf2b00800)`;                (* vext.8 d0, d0, d0, #8 *)
    `decode (word 0xf3b009e8)`;                (* vtbx.8 d0, {d16, d17}, d24 *)
    `decode (word 0xf3900c01)`;                (* vmull.u16 q0, d0, d1 *)
    `decode (word 0xf420080f)`;                (* vld2.8 {d0, d1}, [r0] *)
    `decode (word 0xf420040f)`;                (* vld3.8 {d0-d2}, [r0] *)
    `decode (word 0xf42f070f)`;                (* vld1.8 {d0}, [pc] *)
    `decode (word 0xec900b00)`;                (* vldmia r0, {} *)
    `decode (word 0xec900b03)`;                (* fldmiax r0, {d0} *)
    `decode (word 0xec900b22)`;                (* vldmia r0, {d0-d16} *)
    `decode (word 0xecd0eb08)`;                (* vldmia r0, {d30-d33} *)
    `decode (word 0xedb00b04)`;                (* P = U = W = 1 *)
    `decode (word 0xed9f0b02)`;                (* vldr d0, [pc, #8] *)
    `decode (word 0xeea0fb90)`];;              (* vdup.32 q8, pc *)

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
