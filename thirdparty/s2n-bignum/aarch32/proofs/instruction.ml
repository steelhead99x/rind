(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Partial AArch32 state and A32 instruction semantics.                      *)
(* ========================================================================= *)

(* Instruction behavior follows the Arm Architecture Reference Manual for
   A-profile architecture (DDI 0487), part F, "The AArch32 Instruction Sets",
   whose A32 encodings are those of the ARMv7-A manual (DDI 0406). The
   semantics transcribe the manual's pseudocode: `ConditionHolds`,
   `Shift_C`, `A32ExpandImm_C`, and `AddWithCarry`, and each instruction's
   "Operation".

   https://developer.arm.com/documentation/ddi0487/latest
   https://developer.arm.com/documentation/ddi0406/latest

   The state is the A32 instruction set's, at user level: R0-R12, SP, LR,
   the program counter with the T bit, the NZCV flags, the Advanced SIMD
   registers Q0-Q15, and flat 32-bit memory. It omits T32's instructions,
   the GE and Q flags, VFP's S registers, FPSCR, banked registers,
   exceptions, and the system registers. The Advanced SIMD and
   crypto-extension instructions follow DDI 0406's chapter A7 and DDI 0487's
   F6 pseudocode.

   A branch to a register's or a loaded word's value interworks, as
   `BXWritePC` says: bit 0 of the target is the T bit, which selects T32 at
   the target with that bit cleared, and a target with bit 1 set alone is
   UNPREDICTABLE. PC holds the T bit as its bit 0, as LR and BX's operand
   do, so BX and a load into PC step to an aligned target or to one with
   bit 0 set (`aarch32_bx_target`), and allow every next state otherwise,
   as s2n-bignum's models do an instruction whose side condition fails: a
   proof that reaches one proves nothing. The fetch takes only an aligned
   PC, so a state in T32 steps nowhere: a proof ends there, as a
   subroutine's return to a T32 caller does, which is all a T32 caller
   needs of A32 code.

   Unaligned word loads and stores are architectural on ARMv7 and later when
   SCTLR.A is clear, as Linux and Android leave it at user level, so LDR and
   STR here access any address. LDRD, STRD, LDM, and STM fault on an address
   that is not word-aligned whatever SCTLR.A holds, and a load into PC from
   one is UNPREDICTABLE, so those take only an aligned address, and allow
   every next state otherwise, as an unaligned branch target does. A transfer
   whose bytes would run past 0xffffffff is UNPREDICTABLE too, so one leaves
   the model the same way.

   Every instruction records the same list of events whatever its inputs,
   as s2n-bignum's safety proofs need (common/safety.ml). A32 predicates
   nearly every instruction, so one whose condition fails records what it
   would have: a branch its jump to the next instruction, and a load or store
   an access of no bytes at the address it would have used, which the bounds
   check accepts of any list of ranges that is not empty. So the condition
   shows in an access's length and in a branch's target, a load into PC's
   in both.
   Such an instruction does not fault, as the hardware transfers nothing,
   but one whose bytes would run past 0xffffffff leaves the model as if it
   ran: allowing any state there is sound whatever the hardware does. *)

new_type_abbrev
 ("aarch32_uarch_event",`:32 address_uarch_event`);;

let aarch32state_INDUCT,aarch32state_RECURSION,aarch32state_COMPONENTS =
  define_auto_record_type
   "aarch32state =
     { PC: int32;                       // address of the next instruction
       registers: 4 word -> int32;      // R0-R14; R15 is PC
       flags: 4 word;                   // NZCV
       simdregisters: 4 word -> int128; // Q0-Q15, which D0-D31 halve
       memory: int32 -> byte;           // memory
       events: aarch32_uarch_event list // observable events
     }";;

loadt "common/code_loading.ml";;

let ALIGNED_BYTES_LOADED_APPEND_CLAUSE = prove
 (`aligned_bytes_loaded s (word pc) (APPEND prog data) /\
   read PC s = pcin /\
   rest <=>
   aligned_bytes_loaded s (word pc) prog /\
   read PC s = pcin /\
   bytes_loaded s (word(pc + LENGTH prog)) data /\
   rest`,
  REWRITE_TAC[aligned_bytes_loaded_append_alt; GSYM WORD_ADD; CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Flags, numbered as in the APSR's bits 31 to 28.                           *)
(* ------------------------------------------------------------------------- *)

let NF = define `NF = flags :> bitelement 3`;;

let ZF = define `ZF = flags :> bitelement 2`;;

let CF = define `CF = flags :> bitelement 1`;;

let VF = define `VF = flags :> bitelement 0`;;

add_component_alias_thms [NF; ZF; CF; VF];;

(* ------------------------------------------------------------------------- *)
(* Core registers. R15 is PC, which only branches, loads into PC, and the   *)
(* fetch write.                                                              *)
(* ------------------------------------------------------------------------- *)

let RREG = define
 `RREG n = registers :> element (word n)`;;

add_component_alias_thms
 (map (fun n -> let tm = mk_comb(`RREG`,mk_small_numeral n) in
                (GEN_REWRITE_CONV I [RREG] THENC NUM_REDUCE_CONV) tm)
      (0--14));;

let R0  = define `R0  = RREG 0`
and R1  = define `R1  = RREG 1`
and R2  = define `R2  = RREG 2`
and R3  = define `R3  = RREG 3`
and R4  = define `R4  = RREG 4`
and R5  = define `R5  = RREG 5`
and R6  = define `R6  = RREG 6`
and R7  = define `R7  = RREG 7`
and R8  = define `R8  = RREG 8`
and R9  = define `R9  = RREG 9`
and R10 = define `R10 = RREG 10`
and R11 = define `R11 = RREG 11`
and R12 = define `R12 = RREG 12`
and SP  = define `SP  = RREG 13`
and LR  = define `LR  = RREG 14`;;

add_component_alias_thms
 [R0; R1; R2; R3; R4; R5; R6; R7; R8; R9; R10; R11; R12; SP; LR];;

(* Map a four-bit register field other than 15 to its named component. *)

let aarch32_reg = define
 `aarch32_reg (n:4 word) =
    if n = word 0 then R0 else
    if n = word 1 then R1 else
    if n = word 2 then R2 else
    if n = word 3 then R3 else
    if n = word 4 then R4 else
    if n = word 5 then R5 else
    if n = word 6 then R6 else
    if n = word 7 then R7 else
    if n = word 8 then R8 else
    if n = word 9 then R9 else
    if n = word 10 then R10 else
    if n = word 11 then R11 else
    if n = word 12 then R12 else
    if n = word 13 then SP else LR`;;

(* R15 as an operand: the instruction's address plus 8. PC already holds the
   address plus 4 when the semantics run. The manual aligns the value to
   four bytes for ADR and literal loads, which changes nothing here: the
   fetch takes only an aligned PC. *)

let aarch32_R15 = define
 `aarch32_R15:(aarch32state,int32)component =
    component((\s. word_add (read PC s) (word 4)),(\y s. s))`;;

(* A four-bit register field that may name R15 as an operand. *)

let aarch32_src = define
 `aarch32_src (n:4 word) =
    if n = word 15 then aarch32_R15 else aarch32_reg n`;;

(* ------------------------------------------------------------------------- *)
(* The Advanced SIMD registers: Q0-Q15, whose halves are D0-D31, D(2k) the  *)
(* low half of Qk and D(2k+1) the high. A32 writes a D register and leaves   *)
(* its pair, so the step conversion turns each D read and write into one of  *)
(* Q's, and a state holds only Q registers.                                  *)
(* ------------------------------------------------------------------------- *)

let QREG = define
 `QREG n = simdregisters :> element (word n)`;;

add_component_alias_thms
 (map (fun n -> let tm = mk_comb(`QREG`,mk_small_numeral n) in
                (GEN_REWRITE_CONV I [QREG] THENC NUM_REDUCE_CONV) tm)
      (0--15));;

let Q0  = define `Q0  = QREG 0`
and Q1  = define `Q1  = QREG 1`
and Q2  = define `Q2  = QREG 2`
and Q3  = define `Q3  = QREG 3`
and Q4  = define `Q4  = QREG 4`
and Q5  = define `Q5  = QREG 5`
and Q6  = define `Q6  = QREG 6`
and Q7  = define `Q7  = QREG 7`
and Q8  = define `Q8  = QREG 8`
and Q9  = define `Q9  = QREG 9`
and Q10 = define `Q10 = QREG 10`
and Q11 = define `Q11 = QREG 11`
and Q12 = define `Q12 = QREG 12`
and Q13 = define `Q13 = QREG 13`
and Q14 = define `Q14 = QREG 14`
and Q15 = define `Q15 = QREG 15`;;

add_component_alias_thms
 [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15];;

(* D0-D31, as `D5 = Q2 :> top_64`. *)

let AARCH32_DREGS =
  map (fun n ->
         define (parse_term (Printf.sprintf "D%d = Q%d :> %s" n (n / 2)
                   (if n mod 2 = 0 then "bottom_64" else "top_64"))))
      (0--31);;

(* What a read and a write of a half are in terms of the whole. *)

let AARCH32_HALF_READS = prove
 (`(!(c:(A,int128)component) s.
      read (c :> bottom_64) s = word_subword (read c s) (0,64)) /\
   (!(c:(A,int128)component) s.
      read (c :> top_64) s = word_subword (read c s) (64,64))`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bottom_64; top_64; bottomhalf; tophalf;
              DIMINDEX_64; READ_SUBWORD]);;

let AARCH32_HALF_WRITES = prove
 (`(!(c:(A,int128)component) (y:int64) s.
      write (c :> bottom_64) y s =
      write c (word_join (word_subword (read c s) (64,64):int64) y) s) /\
   (!(c:(A,int128)component) (y:int64) s.
      write (c :> top_64) y s =
      write c (word_join y (word_subword (read c s) (0,64):int64)) s)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; bottom_64; top_64; bottomhalf;
              tophalf; DIMINDEX_64; through; write] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC (`read (c:(A,int128)component) s:int128`,`d:int128`) THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[WRITE_SUBWORD_BITWISE; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Conditions: the pseudocode's ConditionHolds.                              *)
(* ------------------------------------------------------------------------- *)

let aarch32_condition = define
 `aarch32_condition (cond:4 word) s <=>
    let base =
      if word_subword cond (1,3) = (word 0:3 word) then read ZF s else
      if word_subword cond (1,3) = (word 1:3 word) then read CF s else
      if word_subword cond (1,3) = (word 2:3 word) then read NF s else
      if word_subword cond (1,3) = (word 3:3 word) then read VF s else
      if word_subword cond (1,3) = (word 4:3 word)
      then read CF s /\ ~read ZF s else
      if word_subword cond (1,3) = (word 5:3 word)
      then (read NF s <=> read VF s) else
      if word_subword cond (1,3) = (word 6:3 word)
      then (read NF s <=> read VF s) /\ ~read ZF s
      else T in
    if bit 0 cond /\ ~(cond = word 15) then ~base else base`;;

(* One clause per condition, EQ to AL, for the step conversion. *)

let AARCH32_CONDITION_CLAUSES =
  let conv =
    REWRITE_CONV[aarch32_condition] THENC
    DEPTH_CONV WORD_RED_CONV THENC
    REWRITE_CONV[LET_DEF; LET_END_DEF] THENC
    TOP_DEPTH_CONV BETA_CONV THENC
    REWRITE_CONV[] in
  map (fun n ->
         GEN `s:aarch32state`
          (conv (mk_comb(mk_comb(`aarch32_condition`,
                   mk_comb(`word:num->4 word`,mk_small_numeral n)),
                 `s:aarch32state`))))
      (0--14);;

(* An instruction under a condition other than AL: a no-op when the
   condition fails. The step conversion decides the condition from the
   flags it knows, and fails when it cannot. Loads and stores take their
   condition themselves, as B does, since they record an access either
   way. *)

let aarch32_cond = define
 `aarch32_cond (cond:4 word) (i:aarch32state->aarch32state->bool) =
    \s. if aarch32_condition cond s then i s else (=) s`;;

(* A branch under such a condition: when the condition fails, it records the
   jump to the next instruction, as B does and as the other models'
   conditional branches do, so every branch leaves the same event shape. A
   load into PC takes its condition itself, as other loads do. *)

let aarch32_cond_branch = define
 `aarch32_cond_branch (cond:4 word) (i:aarch32state->aarch32state->bool) =
    \s. if aarch32_condition cond s then i s
        else (events := CONS (EventJump (word_sub (read PC s) (word 4),
                                         read PC s))
                             (read events s)) s`;;

(* ------------------------------------------------------------------------- *)
(* Shifted-register operands and their carry out: the pseudocode's Shift_C. *)
(* Each is a read-only component; the decoder picks the shift and amount,    *)
(* and gives the carry as a bit of the source register, as Shift_C does.     *)
(* A register-shifted register takes the amount from the low byte of `rs`:   *)
(* up to 255, and zero leaves both the value and the carry.                  *)
(* ------------------------------------------------------------------------- *)

let aarch32_LSL = define
 `aarch32_LSL (r:(aarch32state,int32)component) n =
    component((\s. word_shl (read r s) n),(\y s. s))`;;

let aarch32_LSR = define
 `aarch32_LSR (r:(aarch32state,int32)component) n =
    component((\s. word_ushr (read r s) n),(\y s. s))`;;

let aarch32_ASR = define
 `aarch32_ASR (r:(aarch32state,int32)component) n =
    component((\s. word_ishr (read r s) n),(\y s. s))`;;

let aarch32_ROR = define
 `aarch32_ROR (r:(aarch32state,int32)component) n =
    component((\s. word_ror (read r s) n),(\y s. s))`;;

let aarch32_RRX = define
 `aarch32_RRX (r:(aarch32state,int32)component) =
    component((\s. word_or (word_ushr (read r s) 1)
                           (word_shl (word(bitval(read CF s))) 31)),
              (\y s. s))`;;

let aarch32_BIT = define
 `aarch32_BIT (r:(aarch32state,int32)component) i =
    component((\s. bit i (read r s)),(\y s. s))`;;

let aarch32_NEG = define
 `aarch32_NEG (r:(aarch32state,int32)component) =
    component((\s. word_neg (read r s)),(\y s. s))`;;

let aarch32_LSL_R = define
 `aarch32_LSL_R (r:(aarch32state,int32)component)
                (rs:(aarch32state,int32)component) =
    component((\s. word_shl (read r s) (val(read rs s) MOD 256)),(\y s. s))`;;

let aarch32_LSR_R = define
 `aarch32_LSR_R (r:(aarch32state,int32)component)
                (rs:(aarch32state,int32)component) =
    component((\s. word_ushr (read r s) (val(read rs s) MOD 256)),(\y s. s))`;;

let aarch32_ASR_R = define
 `aarch32_ASR_R (r:(aarch32state,int32)component)
                (rs:(aarch32state,int32)component) =
    component((\s. word_ishr (read r s) (val(read rs s) MOD 256)),(\y s. s))`;;

let aarch32_ROR_R = define
 `aarch32_ROR_R (r:(aarch32state,int32)component)
                (rs:(aarch32state,int32)component) =
    component((\s. word_ror (read r s) (val(read rs s) MOD 256)),(\y s. s))`;;

(* Their carries out: the last bit shifted out, which past 32 places is zero
   for the logical shifts and the sign for ASR. *)

let aarch32_LSL_RC = define
 `aarch32_LSL_RC (r:(aarch32state,int32)component)
                 (rs:(aarch32state,int32)component) =
    component((\s. if val(read rs s) MOD 256 = 0 then read CF s
                   else val(read rs s) MOD 256 <= 32 /\
                        bit (32 - val(read rs s) MOD 256) (read r s)),
              (\y s. s))`;;

let aarch32_LSR_RC = define
 `aarch32_LSR_RC (r:(aarch32state,int32)component)
                 (rs:(aarch32state,int32)component) =
    component((\s. if val(read rs s) MOD 256 = 0 then read CF s
                   else bit (val(read rs s) MOD 256 - 1) (read r s)),
              (\y s. s))`;;

let aarch32_ASR_RC = define
 `aarch32_ASR_RC (r:(aarch32state,int32)component)
                 (rs:(aarch32state,int32)component) =
    component((\s. if val(read rs s) MOD 256 = 0 then read CF s
                   else bit (MIN (val(read rs s) MOD 256 - 1) 31) (read r s)),
              (\y s. s))`;;

let aarch32_ROR_RC = define
 `aarch32_ROR_RC (r:(aarch32state,int32)component)
                 (rs:(aarch32state,int32)component) =
    component((\s. if val(read rs s) MOD 256 = 0 then read CF s
                   else bit ((val(read rs s) MOD 256 - 1) MOD 32) (read r s)),
              (\y s. s))`;;

let AARCH32_OPERAND_READS = prove
 (`(!s. read aarch32_R15 s = word_add (read PC s) (word 4)) /\
   (!r n s. read (aarch32_LSL r n) s = word_shl (read r s) n) /\
   (!r n s. read (aarch32_LSR r n) s = word_ushr (read r s) n) /\
   (!r n s. read (aarch32_ASR r n) s = word_ishr (read r s) n) /\
   (!r n s. read (aarch32_ROR r n) s = word_ror (read r s) n) /\
   (!r s. read (aarch32_RRX r) s =
          word_or (word_ushr (read r s) 1)
                  (word_shl (word(bitval(read CF s))) 31)) /\
   (!r i s. read (aarch32_BIT r i) s = bit i (read r s)) /\
   (!r s. read (aarch32_NEG r) s = word_neg (read r s)) /\
   (!r rs s. read (aarch32_LSL_R r rs) s =
             word_shl (read r s) (val(read rs s) MOD 256)) /\
   (!r rs s. read (aarch32_LSR_R r rs) s =
             word_ushr (read r s) (val(read rs s) MOD 256)) /\
   (!r rs s. read (aarch32_ASR_R r rs) s =
             word_ishr (read r s) (val(read rs s) MOD 256)) /\
   (!r rs s. read (aarch32_ROR_R r rs) s =
             word_ror (read r s) (val(read rs s) MOD 256)) /\
   (!r rs s. read (aarch32_LSL_RC r rs) s <=>
             if val(read rs s) MOD 256 = 0 then read CF s
             else val(read rs s) MOD 256 <= 32 /\
                  bit (32 - val(read rs s) MOD 256) (read r s)) /\
   (!r rs s. read (aarch32_LSR_RC r rs) s <=>
             if val(read rs s) MOD 256 = 0 then read CF s
             else bit (val(read rs s) MOD 256 - 1) (read r s)) /\
   (!r rs s. read (aarch32_ASR_RC r rs) s <=>
             if val(read rs s) MOD 256 = 0 then read CF s
             else bit (MIN (val(read rs s) MOD 256 - 1) 31) (read r s)) /\
   (!r rs s. read (aarch32_ROR_RC r rs) s <=>
             if val(read rs s) MOD 256 = 0 then read CF s
             else bit ((val(read rs s) MOD 256 - 1) MOD 32) (read r s))`,
  REWRITE_TAC[aarch32_R15; aarch32_LSL; aarch32_LSR; aarch32_ASR;
              aarch32_ROR; aarch32_RRX; aarch32_BIT; aarch32_NEG;
              aarch32_LSL_R; aarch32_LSR_R; aarch32_ASR_R; aarch32_ROR_R;
              aarch32_LSL_RC; aarch32_LSR_RC; aarch32_ASR_RC; aarch32_ROR_RC;
              read]);;

(* ------------------------------------------------------------------------- *)
(* Data processing. `Rm` is the shifted register or immediate operand, and  *)
(* `Rc` the shifter's carry out, which the logical operations' S forms put   *)
(* in C. The arithmetic flags are AddWithCarry's, written as for AArch64.    *)
(* ------------------------------------------------------------------------- *)

let aarch32_AND = define
 `aarch32_AND Rd Rn Rm =
    \s:aarch32state.
        let d:int32 = word_and (read Rn s) (read Rm s) in
        (Rd := d) s`;;

let aarch32_ANDS = define
 `aarch32_ANDS Rd Rn Rm Rc =
    \s:aarch32state.
        let d:int32 = word_and (read Rn s) (read Rm s)
        and c = read Rc s in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := c) s`;;

let aarch32_EOR = define
 `aarch32_EOR Rd Rn Rm =
    \s:aarch32state.
        let d:int32 = word_xor (read Rn s) (read Rm s) in
        (Rd := d) s`;;

let aarch32_EORS = define
 `aarch32_EORS Rd Rn Rm Rc =
    \s:aarch32state.
        let d:int32 = word_xor (read Rn s) (read Rm s)
        and c = read Rc s in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := c) s`;;

let aarch32_ORR = define
 `aarch32_ORR Rd Rn Rm =
    \s:aarch32state.
        let d:int32 = word_or (read Rn s) (read Rm s) in
        (Rd := d) s`;;

let aarch32_ORRS = define
 `aarch32_ORRS Rd Rn Rm Rc =
    \s:aarch32state.
        let d:int32 = word_or (read Rn s) (read Rm s)
        and c = read Rc s in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := c) s`;;

let aarch32_BIC = define
 `aarch32_BIC Rd Rn Rm =
    \s:aarch32state.
        let d:int32 = word_and (read Rn s) (word_not(read Rm s)) in
        (Rd := d) s`;;

let aarch32_BICS = define
 `aarch32_BICS Rd Rn Rm Rc =
    \s:aarch32state.
        let d:int32 = word_and (read Rn s) (word_not(read Rm s))
        and c = read Rc s in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := c) s`;;

let aarch32_MOV = define
 `aarch32_MOV Rd Rm =
    \s:aarch32state.
        let d:int32 = read Rm s in
        (Rd := d) s`;;

let aarch32_MOVS = define
 `aarch32_MOVS Rd Rm Rc =
    \s:aarch32state.
        let d:int32 = read Rm s
        and c = read Rc s in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := c) s`;;

let aarch32_MVN = define
 `aarch32_MVN Rd Rm =
    \s:aarch32state.
        let d:int32 = word_not(read Rm s) in
        (Rd := d) s`;;

let aarch32_MVNS = define
 `aarch32_MVNS Rd Rm Rc =
    \s:aarch32state.
        let d:int32 = word_not(read Rm s)
        and c = read Rc s in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := c) s`;;

let aarch32_TST = define
 `aarch32_TST Rn Rm Rc =
    \s:aarch32state.
        let d:int32 = word_and (read Rn s) (read Rm s)
        and c = read Rc s in
        (NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := c) s`;;

let aarch32_TEQ = define
 `aarch32_TEQ Rn Rm Rc =
    \s:aarch32state.
        let d:int32 = word_xor (read Rn s) (read Rm s)
        and c = read Rc s in
        (NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := c) s`;;

let aarch32_ADD = define
 `aarch32_ADD Rd Rn Rm =
    \s:aarch32state.
        let d:int32 = word_add (read Rn s) (read Rm s) in
        (Rd := d) s`;;

let aarch32_ADDS = define
 `aarch32_ADDS Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s in
        let d:int32 = word_add n m in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := ~(val n + val m = val d) ,,
         VF := ~(ival n + ival m = ival d)) s`;;

let aarch32_CMN = define
 `aarch32_CMN Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s in
        let d:int32 = word_add n m in
        (NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := ~(val n + val m = val d) ,,
         VF := ~(ival n + ival m = ival d)) s`;;

let aarch32_ADC = define
 `aarch32_ADC Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s
        and c = bitval(read CF s) in
        let d:int32 = word_add (word_add n m) (word c) in
        (Rd := d) s`;;

let aarch32_ADCS = define
 `aarch32_ADCS Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s
        and c = bitval(read CF s) in
        let d:int32 = word_add (word_add n m) (word c) in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := ~(val n + val m + c = val d) ,,
         VF := ~(ival n + ival m + &c = ival d)) s`;;

let aarch32_SUB = define
 `aarch32_SUB Rd Rn Rm =
    \s:aarch32state.
        let d:int32 = word_sub (read Rn s) (read Rm s) in
        (Rd := d) s`;;

let aarch32_SUBS = define
 `aarch32_SUBS Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s in
        let d:int32 = word_sub n m in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (&(val n) - &(val m):int = &(val d)) ,,
         VF := ~(ival n - ival m = ival d)) s`;;

let aarch32_CMP = define
 `aarch32_CMP Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s in
        let d:int32 = word_sub n m in
        (NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (&(val n) - &(val m):int = &(val d)) ,,
         VF := ~(ival n - ival m = ival d)) s`;;

let aarch32_RSB = define
 `aarch32_RSB Rd Rn Rm =
    \s:aarch32state.
        let d:int32 = word_sub (read Rm s) (read Rn s) in
        (Rd := d) s`;;

let aarch32_RSBS = define
 `aarch32_RSBS Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s in
        let d:int32 = word_sub m n in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (&(val m) - &(val n):int = &(val d)) ,,
         VF := ~(ival m - ival n = ival d)) s`;;

let aarch32_SBC = define
 `aarch32_SBC Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s
        and c = bitval(~read CF s) in
        let d:int32 = word_sub n (word_add m (word c)) in
        (Rd := d) s`;;

let aarch32_SBCS = define
 `aarch32_SBCS Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s
        and c = bitval(~read CF s) in
        let d:int32 = word_sub n (word_add m (word c)) in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (&(val n) - (&(val m) + &c):int = &(val d)) ,,
         VF := ~(ival n - (ival m + &c) = ival d)) s`;;

let aarch32_RSC = define
 `aarch32_RSC Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s
        and c = bitval(~read CF s) in
        let d:int32 = word_sub m (word_add n (word c)) in
        (Rd := d) s`;;

let aarch32_RSCS = define
 `aarch32_RSCS Rd Rn Rm =
    \s:aarch32state.
        let n = read Rn s
        and m = read Rm s
        and c = bitval(~read CF s) in
        let d:int32 = word_sub m (word_add n (word c)) in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (&(val m) - (&(val n) + &c):int = &(val d)) ,,
         VF := ~(ival m - (ival n + &c) = ival d)) s`;;

(* MOVW writes a 16-bit immediate; MOVT replaces the top half. *)

let aarch32_MOVW = define
 `aarch32_MOVW Rd (imm:16 word) =
    \s:aarch32state.
        let d:int32 = word_zx imm in
        (Rd := d) s`;;

let aarch32_MOVT = define
 `aarch32_MOVT Rd (imm:16 word) =
    \s:aarch32state.
        let d:int32 = word_join imm (word_subword (read Rd s) (0,16):16 word) in
        (Rd := d) s`;;

(* MUL keeps the product's low word; UMULL writes the whole 64-bit product
   of two words, and UMLAL adds it to the 64-bit value already in RdHi:RdLo.
   None sets flags: the decoder refuses their S forms. *)

let aarch32_MUL = define
 `aarch32_MUL Rd Rn Rm =
    \s:aarch32state.
        let d:int32 = word_mul (read Rn s) (read Rm s) in
        (Rd := d) s`;;

let aarch32_UMULL = define
 `aarch32_UMULL RdLo RdHi Rn Rm =
    \s:aarch32state.
        let p = val(read Rn s:int32) * val(read Rm s:int32) in
        (RdLo := (word p:int32) ,,
         RdHi := (word(p DIV 2 EXP 32):int32)) s`;;

let aarch32_UMLAL = define
 `aarch32_UMLAL RdLo RdHi Rn Rm =
    \s:aarch32state.
        let p = val(read Rn s:int32) * val(read Rm s:int32) +
                (2 EXP 32 * val(read RdHi s:int32) + val(read RdLo s:int32)) in
        (RdLo := (word p:int32) ,,
         RdHi := (word(p DIV 2 EXP 32):int32)) s`;;

let aarch32_REV = define
 `aarch32_REV Rd Rm =
    \s:aarch32state.
        let d:int32 = word_bytereverse (read Rm s) in
        (Rd := d) s`;;

(* NOP, and DMB, which orders memory accesses and changes no state here. *)

let aarch32_NOP = define
 `aarch32_NOP = \s:aarch32state. (=) s`;;

let aarch32_DMB = define
 `aarch32_DMB = \s:aarch32state. (=) s`;;

(* ------------------------------------------------------------------------- *)
(* Branches. `off` is the target's offset from the branch's own address: the *)
(* decoder folds in A32's PC bias of 8. PC already holds the branch's        *)
(* address plus 4 when the semantics run, which is what BL leaves in LR.     *)
(* ------------------------------------------------------------------------- *)

let aarch32_B = define
 `aarch32_B (cond:4 word) (off:int32) =
    \s:aarch32state.
        let pc = word_sub (read PC s) (word 4) in
        let pc_next = if aarch32_condition cond s
                      then word_add pc off
                      else read PC s in
        (PC := pc_next ,,
         events := CONS (EventJump (pc,pc_next)) (read events s)) s`;;

let aarch32_BL = define
 `aarch32_BL (off:int32) =
    \s:aarch32state.
        let pc_incr = read PC s in
        let pc = word_sub pc_incr (word 4) in
        let pc_next = word_add pc off in
        (LR := pc_incr ,,
         PC := pc_next ,,
         events := CONS (EventJump (pc,pc_next)) (read events s)) s`;;

(* Where BX and a load into PC may go: an A32 address, aligned to four
   bytes, or a T32 one, whose bit 0 is the T bit. *)

let aarch32_bx_target = define
 `aarch32_bx_target (a:int32) <=> aligned 4 a \/ bit 0 a`;;

let aarch32_BX = define
 `aarch32_BX Rm =
    \s:aarch32state.
        let pc = word_sub (read PC s) (word 4) in
        let pc_next:int32 = read Rm s in
        (if aarch32_bx_target pc_next then
           PC := pc_next ,,
           events := CONS (EventJump (pc,pc_next)) (read events s)
         else ASSIGNS entirety) s`;;

(* ------------------------------------------------------------------------- *)
(* Loads and stores. Each takes its condition, and when it fails records    *)
(* an access of no bytes at the address it would have used, and a load into *)
(* PC its jump to the next instruction too, and changes nothing else. A word *)
(* or more that would run past 0xffffffff leaves the model either way.      *)
(* ------------------------------------------------------------------------- *)

(* Whether `len` bytes from `addr` stay below 2^32: a transfer that would run
   past 0xffffffff is UNPREDICTABLE. The step conversion decides it from
   `aligned 4` for four bytes or fewer, from the values the assumptions give
   the address's terms, or from an assumption that a region holding the
   bytes stays below 2^32. *)

let aarch32_nowrap = define
 `aarch32_nowrap (addr:int32) len <=> val addr + len <= 2 EXP 32`;;

(* Word and byte. `Rm` is the offset operand, an immediate or a shifted
   register, negated when the instruction subtracts it; `indexed` whether the
   access uses the offset address, and `wback` whether Rn takes it: offset,
   pre-indexed, and post-indexed forms. Rn is R15 for a literal load. A byte
   cannot run past 0xffffffff. *)

let aarch32_LDR = define
 `aarch32_LDR (cond:4 word) Rt Rn Rm indexed wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        let offset_addr = word_add base (read Rm s) in
        let addr = if indexed then offset_addr else base in
        (if aarch32_nowrap addr 4 then
           if aarch32_condition cond s then
             Rt := read (memory :> bytes32 addr) s ,,
             events := CONS (EventLoad (addr,4)) (read events s) ,,
             (if wback then Rn := offset_addr else (=))
           else events := CONS (EventLoad (addr,0)) (read events s)
         else ASSIGNS entirety) s`;;

let aarch32_LDRB = define
 `aarch32_LDRB (cond:4 word) Rt Rn Rm indexed wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        let offset_addr = word_add base (read Rm s) in
        let addr = if indexed then offset_addr else base in
        (if aarch32_condition cond s then
           Rt := word_zx (read (memory :> bytes8 addr) s) ,,
           events := CONS (EventLoad (addr,1)) (read events s) ,,
           (if wback then Rn := offset_addr else (=))
         else events := CONS (EventLoad (addr,0)) (read events s)) s`;;

let aarch32_STR = define
 `aarch32_STR (cond:4 word) Rt Rn Rm indexed wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        let offset_addr = word_add base (read Rm s) in
        let addr = if indexed then offset_addr else base in
        (if aarch32_nowrap addr 4 then
           if aarch32_condition cond s then
             memory :> bytes32 addr := read Rt s ,,
             events := CONS (EventStore (addr,4)) (read events s) ,,
             (if wback then Rn := offset_addr else (=))
           else events := CONS (EventStore (addr,0)) (read events s)
         else ASSIGNS entirety) s`;;

let aarch32_STRB = define
 `aarch32_STRB (cond:4 word) Rt Rn Rm indexed wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        let offset_addr = word_add base (read Rm s) in
        let addr = if indexed then offset_addr else base in
        (if aarch32_condition cond s then
           memory :> bytes8 addr := word_zx (read Rt s) ,,
           events := CONS (EventStore (addr,1)) (read events s) ,,
           (if wback then Rn := offset_addr else (=))
         else events := CONS (EventStore (addr,0)) (read events s)) s`;;

(* LDR into PC: a branch to the loaded word, from an aligned address. *)

let aarch32_LDR_PC = define
 `aarch32_LDR_PC (cond:4 word) Rn Rm indexed wback =
    \s:aarch32state.
        let pc = word_sub (read PC s) (word 4) in
        let base:int32 = read Rn s in
        let offset_addr = word_add base (read Rm s) in
        let addr = if indexed then offset_addr else base in
        let pc_next:int32 = read (memory :> bytes32 addr) s in
        (if aarch32_nowrap addr 4 then
           if aarch32_condition cond s then
             if aligned 4 addr /\ aarch32_bx_target pc_next then
               PC := pc_next ,,
               events := CONS (EventJump (pc,pc_next))
                              (CONS (EventLoad (addr,4)) (read events s)) ,,
               (if wback then Rn := offset_addr else (=))
             else ASSIGNS entirety
           else events := CONS (EventJump (pc,read PC s))
                               (CONS (EventLoad (addr,0)) (read events s))
         else ASSIGNS entirety) s`;;

(* LDRD and STRD: two words, Rt at the address and Rt2 four bytes on. *)

let aarch32_LDRD = define
 `aarch32_LDRD (cond:4 word) Rt Rt2 Rn Rm indexed wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        let offset_addr = word_add base (read Rm s) in
        let addr = if indexed then offset_addr else base in
        (if aarch32_nowrap addr 8 then
           if aarch32_condition cond s then
             if aligned 4 addr then
               Rt := read (memory :> bytes32 addr) s ,,
               Rt2 := read (memory :> bytes32 (word_add addr (word 4))) s ,,
               events := CONS (EventLoad (addr,8)) (read events s) ,,
               (if wback then Rn := offset_addr else (=))
             else ASSIGNS entirety
           else events := CONS (EventLoad (addr,0)) (read events s)
         else ASSIGNS entirety) s`;;

let aarch32_STRD = define
 `aarch32_STRD (cond:4 word) Rt Rt2 Rn Rm indexed wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        let offset_addr = word_add base (read Rm s) in
        let addr = if indexed then offset_addr else base in
        (if aarch32_nowrap addr 8 then
           if aarch32_condition cond s then
             if aligned 4 addr then
               memory :> bytes32 addr := read Rt s ,,
               memory :> bytes32 (word_add addr (word 4)) := read Rt2 s ,,
               events := CONS (EventStore (addr,8)) (read events s) ,,
               (if wback then Rn := offset_addr else (=))
             else ASSIGNS entirety
           else events := CONS (EventStore (addr,0)) (read events s)
         else ASSIGNS entirety) s`;;

(* ------------------------------------------------------------------------- *)
(* LDM and STM, PUSH and POP among them. `regs` is the registers in          *)
(* ascending order, which take ascending addresses; `off` the lowest         *)
(* address's offset from Rn, `len` the bytes transferred, and `wb` what Rn   *)
(* gains when `wback`: the decoder works them out from the addressing mode.  *)
(* Every value is read from the state before the instruction, so a base      *)
(* register in the list loads and stores as the manual says. The addresses   *)
(* are aligned exactly when Rn is.                                           *)
(* ------------------------------------------------------------------------- *)

let aarch32_loads = define
 `(aarch32_loads [] (base:int32) (off:int32) (s:aarch32state)
                 (k:aarch32state->aarch32state->bool) = k) /\
  (aarch32_loads (CONS (r:(aarch32state,int32)component) rs) base off s k =
     (r := read (memory :> bytes32 (word_add base off)) s ,,
      aarch32_loads rs base (word_add off (word 4)) s k))`;;

let aarch32_stores = define
 `(aarch32_stores [] (base:int32) (off:int32) (s:aarch32state)
                  (k:aarch32state->aarch32state->bool) = k) /\
  (aarch32_stores (CONS (r:(aarch32state,int32)component) rs) base off s k =
     (memory :> bytes32 (word_add base off) := read r s ,,
      aarch32_stores rs base (word_add off (word 4)) s k))`;;

let aarch32_LDM = define
 `aarch32_LDM (cond:4 word) regs Rn (off:int32) len (wb:int32) wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        (if aarch32_nowrap (word_add base off) len then
           if aarch32_condition cond s then
             if aligned 4 base then
               aarch32_loads regs base off s
                (events := CONS (EventLoad (word_add base off,len))
                                (read events s) ,,
                 (if wback then Rn := word_add base wb else (=)))
             else ASSIGNS entirety
           else events := CONS (EventLoad (word_add base off,0))
                               (read events s)
         else ASSIGNS entirety) s`;;

let aarch32_STM = define
 `aarch32_STM (cond:4 word) regs Rn (off:int32) len (wb:int32) wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        (if aarch32_nowrap (word_add base off) len then
           if aarch32_condition cond s then
             if aligned 4 base then
               aarch32_stores regs base off s
                (events := CONS (EventStore (word_add base off,len))
                                (read events s) ,,
                 (if wback then Rn := word_add base wb else (=)))
             else ASSIGNS entirety
           else events := CONS (EventStore (word_add base off,0))
                               (read events s)
         else ASSIGNS entirety) s`;;

(* LDM with PC in the list: PC is the last word, at `pcoff` from Rn, and the
   instruction branches to it. *)

let aarch32_LDM_PC = define
 `aarch32_LDM_PC (cond:4 word) regs Rn (off:int32) (pcoff:int32) len
                 (wb:int32) wback =
    \s:aarch32state.
        let pc = word_sub (read PC s) (word 4) in
        let base:int32 = read Rn s in
        let pc_next:int32 = read (memory :> bytes32 (word_add base pcoff)) s in
        (if aarch32_nowrap (word_add base off) len then
           if aarch32_condition cond s then
             if aligned 4 base /\ aarch32_bx_target pc_next then
               aarch32_loads regs base off s
                (PC := pc_next ,,
                 events := CONS (EventJump (pc,pc_next))
                                (CONS (EventLoad (word_add base off,len))
                                      (read events s)) ,,
                 (if wback then Rn := word_add base wb else (=)))
             else ASSIGNS entirety
           else events := CONS (EventJump (pc,read PC s))
                               (CONS (EventLoad (word_add base off,0))
                                     (read events s))
         else ASSIGNS entirety) s`;;

(* ------------------------------------------------------------------------- *)
(* Advanced SIMD data processing. Each form applies a function to its        *)
(* operands' values, which the decoder builds from HOL Light's `simd` and    *)
(* `usimd` lane combinators and the lane operations below, any shift, index, *)
(* or count first, so that a decoded instruction holds no binder and its     *)
(* evaluation leaves numerals in place. An operation AArch64 shares, the AES *)
(* rounds, the SHA-256 steps, and polynomial multiplication, is s2n-bignum's *)
(* aarch64 model's. The instructions are unconditional but for those in the  *)
(* coprocessor space, VLDM, VSTM, VMOV to a lane, and VDUP from a core       *)
(* register, which the decoder guards as it does the integer ones.           *)
(* ------------------------------------------------------------------------- *)

let aarch32_VMOV = define
 `aarch32_VMOV (Vd:(aarch32state,N word)component) Vm =
    \s:aarch32state. (Vd := read Vm s) s`;;

let aarch32_VUNARY = define
 `aarch32_VUNARY (f:M word->N word) (Vd:(aarch32state,N word)component) Vm =
    \s:aarch32state. (Vd := f (read Vm s)) s`;;

let aarch32_VBINARY = define
 `aarch32_VBINARY (f:L word->M word->N word)
                  (Vd:(aarch32state,N word)component) Vn Vm =
    \s:aarch32state. (Vd := f (read Vn s) (read Vm s)) s`;;

(* An operation that reads its destination too: Vd := f Vd Vm. *)

let aarch32_VUPDATE = define
 `aarch32_VUPDATE (f:N word->M word->N word)
                  (Vd:(aarch32state,N word)component) Vm =
    \s:aarch32state. (Vd := f (read Vd s) (read Vm s)) s`;;

let aarch32_VTERNARY = define
 `aarch32_VTERNARY (f:N word->L word->M word->N word)
                   (Vd:(aarch32state,N word)component) Vn Vm =
    \s:aarch32state. (Vd := f (read Vd s) (read Vn s) (read Vm s)) s`;;

(* VSWP and VTRN write both registers from both old values, and VZIP the
   two halves of what `f` makes of them. The decoder refuses Vd = Vm. *)

let aarch32_VSWP = define
 `aarch32_VSWP (Vd:(aarch32state,N word)component) Vm =
    \s:aarch32state.
        let d = read Vd s and m = read Vm s in
        (Vd := m ,, Vm := d) s`;;

let aarch32_VTRN = define
 `aarch32_VTRN (f:N word->N word->N word) g
               (Vd:(aarch32state,N word)component) Vm =
    \s:aarch32state.
        let d = read Vd s and m = read Vm s in
        (Vd := f d m ,, Vm := g d m) s`;;

let aarch32_VZIP = define
 `aarch32_VZIP (f:N word->N word->(N tybit0)word)
               (Vd:(aarch32state,N word)component) Vm =
    \s:aarch32state.
        let z = f (read Vd s) (read Vm s) in
        (Vd := word_subword z (0,dimindex(:N)) ,,
         Vm := word_subword z (dimindex(:N),dimindex(:N))) s`;;

(* VTBL looks each byte of Dm up in a table of `len` D registers, up to four,
   the first in the low bytes, with `rvalue (word 0)` for the rest. *)

let aarch32_tbl = define
 `aarch32_tbl len (t:256 word) (x:byte) : byte =
    if val x < 8 * len then word_subword t (8 * val x,8) else word 0`;;

let aarch32_VTBL = define
 `aarch32_VTBL (Dd:(aarch32state,int64)component)
               (Dn1:(aarch32state,int64)component)
               (Dn2:(aarch32state,int64)component)
               (Dn3:(aarch32state,int64)component)
               (Dn4:(aarch32state,int64)component) len Dm =
    \s:aarch32state.
        let t:256 word =
          word_join (word_join (read Dn4 s) (read Dn3 s):int128)
                    (word_join (read Dn2 s) (read Dn1 s):int128) in
        (Dd := usimd8 (aarch32_tbl len t) (read Dm s)) s`;;

(* The lane operations. Shifts take their amount first; a right shift by the
   whole lane, which VSHR and VSRI encode, leaves zero or the sign. *)

let aarch32_shl = define
 `aarch32_shl n (x:N word) = word_shl x n`;;

let aarch32_ushr = define
 `aarch32_ushr n (x:N word) = word_ushr x n`;;

let aarch32_sshr = define
 `aarch32_sshr n (x:N word) = word_ishr x n`;;

(* VSLI keeps the destination's low n bits, VSRI its high n. *)

let aarch32_sli = define
 `aarch32_sli n (d:N word) (m:N word) =
    word_or (word_shl m n) (word_and d (word(2 EXP n - 1)))`;;

let aarch32_sri = define
 `aarch32_sri n (d:N word) (m:N word) =
    word_or (word_ushr m n)
            (word_and d (word_not(word(2 EXP (dimindex(:N) - n) - 1))))`;;

(* VSHRN keeps each lane's shifted low half, and VSHLL widens then shifts. *)

let aarch32_shrn = define
 `aarch32_shrn n (x:(N tybit0)word) : N word =
    word_subword (word_ushr x n) (0,dimindex(:N))`;;

let aarch32_ushll = define
 `aarch32_ushll n (x:N word) : (N tybit0)word = word_shl (word_zx x) n`;;

let aarch32_sshll = define
 `aarch32_sshll n (x:N word) : (N tybit0)word = word_shl (word_sx x) n`;;

(* VSHL by register: by the signed low byte of the other lane, rightward when
   it is negative. *)

let aarch32_ushl = define
 `aarch32_ushl (x:N word) (y:N word) =
    if bit 7 (word_subword y (0,8):byte)
    then word_ushr x (val(word_neg(word_subword y (0,8):byte)))
    else word_shl x (val(word_subword y (0,8):byte))`;;

let aarch32_sshl = define
 `aarch32_sshl (x:N word) (y:N word) =
    if bit 7 (word_subword y (0,8):byte)
    then word_ishr x (val(word_neg(word_subword y (0,8):byte)))
    else word_shl x (val(word_subword y (0,8):byte))`;;

let aarch32_bic = define
 `aarch32_bic (x:N word) y = word_and x (word_not y)`;;

let aarch32_bsl = define
 `aarch32_bsl (d:N word) n m =
    word_or (word_and n d) (word_and m (word_not d))`;;

let aarch32_tst = define
 `aarch32_tst (x:N word) y =
    if word_and x y = word 0 then word 0 else word_not(word 0)`;;

(* VEXT: the bytes from `k` on of Vm:Vn. *)

let aarch32_ext = define
 `aarch32_ext k (n:N word) (m:N word) : N word =
    word_subword (word_join m n:(N tybit0)word) (8 * k,dimindex(:N))`;;

(* VTRN's lane pairs, per container of two lanes, and VZIP's interleave. *)

let aarch32_trn1 = define
 `aarch32_trn1 (x:(N tybit0)word) (y:(N tybit0)word) : (N tybit0)word =
    word_join (word_subword y (0,dimindex(:N)):N word)
              (word_subword x (0,dimindex(:N)):N word)`;;

let aarch32_trn2 = define
 `aarch32_trn2 (x:(N tybit0)word) (y:(N tybit0)word) : (N tybit0)word =
    word_join (word_subword y (dimindex(:N),dimindex(:N)):N word)
              (word_subword x (dimindex(:N),dimindex(:N)):N word)`;;

let aarch32_pair = define
 `aarch32_pair (x:N word) (y:N word) : (N tybit0)word = word_join y x`;;

(* `simd2` for an operation whose lanes widen. *)

let aarch32_simd2 = define
 `aarch32_simd2 (f:N word->N word->M word) (x:(N tybit0)word)
                (y:(N tybit0)word) : (M tybit0)word =
    word_join (f (word_subword x (dimindex(:N),dimindex(:N)))
                 (word_subword y (dimindex(:N),dimindex(:N))))
              (f (word_subword x (0,dimindex(:N)))
                 (word_subword y (0,dimindex(:N))))`;;

let aarch32_simd4 = define
 `aarch32_simd4 (f:N word->N word->M word) = aarch32_simd2 (aarch32_simd2 f)`;;

let aarch32_simd8 = define
 `aarch32_simd8 (f:N word->N word->M word) = aarch32_simd2 (aarch32_simd4 f)`;;

let aarch32_simd16 = define
 `aarch32_simd16 (f:N word->N word->M word) = aarch32_simd2 (aarch32_simd8 f)`;;

(* Lane `x` of a scalar operand, everywhere; and VMOV's write of a core
   register's low `len` bits at `pos`. *)

let aarch32_dup8 = define
 `aarch32_dup8 x (m:M word) : N word =
    word_duplicate (word_subword m (8 * x,8):byte)`;;

let aarch32_dup16 = define
 `aarch32_dup16 x (m:M word) : N word =
    word_duplicate (word_subword m (16 * x,16):int16)`;;

let aarch32_dup32 = define
 `aarch32_dup32 x (m:M word) : N word =
    word_duplicate (word_subword m (32 * x,32):int32)`;;

let aarch32_ins = define
 `aarch32_ins pos len (d:N word) (r:M word) = word_insert d (pos,len) r`;;

(* The long multiplies, of 32-bit lanes, as AArch64's UMULL and SMULL; the
   polynomial ones of 8-bit lanes as its PMULL. *)

let aarch32_umull = define
 `aarch32_umull (n:int64) (m:int64) : int128 =
    simd2 word_mul (usimd2 word_zx n) (usimd2 word_zx m)`;;

let aarch32_smull = define
 `aarch32_smull (n:int64) (m:int64) : int128 =
    simd2 word_mul (usimd2 word_sx n) (usimd2 word_sx m)`;;

let aarch32_umlal = define
 `aarch32_umlal (d:int128) n m = simd2 word_add d (aarch32_umull n m)`;;

let aarch32_smlal = define
 `aarch32_smlal (d:int128) n m = simd2 word_add d (aarch32_smull n m)`;;

let aarch32_umull_lane = define
 `aarch32_umull_lane x n (m:int64) = aarch32_umull n (aarch32_dup32 x m)`;;

let aarch32_smull_lane = define
 `aarch32_smull_lane x n (m:int64) = aarch32_smull n (aarch32_dup32 x m)`;;

let aarch32_umlal_lane = define
 `aarch32_umlal_lane x d n (m:int64) = aarch32_umlal d n (aarch32_dup32 x m)`;;

let aarch32_smlal_lane = define
 `aarch32_smlal_lane x d n (m:int64) = aarch32_smlal d n (aarch32_dup32 x m)`;;

let aarch32_pmull8 = define
 `aarch32_pmull8 (n:int64) (m:int64) : int128 =
    simd8 (word_pmul:int16->int16->int16) (usimd8 word_zx n) (usimd8 word_zx m)`;;

(* What the step conversion unfolds a decoded operation with, before the
   widths' `dimindex` and the lanes' subwords reduce. A VTBL lane stays
   `aarch32_tbl` until its index is a numeral, since unfolding one with a
   variable index leaves a conditional per lane, and vpaes's lookups chain
   dozens of them. *)

let AARCH32_SIMD_EXPANSIONS =
  [usimd16; usimd8; usimd4; usimd2; simd16; simd8; simd4; simd2;
   aarch32_simd16; aarch32_simd8; aarch32_simd4; aarch32_simd2;
   aarch32_shl; aarch32_ushr; aarch32_sshr; aarch32_sli; aarch32_sri;
   aarch32_shrn; aarch32_ushll; aarch32_sshll; aarch32_ushl; aarch32_sshl;
   aarch32_bic; aarch32_bsl; aarch32_tst; aarch32_ext; aarch32_trn1;
   aarch32_trn2; aarch32_pair; aarch32_dup8; aarch32_dup16; aarch32_dup32;
   aarch32_ins; aarch32_umull_lane; aarch32_smull_lane; aarch32_umlal_lane;
   aarch32_smlal_lane; aarch32_umlal; aarch32_smlal; aarch32_umull;
   aarch32_smull; aarch32_pmull8];;

(* A VTBL lane whose index is a numeral, as the step's simplification and
   cosimulation meet it once the index register's value is known: the
   table's byte there, or zero. *)

let AARCH32_TBL_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("aarch32_tbl",_),_),_),
         Comb(Const("word",_),n)) when is_numeral n ->
      (GEN_REWRITE_CONV I [aarch32_tbl] THENC
       DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV THENC
       REWRITE_CONV[] THENC
       TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) tm
  | _ -> failwith "AARCH32_TBL_CONV";;

extra_word_CONV := AARCH32_TBL_CONV :: !extra_word_CONV;;

(* ------------------------------------------------------------------------- *)
(* Advanced SIMD loads and stores. A D register is the eight bytes at its    *)
(* address, little-endian whatever the element size; `regs` lists D          *)
(* registers in ascending order, which take ascending addresses. VLD1 and    *)
(* VST1 add `Rm`'s value to Rn when `wback`, the transfer's length for the   *)
(* `!` form, and need the address aligned to `align`, which is 1 without an  *)
(* alignment qualifier. VLDM, VSTM, VLDR, and VSTR take a condition, as LDM  *)
(* does, and a word-aligned base, as their word accesses fault otherwise.    *)
(* ------------------------------------------------------------------------- *)

let aarch32_vloads = define
 `(aarch32_vloads [] (base:int32) (off:int32) (s:aarch32state)
                  (k:aarch32state->aarch32state->bool) = k) /\
  (aarch32_vloads (CONS (r:(aarch32state,int64)component) rs) base off s k =
     (r := read (memory :> bytes64 (word_add base off)) s ,,
      aarch32_vloads rs base (word_add off (word 8)) s k))`;;

let aarch32_vstores = define
 `(aarch32_vstores [] (base:int32) (off:int32) (s:aarch32state)
                   (k:aarch32state->aarch32state->bool) = k) /\
  (aarch32_vstores (CONS (r:(aarch32state,int64)component) rs) base off s k =
     (memory :> bytes64 (word_add base off) := read r s ,,
      aarch32_vstores rs base (word_add off (word 8)) s k))`;;

let aarch32_vdups = define
 `(aarch32_vdups [] (v:int64) (k:aarch32state->aarch32state->bool) = k) /\
  (aarch32_vdups (CONS (r:(aarch32state,int64)component) rs) v k =
     (r := v ,, aarch32_vdups rs v k))`;;

let aarch32_VLD1 = define
 `aarch32_VLD1 regs Rn (Rm:(aarch32state,int32)component) len align wback =
    \s:aarch32state.
        let addr:int32 = read Rn s in
        (if aarch32_nowrap addr len then
           if aligned align addr then
             aarch32_vloads regs addr (word 0) s
              (events := CONS (EventLoad (addr,len)) (read events s) ,,
               (if wback then Rn := word_add addr (read Rm s) else (=)))
           else ASSIGNS entirety
         else ASSIGNS entirety) s`;;

let aarch32_VST1 = define
 `aarch32_VST1 regs Rn (Rm:(aarch32state,int32)component) len align wback =
    \s:aarch32state.
        let addr:int32 = read Rn s in
        (if aarch32_nowrap addr len then
           if aligned align addr then
             aarch32_vstores regs addr (word 0) s
              (events := CONS (EventStore (addr,len)) (read events s) ,,
               (if wback then Rn := word_add addr (read Rm s) else (=)))
           else ASSIGNS entirety
         else ASSIGNS entirety) s`;;

(* One lane, `esize` bits at bit `pos` of Dd, from or to the `len` bytes that
   `mem` names at the address, such as `bytes32`. *)

let aarch32_VLD1_LANE = define
 `aarch32_VLD1_LANE (Dd:(aarch32state,int64)component)
                    (mem:int32->(int32->byte,L word)component) pos esize len
                    Rn (Rm:(aarch32state,int32)component) align wback =
    \s:aarch32state.
        let addr:int32 = read Rn s in
        (if aarch32_nowrap addr len then
           if aligned align addr then
             Dd := word_insert (read Dd s) (pos,esize)
                     (read (memory :> mem addr) s) ,,
             events := CONS (EventLoad (addr,len)) (read events s) ,,
             (if wback then Rn := word_add addr (read Rm s) else (=))
           else ASSIGNS entirety
         else ASSIGNS entirety) s`;;

let aarch32_VST1_LANE = define
 `aarch32_VST1_LANE (Dd:(aarch32state,int64)component)
                    (mem:int32->(int32->byte,L word)component) pos esize len
                    Rn (Rm:(aarch32state,int32)component) align wback =
    \s:aarch32state.
        let addr:int32 = read Rn s in
        (if aarch32_nowrap addr len then
           if aligned align addr then
             memory :> mem addr := word_subword (read Dd s) (pos,esize) ,,
             events := CONS (EventStore (addr,len)) (read events s) ,,
             (if wback then Rn := word_add addr (read Rm s) else (=))
           else ASSIGNS entirety
         else ASSIGNS entirety) s`;;

(* One element into every lane of each register in `regs`. *)

let aarch32_VLD1_ALL = define
 `aarch32_VLD1_ALL regs (mem:int32->(int32->byte,L word)component) len
                   Rn (Rm:(aarch32state,int32)component) align wback =
    \s:aarch32state.
        let addr:int32 = read Rn s in
        (if aarch32_nowrap addr len then
           if aligned align addr then
             aarch32_vdups regs
              (word_duplicate (read (memory :> mem addr) s))
              (events := CONS (EventLoad (addr,len)) (read events s) ,,
               (if wback then Rn := word_add addr (read Rm s) else (=)))
           else ASSIGNS entirety
         else ASSIGNS entirety) s`;;

(* `off`, `len`, and `wb` as for LDM; VLDR is one register at an offset. *)

let aarch32_VLDM = define
 `aarch32_VLDM (cond:4 word) regs Rn (off:int32) len (wb:int32) wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        (if aarch32_nowrap (word_add base off) len then
           if aarch32_condition cond s then
             if aligned 4 base then
               aarch32_vloads regs base off s
                (events := CONS (EventLoad (word_add base off,len))
                                (read events s) ,,
                 (if wback then Rn := word_add base wb else (=)))
             else ASSIGNS entirety
           else events := CONS (EventLoad (word_add base off,0))
                               (read events s)
         else ASSIGNS entirety) s`;;

let aarch32_VSTM = define
 `aarch32_VSTM (cond:4 word) regs Rn (off:int32) len (wb:int32) wback =
    \s:aarch32state.
        let base:int32 = read Rn s in
        (if aarch32_nowrap (word_add base off) len then
           if aarch32_condition cond s then
             if aligned 4 base then
               aarch32_vstores regs base off s
                (events := CONS (EventStore (word_add base off,len))
                                (read events s) ,,
                 (if wback then Rn := word_add base wb else (=)))
             else ASSIGNS entirety
           else events := CONS (EventStore (word_add base off,0))
                               (read events s)
         else ASSIGNS entirety) s`;;

(* ------------------------------------------------------------------------- *)
(* The instruction semantics the step conversion unfolds.                    *)
(* ------------------------------------------------------------------------- *)

let AARCH32_INSTRUCTIONS =
  [aarch32_AND; aarch32_ANDS; aarch32_EOR; aarch32_EORS; aarch32_ORR;
   aarch32_ORRS; aarch32_BIC; aarch32_BICS; aarch32_MOV; aarch32_MOVS;
   aarch32_MVN; aarch32_MVNS; aarch32_TST; aarch32_TEQ; aarch32_ADD;
   aarch32_ADDS; aarch32_CMN; aarch32_ADC; aarch32_ADCS; aarch32_SUB;
   aarch32_SUBS; aarch32_CMP; aarch32_RSB; aarch32_RSBS; aarch32_SBC;
   aarch32_SBCS; aarch32_RSC; aarch32_RSCS; aarch32_MOVW; aarch32_MOVT;
   aarch32_MUL; aarch32_UMULL; aarch32_UMLAL; aarch32_REV; aarch32_NOP;
   aarch32_DMB; aarch32_B; aarch32_BL; aarch32_BX; aarch32_LDR; aarch32_LDRB;
   aarch32_STR; aarch32_STRB; aarch32_LDR_PC; aarch32_LDRD; aarch32_STRD;
   aarch32_loads; aarch32_stores; aarch32_LDM; aarch32_STM; aarch32_LDM_PC;
   aarch32_VMOV; aarch32_VUNARY; aarch32_VBINARY; aarch32_VUPDATE;
   aarch32_VTERNARY; aarch32_VSWP; aarch32_VTRN; aarch32_VZIP; aarch32_VTBL;
   aarch32_vloads; aarch32_vstores; aarch32_vdups; aarch32_VLD1;
   aarch32_VST1; aarch32_VLD1_LANE; aarch32_VST1_LANE; aarch32_VLD1_ALL;
   aarch32_VLDM; aarch32_VSTM];;
