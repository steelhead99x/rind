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
   the program counter, the NZCV flags, and flat 32-bit memory. It omits
   Thumb (T32) and interworking, the GE and Q flags, NEON and VFP registers,
   FPSCR, banked registers, exceptions, and the system registers.

   Unaligned word loads and stores are architectural on ARMv7 and later when
   SCTLR.A is clear, as Linux and Android leave it at user level, so LDR and
   STR here access any address. *)

new_type_abbrev
 ("aarch32_uarch_event",`:32 address_uarch_event`);;

let aarch32state_INDUCT,aarch32state_RECURSION,aarch32state_COMPONENTS =
  define_auto_record_type
   "aarch32state =
     { PC: int32;                       // address of the next instruction
       registers: 4 word -> int32;      // R0-R14; R15 is PC
       flags: 4 word;                   // NZCV
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
(* Core registers. R15 is PC, which only branches and the fetch write.      *)
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
   flags it knows, and fails when it cannot. *)

let aarch32_cond = define
 `aarch32_cond (cond:4 word) (i:aarch32state->aarch32state->bool) =
    \s. if aarch32_condition cond s then i s else (=) s`;;

(* ------------------------------------------------------------------------- *)
(* Shifted-register operands and their carry out: the pseudocode's Shift_C. *)
(* Each is a read-only component; the decoder picks the shift and amount,    *)
(* and gives the carry as a bit of the source register, as Shift_C does.     *)
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

let AARCH32_OPERAND_READS = prove
 (`(!r n s. read (aarch32_LSL r n) s = word_shl (read r s) n) /\
   (!r n s. read (aarch32_LSR r n) s = word_ushr (read r s) n) /\
   (!r n s. read (aarch32_ASR r n) s = word_ishr (read r s) n) /\
   (!r n s. read (aarch32_ROR r n) s = word_ror (read r s) n) /\
   (!r s. read (aarch32_RRX r) s =
          word_or (word_ushr (read r s) 1)
                  (word_shl (word(bitval(read CF s))) 31)) /\
   (!r i s. read (aarch32_BIT r i) s = bit i (read r s))`,
  REWRITE_TAC[aarch32_LSL; aarch32_LSR; aarch32_ASR; aarch32_ROR;
              aarch32_RRX; aarch32_BIT; read]);;

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

(* ------------------------------------------------------------------------- *)
(* Branches. `off` is the target's offset from the branch's own address: the *)
(* decoder folds in A32's PC bias of 8. PC already holds the branch's        *)
(* address plus 4 when the semantics run.                                    *)
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

(* ------------------------------------------------------------------------- *)
(* Loads and stores, word and byte, with an immediate offset. `off` is the   *)
(* signed offset, `indexed` whether the access uses the offset address, and  *)
(* `wback` whether Rn takes it: offset, pre-indexed, and post-indexed forms. *)
(* ------------------------------------------------------------------------- *)

let aarch32_LDR = define
 `aarch32_LDR Rt Rn (off:int32) indexed wback =
    \s:aarch32state.
        let base = read Rn s in
        let offset_addr = word_add base off in
        let addr = if indexed then offset_addr else base in
        (Rt := read (memory :> bytes32 addr) s ,,
         events := CONS (EventLoad (addr,4)) (read events s) ,,
         (if wback then Rn := offset_addr else (=))) s`;;

let aarch32_LDRB = define
 `aarch32_LDRB Rt Rn (off:int32) indexed wback =
    \s:aarch32state.
        let base = read Rn s in
        let offset_addr = word_add base off in
        let addr = if indexed then offset_addr else base in
        (Rt := word_zx (read (memory :> bytes8 addr) s) ,,
         events := CONS (EventLoad (addr,1)) (read events s) ,,
         (if wback then Rn := offset_addr else (=))) s`;;

let aarch32_STR = define
 `aarch32_STR Rt Rn (off:int32) indexed wback =
    \s:aarch32state.
        let base = read Rn s in
        let offset_addr = word_add base off in
        let addr = if indexed then offset_addr else base in
        (memory :> bytes32 addr := read Rt s ,,
         events := CONS (EventStore (addr,4)) (read events s) ,,
         (if wback then Rn := offset_addr else (=))) s`;;

let aarch32_STRB = define
 `aarch32_STRB Rt Rn (off:int32) indexed wback =
    \s:aarch32state.
        let base = read Rn s in
        let offset_addr = word_add base off in
        let addr = if indexed then offset_addr else base in
        (memory :> bytes8 addr := word_zx (read Rt s) ,,
         events := CONS (EventStore (addr,1)) (read events s) ,,
         (if wback then Rn := offset_addr else (=))) s`;;

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
   aarch32_B; aarch32_LDR; aarch32_LDRB; aarch32_STR; aarch32_STRB];;
