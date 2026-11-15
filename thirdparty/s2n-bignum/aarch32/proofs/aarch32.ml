(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A32 execution and proof automation.                                       *)
(* ========================================================================= *)

let aarch32_print_log = ref false;;

let aarch32_execute = define
 `aarch32_execute = \i:(aarch32state->aarch32state->bool). i`;;

(* One step decodes the word at PC, advances PC by four bytes, and applies
   the decoded instruction, which sees PC as its own address plus 4. *)

let aarch32 = define
 `aarch32 s s' <=>
    ?instr. aarch32_decode s (read PC s) instr /\
            (PC := word_add (read PC s) (word 4) ,,
             aarch32_execute instr) s s'`;;

(* ------------------------------------------------------------------------- *)
(* Forward symbolic execution, as for RV32: `read PC s` must be `word pc` or *)
(* `word (pc + n)` for the code's symbolic base `pc`.                        *)
(* ------------------------------------------------------------------------- *)

let AARCH32_THM =
  let pth = prove
   (`read PC s = word pc ==> aarch32_decode s (word pc) instr ==>
     (aarch32 s s' <=> (PC := word (pc + 4) ,, instr) s s')`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[aarch32] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD; aarch32_execute] THEN
    ASM_MESON_TAC[aarch32_decode_unique]) in
  fun (execth2:thm option array) loaded_mc_th pc_th ->
    let th = MATCH_MP pth pc_th in
    let pc_ofs =
      let pc_expr = snd (dest_comb (snd (dest_eq (concl pc_th)))) in
      if is_var pc_expr then 0
      else
        try
          let _,ofs = dest_binary "+" pc_expr in
          dest_small_numeral ofs
        with Failure _ ->
          failwith
            ("AARCH32_THM: cannot decompose PC expression: " ^
             string_of_term (concl pc_th)) in
    let _ =
      if pc_ofs >= Array.length execth2 then
        failwith
          ("AARCH32_THM: no decoded instruction at `pc + " ^
           string_of_int pc_ofs ^ "`") in
    let _ =
      if !aarch32_print_log then
        let opt = option_get execth2.(pc_ofs) in
        let t = snd (strip_forall (concl opt)) in
        let t = snd (dest_imp t) in
        let term = snd (dest_comb t) in
        Printf.printf "Instruction at `pc + %d (%#x)`: `%s`\n"
          pc_ofs pc_ofs (string_of_term term) in
    MATCH_MP th (MATCH_MP (option_get execth2.(pc_ofs)) loaded_mc_th);;

let AARCH32_ENSURES_SUBLEMMA_TAC =
  ENSURES_SUBLEMMA_TAC o
  MATCH_MP aligned_bytes_loaded_update o CONJUNCT1;;

let AARCH32_ENSURES_SUBSUBLEMMA_TAC =
  ENSURES_SUBSUBLEMMA_TAC o
  map (MATCH_MP aligned_bytes_loaded_update o CONJUNCT1);;

let is_read_pc = is_read_named_component "PC";;

let is_read_events = is_read_named_component "events";;

(* The assumptions that say what a flag holds, which decide a conditional
   instruction's condition: `read F s`, its negation, or `read F s <=> b`. *)

let aarch32_flag_ths =
  let flags = [`NF`; `ZF`; `CF`; `VF`] in
  let is_flag_read t =
    is_binary "read" t && mem (fst (dest_binary "read" t)) flags in
  filter (fun th ->
    let c = concl th in
    let c = if is_neg c then dest_neg c else c in
    is_flag_read c || (is_eq c && is_flag_read (lhs c)));;

(* Fails unless every conditional instruction's condition is decided, since
   the state after one that is not is no single update. *)

let AARCH32_CHECK_DECIDED_CONV tm =
  let rel_ty = `:aarch32state->bool` in
  if can (find_term (fun t ->
            is_cond t && type_of t = rel_ty)) tm
  then failwith
   ("AARCH32_CONV: a conditional instruction's condition is undecided; " ^
    "establish the flags it reads first")
  else REFL tm;;

(* Convert one symbolic machine step to the explicit state update for the
   instruction at the current PC. `ths` must hold the current `read PC`
   equation and the code's `aligned_bytes_loaded` fact, and `tm` is
   `aarch32 s s'`. *)

let AARCH32_CONV (decode_ths:thm option array) (ths:thm list) tm =
  let pc_th =
    try
      find
        (fun th ->
          let c = concl th in
          is_eq c && is_read_pc (fst (dest_eq c)))
        ths
    with Failure _ ->
      failwith "AARCH32_CONV: cannot find `read PC .. = ..`" in
  let aligned_bytes_loaded_mc_ths =
    let the_mc =
      option_bind decode_ths.(0)
        (fun th ->
          let t = concl th in
          let loaded = fst (dest_imp (snd (strip_forall t))) in
          let mc = last (snd (strip_comb loaded)) in
          if is_const mc then Some mc else None) in
    let loaded_tm = `aligned_bytes_loaded` in
    let res =
      filter
        (fun th ->
          let c,args = strip_comb (concl th) in
          c = loaded_tm &&
          (the_mc = None || last args = option_get the_mc))
        ths in
    if res = [] then
      failwith "AARCH32_CONV: cannot find aligned code-loading assumption"
    else
      res in
  let eth =
    try
      tryfind
        (fun loaded_mc_th ->
          GEN_REWRITE_CONV I
            [AARCH32_THM decode_ths loaded_mc_th pc_th] tm)
        aligned_bytes_loaded_mc_ths
    with Failure _ ->
      failwith "AARCH32_CONV: cannot match code loading to the current PC" in
  let flag_ths = aarch32_flag_ths ths in
  (K eth THENC
   REWRITE_CONV
    ([aarch32_execute; aarch32_cond; SEQ] @ AARCH32_INSTRUCTIONS) THENC
   REWRITE_CONV[LET_DEF; LET_END_DEF] THENC
   TOP_DEPTH_CONV BETA_CONV THENC
   REWRITE_CONV AARCH32_CONDITION_CLAUSES THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   REWRITE_CONV flag_ths THENC
   AARCH32_CHECK_DECIDED_CONV THENC
   REWRITE_CONV[SEQ] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [assign] THENC
   REWRITE_CONV[] THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   REWRITE_CONV (READ_RVALUE :: WRITE_RVALUE :: WORD_ADD_0 ::
                 CONJUNCTS AARCH32_OPERAND_READS) THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   WORD_REDUCE_CONV THENC
   ONCE_REWRITE_CONV[WORD_SUB_ADD] THENC
   ONCE_DEPTH_CONV
    (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV) THENC
   ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
     GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
     RAND_CONV NUM_REDUCE_CONV) THENC
   TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
   GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL] THENC
   ONCE_DEPTH_CONV WORD_PC_PLUS_CONV THENC
   ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
   ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) tm;;

let AARCH32_BASIC_STEP_TAC =
  GEN_BASIC_STEP_TAC "AARCH32" `aarch32` `:aarch32state` AARCH32_CONV ALL_TAC;;

let AARCH32_STEP_TAC (mc_length_th,decode_ths) subths sname
      (store_inst_term_to:term ref option)
      (strip_component_tac:thm_tactic) =
  GEN_STEP_TAC AARCH32_BASIC_STEP_TAC ALL_TAC aligned_bytes_loaded_update
    (fun th thl ->
      if !aarch32_print_log then begin
        Printf.printf "State update: `%s`\n" (string_of_thm th);
        List.iter
          (fun th' ->
            Printf.printf "New component: `%s`\n" (string_of_thm th'))
          thl
      end)
    (mc_length_th,decode_ths) subths sname
    store_inst_term_to strip_component_tac;;

let AARCH32_VERBOSE_STEP_TAC =
  GEN_VERBOSE_STEP_TAC AARCH32_STEP_TAC;;

let AARCH32_VERBOSE_SUBSTEP_TAC =
  GEN_VERBOSE_SUBSTEP_TAC AARCH32_STEP_TAC;;

let DISCARD_FLAGS_TAC =
  DISCARD_MATCHING_ASSUMPTIONS
   [`read CF s = y`; `read ZF s = y`;
    `read NF s = y`; `read VF s = y`];;

let DISCARD_STATE_TAC =
  GEN_DISCARD_STATE_TAC `:aarch32state`;;

let DISCARD_OLDSTATE_TAC =
  GEN_DISCARD_OLDSTATE_TAC `:aarch32state` aarch32_print_log;;

let AARCH32_SINGLE_STEP_TAC =
  GEN_SINGLE_STEP_TAC AARCH32_VERBOSE_STEP_TAC DISCARD_OLDSTATE_TAC;;

let AARCH32_VSTEPS_TAC =
  GEN_VSTEPS_TAC AARCH32_VERBOSE_STEP_TAC;;

let AARCH32_STEPS_TAC =
  GEN_STEPS_TAC AARCH32_SINGLE_STEP_TAC;;

let AARCH32_SIM_TAC ?(preprocess_tac:tactic option)
    ?(canonicalize_pc_diff=true) execth snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  (match preprocess_tac with Some t -> t | None -> ALL_TAC) THEN
  AARCH32_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (if canonicalize_pc_diff then
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[]
   else
    ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The flags, for MAYCHANGE lists.                                           *)
(* ------------------------------------------------------------------------- *)

let SOME_FLAGS = new_definition
 `SOME_FLAGS = [NF; ZF; CF; VF]`;;

(* ------------------------------------------------------------------------- *)
(* The 32-bit counterparts of W64_GEN_TAC and VAL_INT64_TAC.                 *)
(* ------------------------------------------------------------------------- *)

let W32_GEN_TAC =
  let pth = prove
   (`(!x:int32. P (val x) x) <=>
     (!x. x < 2 EXP 32 /\ val(word x:int32) = x
          ==> P x (word x))`,
    GEN_REWRITE_TAC LAND_CONV [FORALL_VAL_GEN] THEN
    MESON_TAC[VAL_WORD_EQ_EQ; DIMINDEX_32]) in
  let tac = GEN_REWRITE_TAC I [pth] in
  fun w -> tac THEN X_GEN_TAC w THEN STRIP_TAC;;

let VAL_INT32_TAC =
  let pth = prove
   (`!n. n < 4294967296 ==> val(word n:int32) = n`,
    REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_32] THEN ARITH_TAC) in
  fun t -> MP_TAC(SPEC t pth) THEN
           ANTS_TAC THENL [SIMPLE_ARITH_TAC THEN NO_TAC; DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The AAPCS's integer arguments, in R0-R3, and result, in R0.               *)
(* ------------------------------------------------------------------------- *)

let C_ARGUMENTS = define
 `(C_ARGUMENTS [a1;a2;a3;a4] s <=>
        read R0 s = a1 /\ read R1 s = a2 /\ read R2 s = a3 /\
        read R3 s = a4) /\
  (C_ARGUMENTS [a1;a2;a3] s <=>
        read R0 s = a1 /\ read R1 s = a2 /\ read R2 s = a3) /\
  (C_ARGUMENTS [a1;a2] s <=>
        read R0 s = a1 /\ read R1 s = a2) /\
  (C_ARGUMENTS [a1] s <=>
        read R0 s = a1) /\
  (C_ARGUMENTS [] s <=>
        T)`;;

let C_RETURN = define
 `C_RETURN = read R0`;;

(* The AAPCS lets a subroutine change R0-R3, R12, and the flags; it keeps
   R4-R11 and SP, and returns through LR. *)

let MODIFIABLE_GPRS = define
 `MODIFIABLE_GPRS = [R0; R1; R2; R3; R12]`;;

let MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI = REWRITE_RULE
  [SOME_FLAGS; MODIFIABLE_GPRS]
  (new_definition `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI =
      MAYCHANGE [PC] ,, MAYCHANGE MODIFIABLE_GPRS ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`);;
