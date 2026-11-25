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

(* The current PC's offset from `pc`, from its `read PC s = word (pc + n)`. *)

let aarch32_pc_offset pc_th =
  let pc_expr = snd (dest_comb (snd (dest_eq (concl pc_th)))) in
  if is_var pc_expr then 0
  else
    try
      let _,ofs = dest_binary "+" pc_expr in
      dest_small_numeral ofs
    with Failure _ ->
      failwith
        ("AARCH32_THM: cannot decompose PC expression: " ^
         string_of_term (concl pc_th));;

let AARCH32_THM =
  let pth = prove
   (`read PC s = word pc ==> aarch32_decode s (word pc) instr ==>
     (aarch32 s s' <=> (PC := word (pc + 4) ,, instr) s s')`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[aarch32] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD; aarch32_execute] THEN
    ASM_MESON_TAC[aarch32_decode_unique]) in
  fun (execth2:thm option array) loaded_mc_th pc_th ->
    let th = MATCH_MP pth pc_th in
    let pc_ofs = aarch32_pc_offset pc_th in
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

(* Decides `aligned n (word m)` for numerals, as a branch to a concrete
   address needs. *)

let AARCH32_ALIGNED_NUMERAL_CONV =
  let conv =
    GEN_REWRITE_CONV I [aligned] THENC
    DEPTH_CONV(WORD_RED_CONV ORELSEC DIMINDEX_CONV ORELSEC NUM_RED_CONV) THENC
    DEPTH_CONV DIVIDES_CONV THENC
    REWRITE_CONV[] in
  fun tm ->
    match tm with
      Comb(Comb(Const("aligned",_),n),Comb(Const("word",_),m))
        when is_numeral n && is_numeral m -> conv tm
    | _ -> failwith "AARCH32_ALIGNED_NUMERAL_CONV";;

(* Folds a constant offset from R15's value, `word (pc + a)`, into it: what
   ADR and a literal load compute. The offset is added, perhaps as a negative
   number's 32-bit encoding, or subtracted. An address at or after `pc` comes
   out as `word (pc + n)` and one before it as `word_sub (word pc) (word n)`,
   whichever way the instruction spells the offset. *)

let AARCH32_PC_RELATIVE_CONV =
  let pth_add = (UNDISCH o prove)
   (`a + b = c ==> word_add (word (pc + a)) (word b):int32 = word (pc + c)`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_ADD] THEN
    CONV_TAC WORD_RULE)
  and pth_wrap = (UNDISCH o prove)
   (`a + b = c + 4294967296
     ==> word_add (word (pc + a)) (word b):int32 = word (pc + c)`,
    DISCH_TAC THEN
    SUBGOAL_THEN `word 4294967296:int32 = word 0` ASSUME_TAC THENL
     [REWRITE_TAC[WORD_EQ; DIMINDEX_32; CONG] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_ADD; GSYM ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE)
  and pth_add_back = (UNDISCH o prove)
   (`a + b + c = 4294967296
     ==> word_add (word (pc + a)) (word b):int32 =
         word_sub (word pc) (word c)`,
    DISCH_TAC THEN
    SUBGOAL_THEN
     `word_add (word a) (word_add (word b) (word c)):int32 = word 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[WORD_EQ; DIMINDEX_32; CONG] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD; WORD_RULE
     `word_add (word_add p x) y:int32 = word_sub p z <=>
      word_add x (word_add y z) = word 0`])
  and pth_sub = (UNDISCH o prove)
   (`b + c = a ==> word_sub (word (pc + a)) (word b):int32 = word (pc + c)`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_ADD] THEN
    CONV_TAC WORD_RULE)
  and pth_sub_back = (UNDISCH o prove)
   (`a + c = b
     ==> word_sub (word (pc + a)) (word b):int32 =
         word_sub (word pc) (word c)`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_ADD] THEN
    CONV_TAC WORD_RULE)
  and two31 = pow2 31
  and two32 = pow2 32
  and ea,eb,ec,epc = `a:num`,`b:num`,`c:num`,`pc:num` in
  let finish pth pc a b c =
    let th = INST [pc,epc; a,ea; b,eb; mk_numeral c,ec] pth in
    PROVE_HYP (EQT_ELIM(NUM_REDUCE_CONV(hd(hyp th)))) th in
  fun tm ->
    match tm with
      Comb(Comb(Const(op,_),
             Comb(Const("word",_),Comb(Comb(Const("+",_),pc),a))),
           Comb(Const("word",_),b))
        when is_numeral a && is_numeral b && type_of tm = `:int32` ->
          let na = dest_numeral a and nb = dest_numeral b in
          if op = "word_add" && nb </ two31 && na +/ nb </ two32 then
            finish pth_add pc a b (na +/ nb)
          else if op = "word_add" && two31 <=/ nb && nb </ two32 then
            (* The offset is the negative number `nb - 2^32`. *)
            if two32 <=/ na +/ nb then
              finish pth_wrap pc a b (na +/ nb -/ two32)
            else finish pth_add_back pc a b (two32 -/ na -/ nb)
          else if op = "word_sub" && nb <=/ na then
            finish pth_sub pc a b (na -/ nb)
          else if op = "word_sub" then
            finish pth_sub_back pc a b (nb -/ na)
          else failwith "AARCH32_PC_RELATIVE_CONV"
    | _ -> failwith "AARCH32_PC_RELATIVE_CONV";;

(* What decides `aarch32_nowrap` of an address: four bytes or fewer from an
   aligned one, the address's value once the assumptions' `val x = n` give
   each of its terms one, or its offset into a region an assumption says
   stays below 2^32, such as a buffer's or a stack frame's. *)

let AARCH32_NOWRAP_ALIGNED = prove
 (`!(a:int32) len. aligned 4 a /\ len <= 4 ==> aarch32_nowrap a len`,
  REWRITE_TAC[aarch32_nowrap; aligned; DIMINDEX_32] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT2) ASSUME_TAC) THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN ASM_REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 4 * 1073741824`; LT_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let AARCH32_NOWRAP_OFFSET = prove
 (`!(b:int32) n d len.
      aarch32_nowrap b n /\ d + len <= n
      ==> aarch32_nowrap (word_add b (word d)) len`,
  REWRITE_TAC[aarch32_nowrap; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `val(b:int32) + d < 2 EXP 32` THENL
   [SUBGOAL_THEN `d < 2 EXP 32` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `len = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC LT_IMP_LE THEN
    REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* Decides `aarch32_nowrap a len` for a numeral `len`, after `addr_conv`
   rewrites `a` to its value, or fails. `aligned_ths` decide alignment, as
   for the step's other guards, and `ths` are the assumptions. A region's
   length may be symbolic, such as a buffer's, if the assumptions' arithmetic
   bounds it. *)

let AARCH32_NOWRAP_CONV =
  let two32 = pow2 32 and word_tm = `word:num->int32`
  and nowrap_tm = `aarch32_nowrap` in
  let wrap x = mod_num x two32 in
  (* An address as a base, or none, and a numeral offset modulo 2^32. A sum
     of two symbolic terms is a base of its own. *)
  let rec offset t =
    match t with
      Comb(Comb(Const("word_add",_),x),y) ->
        (match offset x,offset y with
           (Some _,_),(Some _,_) -> Some t,num_0
         | (b,kx),(None,ky) | (None,kx),(b,ky) -> b,wrap(kx +/ ky))
    | Comb(Comb(Const("word_sub",_),x),y) ->
        (match offset x,offset y with
           (b,kx),(None,ky) -> b,wrap(kx -/ ky +/ two32)
         | _ -> Some t,num_0)
    | Comb(Const("word_neg",_),y) ->
        (match offset y with
           None,ky -> None,wrap(two32 -/ ky)
         | _ -> Some t,num_0)
    | Comb(Const("word",_),n) when is_numeral n -> None,wrap(dest_numeral n)
    | Comb(Const("word",_) as w,Comb(Comb(Const("+",_),p),n))
        when is_numeral n -> Some(mk_comb(w,p)),wrap(dest_numeral n)
    | _ -> Some t,num_0 in
  let numeral_conv =
    REWR_CONV aarch32_nowrap THENC
    DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC DIMINDEX_CONV) in
  (* The assumptions comparing numbers that reach `n` through shared
     variables, such as `8 <= m` beside `m <= n`. *)
  let arith_facts n ths =
    let is_arith th =
      match concl th with
        Comb(Comb(Const(("<=" | "<" | ">=" | ">" | "="),_),x),_) ->
          type_of x = `:num`
      | _ -> false in
    let rec grow vars kept rest =
      let near,far = partition
        (fun th -> intersect vars (frees(concl th)) <> []) rest in
      if near = [] then kept else
      grow (itlist (union o frees o concl) near vars) (near @ kept) far in
    grow (frees n) [] (filter is_arith ths) in
  let decided th =
    match rhs(concl th) with
      Const("T",_) | Const("F",_) -> th
    | _ -> failwith "AARCH32_NOWRAP_CONV" in
  (* `a = word_add b (word d)`, or `a = word d` without a base. *)
  let as_offset a b d =
    let rhs = match b with
        Some b -> mk_binop `word_add:int32->int32->int32` b
                   (mk_comb(word_tm,mk_numeral d))
      | None -> mk_comb(word_tm,mk_numeral d) in
    prove(mk_eq(a,rhs),REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE) in
  fun aligned_ths ths addr_conv tm ->
    match tm with
      Comb(Comb(Const("aarch32_nowrap",_),a0),len) when is_numeral len ->
        let nth = addr_conv a0 in
        let a = rhs(concl nth) in
        let l = dest_numeral len in
        let b,d = offset a in
        let on th = (* `aarch32_nowrap a len` from one of `a'`, `a = a'` *)
          fun eq -> TRANS (AP_THM (AP_TERM nowrap_tm (TRANS nth eq)) len) th in
        (match b with
           None ->
             let eq = as_offset a None d in
             on (decided(numeral_conv
                  (mk_comb(mk_comb(nowrap_tm,rand(concl eq)),len)))) eq
         | Some base ->
             let by_alignment () =
               if l >/ num 4 then failwith "AARCH32_NOWRAP_CONV" else
               let ath = ALIGNED_WORD_EXTENDED_CONV aligned_ths
                          (mk_comb(`aligned 4:int32->bool`,a)) in
               if rhs(concl ath) <> `T` then failwith "AARCH32_NOWRAP_CONV" else
               let th = MP (SPECL [a;len] AARCH32_NOWRAP_ALIGNED)
                         (CONJ (EQT_ELIM ath)
                               (EQT_ELIM(NUM_REDUCE_CONV
                                 (mk_binop `(<=):num->num->bool` len `4`)))) in
               TRANS (AP_THM (AP_TERM nowrap_tm nth) len) (EQT_INTRO th)
             and by_value () =
               (* `x = word n` from each `val x = n`, such as a buffer's or
                  the code's known address. *)
               let values = mapfilter (fun th ->
                 match concl th with
                   Comb(Comb(Const("=",_),Comb(Const("val",_),x)),n)
                     when is_numeral n && type_of x = `:int32` ->
                       REWRITE_RULE[WORD_VAL] (AP_TERM word_tm th)
                 | _ -> failwith "") ths in
               if values = [] then failwith "AARCH32_NOWRAP_CONV" else
               let eq = (REWRITE_CONV[WORD_ADD] THENC
                         GEN_REWRITE_CONV TOP_DEPTH_CONV values THENC
                         WORD_REDUCE_CONV) a in
               match rhs(concl eq) with
                 Comb(Const("word",_),n) when is_numeral n ->
                   on (decided(numeral_conv
                        (mk_comb(mk_comb(nowrap_tm,rhs(concl eq)),len)))) eq
               | _ -> failwith "AARCH32_NOWRAP_CONV"
             and by_region () =
               tryfind (fun th ->
                 match concl th with
                   Comb(Comb(Const("aarch32_nowrap",_),r),n) ->
                     (match offset r with
                        Some b',d0 when b' = base ->
                          let dd = wrap(d -/ d0 +/ two32) in
                          let goal = mk_binop `(<=):num->num->bool`
                            (mk_binop `(+):num->num->num` (mk_numeral dd) len)
                            n in
                          let fit =
                            if is_numeral n then
                              if dd +/ l >/ dest_numeral n then failwith "" else
                              EQT_ELIM(NUM_REDUCE_CONV goal)
                            else
                              match arith_facts n ths with
                                [] -> ARITH_RULE goal
                              | facts ->
                                  MP (ARITH_RULE
                                       (mk_imp(list_mk_conj(map concl facts),goal)))
                                     (end_itlist CONJ facts) in
                          let eq = prove
                           (mk_eq(a,mk_binop `word_add:int32->int32->int32` r
                                      (mk_comb(word_tm,mk_numeral dd))),
                            REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE) in
                          let th' = MP (SPECL [r;n;mk_numeral dd;len]
                                          AARCH32_NOWRAP_OFFSET)
                                       (CONJ th fit) in
                          on (EQT_INTRO th') eq
                      | _ -> failwith "")
                 | _ -> failwith "") ths in
             try by_alignment () with Failure _ ->
             try by_value () with Failure _ ->
             by_region ())
    | _ -> failwith "AARCH32_NOWRAP_CONV";;

(* Fails unless every conditional instruction's condition is decided, every
   address and branch target an instruction needs aligned is known to be, and
   every transfer is known to stay below 2^32, since the state after one that
   is not is no single update. *)

let AARCH32_CHECK_DECIDED_CONV tm =
  let rel_tys = [`:aarch32state->bool`; `:aarch32state->aarch32state->bool`] in
  if can (find_term (fun t ->
            is_cond t && mem (type_of t) rel_tys)) tm
  then failwith
   ("AARCH32_CONV: a conditional instruction's condition is undecided, " ^
    "an address or branch target is not known to be aligned, or a " ^
    "transfer is not known to stay below 2^32; establish the flags it " ^
    "reads, or assume `aligned 4` of the address, or `aarch32_nowrap` of " ^
    "a region holding the transfer or the value of its base, first")
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
      option_bind
        (* The first word that decodes: a routine may open with data. *)
        (try find (function Some _ -> true | None -> false)
               (Array.to_list decode_ths)
         with Failure _ -> None)
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
    (* A PC this cannot read as `pc + n` is AARCH32_THM's to report. *)
    let undecoded =
      try
        let ofs = aarch32_pc_offset pc_th in
        if ofs < Array.length decode_ths &&
           (match decode_ths.(ofs) with None -> true | Some _ -> false)
        then Some ofs else None
      with Failure _ -> None in
    match undecoded with
      Some ofs ->
        failwith
          ("AARCH32_CONV: the word at `pc + " ^ string_of_int ofs ^
           "` does not decode, such as a literal pool's")
    | None ->
    try
      tryfind
        (fun loaded_mc_th ->
          GEN_REWRITE_CONV I
            [AARCH32_THM decode_ths loaded_mc_th pc_th] tm)
        aligned_bytes_loaded_mc_ths
    with Failure _ ->
      failwith "AARCH32_CONV: cannot match code loading to the current PC" in
  let flag_ths = aarch32_flag_ths ths in
  let aligned_ths =
    map (MATCH_MP aligned_bytes_loaded_aligned) aligned_bytes_loaded_mc_ths @
    ths in
  (* A branch target is a loaded word, which the assumptions give only at
     its address's normal form, and an address may be a known base's
     offset, which is aligned or not only once the sum is taken. *)
  let target_conv =
    SUB_ALIGNED_WORD_CONV
     (TOP_DEPTH_CONV
       (GEN_REWRITE_CONV I (filter (is_eq o concl) ths) ORELSEC
        WORD_RED_CONV ORELSEC
        NORMALIZE_RELATIVE_ADDRESS_CONV)) in
  (* A transfer's address, as far as the assumptions give it, for deciding
     whether it stays below 2^32. *)
  let addr_conv =
    TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
    REWRITE_CONV (READ_RVALUE :: CONJUNCTS AARCH32_OPERAND_READS) THENC
    TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
    REWRITE_CONV (BITVAL_CLAUSES :: flag_ths) THENC
    TOP_DEPTH_CONV
     (GEN_REWRITE_CONV I (filter (is_eq o concl) ths) ORELSEC
      WORD_RED_CONV ORELSEC
      NORMALIZE_RELATIVE_ADDRESS_CONV) in
  (K eth THENC
   REWRITE_CONV
    ([aarch32_execute; aarch32_cond; aarch32_cond_branch; SEQ] @
     AARCH32_INSTRUCTIONS) THENC
   REWRITE_CONV[LET_DEF; LET_END_DEF] THENC
   TOP_DEPTH_CONV BETA_CONV THENC
   REWRITE_CONV AARCH32_CONDITION_CLAUSES THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   REWRITE_CONV (READ_RVALUE :: flag_ths) THENC
   target_conv THENC
   ALIGNED_WORD_EXTENDED_CONV aligned_ths THENC
   ONCE_DEPTH_CONV AARCH32_ALIGNED_NUMERAL_CONV THENC
   ONCE_DEPTH_CONV (AARCH32_NOWRAP_CONV aligned_ths ths addr_conv) THENC
   REWRITE_CONV[] THENC
   AARCH32_CHECK_DECIDED_CONV THENC
   REWRITE_CONV[SEQ] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [assign] THENC
   REWRITE_CONV[] THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   REWRITE_CONV (READ_RVALUE :: WRITE_RVALUE :: WORD_ADD_0 ::
                 CONJUNCTS AARCH32_OPERAND_READS) THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   (* RRX reads C, which appears only once its operand is unfolded. *)
   REWRITE_CONV (BITVAL_CLAUSES :: flag_ths) THENC
   WORD_REDUCE_CONV THENC
   ONCE_REWRITE_CONV[WORD_SUB_ADD] THENC
   ONCE_DEPTH_CONV
    (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV) THENC
   (* Before the next fold, which would leave an address before `pc` as
      `word (pc + n)` for an `n` just under 2^32. *)
   TOP_DEPTH_CONV AARCH32_PC_RELATIVE_CONV THENC
   ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
     GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
     RAND_CONV NUM_REDUCE_CONV) THENC
   TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
   GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
   (* An address with a register offset the assumptions give a value. *)
   SUB_COMPONENTS_CONV (DEPTH_CONV WORD_RED_CONV) THENC
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
(* Simulate through a core correctness theorem.                              *)
(* ------------------------------------------------------------------------- *)

let (AARCH32_BIGSTEP_TAC:(thm*thm option array)->string->tactic) =
  GEN_BIGSTEP_TAC
    "AARCH32" aligned_bytes_loaded_update DISCARD_OLDSTATE_TAC;;

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

(* The AAPCS lets a subroutine change R0-R3, R12, the flags, and LR, which
   it returns through and may use as scratch once saved; it keeps R4-R11 and
   SP. *)

let MODIFIABLE_GPRS = define
 `MODIFIABLE_GPRS = [R0; R1; R2; R3; R12; LR]`;;

let MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI = REWRITE_RULE
  [SOME_FLAGS; MODIFIABLE_GPRS]
  (new_definition `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI =
      MAYCHANGE [PC] ,, MAYCHANGE MODIFIABLE_GPRS ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`);;

(* ------------------------------------------------------------------------- *)
(* Promote core correctness theorems to AAPCS subroutine theorems, as        *)
(* s2n-bignum's RISCV_ADD_RETURN_NOSTACK_TAC and RISCV_ADD_RETURN_STACK_TAC  *)
(* do. The subroutine theorem assumes `aligned 4 returnaddress`: it covers   *)
(* an A32 caller, since returning to a Thumb one leaves the model. One with  *)
(* a stack frame assumes `aligned 4 stackpointer` too, as the AAPCS keeps SP *)
(* at every instruction, and `aarch32_nowrap` of the frame, which a push of  *)
(* more than one word needs.                                                 *)
(* ------------------------------------------------------------------------- *)

let AARCH32_CHECK_FORALLVARS_TAC:tactic =
  GEN_CHECK_FORALLVARS_TAC
    [`read LR s`; `read events s`; `read SP s`];;

(* Promote a core theorem whose postcondition stops just before the final
   `bx lr`:

       add r0, r0, #1     @ covered by coreth
       bx lr              @ executed by this tactic

   The promoted theorem returns to LR and widens the frame to what the AAPCS
   lets a callee change. *)

let AARCH32_ADD_RETURN_NOSTACK_TAC =
  fun execth coreth ->
    let is_coreth_safety = is_exists (concl coreth) in

    (fun (asl,w) ->
      if is_coreth_safety <> is_exists w then
        failwith "coreth must be `exists ..` iff the conclusion is"
      else ALL_TAC (asl,w)) THEN

    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      META_EXISTS_TAC THEN
      AARCH32_CHECK_FORALLVARS_TAC THEN
      FIRST_X_ASSUM
        (fun th -> MP_TAC (ONCE_REWRITE_RULE[SUBROUTINE_APPEND_FORALL] th)) THEN
      REPEAT
       (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[SWAP_FORALL_THM])) THEN
        MATCH_MP_TAC SUBROUTINE_MONO_FORALL2 THEN GEN_TAC)
     else
      AARCH32_CHECK_FORALLVARS_TAC THEN
      MP_TAC coreth THEN
      REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC)) THEN

    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    (if is_coreth_safety then
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN META_EXISTS_TAC
     else ALL_TAC) THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      ((ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
       (ALIGNED_WORD_TAC THEN NO_TAC) ORELSE
       (TRY DISJ2_TAC THEN NONOVERLAPPING_TAC));
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN MP_TAC th) THEN
    AARCH32_BIGSTEP_TAC execth "s1" THEN
    (if is_coreth_safety then
      TRY
       (TRY(GEN_REWRITE_TAC I [SUBROUTINE_APPEND_PREFIX_NIL]) THEN
        TRY(CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV)) THEN
        BINOP_TAC THENL [UNIFY_REFL_TAC; REFL_TAC] THEN NO_TAC)
     else ALL_TAC) THEN
    AARCH32_STEPS_TAC execth [2] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];;

(* Promote a core theorem surrounded by a stack prologue and epilogue:

       push {r4, r5, lr}  @ prologue
       ...                @ covered by coreth
       pop {r4, r5, pc}   @ epilogue, which returns

   `reglist` names the callee-saved registers the prologue saves and
   `stackoff` is the frame's size in bytes. The prologue is `pre_n` steps
   and the epilogue with its return `post_n`, each one unless
   `pre_post_nsteps` says otherwise, as for `pop {r4, r5, lr}` and `bx lr`.
   The tactic runs them, proves that SP and the listed registers are
   restored, and applies the AAPCS frame. *)

let AARCH32_ADD_RETURN_STACK_TAC =
  let sp_tm = `SP` in
  fun ?(pre_post_nsteps = (1,1))
      ?(core_precondition_tac = ALL_TAC)
      execth coreth reglist stackoff ->
    let is_coreth_safety = is_exists (concl coreth) in
    let regs = dest_list reglist in
    let pre_n,post_n = pre_post_nsteps in

    (fun (asl,w) ->
      if is_coreth_safety <> is_exists w then
        failwith "coreth must be `exists ..` iff the conclusion is"
      else ALL_TAC (asl,w)) THEN

    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      META_EXISTS_TAC THEN
      AARCH32_CHECK_FORALLVARS_TAC THEN
      FIRST_X_ASSUM
        (fun th -> MP_TAC (ONCE_REWRITE_RULE[SUBROUTINE_APPEND_FORALL] th))
     else
      AARCH32_CHECK_FORALLVARS_TAC THEN MP_TAC coreth) THEN

    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; fst execth] THEN
    (if is_coreth_safety then
      REPEAT
       (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[SWAP_FORALL_THM])) THEN
        MATCH_MP_TAC SUBROUTINE_MONO_FORALL3 THEN GEN_TAC) THEN
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[SWAP_FORALL_THM]))
     else
      REPEAT(MATCH_MP_TAC SUBROUTINE_MONO_FORALL2 THEN GEN_TAC)) THEN
    (if vfree_in sp_tm (concl coreth) then
      DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
     else
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(fun th ->
        WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    (if is_coreth_safety then
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN META_EXISTS_TAC
     else ALL_TAC) THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      ((ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
       (ALIGNED_WORD_TAC THEN NO_TAC) ORELSE
       (TRY DISJ2_TAC THEN NONOVERLAPPING_TAC));
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      ((ENSURES_EXISTING_PRESERVED_TAC sp_tm THEN
        MAP_EVERY
         (fun c ->
           ENSURES_PRESERVED_TAC ("init_" ^ fst(dest_const c)) c)
         regs)
       ORELSE
       FAIL_TAC
        "callee-save registers are still in MAYCHANGE, or `read SP s` is absent") THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN
      AARCH32_STEPS_TAC execth (1--pre_n) THEN
      MP_TAC th) THEN
    AARCH32_BIGSTEP_TAC execth ("s" ^ string_of_int(pre_n + 1)) THEN
    (if is_coreth_safety then
      TRY
       (TRY(GEN_REWRITE_TAC I [SUBROUTINE_APPEND_PREFIX_NIL]) THEN
        TRY(CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV)) THEN
        BINOP_TAC THENL [UNIFY_REFL_TAC; REFL_TAC] THEN NO_TAC)
     else ALL_TAC) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    TRY(core_precondition_tac THEN NO_TAC) THEN
    AARCH32_STEPS_TAC execth
      ((pre_n + 2)--(pre_n + post_n + 1)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The wrappers, literal loads after and before the code, a load at a known *)
(* base's offset, and what untaken branches, loads, and stores record,       *)
(* proven of small routines as this file loads, as                           *)
(* riscv/tutorial/subroutine.ml proves s2n-bignum's; and which transfers     *)
(* that run past 0xffffffff leave the model.                                 *)
(* ------------------------------------------------------------------------- *)

let AARCH32_SUBROUTINE_TESTS =
  let define name words =
    define_assert_word_list name
     (mk_flist
       (flat (map (fun w ->
                map (fun i -> mk_comb(`word:num->byte`,
                       mk_small_numeral ((w lsr (8 * i)) land 0xff)))
                    (0--3))
              words)))
     words in
  (* add r0, r0, #1; bx lr *)
  let nostack_mc = define "aarch32_test_nostack_mc" [0xe2800001; 0xe12fff1e] in
  let nostack_exec = AARCH32_MK_EXEC_RULE nostack_mc in
  let nostack_core = prove
   (`!pc a.
      ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_nostack_mc /\
             read PC s = word pc /\
             C_ARGUMENTS [a] s)
        (\s. read PC s = word (pc + 4) /\
             C_RETURN s = word_add a (word 1))
        (MAYCHANGE [PC] ,, MAYCHANGE [R0])`,
    REWRITE_TAC[fst nostack_exec; C_ARGUMENTS; C_RETURN] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC nostack_exec [1]) in
  let nostack = prove
   (`!pc a (returnaddress:int32).
      aligned 4 returnaddress
      ==> ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_nostack_mc /\
             read PC s = word pc /\
             read LR s = returnaddress /\
             C_ARGUMENTS [a] s)
        (\s. read PC s = returnaddress /\
             C_RETURN s = word_add a (word 1))
        MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
    REWRITE_TAC[fst nostack_exec] THEN
    AARCH32_ADD_RETURN_NOSTACK_TAC nostack_exec
      (REWRITE_RULE[fst nostack_exec] nostack_core)) in
  (* push {r4, lr}; mov r4, r0; add r0, r4, #1; pop {r4, pc} *)
  let stack_mc = define "aarch32_test_stack_mc"
    [0xe92d4010; 0xe1a04000; 0xe2840001; 0xe8bd8010] in
  let stack_exec = AARCH32_MK_EXEC_RULE stack_mc in
  let stack_core = prove
   (`!pc a.
      ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_stack_mc /\
             read PC s = word (pc + 4) /\
             C_ARGUMENTS [a] s)
        (\s. read PC s = word (pc + 12) /\
             C_RETURN s = word_add a (word 1))
        (MAYCHANGE [PC] ,, MAYCHANGE [R0; R4])`,
    REWRITE_TAC[fst stack_exec; C_ARGUMENTS; C_RETURN] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC stack_exec [1;2]) in
  let stack = prove
   (`!pc a (stackpointer:int32) (returnaddress:int32).
      aligned 4 returnaddress /\ aligned 4 stackpointer /\
      aarch32_nowrap (word_sub stackpointer (word 8)) 8 /\
      nonoverlapping
        ((word pc):int32,LENGTH aarch32_test_stack_mc)
        (word_sub stackpointer (word 8),8)
      ==> ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_stack_mc /\
             read PC s = word pc /\
             read SP s = stackpointer /\
             read LR s = returnaddress /\
             C_ARGUMENTS [a] s)
        (\s. read PC s = returnaddress /\
             read SP s = stackpointer /\
             C_RETURN s = word_add a (word 1))
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE
          [memory :> bytes (word_sub stackpointer (word 8),8)])`,
    REWRITE_TAC[fst stack_exec] THEN
    AARCH32_ADD_RETURN_STACK_TAC stack_exec
      (REWRITE_RULE[fst stack_exec] stack_core)
      `[R4]` 8) in
  (* ldr r0, [pc, #4]; sub r1, pc, #12; bx lr; then two words of data, the
     second of which is no instruction. *)
  let literal_mc = define "aarch32_test_literal_mc"
    [0xe59f0004; 0xe24f100c; 0xe12fff1e; 0xffffffff; 0x12345678] in
  let literal_exec = AARCH32_MK_EXEC_RULE literal_mc in
  let literal = prove
   (`!pc v.
      ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_literal_mc /\
             read PC s = word pc /\
             read (memory :> bytes32 (word (pc + 12))) s = v)
        (\s. read PC s = word (pc + 8) /\
             read R0 s = v /\ read R1 s = word pc)
        (MAYCHANGE [PC] ,, MAYCHANGE [R0; R1] ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst literal_exec] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC literal_exec [1;2]) in
  (* ldrd r4, r5, [r0, #3], at an address that only the sum aligns. *)
  let offset_mc = define "aarch32_test_offset_mc" [0xe1c040d3] in
  let offset_exec = AARCH32_MK_EXEC_RULE offset_mc in
  let offset = prove
   (`!pc.
      ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_offset_mc /\
             read PC s = word pc /\
             read R0 s = word 0x1001)
        (\s. read PC s = word (pc + 4))
        (MAYCHANGE [PC] ,, MAYCHANGE [R4; R5] ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst offset_exec] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC offset_exec [1]) in
  (* ldr r0, [pc, #-12]; sub r1, pc, #16: a word and an address before the
     code, each 4 bytes before it. *)
  let before_mc = define "aarch32_test_before_mc" [0xe51f000c; 0xe24f1010] in
  let before_exec = AARCH32_MK_EXEC_RULE before_mc in
  let before = prove
   (`!pc v.
      ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_before_mc /\
             read PC s = word pc /\
             read (memory :> bytes32 (word_sub (word pc) (word 4))) s = v)
        (\s. read PC s = word (pc + 8) /\
             read R0 s = v /\ read R1 s = word_sub (word pc) (word 4))
        (MAYCHANGE [PC] ,, MAYCHANGE [R0; R1] ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst before_exec] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC before_exec [1;2]) in
  (* blne #0 with Z set: a branch not taken records its fall-through. *)
  let untaken_mc = define "aarch32_test_untaken_mc" [0x1b000000] in
  let untaken_exec = AARCH32_MK_EXEC_RULE untaken_mc in
  let untaken = prove
   (`!pc e.
      ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_untaken_mc /\
             read PC s = word pc /\ read ZF s /\ read events s = e)
        (\s. read PC s = word (pc + 4) /\
             read events s =
               CONS (EventJump (word pc:int32,word (pc + 4))) e)
        (MAYCHANGE [PC] ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst untaken_exec] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC untaken_exec [1]) in
  (* mov r0, r0, then a word that does not decode: a step onto it says so. *)
  let data_mc = define "aarch32_test_data_mc" [0xe1a00000; 0xffffffff] in
  let data_exec = AARCH32_MK_EXEC_RULE data_mc in
  let () =
    let msg =
      try
        ignore (prove
         (`!pc.
            ensures aarch32
              (\s. aligned_bytes_loaded s (word pc) aarch32_test_data_mc /\
                   read PC s = word pc)
              (\s. read PC s = word (pc + 8))
              (MAYCHANGE [PC] ,, MAYCHANGE [R0] ,, MAYCHANGE [events])`,
          REWRITE_TAC[fst data_exec] THEN
          REPEAT STRIP_TAC THEN
          AARCH32_SIM_TAC data_exec [1;2]));
        "the step succeeded"
      with Failure msg -> msg in
    if msg <> "AARCH32_CONV: the word at `pc + 4` does not decode, such as \
               a literal pool's"
    then failwith ("AARCH32_SUBROUTINE_TESTS: a step onto data: " ^ msg) in
  (* str r12, [sp, -r3, rrx]! with C clear: an address that reads C, which
     appears only once the operand unfolds. *)
  let rrx_mc = define "aarch32_test_rrx_mc" [0xe72dc063] in
  let rrx_exec = AARCH32_MK_EXEC_RULE rrx_mc in
  let rrx = prove
   (`!pc (scratch:int32) (v:int32).
      nonoverlapping ((word pc):int32,LENGTH aarch32_test_rrx_mc) (scratch,256) /\
      aarch32_nowrap scratch 256
      ==> ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_rrx_mc /\
             read PC s = word pc /\
             read SP s = word_add scratch (word 128) /\
             read R3 s = word 32 /\ ~read CF s /\ read R12 s = v)
        (\s. read PC s = word (pc + 4) /\
             read SP s = word_add scratch (word 112) /\
             read (memory :> bytes32 (word_add scratch (word 112))) s = v)
        (MAYCHANGE [PC; SP] ,, MAYCHANGE [memory :> bytes(scratch,256)] ,,
         MAYCHANGE [events])`,
    REWRITE_TAC[fst rrx_exec] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC rrx_exec [1]) in
  (* ldrne r0, [r1]; strdne r4, r5, [r0, #3]; popne {r4, pc}, with Z set:
     each records an access of no bytes, at an address that need not be
     aligned, and the pop its fall-through too. *)
  let skipped_mc = define "aarch32_test_skipped_mc"
    [0x15910000; 0x11c040f3; 0x18bd8010] in
  let skipped_exec = AARCH32_MK_EXEC_RULE skipped_mc in
  let skipped = prove
   (`!pc a (sp:int32) e.
      aarch32_nowrap a 4 /\ aarch32_nowrap sp 8
      ==> ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_skipped_mc /\
             read PC s = word pc /\ read ZF s /\
             read R0 s = word 0x1002 /\ read R1 s = a /\ read SP s = sp /\
             read events s = e)
        (\s. read PC s = word (pc + 12) /\
             read events s =
               CONS (EventJump (word (pc + 8):int32,word (pc + 12)))
                (CONS (EventLoad (sp,0))
                  (CONS (EventStore (word 0x1005,0))
                    (CONS (EventLoad (a,0)) e))))
        (MAYCHANGE [PC] ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst skipped_exec] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC skipped_exec [1;2;3]) in
  (* ldr r0, [r1, r2], at a sum of two symbolic words that only an
     assumption aligns, so the word cannot run past 0xffffffff. *)
  let sum_mc = define "aarch32_test_sum_mc" [0xe7910002] in
  let sum_exec = AARCH32_MK_EXEC_RULE sum_mc in
  let sum = prove
   (`!pc (a:int32) b.
      aligned 4 (word_add a b)
      ==> ensures aarch32
        (\s. aligned_bytes_loaded s (word pc) aarch32_test_sum_mc /\
             read PC s = word pc /\ read R1 s = a /\ read R2 s = b)
        (\s. read PC s = word (pc + 4))
        (MAYCHANGE [PC] ,, MAYCHANGE [R0] ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst sum_exec] THEN
    REPEAT STRIP_TAC THEN
    AARCH32_SIM_TAC sum_exec [1]) in
  (* ldr r0, [r1, #4], then #8, in a region of symbolic length `n`, at least
     8 through `m`, that nothing aligns: the first word fits, and the second
     is not known to, so its step stops at the bound. A region `8 + k` long
     bounds the first word by its own shape. *)
  let region name word hyp =
    let mc = define name [word] in
    let exec = AARCH32_MK_EXEC_RULE mc in
    if (snd exec).(0) = None then
      failwith ("AARCH32_SUBROUTINE_TESTS: " ^ name ^ " does not decode") else
    let tm = vsubst [lhs(concl mc),`code:byte list`]
     (mk_imp(hyp,
       `ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) code /\
               read PC s = word pc /\ read R1 s = (a:int32))
          (\s. read PC s = word (pc + 4))
          (MAYCHANGE [PC] ,, MAYCHANGE [R0] ,, MAYCHANGE [events])`)) in
    fun () -> prove
     (list_mk_forall(frees tm,tm),
      REWRITE_TAC[fst exec] THEN
      REPEAT STRIP_TAC THEN
      AARCH32_SIM_TAC exec [1]) in
  let chain = `aarch32_nowrap (a:int32) n /\ m >= 8 /\ m <= n` in
  let region4 = region "aarch32_test_region_mc" 0xe5910004 chain () in
  let shaped = region "aarch32_test_region_shaped_mc" 0xe5910004
    `aarch32_nowrap (a:int32) (8 + k)` () in
  let () =
    let past = region "aarch32_test_region_past_mc" 0xe5910008 chain in
    let msg = try ignore (past ()); "the step succeeded"
              with Failure msg -> msg in
    let undecided =
      "AARCH32_CONV: a conditional instruction's condition is undecided" in
    let k = String.length undecided in
    if String.length msg < k || String.sub msg 0 k <> undecided then
      failwith ("AARCH32_SUBROUTINE_TESTS: a word past a region: " ^ msg) in
  (* One instruction stepped with R0 at an address near the top of memory,
     and Z set: whether its step leaves the model. *)
  let leaves name word r0 =
    let mc = define name [word] in
    let exec = AARCH32_MK_EXEC_RULE mc in
    let ths = map ASSUME
     [mk_comb(`aligned_bytes_loaded (s:aarch32state) (word pc:int32)`,lhs(concl mc));
      `read PC (s:aarch32state) = word pc`;
      mk_eq(`read R0 (s:aarch32state)`,
            mk_comb(`word:num->int32`,mk_small_numeral r0));
      `read ZF (s:aarch32state)`] in
    let th = AARCH32_CONV (snd exec) ths `aarch32 s s'` in
    can (find_term (function
           Comb(Const("ASSIGNS",_),Const("entirety",_)) -> true
         | _ -> false)) (rhs(concl th)) in
  let () = List.iter (fun (name,word,r0,expected) ->
      if leaves name word r0 <> expected then
        failwith ("AARCH32_SUBROUTINE_TESTS: " ^ name ^ " at " ^
                  string_of_int r0))
   [(* ldr r1, [r0]: a word may be unaligned, but not run past the top. *)
    "aarch32_test_wrap_ldr_mc",0xe5901000,0xfffffffd,true;
    "aarch32_test_top_ldr_mc",0xe5901000,0xfffffffc,false;
    (* str r1, [r0] *)
    "aarch32_test_wrap_str_mc",0xe5801000,0xffffffff,true;
    (* ldrd r4, r5, [r0] *)
    "aarch32_test_wrap_ldrd_mc",0xe1c040d0,0xfffffffc,true;
    "aarch32_test_top_ldrd_mc",0xe1c040d0,0xfffffff8,false;
    (* ldm r0, {r1, r2} *)
    "aarch32_test_wrap_ldm_mc",0xe8900006,0xfffffffc,true;
    "aarch32_test_top_ldm_mc",0xe8900006,0xfffffff8,false;
    (* stmdb r0, {r1, r2}, whose lowest address is R0 less 8. *)
    "aarch32_test_wrap_stmdb_mc",0xe9000006,4,true;
    "aarch32_test_top_stmdb_mc",0xe9000006,0,false;
    (* ldrdne r4, r5, [r0] with Z set: nothing is transferred, at an
       unaligned address, but one past the top still leaves the model. *)
    "aarch32_test_skipped_ldrd_mc",0x11c040d0,0xfffffff5,false;
    "aarch32_test_skipped_wrap_mc",0x11c040d0,0xfffffffd,true] in
  [nostack; stack; literal; offset; before; untaken; rrx; skipped; sum;
   region4; shaped];;
