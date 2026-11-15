(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Cosimulation tests for the AArch32 model, after riscv/proofs/simulator.ml.
 *
 * Each case is one A32 instruction from the model's decoder, with a random
 * condition, and a random machine state. The executor, cosim_runner.c on an
 * Armv7-A CPU or under qemu-arm, runs it, and the model must then prove that
 * the same input reaches exactly the state the executor returned:
 *
 *   choose case -> execute concrete state -> instantiate theorem -> prove
 *                                                        symbolic agreement
 *
 * The transport holds R0-R12, LR, the four flags, SP's offset into a private
 * 256-byte scratch buffer, PC's offset from the instruction, and the buffer's
 * 64 words. SP starts at the buffer's middle and is the base of every load and
 * store, whose offsets stay inside the buffer, so the other registers take any
 * value. A branch lands 8 or 4 bytes before the instruction, or 8, 12, or 16
 * past it, where the executor has a landing slot, and falling through lands
 * at 4, as a branch to there does too.
 *)

needs "common/cosim.ml";;
needs "common/sematest.ml";;
needs "aarch32/proofs/base.ml";;

let aarch32_regfile =
  let regs = ["R0";"R1";"R2";"R3";"R4";"R5";"R6";"R7";"R8";"R9";"R10";
              "R11";"R12";"LR"]
  and flags = ["NF";"ZF";"CF";"VF"]
  and memory i =
    if i = 0 then "val(read (memory :> bytes32 scratch) s)"
    else Printf.sprintf
      "val(read (memory :> bytes32(word_add scratch (word %d))) s)" (4 * i) in
  new_definition (parse_term
   ("aarch32_regfile (pc:num) (scratch:int32) (s:aarch32state) = [" ^
    String.concat "; "
     (map (fun r -> "val(read " ^ r ^ " s)") regs @
      map (fun f -> "bitval(read " ^ f ^ " s)") flags @
      ["val(word_sub (read SP s) scratch)";
       "val(word_sub (read PC s) (word pc))"] @
      map memory (0--63)) ^ "]"));;

let template =
 `nonoverlapping (word pc,LENGTH ibytes) (scratchpointer,256)
  ==> ensures aarch32
       (\s. aligned_bytes_loaded s (word pc) ibytes /\
            read PC s = word pc /\
            read SP s = word_add scratchpointer (word 128) /\
            aarch32_regfile pc scratchpointer s = input_state)
       (\s. aarch32_regfile pc scratchpointer s = output_state)
       (MAYCHANGE [PC; R0; R1; R2; R3; R4; R5; R6; R7; R8; R9; R10; R11;
                   R12; SP; LR] ,,
        MAYCHANGE [NF; ZF; CF; VF] ,,
        MAYCHANGE [memory :> bytes(scratchpointer,256)] ,,
        MAYCHANGE [events])`;;

let random_boold d = Random.int 64 < d;;

let randomnd n density =
  funpow n
    (fun value ->
      (if random_boold density then num_1 else num_0) +/ num_2 */ value)
    num_0;;

let random32 density = randomnd 32 density;;

let instruction_bytes instruction =
  [instruction land 0xff;
   (instruction lsr 8) land 0xff;
   (instruction lsr 16) land 0xff;
   (instruction lsr 24) land 0xff];;

(* Any register but SP and PC. *)
let random_register () =
  let register = Random.int 14 in
  if register = 13 then 14 else register;;

(* AL half the time, so unconditional forms get as many cases as the
   fourteen conditions together. *)
let random_condition () =
  if Random.bool () then 14 else Random.int 14;;

let random_flag () = if Random.bool () then num_1 else num_0;;

let make_input_state density =
  map (fun _ -> random32 density) (0--13) @
  map (fun _ -> random_flag ()) (1--4) @
  [num 128; num_0] @
  map (fun _ -> random32 density) (0--63);;

type aarch32_test_case =
 { case_instruction: int;
   case_memop: bool;
   case_input: num list };;

let bit b = if b then 1 else 0;;

(* [cond:4; 000; opc:4; S; Rn:4; Rd:4; imm5:5; type:2; 0; Rm:4] *)
let encode_dp_reg cond opc s rn rd imm5 ty rm =
  (cond lsl 28) lor (opc lsl 21) lor (bit s lsl 20) lor (rn lsl 16) lor
  (rd lsl 12) lor (imm5 lsl 7) lor (ty lsl 5) lor rm;;

(* [cond:4; 001; opc:4; S; Rn:4; Rd:4; rot:4; imm8:8] *)
let encode_dp_imm cond opc s rn rd rot imm8 =
  (cond lsl 28) lor (1 lsl 25) lor (opc lsl 21) lor (bit s lsl 20) lor
  (rn lsl 16) lor (rd lsl 12) lor (rot lsl 8) lor imm8;;

(* [cond:4; 010; P; U; B; W; L; Rn:4; Rt:4; imm12:12] *)
let encode_ldst cond p u b w l rn rt imm12 =
  (cond lsl 28) lor (1 lsl 26) lor (bit p lsl 24) lor (bit u lsl 23) lor
  (bit b lsl 22) lor (bit w lsl 21) lor (bit l lsl 20) lor (rn lsl 16) lor
  (rt lsl 12) lor imm12;;

(* A data-processing opcode with its S, Rd, and Rn fields: the compares and
   tests always set flags and have Rd zero, and the moves have Rn zero. *)
let dp_fields opc =
  let s = Random.bool () and rd = random_register ()
  and rn = random_register () in
  if opc >= 8 && opc <= 11 then true,0,rn
  else if opc = 13 || opc = 15 then s,rd,0
  else s,rd,rn;;

let make_dp_reg_case input =
  let opc = Random.int 16 in
  let s,rd,rn = dp_fields opc in
  { case_instruction =
      encode_dp_reg (random_condition ()) opc s rn rd (Random.int 32)
        (Random.int 4) (random_register ());
    case_memop = false; case_input = input };;

let make_dp_imm_case input =
  let opc = Random.int 16 in
  let s,rd,rn = dp_fields opc in
  { case_instruction =
      encode_dp_imm (random_condition ()) opc s rn rd (Random.int 16)
        (Random.int 256);
    case_memop = false; case_input = input };;

(* MOVW (opc 8) and MOVT (opc 10): the compare opcodes without S. *)
let make_movw_movt_case input =
  let opc = if Random.bool () then 8 else 10 in
  { case_instruction =
      encode_dp_imm (random_condition ()) opc false (Random.int 16)
        (random_register ()) (Random.int 16) (Random.int 256);
    case_memop = false; case_input = input };;

(* B's imm24 for each of the executor's landing slots, from 8 bytes back to
   16 on, the PC bias of 8 included; -2 would branch to itself. *)
let branch_imm24s = [0xfffffc; 0xfffffd; 0xffffff; 0; 1; 2];;

let encode_branch cond imm24 = (cond lsl 28) lor (0b1010 lsl 24) lor imm24;;

let make_branch_case input =
  { case_instruction =
      encode_branch (random_condition ())
        (el (Random.int (length branch_imm24s)) branch_imm24s);
    case_memop = false; case_input = input };;

(* A load or store through SP, at the buffer's middle, whose address, and
   whose written-back SP, stay inside the buffer. A word's offset may be
   unaligned, as the model allows. *)
let make_ldst_case input =
  let byte = Random.bool () and load = Random.bool ()
  and p = Random.bool () and u = Random.bool () in
  let w = p && Random.bool () in
  let imm12 =
    if byte then (if u then Random.int 128 else Random.int 129)
    else if u then Random.int 125 else Random.int 129 in
  { case_instruction =
      encode_ldst (random_condition ()) p u byte w load 13
        (random_register ()) imm12;
    case_memop = true; case_input = input };;

let caseclasses =
  [make_dp_reg_case; make_dp_imm_case; make_movw_movt_case;
   make_branch_case; make_ldst_case];;

let make_case kind =
  el kind caseclasses (make_input_state (Random.int 65));;

(* Edges the random cases reach only by chance: the shifts whose imm5 of 0
   means 32 or RRX, the carries and overflows of the arithmetic, a backward
   branch's sign-extended offset, and word transfers that straddle two of the
   buffer's words, whose bytes differ so a misplaced one shows. *)
let directed_input assignments =
  let base = map (fun _ -> num_0) (0--13) @ map (fun _ -> num_0) (1--4) @
             [num 128; num_0] @ map (fun _ -> num_0) (0--63) in
  itlist (fun (i,v) state ->
            List.mapi (fun j x -> if j = i then v else x) state)
    assignments base;;

let directed_cases =
  let dp opc s rn rd imm5 ty rm assignments =
    { case_instruction = encode_dp_reg 14 opc s rn rd imm5 ty rm;
      case_memop = false; case_input = directed_input assignments } in
  [(* MOVS R0, R1, LSR #32: the carry is bit 31 and the result zero. *)
   dp 13 true 0 0 0 1 1 [1,num 0x80000001];
   (* MOVS R0, R1, ASR #32: the sign fills the result. *)
   dp 13 true 0 0 0 2 1 [1,num 0x80000000];
   (* MOVS R0, R1, RRX, with the carry set. *)
   dp 13 true 0 0 0 3 1 [1,num 1; 16,num 1];
   (* ADDS R0, R1, R2: unsigned and signed overflow at once. *)
   dp 4 true 1 0 0 0 2 [1,num 0x80000000; 2,num 0x80000000];
   (* ADCS R0, R1, R2: 0xffffffff + 0 + C carries out. *)
   dp 5 true 1 0 0 0 2 [1,num 0xffffffff; 16,num 1];
   (* SBCS R0, R1, R2: 0 - 0 - !C borrows. *)
   dp 6 true 1 0 0 0 2 [];
   (* RSCS R0, R1, R2: 0x7fffffff - 0xffffffff - !C overflows. *)
   dp 7 true 1 0 0 0 2 [1,num 0xffffffff; 2,num 0x7fffffff; 16,num 1];
   (* CMP R1, R2 with equal operands: Z and C set. *)
   dp 10 true 1 0 0 0 2 [1,num 0x12345678; 2,num 0x12345678];
   (* B to 8 bytes before itself. *)
   { case_instruction = encode_branch 14 0xfffffc; case_memop = false;
     case_input = directed_input [] }] @
  (* LDR R0, [SP, #1]; LDR R0, [SP, #-2]!; STR R1, [SP, #3];
     STR R1, [SP, #-1]!. Inputs 51 to 53 are the words at SP-4, SP, and
     SP+4. *)
  map (fun (u,w,load,imm12) ->
         { case_instruction =
             encode_ldst 14 true u false w load 13 (if load then 0 else 1)
               imm12;
           case_memop = true;
           case_input = directed_input
             [1,num 0xddccbbaa; 51,num 0x03020100; 52,num 0x07060504;
              53,num 0x0b0a0908] })
    [true,false,true,1; false,true,true,2; true,false,false,3;
     false,true,false,1];;

let aarch32_cosim_executor = lazy
  (start_cosim_executor "RIND_AARCH32_EXECUTOR"
    "qemu-arm -cpu cortex-a15 aarch32/proofs/cosim-runner" "aarch32" 84);;

let AARCH32_MEMORY_SPLIT_TAC k =
  let tac =
    STRIP_ASSUME_TAC o
    CONV_RULE (BINOP_CONV(BINOP2_CONV
       (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) WORD_REDUCE_CONV)) o
    GEN_REWRITE_RULE I [el k (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] in
  EVERY_ASSUM (fun th -> try tac th with Failure _ -> ALL_TAC);;

let AARCH32_OFFSET_RULES = map (fun t -> WORD_RULE t)
 [`!x y:int32. word_sub (word_add x y) x = y`;
  `!x:int32. word_sub x x = word 0`;
  `!a b. word_sub (word(a + b)) (word a):int32 = word b`];;

let tac_before memop =
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[aarch32_regfile; CONS_11; VAL_WORD_GALOIS;
              BITVAL_EQ_0; BITVAL_EQ_1] THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ENSURES_INIT_TAC "s0" THEN
  (if memop then MAP_EVERY AARCH32_MEMORY_SPLIT_TAC (1--4) else ALL_TAC)
and tac_main memop execth =
  if memop then AARCH32_VSTEPS_TAC execth [1]
  else AARCH32_STEPS_TAC execth [1]
and tac_after memop =
  (if memop then MAP_EVERY AARCH32_MEMORY_SPLIT_TAC (0--4) else ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (if memop then CONV_TAC(ONCE_DEPTH_CONV READ_MEMORY_FULLMERGE_CONV)
   else ALL_TAC) THEN
  REWRITE_TAC AARCH32_OFFSET_RULES THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC WORD_NUM_RED_CONV ORELSEC
                      INT_RED_CONV ORELSEC NUM_RED_CONV)) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  TRY(MONOTONE_MAYCHANGE_TAC) THEN
  PRINT_GOAL_TAC THEN NO_TAC;;

let cosimulate_case test_case =
  let bytes = instruction_bytes test_case.case_instruction in
  let ibyteterm =
    mk_flist
      (map (curry mk_comb `word:num->byte` o mk_small_numeral) bytes) in
  let execution =
    cosim_execute (Lazy.force aarch32_cosim_executor)
      (cosim_hex_of_bytes bytes)
      (map string_of_num test_case.case_input) in
  match execution with
  | Cosim_trap details ->
      Printf.printf "Unexpected AArch32 trap: %s\n"
        (String.concat " " details);
      mk_numeral (num test_case.case_instruction),false
  | Cosim_ok output_words ->
      let output_state = map num_of_string output_words in
      let goal = subst
        [ibyteterm,`ibytes:byte list`;
         mk_flist (map mk_numeral test_case.case_input),
         `input_state:num list`;
         mk_flist (map mk_numeral output_state),`output_state:num list`]
        template in
      let execth = AARCH32_MK_EXEC_RULE (REFL ibyteterm) in
      let decoded =
        (rand o rand o snd o strip_forall o concl o option_get)
          (snd execth).(0) in
      let proof_tactic =
        PURE_REWRITE_TAC [fst execth] THEN
        tac_before test_case.case_memop THEN
        tac_main test_case.case_memop execth THEN
        tac_after test_case.case_memop in
      let result =
        try
          ignore (prove (goal,proof_tactic));
          true
        with error ->
          Printf.printf "AArch32 proof failure: %s\n"
            (Printexc.to_string error);
          false in
      decoded,result;;

let instruction_kinds = length caseclasses;;
let time_limit_sec = sematest_seconds 2400.0;;
let case_limit = sematest_case_limit ();;

let run_case test_case count =
  let decoded,result = cosimulate_case test_case in
  if not result then begin
    Printf.printf "Error: %08x, term `%s`\n" test_case.case_instruction
      (string_of_term decoded);
    failwith "AArch32 simulator"
  end;
  Printf.printf "OK: %08x %s\n" test_case.case_instruction
    (string_of_term decoded);
  count + 1;;

let rec run_directed_cases start_time count cases =
  match cases with
  | [] -> count
  | test_case::rest ->
      let tested = run_case test_case count in
      if sematest_finished time_limit_sec case_limit start_time tested then
        tested
      else run_directed_cases start_time tested rest;;

let rec run_random_simulations start_time count =
  let kind = count mod instruction_kinds in
  let tested = run_case (make_case kind) count in
  if sematest_finished time_limit_sec case_limit start_time tested then
    tested
  else run_random_simulations start_time tested;;

(* The seed is S2N_BIGNUM_SEMATEST_SEED's, or else a fresh one, printed either
   way so a failing campaign can be rerun. *)
let aarch32_seed =
  match sematest_getenv "S2N_BIGNUM_SEMATEST_SEED" with
  | Some s -> int_of_string s
  | None -> Random.self_init (); Random.bits ();;

Printf.printf "AArch32 cosimulation seed %d\n" aarch32_seed;;
Random.init aarch32_seed;;

let start_time = Unix.gettimeofday () in
let tested = run_directed_cases start_time 0 directed_cases in
let tested =
  if sematest_finished time_limit_sec case_limit start_time tested then tested
  else run_random_simulations start_time tested in
  Printf.printf "Finished AArch32 cosimulation testing: %d cases\n" tested;
  close_cosim_executor (Lazy.force aarch32_cosim_executor);;
