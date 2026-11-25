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
 * 64 words. A load or store goes through SP, which starts at the buffer's
 * middle, or through a register a case gives that address, at offsets that
 * stay inside the buffer, so the other registers take any value; one whose
 * condition fails, which transfers nothing, may go anywhere. A branch
 * lands 8 or 4 bytes before the instruction, or 8, 12, or 16 past it, where
 * the executor has a landing slot, and falling through lands at 4, as a
 * branch to there does too.
 *
 * The executor's greeting gives the instruction's and the buffer's addresses.
 * Each theorem assumes them of `pc` and the buffer, so that it can say what
 * an instruction that reads PC computes, and a case can put a landing slot's
 * address in a register or the buffer for BX or a load into PC to branch to.
 * The proof steps the instruction with both still symbolic, and only then
 * replaces them with the addresses.
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
 `val(word pc:int32) = slot_address /\
  val(scratchpointer:int32) = scratch_address
  ==> nonoverlapping (word pc,LENGTH ibytes) (scratchpointer,256)
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

(* Where the executor holds the instruction and the scratch buffer, from its
   greeting. *)
let aarch32_cosim_executor = lazy
  (start_cosim_executor "RIND_AARCH32_EXECUTOR"
    "qemu-arm -cpu cortex-a15 aarch32/proofs/cosim-runner" "aarch32" 84);;

let executor_address name =
  let prefix = name ^ "=" in
  let n = String.length prefix in
  let metadata = (Lazy.force aarch32_cosim_executor).cosim_metadata in
  match filter (fun s -> String.length s > n && String.sub s 0 n = prefix)
               metadata with
  | [s] -> int_of_string (String.sub s n (String.length s - n))
  | _ ->
      failwith ("AArch32 executor's greeting lacks " ^ prefix ^
                ": build it from this tree's cosim_runner.c and cosim_start.S");;

let slot_address = lazy (executor_address "slot");;
let scratch_address = lazy (executor_address "scratch");;

(* The input state with register `r`, any but SP and PC, or scratch word `i`,
   set to `v`. *)
let with_index index v input =
  List.mapi (fun j x -> if j = index then v else x) input;;

let with_register r = with_index (if r = 14 then 13 else r);;

let with_word i = with_index (20 + i);;

let with_carry c = with_index 16 (if c then num_1 else num_0);;

(* [cond:4; 000; opc:4; S; Rn:4; Rd:4; Rs:4; 0; type:2; 1; Rm:4] *)
let encode_dp_rsr cond opc s rn rd rs ty rm =
  (cond lsl 28) lor (opc lsl 21) lor (bit s lsl 20) lor (rn lsl 16) lor
  (rd lsl 12) lor (rs lsl 8) lor (ty lsl 5) lor (1 lsl 4) lor rm;;

(* A register-shifted register, whose amount is as often one of the edges, 0
   and 31 to 33, as any byte, under whatever the rest of Rs holds. *)
let make_dp_rsr_case input =
  let opc = Random.int 16 in
  let s,rd,rn = dp_fields opc in
  let rs = random_register () in
  let amount =
    if Random.bool () then el (Random.int 5) [0; 1; 31; 32; 33]
    else Random.int 256 in
  let high = Random.int 0x1000000 in
  { case_instruction =
      encode_dp_rsr (random_condition ()) opc s rn rd rs (Random.int 4)
        (random_register ());
    case_memop = false;
    case_input = with_register rs (num (high * 256 + amount)) input };;

(* R15 as the first operand of an immediate form, or as the first, the
   second, or both of a register form. *)
let make_dp_pc_case input =
  let opc = Random.int 16 in
  let s,rd,rn = dp_fields opc in
  let cond = random_condition () in
  let moves = opc = 13 || opc = 15 in
  let instruction =
    match Random.int 3 with
    | 0 when not moves ->
        encode_dp_imm cond opc s 15 rd (Random.int 16) (Random.int 256)
    | 1 when not moves ->
        encode_dp_reg cond opc s 15 rd (Random.int 32) (Random.int 4)
          (random_register ())
    | _ ->
        encode_dp_reg cond opc s
          (if moves then 0 else if Random.bool () then 15 else rn)
          rd (Random.int 32) (Random.int 4) 15 in
  { case_instruction = instruction; case_memop = false; case_input = input };;

(* MUL [cond:4; 0000000; S; Rd:4; 0000; Rm:4; 1001; Rn:4], and UMULL and
   UMLAL [cond:4; 000010; A; S; RdHi:4; RdLo:4; Rm:4; 1001; Rn:4], whose
   RdHi and RdLo differ. *)
let make_multiply_case input =
  let cond = random_condition () and rn = random_register ()
  and rm = random_register () and rd = random_register () in
  let instruction =
    if Random.int 3 = 0 then
      (cond lsl 28) lor (rd lsl 16) lor (rm lsl 8) lor (0b1001 lsl 4) lor rn
    else
      let rec other () =
        let r = random_register () in if r = rd then other () else r in
      (cond lsl 28) lor (1 lsl 23) lor (bit (Random.bool ()) lsl 21) lor
      (rd lsl 16) lor (other () lsl 12) lor (rm lsl 8) lor (0b1001 lsl 4) lor
      rn in
  { case_instruction = instruction; case_memop = false; case_input = input };;

(* REV [cond:4; 0110 1011 1111; Rd:4; 1111 0011; Rm:4], NOP, and DMB under
   each of its options. *)
let make_misc_case input =
  let instruction =
    match Random.int 4 with
    | 0 -> (random_condition () lsl 28) lor 0x0320f000
    | 1 -> 0xf57ff050 lor Random.int 16
    | _ -> (random_condition () lsl 28) lor 0x06bf0f30 lor
           (random_register () lsl 12) lor random_register () in
  { case_instruction = instruction; case_memop = false; case_input = input };;

(* How far from the instruction each of the executor's landing slots is. *)
let landings = [-8; -4; 4; 8; 12; 16];;

let random_landing () =
  num (Lazy.force slot_address + el (Random.int (length landings)) landings);;

let make_bl_case input =
  { case_instruction =
      (random_condition () lsl 28) lor (0b1011 lsl 24) lor
      el (Random.int (length branch_imm24s)) branch_imm24s;
    case_memop = false; case_input = input };;

(* BX to a landing slot, whose address the register holds. *)
let make_bx_case input =
  let rm = random_register () in
  { case_instruction = (random_condition () lsl 28) lor 0x012fff10 lor rm;
    case_memop = false;
    case_input = with_register rm (random_landing ()) input };;

(* [cond:4; 011; P; U; B; W; L; Rn:4; Rt:4; imm5:5; type:2; 0; Rm:4]: a load
   or store through SP with a register offset, under each shift. Rm holds
   what the shift takes to an offset inside the buffer, with bits the shift
   drops set at random. *)
let make_ldst_reg_case input =
  let byte = Random.bool () and load = Random.bool ()
  and p = Random.bool () and u = Random.bool () in
  let w = p && Random.bool () in
  let rm = random_register () in
  let rec rt () = let r = random_register () in if r = rm then rt () else r in
  (* One past the largest offset that keeps the access inside the buffer. *)
  let limit = if not u then 129 else if byte then 128 else 125 in
  let ty = Random.int 4 in
  let imm5,value,carry =
    match ty with
    | 0 ->
        let k = Random.int 4 in
        k,Random.int (((limit - 1) lsr k) + 1) +
          (if k = 0 then 0 else Random.int (1 lsl k) lsl (32 - k)),None
    | 1 | 2 ->
        (* imm5 of 0 shifts by 32, to no offset from a positive value. *)
        let k = Random.int 24 in
        if k = 0 then 0,Random.int 0x3fffffff,None
        else k,(Random.int limit lsl k) + Random.int (1 lsl k),None
    | _ ->
        (* imm5 of 0 is RRX, which shifts the carry in. *)
        let k = Random.int 32 and offset = Random.int limit in
        if k = 0 then 0,2 * offset + Random.int 2,Some false
        else k,((offset lsl k) lor (offset lsr (32 - k))) land 0xffffffff,
             None in
  let input = with_register rm (num value) input in
  let input = match carry with Some c -> with_carry c input | None -> input in
  { case_instruction =
      (random_condition () lsl 28) lor (0b011 lsl 25) lor (bit p lsl 24) lor
      (bit u lsl 23) lor (bit byte lsl 22) lor (bit w lsl 21) lor
      (bit load lsl 20) lor (13 lsl 16) lor (rt () lsl 12) lor (imm5 lsl 7) lor
      (ty lsl 5) lor rm;
    case_memop = true; case_input = input };;

(* [cond:4; 000; P; U; 1; W; 0; Rn:4; Rt:4; imm4H:4; 11; St; 1; imm4L:4]:
   LDRD and STRD through SP, Rt even and below R12, whose pair would end in
   SP, at a word-aligned offset, since any other faults. *)
let make_ldstd_case input =
  let store = Random.bool () and p = Random.bool () and u = Random.bool () in
  let w = p && Random.bool () in
  let imm8 = 4 * (if u then Random.int 31 else Random.int 33) in
  { case_instruction =
      (random_condition () lsl 28) lor (bit p lsl 24) lor (bit u lsl 23) lor
      (1 lsl 22) lor (bit w lsl 21) lor (13 lsl 16) lor
      (2 * Random.int 6 lsl 12) lor ((imm8 lsr 4) lsl 8) lor (0b1101 lsl 4) lor
      (bit store lsl 5) lor (imm8 land 15);
    case_memop = true; case_input = input };;

(* [cond:4; 100; P; U; 0; W; L; Rn:4; register_list:16]: LDM and STM in each
   addressing mode, of a random list of R0 to R12 and LR, through SP, or
   through another register that holds the address of the buffer's middle
   and is as often in the list as not, where it cannot be written back. *)
let random_register_list () =
  let rec go () =
    let l = Random.int 0x8000 land 0x5fff in if l = 0 then go () else l in
  go ();;

let encode_ldstm cond p u w l rn list =
  (cond lsl 28) lor (0b100 lsl 25) lor (bit p lsl 24) lor (bit u lsl 23) lor
  (bit w lsl 21) lor (bit l lsl 20) lor (rn lsl 16) lor list;;

let make_ldstm_case input =
  let cond = random_condition () and p = Random.bool () and u = Random.bool ()
  and load = Random.bool () and list = random_register_list () in
  if Random.bool () then
    { case_instruction = encode_ldstm cond p u (Random.bool ()) load 13 list;
      case_memop = true; case_input = input }
  else
    let rn = random_register () in
    let list = if Random.bool () then list lor (1 lsl rn) else list in
    let w = list land (1 lsl rn) = 0 && Random.bool () in
    { case_instruction = encode_ldstm cond p u w load rn list;
      case_memop = true;
      case_input =
        with_register rn (num (Lazy.force scratch_address + 128)) input };;

let popcount n =
  let rec go n c = if n = 0 then c else go (n lsr 1) (c + (n land 1)) in
  go n 0;;

(* LDM through SP of a list that ends in PC, and LDR into PC, each from a
   word of the buffer that holds a landing slot's address. *)
let make_load_pc_case input =
  if Random.bool () then
    let p = Random.bool () and u = Random.bool () in
    let list = (Random.int 0x8000 land 0x5fff) lor 0x8000 in
    let n = popcount list in
    (* PC's word: the highest the instruction reads. *)
    let top =
      if u then 128 + 4 * (n - 1) + (if p then 4 else 0)
      else 128 - (if p then 4 else 0) in
    { case_instruction =
        encode_ldstm (random_condition ()) p u (Random.bool ()) true 13 list;
      case_memop = false;
      case_input = with_word (top / 4) (random_landing ()) input }
  else
    let p = Random.bool () and u = Random.bool () in
    let w = p && Random.bool () in
    let imm12 = 4 * (if u then Random.int 32 else Random.int 33) in
    let at = if p then (if u then 128 + imm12 else 128 - imm12) else 128 in
    { case_instruction =
        encode_ldst (random_condition ()) p u false w true 13 15 imm12;
      case_memop = false;
      case_input = with_word (at / 4) (random_landing ()) input };;

(* A literal load of one of the buffer's 64 words that follow the
   instruction closely enough for its 12-bit offset. *)
let make_literal_case input =
  let reach = Lazy.force scratch_address - (Lazy.force slot_address + 8) in
  let words = min 64 ((4096 - reach) / 4) in
  if reach < 0 || reach mod 4 <> 0 || words <= 0 then
    failwith "AArch32 executor's buffer is out of a literal load's reach";
  { case_instruction =
      encode_ldst (random_condition ()) true true false false true 15
        (random_register ()) (reach + 4 * Random.int words);
    case_memop = false; case_input = input };;

(* Whether condition `cond` holds of an input state's flags, NZCV at inputs
   14 to 17, as ConditionHolds says. *)
let condition_holds cond input =
  let flag i = el (14 + i) input = num_1 in
  let n = flag 0 and z = flag 1 and c = flag 2 and v = flag 3 in
  let base =
    match cond lsr 1 with
    | 0 -> z | 1 -> c | 2 -> n | 3 -> v | 4 -> c && not z
    | 5 -> n = v | 6 -> n = v && not z | _ -> true in
  if cond land 1 = 1 && cond <> 15 then not base else base;;

(* A load or store whose condition fails, through a register that holds any
   address from 64 KiB to 64 KiB short of the top: the CPU transfers
   nothing, so the instruction does not fault, though its address may be
   unaligned or unmapped, and none of these offsets runs it past 0xffffffff,
   which would leave the model. LDR, LDRB, STR, STRB, and LDR into PC with an
   immediate offset, LDRD and STRD, and LDM and STM, with PC in a load's list
   half the time. *)
let make_skipped_case input =
  let rec failing () =
    let cond = Random.int 14 in
    if condition_holds cond input then failing () else cond in
  let cond = failing () and rn = random_register () in
  let input =
    with_register rn
      (num 0x10000 +/ mod_num (random32 32) (num 0xfffe0000)) input in
  let rec other () =
    let r = random_register () in if r = rn then other () else r in
  let p = Random.bool () and u = Random.bool () in
  let instruction =
    match Random.int 3 with
    | 0 ->
        let load = Random.bool () in
        let rt = if load && Random.int 4 = 0 then 15 else other () in
        encode_ldst cond p u (rt <> 15 && Random.bool ()) false load rn rt
          (Random.int 4096)
    | 1 ->
        let rec even () =
          let r = 2 * Random.int 6 in
          if r = rn || r + 1 = rn then even () else r in
        let imm8 = Random.int 256 in
        (cond lsl 28) lor (bit p lsl 24) lor (bit u lsl 23) lor (1 lsl 22) lor
        (rn lsl 16) lor (even () lsl 12) lor ((imm8 lsr 4) lsl 8) lor
        (0b1101 lsl 4) lor (bit (Random.bool ()) lsl 5) lor (imm8 land 15)
    | _ ->
        let load = Random.bool () in
        let list = random_register_list () lor
                   (if load && Random.bool () then 0x8000 else 0) in
        encode_ldstm cond p u false load rn list in
  { case_instruction = instruction; case_memop = true; case_input = input };;

let caseclasses =
  [make_dp_reg_case; make_dp_imm_case; make_movw_movt_case;
   make_branch_case; make_ldst_case; make_dp_rsr_case; make_dp_pc_case;
   make_multiply_case; make_misc_case; make_bl_case; make_bx_case;
   make_ldst_reg_case; make_ldstd_case; make_ldstm_case; make_load_pc_case;
   make_literal_case; make_skipped_case];;

let make_case kind =
  el kind caseclasses (make_input_state (Random.int 65));;

(* Edges the random cases reach only by chance: the shifts whose imm5 of 0
   means 32 or RRX, a register's shift by 0, 32, 33, and 255 places, the
   carries and overflows of the arithmetic, UMLAL's largest sum, a backward
   branch's sign-extended offset, word transfers that straddle two of the
   buffer's words, whose bytes differ so a misplaced one shows, a push and a
   load of every register a list can name here, and skipped transfers at an
   address that would fault. *)
let directed_input assignments =
  let base = map (fun _ -> num_0) (0--13) @ map (fun _ -> num_0) (1--4) @
             [num 128; num_0] @ map (fun _ -> num_0) (0--63) in
  itlist (fun (i,v) state ->
            List.mapi (fun j x -> if j = i then v else x) state)
    assignments base;;

let directed_cases =
  let dp opc s rn rd imm5 ty rm assignments =
    { case_instruction = encode_dp_reg 14 opc s rn rd imm5 ty rm;
      case_memop = false; case_input = directed_input assignments }
  and rsr ty assignments =
    { case_instruction = encode_dp_rsr 14 13 true 0 0 2 ty 1;
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
     case_input = directed_input [] };
   (* MOVS R0, R1, LSL R2 by 32: the carry is bit 0 and the result zero. *)
   rsr 0 [1,num 1; 2,num 32];
   (* By 33: the carry is clear too. *)
   rsr 0 [1,num 0xffffffff; 2,num 33; 16,num 1];
   (* MOVS R0, R1, LSR R2 by 0, under a set bit 8: nothing changes. *)
   rsr 1 [1,num 5; 2,num 0x100; 16,num 1];
   (* MOVS R0, R1, ASR R2 by 255: the sign fills the result and the carry. *)
   rsr 2 [1,num 0x80000000; 2,num 0xffffffff];
   (* MOVS R0, R1, ROR R2 by 32: the value stays and the carry is bit 31. *)
   rsr 3 [1,num 0x80000001; 2,num 32];
   (* UMLAL R0, R1, R2, R3: 0xffffffff squared plus 2^64 - 1 wraps. *)
   { case_instruction = 0xe0a10392; case_memop = false;
     case_input = directed_input
       [0,num 0xffffffff; 1,num 0xffffffff; 2,num 0xffffffff;
        3,num 0xffffffff] };
   (* STMDB SP!, {R0-R12, LR} and LDMIB SP, {R0-R12, LR}. *)
   { case_instruction = 0xe92d5fff; case_memop = true;
     case_input = directed_input (map (fun i -> i,num (0x01010101 * (i + 1)))
                                      (0--13)) };
   { case_instruction = 0xe99d5fff; case_memop = true;
     case_input = directed_input (map (fun i -> 53 + i,num (0x01010101 * (i + 1)))
                                      (0--13)) };
   (* LDRDNE R4, R5, [R0] and LDMNE R0, {R4, PC} with Z set and R0 at
      0xfffffff5: unaligned and unmapped, but skipped. *)
   { case_instruction = 0x11c040d0; case_memop = true;
     case_input = directed_input [0,num 0xfffffff5; 15,num 1] };
   { case_instruction = 0x18908010; case_memop = true;
     case_input = directed_input [0,num 0xfffffff5; 15,num 1] }] @
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
     false,true,false,1] @
  (* LDR R1, [SP, R0, LSR #k] with R0 holding an address in the buffer, which
     the proof restates as the buffer's offset, shifted to a small offset. *)
  (let a = Lazy.force scratch_address + 128 in
   let rec shift k = if a lsr k < 125 then k else shift (k + 1) in
   let k = shift 1 in
   [{ case_instruction = 0xe79d1020 lor (k lsl 7); case_memop = true;
      case_input = directed_input [0,num a] }]);;

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

(* Replaces `pc` and the buffer with the executor's addresses, in the goal
   and in what is known of the state before the instruction. *)
let AARCH32_ADDRESSES_TAC =
  let rule = REWRITE_RULE[WORD_VAL] o AP_TERM `word:num->int32` in
  USE_THEN "slot" (fun slot -> USE_THEN "scratch" (fun scratch ->
    let ths = [WORD_ADD; rule slot; rule scratch] in
    RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV ths THENC WORD_REDUCE_CONV)) THEN
    REWRITE_TAC ths THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[]));;

(* The buffer is word-aligned, which LDRD, STRD, LDM, and STM need of SP. *)
let AARCH32_SCRATCH_ALIGNED_TAC =
  USE_THEN "scratch" (fun scratch ->
    let eq = REWRITE_RULE[WORD_VAL] (AP_TERM `word:num->int32` scratch) in
    let th = AP_TERM `aligned 4:int32->bool` eq in
    ASSUME_TAC(EQ_MP (SYM th)
     (EQT_ELIM(AARCH32_ALIGNED_NUMERAL_CONV(rhs(concl th))))));;

(* What is known of each of the buffer's words, restated at the word's
   offset from `pc`, where a literal load reads it. *)
let AARCH32_LITERALS_TAC =
  let rule = REWRITE_RULE[WORD_VAL] o AP_TERM `word:num->int32`
  and plus = `(+):num->num->num` and word = `word:num->int32` in
  USE_THEN "slot" (fun slot -> USE_THEN "scratch" (fun scratch ->
    let ths = [WORD_ADD; rule slot; rule scratch]
    and delta = Lazy.force scratch_address - Lazy.force slot_address in
    let relocate th =
      match concl th with
        Comb(Comb(Const("=",_),
          Comb(Comb(Const("read",_),
            Comb(Comb(Const(":>",_),Const("memory",_)),
                 Comb(Const("bytes32",_),a))),_)),_) ->
          let k =
            match a with
              Var("scratchpointer",_) -> 0
            | Comb(Comb(Const("word_add",_),Var("scratchpointer",_)),
                   Comb(Const("word",_),n)) -> dest_small_numeral n
            | _ -> failwith "relocate" in
          let a' = mk_comb(word,
            mk_comb(mk_comb(plus,`pc:num`),mk_small_numeral(delta + k))) in
          let eq = EQT_ELIM
           ((REWRITE_CONV ths THENC WORD_REDUCE_CONV) (mk_eq(a,a'))) in
          ASSUME_TAC(CONV_RULE
           (LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV(K eq))))) th)
      | _ -> failwith "relocate" in
    EVERY_ASSUM (fun th -> try relocate th with Failure _ -> ALL_TAC)));;

(* A register that holds an address in the buffer, restated as its offset
   from the buffer, as SP's is, so that what it reaches is the buffer's. *)
let AARCH32_SCRATCH_REGISTERS_TAC =
  let rule = REWRITE_RULE[WORD_VAL] o AP_TERM `word:num->int32`
  and word = `word:num->int32` in
  USE_THEN "scratch" (fun scratch ->
    let scratch_th = rule scratch
    and base = Lazy.force scratch_address in
    RULE_ASSUM_TAC (fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(_,_)),_)),
             Comb(Const("word",_),n))
          when is_numeral n && dest_numeral n >=/ num base &&
               dest_numeral n <=/ num (base + 256) ->
            let k = Num.int_of_num (dest_numeral n) - base in
            let address =
              if k = 0 then `scratchpointer:int32`
              else mk_comb(mk_comb(`word_add:int32->int32->int32`,
                                   `scratchpointer:int32`),
                           mk_comb(word,mk_small_numeral k)) in
            let eq = EQT_ELIM
             ((REWRITE_CONV[scratch_th] THENC WORD_REDUCE_CONV)
              (mk_eq(rand(concl th),address))) in
            CONV_RULE(RAND_CONV(K eq)) th
      | _ -> th));;

let tac_before memop literal =
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "slot") (LABEL_TAC "scratch")) THEN
  AARCH32_SCRATCH_ALIGNED_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[aarch32_regfile; CONS_11; VAL_WORD_GALOIS;
              BITVAL_EQ_0; BITVAL_EQ_1] THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ENSURES_INIT_TAC "s0" THEN
  AARCH32_SCRATCH_REGISTERS_TAC THEN
  (if memop then MAP_EVERY AARCH32_MEMORY_SPLIT_TAC (1--4) else ALL_TAC) THEN
  (if literal then AARCH32_LITERALS_TAC else ALL_TAC)
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
  AARCH32_ADDRESSES_TAC THEN
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
         mk_flist (map mk_numeral output_state),`output_state:num list`;
         mk_small_numeral (Lazy.force slot_address),`slot_address:num`;
         mk_small_numeral (Lazy.force scratch_address),`scratch_address:num`]
        template in
      let execth = AARCH32_MK_EXEC_RULE (REFL ibyteterm) in
      let decoded =
        match (snd execth).(0) with
        | Some th -> rand (rand (snd (strip_forall (concl th))))
        | None ->
            failwith (Printf.sprintf
              "AArch32 simulator: case %08x does not decode"
              test_case.case_instruction) in
      let proof_tactic =
        PURE_REWRITE_TAC [fst execth] THEN
        tac_before test_case.case_memop
          (* LDR with R15 as its base. *)
          (test_case.case_instruction land 0x0e1f0000 = 0x041f0000) THEN
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
