(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Random-instruction cosimulation of the instructions x86.patch adds to     *)
(* s2n-bignum's x86 model, against this CPU.                                 *)
(* ========================================================================= *)

(* s2n-bignum's simulator checks each case: it runs the instruction on a
   random state on the CPU and proves, in the model, that the model reaches
   the state the CPU did, all of every YMM register included. Loading it runs
   s2n-bignum's own campaign, which admin/prove limits to one case. The cases
   here are 20 rounds of a random encoding of each form of each added
   instruction: random registers, extended ones included, immediates, VEX
   widths and ignored W bits, and the memory forms on [rsp + disp8], 16-byte
   aligned for the legacy SSE forms that require it. RSP itself is never an
   operand, since the model's is symbolic. The F3 prefix the patch lets RET
   take is not cosimulated, since RET leaves the simulator's harness. *)

loadt "x86/proofs/simulator.ml";;

let rnd n = Random.int n;;

let rex w r b = 0x40 lor (w lsl 3) lor ((r lsr 3) lsl 2) lor (b lsr 3);;

let modrm md reg rm = (md lsl 6) lor ((reg land 7) lsl 3) lor (rm land 7);;

(* 66 [REX] <opcode> with ModRM fields reg and rm, the REX byte also present
   at random where nothing needs it. *)
let sse ?(w=0) opcode md reg rm tail =
  let pre = if w = 1 || reg > 7 || rm > 7 || rnd 4 = 0
            then [rex w reg rm] else [] in
  [0x66] @ pre @ opcode @ [modrm md reg rm] @ tail;;

(* A three-byte VEX prefix for the 0F (1), 0F38 (2) or 0F3A (3) map with
   the 66 prefix. *)
let vex map w v l opcode md reg rm tail =
  [0xc4; ((1 - reg / 8) lsl 7) lor (1 lsl 6) lor ((1 - rm / 8) lsl 5) lor map;
   (w lsl 7) lor (((lnot v) land 15) lsl 3) lor (l lsl 2) lor 1;
   opcode; modrm md reg rm] @ tail;;

(* A random register other than RSP. *)
let gpr () = let r = rnd 15 in if r >= 4 then r + 1 else r;;

(* An immediate, half the time below 40 to cover each shift and selector. *)
let imm () = if rnd 2 = 0 then rnd 40 else rnd 256;;

(* Register forms, run as cosimulate_instructions None 0. *)
let register_forms = [
  (fun () -> sse [0x0f; 0x3a; 0x0f] 3 (rnd 16) (rnd 16) [imm ()]); (* PALIGNR *)
  (fun () -> vex 3 (rnd 2) (rnd 16) (rnd 2) 0x0f 3 (rnd 16) (rnd 16)
               [imm ()]);                                      (* VPALIGNR *)
  (fun () -> sse [0x0f; 0x72] 3 6 (rnd 16) [imm ()]);          (* PSLLD *)
  (fun () -> sse [0x0f; 0x72] 3 2 (rnd 16) [imm ()]);          (* PSRLD *)
  (fun () -> sse [0x0f; 0x73] 3 7 (rnd 16) [imm ()]);          (* PSLLDQ *)
  (fun () -> sse [0x0f; 0x73] 3 3 (rnd 16) [imm ()]);          (* PSRLDQ *)
  (fun () -> sse [0x0f; 0x3a; 0x20] 3 (rnd 16) (gpr ()) [imm ()]); (* PINSRB *)
  (fun () -> sse [0x0f; 0x3a; 0x14] 3 (rnd 16) (gpr ()) [imm ()]); (* PEXTRB *)
  (fun () -> sse ~w:1 [0x0f; 0x3a; 0x16] 3 (rnd 16) (gpr ())
               [imm ()]);                                      (* PEXTRQ *)
  (fun () -> sse [0x0f; 0xeb] 3 (rnd 16) (rnd 16) []);         (* POR *)
  (fun () -> sse [0x0f; 0x62] 3 (rnd 16) (rnd 16) []);         (* PUNPCKLDQ *)
  (fun () -> sse [0x0f; 0x6a] 3 (rnd 16) (rnd 16) []);         (* PUNPCKHDQ *)
  (fun () -> sse [0x0f; 0x6c] 3 (rnd 16) (rnd 16) []);         (* PUNPCKLQDQ *)
  (fun () -> sse [0x0f; 0x6d] 3 (rnd 16) (rnd 16) []);         (* PUNPCKHQDQ *)
];;

(* Memory forms on [rsp + d], run as cosimulate_instructions (Some 0) 32:
   ModRM rm 100 with mod 01 takes a SIB byte, 0x24 for base RSP and no
   index, then disp8. *)
let mem d = [0x24; d];;

let aligned () = 16 * rnd 8;;

let memory_forms = [
  (fun () -> sse [0x0f; 0x3a; 0x20] 1 (rnd 16) 4
               (mem (rnd 128) @ [imm ()]));                    (* PINSRB m8 *)
  (fun () -> sse [0x0f; 0x3a; 0x14] 1 (rnd 16) 4
               (mem (rnd 128) @ [imm ()]));                    (* PEXTRB m8 *)
  (fun () -> sse ~w:1 [0x0f; 0x3a; 0x16] 1 (rnd 16) 4
               (mem (rnd 128) @ [imm ()]));                    (* PEXTRQ m64 *)
  (fun () -> vex 2 0 0 1 0x5a 1 (rnd 16) 4
               (mem (rnd 128)));                         (* VBROADCASTI128 m128 *)
  (fun () -> vex 3 (rnd 2) (rnd 16) (rnd 2) 0x0f 1 (rnd 16) 4
               (mem (rnd 128) @ [imm ()]));                    (* VPALIGNR m *)
  (fun () -> sse [0x0f; 0x3a; 0x0f] 1 (rnd 16) 4
               (mem (aligned ()) @ [imm ()]));                 (* PALIGNR m128 *)
  (fun () -> sse [0x0f; 0xeb] 1 (rnd 16) 4 (mem (aligned ())));   (* POR *)
  (fun () -> sse [0x0f; 0x62] 1 (rnd 16) 4 (mem (aligned ())));   (* PUNPCKLDQ *)
  (fun () -> sse [0x0f; 0x6a] 1 (rnd 16) 4 (mem (aligned ())));   (* PUNPCKHDQ *)
  (fun () -> sse [0x0f; 0x6c] 1 (rnd 16) 4 (mem (aligned ())));   (* PUNPCKLQDQ *)
  (fun () -> sse [0x0f; 0x6d] 1 (rnd 16) 4 (mem (aligned ())));   (* PUNPCKHQDQ *)
];;

let rind_cosim memop add_assum form =
  let ibytes = form () in
  let decoded,result = cosimulate_instructions memop add_assum [ibytes] in
  if result then
    (Format.print_string ("OK: " ^ string_of_term decoded);
     Format.print_newline ())
  else failwith ("cosimulation disagrees: " ^ string_of_term decoded);;

let rind_cosim_rounds = 20;;

for round = 1 to rind_cosim_rounds do
  do_list (rind_cosim None 0) register_forms;
  do_list (rind_cosim (Some 0) 32) memory_forms
done;;

Printf.printf "cosimulated %d cases\n"
  (rind_cosim_rounds * (length register_forms + length memory_forms));;
