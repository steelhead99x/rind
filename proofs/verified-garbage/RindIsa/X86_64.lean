import VerifiedGarbage.TCB.X86_64.Encode

/-!
# rind's extension of VG's x86_64 model

**Trusted.** VG's model (`VerifiedGarbage/TCB/X86_64/`) covers the
instructions VG's own code uses, and keeps the stack pointer to VG's nested
frames of under a page. aws-lc's Montgomery routines make their own frame:
they push the callee-saved registers, move `rsp` down past their scratch
space by `lea`, a page at a time with a probing load at each, and restore
`rsp` from a saved copy in one `lea`. They also use `neg`, `dec`, `ja`,
aligned `movdqa` to and from memory, and padding the assembler lays out.
This model is VG's with those added: its state is VG's with the lowest
address the stack may reach, its instructions are VG's, run by VG's
semantics, and those below, each transcribing the pseudocode of the Intel
SDM Vol. 2 the docs cite, in VG's style, so that the leakage model of
`TCB/Code.lean` applies unchanged: every memory access faults outside the
state's regions, and leaks its address.

The stack: the region at the head of `wr` is the part of the stack the
function has claimed, from `rsp` up. A push or a `lea` that lowers `rsp`
grows it down to the new `rsp`, faulting below `lo`; a `lea` that raises
`rsp` shrinks it, and the bytes it releases are below the stack pointer,
where the system may change them, so they take values the model does not
know, as VG's `lose` gives them for a frame VG's model pops. So the
function reaches its stack only at or above `rsp`, as the System V ABI
lets it rely on, and only above `lo`, which its theorem states the stack
holds: a guard page below the stack is the system's, beyond the model.

`admin/prove vg` cosimulates each of these instructions against the CPU
(`Cosim/RindX86_64.lean`), and `admin/prove lean` checks that each program's bytes
(`layout`) are the ones rind's build emits.
-/

namespace Rind.X86_64

open VG VG.X86_64

/-- VG's machine state with `lo`, the lowest address the function's stack
may reach, which no instruction changes. -/
structure State where
  vg : VG.X86_64.State
  lo : Addr

/-- Branch conditions: VG's, and `ja`. -/
inductive Cond
  | vg (c : VG.X86_64.Cond)
  /-- `ja`: CF = 0 and ZF = 0 -/
  | a
  deriving DecidableEq, Repr

/-- SDM Vol. 2, "Jcc": A, "above (CF=0 and ZF=0)"; VG's for its own. `none`,
and so a fault, if a flag it reads is undefined. -/
def eval : Cond → VG.X86_64.State → Option Bool
  | .vg c, s => VG.X86_64.eval c s
  | .a, s => s.cf.bind fun c => s.zf.map fun z => !c && !z

inductive Instr
  /-- An instruction of VG's model, with VG's semantics. -/
  | vg (i : VG.X86_64.Instr)
  /-- `push r64` (`50+rd`), `r` not `rsp` -/
  | push (r : Reg)
  /-- `lea r64, m` (`REX.W 8D /r`), `d` not `rsp` -/
  | lea (d : Reg) (m : MemOp)
  /-- `lea rsp, m` (`REX.W 8D /r`): moves the stack pointer -/
  | leaRsp (m : MemOp)
  /-- `neg r64` (`REX.W F7 /3`) -/
  | neg (d : Reg)
  /-- `dec r64` (`REX.W FF /1`) -/
  | dec (d : Reg)
  /-- `movdqa xmm, XMMWORD PTR m` (`66 0F 6F /r`) -/
  | movdqaLoad (d : XReg) (m : MemOp)
  /-- `movdqa XMMWORD PTR m, xmm` (`66 0F 7F /r`) -/
  | movdqaStore (m : MemOp) (s : XReg)
  /-- The assembler's padding to the next multiple of `n` bytes, `n` a power
  of two up to 64, which runs as no instructions: see `padding`. -/
  | align (n : Nat)
  /-- `jmp` over the padding to the next multiple of `n` bytes (`EB cb`),
  then that padding: what aws-lc writes as `jmp L` before `.align n` and
  `L:`, which runs as no instructions. -/
  | jmpAlign (n : Nat)
  deriving DecidableEq, Repr

/-- The stack's claimed region, at the head of `wr`: its length, if it
starts at `rsp`. -/
def claimed (g : VG.X86_64.State) : Option Nat :=
  match g.wr with
  | r :: _ => if r.base = g.gpr .rsp then some r.len else none
  | [] => none

/-- Move `rsp` to `v`, growing or shrinking the claimed region (see the
module docs): `none` below `lo`, above the claimed region, or if it is not
at the head of `wr`. Released bytes are VG's `lose`'s, two of the state's
`unknowns` for each quadword or part of one. -/
def moveSp (s : State) (v : Addr) : Option State :=
  let g := s.vg
  let sp := g.gpr .rsp
  (claimed g).bind fun n =>
    if s.lo.toNat ≤ v.toNat ∧ v.toNat ≤ sp.toNat then
      some { s with vg := { g.setReg .rsp v with wr := ⟨v, n + (sp.toNat - v.toNat)⟩ :: g.wr.tail } }
    else if sp.toNat < v.toNat ∧ v.toNat - sp.toNat ≤ n then
      let d := v.toNat - sp.toNat
      some { s with vg := { g.setReg .rsp v with
        wr := ⟨v, n - d⟩ :: g.wr.tail, mem := lose g.mem sp d g.unknowns
        unknowns := fun i => g.unknowns (i + 2 * ((d + 7) / 8)) } }
    else none

/-- Semantics:
* VG's instructions: VG's `exec`, on VG's part of the state.
* "PUSH" (`50+rd`, 64-bit operand and stack address size): `RSP := RSP − 8;
  Memory[SS:RSP] := SRC`; no flags are affected. The stack grows to the new
  `rsp` (`moveSp`), then the store, which faults outside `wr`.
* "LEA" (`REX.W 8D /r`): `DEST := EffectiveAddress(SRC)`, modulo 2⁶⁴; no
  flags are affected and no memory is accessed. Into `rsp`, through
  `moveSp`.
* "NEG": `IF DEST = 0 THEN CF := 0; ELSE CF := 1; FI; DEST := [– (DEST)]`;
  "The OF, SF, ZF, AF, and PF flags are set according to the result": those
  of the subtraction `0 - DEST`.
* "DEC": `DEST := DEST – 1`; "The CF flag is not affected. The OF, SF, ZF,
  AF, and PF flags are set according to the result": those of the
  subtraction `DEST - 1`.
* "MOVDQA" (`66 0F 6F /r`, `66 0F 7F /r`): `DEST := SRC`, 16 bytes,
  little-endian; "When the source or destination operand is a memory
  operand, the operand must be aligned on a 16-byte boundary or a
  general-protection exception (#GP) will be generated": so it faults
  unless the address is a multiple of 16. The legacy SSE form leaves bits
  511:128 of the register unchanged (`setXmm`).
* The padding (`align`, `jmpAlign`): no change. Its bytes are `padding`'s,
  long NOPs, which access no memory (SDM Vol. 2, "NOP": "The memory operand
  form of the instruction allows software to create a byte sequence of “no
  operation” as one instruction"), and the jump's target is the end of the
  padding. -/
def exec : Instr → State → Option State
  | .vg i, s => (VG.X86_64.exec i s.vg).map fun g => { s with vg := g }
  | .push r, s =>
    if r = .rsp then none
    else (moveSp s (s.vg.gpr .rsp - 8)).bind fun s' =>
      (s'.vg.store64 (s'.vg.gpr .rsp) (s.vg.gpr r)).map fun g => { s' with vg := g }
  | .lea d m, s => if d = .rsp then none else some { s with vg := s.vg.setReg d (s.vg.ea m) }
  | .leaRsp m, s => moveSp s (s.vg.ea m)
  | .neg d, s =>
    let a := s.vg.gpr d
    let r := 0 - a
    some { s with vg := (arithFlags s.vg r (a ≠ 0) (subOverflow 0 a r)).setReg d r }
  | .dec d, s =>
    let a := s.vg.gpr d
    let r := a - 1
    some { s with vg := ({ arithFlags s.vg r false (subOverflow a 1 r) with cf := s.vg.cf }).setReg d r }
  | .movdqaLoad d m, s =>
    let a := s.vg.ea m
    if a.toNat % 16 = 0 then (s.vg.load128 a).map fun v => { s with vg := s.vg.setXmm d v } else none
  | .movdqaStore m r, s =>
    let a := s.vg.ea m
    if a.toNat % 16 = 0 then (s.vg.store128 a (s.vg.xmm r)).map fun g => { s with vg := g } else none
  | .align _, s | .jmpAlign _, s => some s

/-- The addresses an instruction accesses: VG's for its own, and for the
others the quadword a push stores or the 16 bytes a `movdqa` moves. -/
def addrs : Instr → State → List Addr
  | .vg i, s => VG.X86_64.addrs i s.vg
  | .push _, s => [s.vg.gpr .rsp - 8]
  | .movdqaLoad _ m, s | .movdqaStore m _, s => [s.vg.ea m]
  | .lea .., _ | .leaRsp _, _ | .neg _, _ | .dec _, _ | .align _, _ | .jmpAlign _, _ => []

/-- The CPU features beyond the baseline: VG's for its own, none for the
others, which are x86-64 and SSE2 baseline instructions. -/
def Instr.requires : Instr → List String
  | .vg i => i.requires
  | _ => []

/-- The model. No program here calls or makes a frame of VG's kind, so
calls, returns, and VG's pushes and pops fault: a function's return is the
`ret` `function` appends, to the return address its theorem shows it
keeps. -/
abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval c s := Rind.X86_64.eval c s.vg
  call _ := none
  callAddrs _ := []
  ret _ _ := none
  retAddrs _ := []
  writesSp
    | .push _ | .leaRsp _ => true
    | _ => false
  push _ _ := none
  pop _ _ _ := none
  requires := Instr.requires

/-! ## Machine code -/

/-- LLVM's NOP of `n` bytes, from 1 to 10, as its x86 assembler pads with
for the generic x86-64 CPU (`X86AsmBackend::writeNopData`). -/
def nop : Nat → List Nat
  | 1 => [0x90]
  | 2 => [0x66, 0x90]
  | 3 => [0x0F, 0x1F, 0x00]
  | 4 => [0x0F, 0x1F, 0x40, 0x00]
  | 5 => [0x0F, 0x1F, 0x44, 0x00, 0x00]
  | 6 => [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]
  | 7 => [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]
  | 8 => [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]
  | 9 => [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]
  | _ => [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- LLVM's padding of `n` bytes: NOPs of 10 bytes, then one of the rest. -/
def padding (n : Nat) : List Nat :=
  if n = 0 then [] else if n ≤ 10 then nop n else nop 10 ++ padding (n - 10)
termination_by n
decreasing_by omega

/-- The bytes from `o` to the next multiple of `n`. -/
def padLen (n o : Nat) : Nat := (n - o % n) % n

/-- The bytes of an instruction at byte offset `o`: VG's encoding of its own
(`Instr.encode`); `push` `50+rd`, with `REX.B` for `r8`–`r15`; `lea`,
`neg`, `dec`, and `movdqa` as their docs give, in VG's encoder's forms; and
the padding, `none` unless `n` is a power of two up to 64 and the jump's
reach (`EB cb`, at most 127) covers it. -/
def Instr.encode (o : Nat) : Instr → Option (List Nat)
  | .vg i => i.encode.map List.flatten
  | .push r => some (Enc.plusReg false [] 0x50 (Enc.reg r))
  | .lea d m => Enc.legacy [] true [0x8D] (Enc.reg d) (Enc.RM.mem m)
  | .leaRsp m => Enc.legacy [] true [0x8D] (Enc.reg .rsp) (Enc.RM.mem m)
  | .neg d => Enc.legacy [] true [0xF7] 3 (Enc.RM.reg (Enc.reg d))
  | .dec d => Enc.legacy [] true [0xFF] 1 (Enc.RM.reg (Enc.reg d))
  | .movdqaLoad d m => Enc.sse 1 1 0x6F (Enc.xreg d) (Enc.RM.mem m)
  | .movdqaStore m r => Enc.sse 1 1 0x7F (Enc.xreg r) (Enc.RM.mem m)
  | .align n => if n ∈ [1, 2, 4, 8, 16, 32, 64] then some (padding (padLen n o)) else none
  | .jmpAlign n =>
    if n ∈ [1, 2, 4, 8, 16, 32, 64] then some ([0xEB, padLen n (o + 2)] ++ padding (padLen n (o + 2)))
    else none

/-- The condition code of a `Jcc` (SDM Vol. 2, "Jcc", `7x cb`, `0F 8x cd`):
B 2, AE 3, E 4, NE 5, A 7. -/
def Cond.cc : Cond → Nat
  | .vg .b => 2
  | .vg .ae => 3
  | .vg .e => 4
  | .vg .ne => 5
  | .a => 7

/-- A `Jcc` from offset `o` to offset `t`, short (`7x cb`) when the
displacement fits a byte, else near (`0F 8x cd`), as LLVM's assembler
relaxes it. -/
def jcc (c : Cond) (o t : Nat) : List Nat :=
  let d : Int := (t : Int) - (o + 2)
  if -128 ≤ d ∧ d < 128 then [0x70 + c.cc, (d % 256).toNat]
  else [0x0F, 0x80 + c.cc] ++ Enc.le 4 (((t : Int) - (o + 6)) % 2 ^ 32).toNat

/-- The bytes a jump into `c`, laid out from `o`, skips: those of the
padding it begins with, as the assembler puts a label after its `.align`. -/
def entry : Prog isa → Nat → Nat
  | .block (.align n :: _), o => padLen n o
  | .seq a _, o => entry a o
  | .loop b _, o => entry b o
  | _, _ => 0

/-- The machine code of a program from byte offset `o` on, as rind's build
emits aws-lc's text: each instruction's bytes; a do-while loop as its body
then the `Jcc` that branches back to its entry; and `if c then t else e`
as a `Jcc` to `t`'s entry, `e`, a short `jmp` (`EB cb`) past `t`, then `t`.
`none` for any other control flow, which no program here has, for an
instruction that does not encode, and for a `jmp` or a `Jcc` to `t` that
does not reach in a byte, which LLVM would relax and this does not. -/
def layout : Prog isa → Nat → Option (List Nat)
  | .block is, o =>
    is.foldlM (init := []) fun bs i => (i.encode (o + bs.length)).map (bs ++ ·)
  | .seq a b, o => do
    let ba ← layout a o
    let bb ← layout b (o + ba.length)
    return ba ++ bb
  | .loop body c, o => do
    let bb ← layout body o
    return bb ++ jcc c (o + bb.length) (o + entry body o)
  | .ite c t e, o => do
    let be ← layout e (o + 2)
    let bt ← layout t (o + 2 + be.length + 2)
    let dt := be.length + 2 + entry t (o + 2 + be.length + 2)
    if dt < 128 ∧ bt.length < 128 then
      return [0x70 + c.cc, dt] ++ be ++ [0xEB, bt.length] ++ bt
    else none
  | _, _ => none

/-- `rep ret` (`F3 C3`), aws-lc's return. -/
def repRet : List Nat := [0xF3, 0xC3]

/-- The machine code of a function whose body is `c`, from a section start:
the body, then `rep ret`. -/
def function (c : Prog isa) : Option (List Nat) :=
  (layout c 0).map (· ++ repRet)

end Rind.X86_64
