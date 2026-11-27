import VerifiedGarbage.TCB.AArch64.Encode

/-!
# rind's extension of VG's AArch64 model

**Trusted.** VG's model (`VerifiedGarbage/TCB/AArch64/`) covers the
instructions VG's own code uses. rind proves code VG did not write, aws-lc's
assembly among it, which also uses the frame pointer `x29`, the multiple
structure forms of LD1 and ST1, and aws-lc's frame of `x29` and `x30`. This
model is VG's with those added: its state is VG's with `x29`, and its
instructions are VG's, run by VG's semantics on VG's part of the state, and
those below, each transcribing the pseudocode of the Arm Architecture
Reference Manual for A-profile (DDI 0487) the docs cite, in VG's style, so
that the leakage model of `TCB/Code.lean` applies unchanged: every memory
access faults outside the state's regions, and leaks its address.

`admin/prove vg` cosimulates each instruction of every program in
`RindIsa/` against the CPU (`Cosim/Rind.lean`), and `admin/prove lean`
checks that each program's bytes (`layout`) are the ones rind's build emits.
-/

namespace Rind.AArch64

open VG VG.AArch64

/-- VG's machine state with the frame pointer `x29`, which VG's model leaves
out (see its module docs) and aws-lc's frames save and restore. -/
structure State where
  vg : VG.AArch64.State
  x29 : BitVec 64

inductive Instr
  /-- An instruction of VG's model, with VG's semantics. -/
  | vg (i : VG.AArch64.Instr)
  /-- `ld1 {vt.<a>, …}, [xn]` with the `cnt` registers from `t` (LD1
  (multiple structures), no offset), or `ld1 {vt.<a>, …}, [xn], #(16 * cnt)`
  if `post` (post-index, immediate offset) -/
  | ld1 (cnt : Nat) (a : VArr) (t : VReg) (n : Reg) (post : Bool)
  /-- `st1 {vt.<a>, …}, [xn]` (ST1 (multiple structures)), as `ld1` -/
  | st1 (cnt : Nat) (a : VArr) (t : VReg) (n : Reg) (post : Bool)
  /-- `stp x29, x30, [sp, #-16]!` (STP, 64-bit, pre-index) -/
  | stpFrame
  /-- `mov x29, sp` (alias of ADD (immediate), `add x29, sp, #0`) -/
  | movFp
  /-- `ldr x29, [sp], #16` (LDR (immediate), 64-bit, post-index) -/
  | ldrFp
  deriving DecidableEq, Repr

/-- Load the `k` vector registers from `t`, 16 bytes each, from `a` on.
DDI 0487 C7.2, "LD1 (multiple structures)": for each register `r` and
element `e`, `Elem[V[t + r], e] = Mem[address + offs, ebytes]`, `offs`
advancing `ebytes` an element and `t` wrapping modulo 32 (`VReg.succ`).
Memory is little-endian, so whatever the arrangement, register `r` holds
the 16 bytes at `a + 16 r`, little-endian: what VG's `State.load` reads. -/
def ldVecs (g : VG.AArch64.State) (a : Addr) : VReg → Nat → Option VG.AArch64.State
  | _, 0 => some g
  | t, k + 1 => (g.load a 16).bind fun x => ldVecs (g.setV t x) (a + 16) t.succ k

/-- Store the `k` vector registers from `t` to `a` on, as `ldVecs` loads
them. DDI 0487 C7.2, "ST1 (multiple structures)": `Mem[address + offs,
ebytes] = Elem[V[t + r], e]`. -/
def stVecs (g : VG.AArch64.State) (a : Addr) : VReg → Nat → Option VG.AArch64.State
  | _, 0 => some g
  | t, k + 1 => (g.store a 16 (g.v t)).bind fun g' => stVecs g' (a + 16) t.succ k

/-- The state after LD1 or ST1 of `cnt` registers through `n`: with `post`,
`n` advances by the bytes accessed (DDI 0487 C7.2, "LD1 (multiple
structures)", post-index, immediate: `offs = imm`, the `#<imm>` the
assembler requires to be `16 * cnt` for 128-bit registers; `if wback then
X[n, 64] = address + offs`). -/
def advance (g : VG.AArch64.State) (n : Reg) (base : Addr) (cnt : Nat) (post : Bool) :
    VG.AArch64.State :=
  if post then g.write .x n (base + BitVec.ofNat 64 (16 * cnt)) else g

/-- Semantics:
* VG's instructions: VG's `exec`, on VG's part of the state.
* "LD1 (multiple structures)", "ST1 (multiple structures)", 1 to 4
  registers (`selem = 1`, `rpt = cnt`): `ldVecs`, `stVecs`, `advance`.
  `address = X[n, 64]` is read before any write, and the accesses are of
  Normal memory, which need no alignment (`SCTLR_ELx.A` 0, as VG's model has
  it for `LDR (immediate, SIMD&FP)`).
* "STP" 64-bit, pre-index, `Rn = SP`, `imm7 = -2` (`offset = -16`):
  `address = SP[] + offset; Mem[address, 8] = X[29]; Mem[address + 8, 8] =
  X[30]; SP[] = address`.
* "ADD (immediate)", `Rd = 29`, `Rn = SP`, `imm12 = 0`: `X[29] = SP[]`.
* "LDR (immediate)" 64-bit, post-index, `Rn = SP`, `imm9 = 16`: `address =
  SP[]; X[29] = Mem[address, 8]; SP[] = address + 16`.

An access through `sp` faults unless it is 16-byte aligned, as Linux's
SCTLR_EL1.SA0 makes it (DDI 0487 D1.3.10, "SP alignment checking"), and
AAPCS64 keeps it (§6.4.5.1, "SP mod 16 = 0"). -/
def exec : Instr → State → Option State
  | .vg i, s => (VG.AArch64.exec i s.vg).map fun g => { s with vg := g }
  | .ld1 cnt _ t n post, s =>
    if 1 ≤ cnt ∧ cnt ≤ 4 then
      (ldVecs s.vg (s.vg.gpr n) t cnt).map fun g =>
        { s with vg := advance g n (s.vg.gpr n) cnt post }
    else none
  | .st1 cnt _ t n post, s =>
    if 1 ≤ cnt ∧ cnt ≤ 4 then
      (stVecs s.vg (s.vg.gpr n) t cnt).map fun g =>
        { s with vg := advance g n (s.vg.gpr n) cnt post }
    else none
  | .stpFrame, s =>
    if s.vg.sp.toNat % 16 = 0 then
      let a := s.vg.sp - 16
      (s.vg.store a 8 s.x29).bind fun g =>
        (g.store (a + 8) 8 (g.gpr .x30)).map fun g => { s with vg := { g with sp := a } }
    else none
  | .movFp, s => some { s with x29 := s.vg.sp }
  | .ldrFp, s =>
    if s.vg.sp.toNat % 16 = 0 then
      (s.vg.load s.vg.sp 8).map fun x => { vg := { s.vg with sp := s.vg.sp + 16 }, x29 := x }
    else none

/-- The addresses an instruction accesses: VG's for its own, and for the
others each register's or doubleword's. -/
def addrs : Instr → State → List Addr
  | .vg i, s => VG.AArch64.addrs i s.vg
  | .ld1 cnt _ _ n _, s | .st1 cnt _ _ n _, s =>
    (List.range cnt).map fun j => s.vg.gpr n + BitVec.ofNat 64 (16 * j)
  | .stpFrame, s => [s.vg.sp - 16, s.vg.sp - 8]
  | .ldrFp, s => [s.vg.sp]
  | .movFp, _ => []

/-- The CPU features beyond the baseline: VG's for its own, none for the
others, which are A64 and AdvSIMD baseline instructions. -/
def Instr.requires : Instr → List String
  | .vg i => i.requires
  | _ => []

/-- The model. No program here calls or makes a frame of VG's kind, so
calls, returns, pushes and pops fault: a function's return is its `ret`,
which `layout` appends, to the return address `x30` its theorem shows it
keeps. -/
abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := VG.AArch64.Cond
  exec := exec
  addrs := addrs
  eval c s := VG.AArch64.eval c s.vg
  call _ := none
  callAddrs _ := []
  ret _ _ := none
  retAddrs _ := []
  writesSp
    | .stpFrame | .ldrFp => true
    | _ => false
  push _ _ := none
  pop _ _ _ := none
  requires := Instr.requires

/-! ## Machine code -/

/-- The `opcode` field (15–12) of LD1 and ST1 (multiple structures) for
`cnt` registers: `0111` one, `1010` two, `0110` three, `0010` four. -/
def ldstOpcode : Nat → Option Nat
  | 1 => some 0b0111
  | 2 => some 0b1010
  | 3 => some 0b0110
  | 4 => some 0b0010
  | _ => none

/-- The machine code of an instruction (DDI 0487 C6.2 and C7.2): VG's
encoding of its own (`Instr.encode`); LD1 and ST1 (multiple structures),
128-bit (`Q = 1`), `0 Q 0011000 L 000000 opcode size Rn Rt` with no offset
and `0 Q 0011001 L 0 11111 opcode size Rn Rt` post-index by the immediate,
`L` 1 for LD1; and the frame's three fixed words. -/
def Instr.encode : Instr → Option (List Nat)
  | .vg i => i.encode
  | .ld1 cnt a t n post =>
    (ldstOpcode cnt).map fun op =>
      [(if post then 0x4CDF0000 else 0x4C400000) ||| op <<< 12 ||| Enc.vsize a <<< 10 |||
        n.index <<< 5 ||| t.index]
  | .st1 cnt a t n post =>
    (ldstOpcode cnt).map fun op =>
      [(if post then 0x4C9F0000 else 0x4C000000) ||| op <<< 12 ||| Enc.vsize a <<< 10 |||
        n.index <<< 5 ||| t.index]
  -- STP (64-bit, pre-index): `10 101 0 011 0 imm7 Rt2 Rn Rt`, `imm7 = -2`.
  | .stpFrame => some [0xA9BF7BFD]
  -- ADD (immediate): `1 0 0 100010 0 imm12 Rn Rd`, `Rn = 31` (SP), `Rd = 29`.
  | .movFp => some [0x910003FD]
  -- LDR (immediate, 64-bit, post-index): `11 111 0 00 01 0 imm9 01 Rn Rt`, `imm9 = 16`.
  | .ldrFp => some [0xF84107FD]

/-- A relocation the linker resolves in a program's machine code: the byte
offset of its instruction, its ELF type, and the symbol it names. -/
structure Reloc where
  off : Nat
  type : String
  sym : String
  deriving DecidableEq, Repr

/-- The machine code of a program from word `o` on, as rind's build emits
it: each instruction's words, `adrSym`'s `adrp` and `add` with zero
immediates and their relocations for the linker to fill (ELF for the Arm
64-bit Architecture, `R_AARCH64_ADR_PREL_PG_HI21` and
`R_AARCH64_ADD_ABS_LO12_NC`), and a do-while loop as its body followed by
the CBZ or CBNZ (`sf 011010 op imm19 Rt`) that branches back to its first
word. `none` for any other control flow, which no program here has, and for
an instruction that does not encode. -/
def layout : Prog isa → Nat → Option (List Nat × List Reloc)
  | .block is, o =>
    is.foldlM (init := ([], [])) fun (ws, rs) i =>
      match i with
      | .vg (.adrSym d name) =>
        let at_ := o + ws.length
        some (ws ++ [0x90000000 ||| d.index, 0x91000000 ||| d.index <<< 5 ||| d.index],
          rs ++ [⟨4 * at_, "R_AARCH64_ADR_PREL_PG_HI21", name⟩,
            ⟨4 * (at_ + 1), "R_AARCH64_ADD_ABS_LO12_NC", name⟩])
      | i => i.encode.map fun w => (ws ++ w, rs)
  | .seq a b, o => do
    let (wa, ra) ← layout a o
    let (wb, rb) ← layout b (o + wa.length)
    return (wa ++ wb, ra ++ rb)
  | .loop body c, o => do
    let (wb, rb) ← layout body o
    let (sz, op, r) := match c with
      | .zero sz r => (sz, 0, r)
      | .nonzero sz r => (sz, 1, r)
    let imm19 := (2 ^ 19 - wb.length) % 2 ^ 19
    if wb.length < 2 ^ 18 then
      return (wb ++ [Enc.sf sz ||| 0b011010 <<< 25 ||| op <<< 24 ||| imm19 <<< 5 ||| r.index], rb)
    else none
  | _, _ => none

/-- The machine code of a function whose body is `c`: the body, then `ret`. -/
def function (c : Prog isa) : Option (List Nat × List Reloc) :=
  (layout c 0).map fun (ws, rs) => (ws ++ [retWord], rs)

end Rind.AArch64
