import Cosim.X86_64
import RindIsa.Proven

/-!
# Cosimulating rind's extension of VG's x86_64 model

Each distinct instruction and branch of the functions rind proves in its
x86_64 model (`RindIsa/Proven.lean`), as its machine code
(`Instr.encode`), run in the model from random states and on the CPU from
the same ones, as `Cosim/X86_64.lean` runs VG's: VG's own instructions
through its cases, the others through `extCase`. The padding (`align`,
`jmpAlign`), which runs as no instructions, is not cosimulated: `admin/prove
lean` checks its bytes.
-/

namespace Cosim.RindX86_64

open VG VG.X86_64 Cosim.X86_64

/-- The straight-line instructions and branch conditions of `c`. -/
def parts : VG.Code Rind.X86_64.Instr Rind.X86_64.Cond → List Rind.X86_64.Instr × List Rind.X86_64.Cond
  | .block is => (is, [])
  | .seq a b | .icall _ _ a b =>
    let (i, c) := parts a
    let (j, d) := parts b
    (i ++ j, c ++ d)
  | .ite c a b =>
    let (i, d) := parts a
    let (j, e) := parts b
    (i ++ j, c :: d ++ e)
  | .loop b c => let (i, d) := parts b; (i, c :: d)
  | .call _ b => parts b
  | .frame i b j => let (is, c) := parts b; (i :: is ++ [j], c)

/-- A case of one of the instructions VG's model lacks: a start image, and
the model's end image with its defined flags. The stack's claimed region
runs from `rsp` to the window's end, and `lo` is 0, so a push or `lea rsp`
moves `rsp` within the model's bounds; a push starts near the window's top,
and a memory operand points into the window, 16-byte aligned for `movdqa`.
Retries a state the model faults in. -/
def extCase (i : Rind.X86_64.Instr) : Gen (Option (Img × Img × Nat)) := do
  for _ in [0:32] do
    let mut img ← randomImg
    match i with
    | .push _ => img := img.setReg .rsp (windowBase + windowLen - 8 * (← below 4))
    | .lea _ m | .leaRsp m => img ← placeMem img m
    | .movdqaLoad _ m | .movdqaStore m _ =>
      img ← placeMem img m
      let a := (img.state.ea m).toNat
      img := img.setReg m.base (((img.gpr[m.base.idx]!).toNat + 2 ^ 64 - a % 16) % 2 ^ 64)
    | _ => pure ()
    let g := img.state
    let sp := (g.gpr .rsp).toNat
    let s : Rind.X86_64.State := ⟨{ g with wr := ⟨g.gpr .rsp, windowBase + windowLen - sp⟩ :: g.wr }, 0⟩
    if let some s' := Rind.X86_64.exec i s then
      let (out, mask) := ofState s'.vg
      return some (img, out, mask)
  return none

/-- The machine code of `i`. -/
def code (i : Rind.X86_64.Instr) : Option ByteArray :=
  (i.encode 0).map fun bs => ⟨(bs.map (·.toUInt8)).toArray⟩

/-- A branch on `c` to `targetAddr`, `jcc rel32`; `ja` is `0F 87`. -/
def jccOf : Rind.X86_64.Cond → ByteArray
  | .vg c => jcc c
  | .a => ByteArray.mk #[0x0F, 0x87] ++ rel32 (insnAddr + 6)

/-- A case of a branch on `c`: taken or not, and nothing else changed. -/
def branchOf (c : Rind.X86_64.Cond) : Gen (Option (Img × Bool)) := do
  let img ← randomImg
  return (Rind.X86_64.eval c img.state).map (img, ·)

/-- The blocks of every function rind proves in its x86_64 model, `n` cases
each, with the CPU features each needs; or why there are none. -/
def blocks (n : Nat) : Gen (Except String (List (Block × List String))) := do
  let (is, cs) := Rind.X86_64.proven.foldl
    (fun (is, cs) p => let (i, c) := parts p.prog; (is ++ i, cs ++ c)) ([], [])
  let mut out := []
  for i in is.eraseDups do
    if let .align _ := i then continue
    if let .jmpAlign _ := i then continue
    let text := reprStr i
    let some bytes := code i | return .error s!"{text}: does not encode"
    let mut cases := #[]
    for _ in [0:n] do
      match i with
      | .vg j =>
        let some (_, img, o, mask) ← insnCase j | return .error s!"{text}: the model faults in every state tried"
        cases := cases.push (caseBytes img o false mask)
      | _ =>
        let some (img, o, mask) ← extCase i | return .error s!"{text}: the model faults in every state tried"
        cases := cases.push (caseBytes img o false mask)
    out := out ++ [({ text, kind := .insn, code := bytes, cases }, i.requires)]
  for c in cs.eraseDups do
    let mut cases := #[]
    for _ in [0:n] do
      let some (img, taken) ← branchOf c | return .error s!"{reprStr c}: the model's condition is undefined"
      cases := cases.push (caseBytes img img taken 15)
    out := out ++ [({ text := reprStr c, kind := .branch, code := jccOf c, cases }, [])]
  return .ok out

end Cosim.RindX86_64
