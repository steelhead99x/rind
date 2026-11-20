import Cosim.AArch64
import RindIsa.Proven

/-!
# Cosimulating rind's extension of VG's AArch64 model

Each distinct instruction and branch of the functions rind proves in its
model (`RindIsa/Proven.lean`), as its machine code (`Instr.encode`), the
words `admin/prove lean` checks rind's build emits, run in the model from
random states and on the CPU from the same ones, as `Cosim/AArch64.lean`
runs VG's: VG's own instructions through its cases, the others through
`extCase`, which also compares `x29`. `adrSym`'s `adrp` and `add`, which the
linker fills, are not cosimulated, as VG's are not.
-/

namespace Cosim.Rind

open VG VG.AArch64 Cosim.AArch64 Rind.AArch64

/-- The straight-line instructions and branch conditions of `c`. -/
def parts : VG.Code Rind.AArch64.Instr VG.AArch64.Cond →
    List Rind.AArch64.Instr × List VG.AArch64.Cond
  | .block is => (is, [])
  | .seq a b | .ite _ a b | .icall _ _ a b =>
    let (i, c) := parts a
    let (j, d) := parts b
    (i ++ j, c ++ d)
  | .loop b c => let (i, d) := parts b; (i, c :: d)
  | .call _ b => parts b
  | .frame i b j => let (is, c) := parts b; (i :: is ++ [j], c)

/-- A case of one of the instructions VG's model lacks: a start image and
the model's end image, with `x29`. A load or store through a register
accesses the window, as do the frame's through `sp`. Retries a state the
model faults in. -/
def extCase (i : Rind.AArch64.Instr) : Gen (Option (Img × Img)) := do
  for _ in [0:32] do
    let mut img ← randomImg
    match i with
    | .ld1 cnt _ _ n _ | .st1 cnt _ _ n _ =>
      img := img.setReg n (windowBase + (← below (windowLen - 16 * cnt + 1)))
    | .stpFrame =>
      img := { img with sp := BitVec.ofNat 64 (← spIn (windowBase + 16) (windowBase + windowLen)) }
    | .ldrFp =>
      img := { img with sp := BitVec.ofNat 64 (← spIn windowBase (windowBase + windowLen - 8)) }
    | _ => pure ()
    if let some s' := Rind.AArch64.exec i ⟨img.state, img.gpr[29]!⟩ then
      let out := ofState img s'.vg
      return some (img, { out with gpr := out.gpr.set! 29 s'.x29 })
  return none

/-- The machine code of `i`. -/
def code (i : Rind.AArch64.Instr) : Option ByteArray :=
  i.encode.map fun ws => ws.foldl pushU32 .empty

/-- The blocks of every function rind proves, `n` cases each, with the CPU
features each needs; or why there are none. -/
def blocks (n : Nat) : Gen (Except String (List (Block × List String))) := do
  let (is, cs) := proven.foldl (fun (is, cs) p => let (i, c) := parts p.prog; (is ++ i, cs ++ c)) ([], [])
  let mut out := []
  for i in is.eraseDups do
    if let .vg (.adrSym ..) := i then continue
    let text := reprStr i
    let some bytes := code i | return .error s!"{text}: does not encode"
    let mut cases := #[]
    for _ in [0:n] do
      match i with
      | .vg j =>
        let some (_, img, o) ← insnCase j | return .error s!"{text}: the model faults in every state tried"
        cases := cases.push (caseBytes img o false)
      | _ =>
        let some (img, o) ← extCase i | return .error s!"{text}: the model faults in every state tried"
        cases := cases.push (caseBytes img o false)
    out := out ++ [({ text, kind := .insn, code := bytes, cases }, i.requires)]
  for c in cs.eraseDups do
    let mut cases := #[]
    for _ in [0:n] do
      let some (img, taken) ← branchCase c | return .error s!"{reprStr c}: the model's condition is undefined"
      cases := cases.push (caseBytes img img taken)
    out := out ++ [({ text := reprStr c, kind := .branch, code := cb c, cases }, [])]
  return .ok out

end Cosim.Rind
