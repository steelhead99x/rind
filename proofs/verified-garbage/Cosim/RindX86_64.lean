import Cosim.X86_64
import RindIsa.Proven

/-!
# Cosimulating rind's extension of VG's x86_64 model

Each distinct instruction and branch of the functions rind proves in its
x86_64 model (`RindIsa/Proven.lean`), as its machine code
(`Instr.encode`), run in the model from random states and on the CPU from
the same ones, as `Cosim/X86_64.lean` runs VG's: VG's own instructions
through its cases, the others through `extCase`. A RIP-relative operand,
whose displacement the linker fills, points at `symTarget` in both: its
displacement in the machine code, and its static's address in the model.
The padding (`align`, `jmpAlign`), which runs as no instructions, is not
cosimulated: `admin/prove lean` checks its bytes.
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

/-- Where a RIP-relative operand points in every case: in the window,
32-byte aligned for `vmovdqa`. An instruction's machine code is the same
in all its cases, so its static is at the same address in each. -/
def symTarget : Nat := windowBase + 256

/-- `placeMem`, then the operand's address moved down to a multiple of
`k`, as an aligned access needs. -/
def placeAligned (img : Img) (m : MemOp) (k : Nat) : Gen Img := do
  let img ← placeMem img m
  let a := (img.state.ea m).toNat
  return img.setReg m.base (((img.gpr[m.base.idx]!).toNat + 2 ^ 64 - a % k) % 2 ^ 64)

/-- A case of one of the instructions VG's model lacks: a start image, and
the model's end image with its defined flags. The stack's claimed region
runs from `rsp` to the window's end, and `lo` is 0, so a push, a pop, or a
move of `rsp` stays within the model's bounds; a push starts near the
window's top and an `add` to `rsp` near its bottom, a memory operand points
into the window, aligned for `movdqa` and `vmovdqa`, and a static at
`symTarget`. Retries a state the model faults in. -/
def extCase (i : Rind.X86_64.Instr) : Gen (Option (Img × Img × Nat)) := do
  for _ in [0:32] do
    let mut img ← randomImg
    match i with
    | .push _ => img := img.setReg .rsp (windowBase + windowLen - 8 * (← below 4))
    | .aluRsp .add _ => img := img.setReg .rsp (windowBase + 8 * (← below 4))
    | .lea _ m | .leaRsp m | .vpshufdLoad _ m _ | .imulMem _ m | .mulxD32 _ _ m | .pinsrb _ m _
    | .pextrb m _ _ =>
      img ← placeMem img m
    | .movdqaLoad _ m | .movdqaStore m _ | .xload _ _ (.op m) | .vmovdqaLoad .l128 _ (.op m)
    | .vmovdqaStore .l128 m _ => img ← placeAligned img m 16
    | .vmovdqaLoad .l256 _ (.op m) | .vmovdqaStore .l256 m _ => img ← placeAligned img m 32
    | _ => pure ()
    let g := img.state
    let g := match i.sym with
      | some m => { g with syms := fun _ => BitVec.ofNat 64 symTarget - BitVec.ofInt 64 m.disp }
      | none => g
    let sp := (g.gpr .rsp).toNat
    let s : Rind.X86_64.State := ⟨{ g with wr := ⟨g.gpr .rsp, windowBase + windowLen - sp⟩ :: g.wr }, 0⟩
    if let some s' := Rind.X86_64.exec i s then
      let (out, mask) := ofState s'.vg
      return some (img, out, mask)
  return none

/-- The machine code of `i` at `insnAddr`: a RIP-relative operand of aws-lc's
code with its displacement, its last four bytes, the distance from its end
to `symTarget`; `rip` with its `disp32` 2, then `jmp` (`EB cb`) over the
static's words, so it reads them. -/
def code (i : Rind.X86_64.Instr) : Option ByteArray :=
  (i.encode 0).map fun bs =>
    let bs : List Nat := match i, i.sym with
      | .rip _ _ ws, _ =>
        let tbl := ws.flatMap fun (w : BitVec 64) => Enc.le 8 w.toNat
        bs.take (bs.length - 4) ++ [2, 0, 0, 0, 0xEB, tbl.length] ++ tbl
      | _, some _ => bs.take (bs.length - 4) ++ Enc.le 4 (((symTarget : Int) - (insnAddr + bs.length)) % 2 ^ 32).toNat
      | _, none => bs
    ⟨(bs.map (·.toUInt8)).toArray⟩

/-- A branch on `c` to `targetAddr`, `jcc rel32` (`0F 80+cc`). `jrcxz`
reaches only a byte's displacement, so `rcxz` branches by it to a `jmp
rel32` there, past which a `jmp` skips when not taken, and `rcxnz` is the
`jrcxz` past a `jmp rel32` that `layout` lays it out as. -/
def jccOf : Rind.X86_64.Cond → ByteArray
  | .rcxz => ByteArray.mk #[0xE3, 0x02, 0xEB, 0x05, 0xE9] ++ rel32 (insnAddr + 9)
  | .rcxnz => ByteArray.mk #[0xE3, 0x05, 0xE9] ++ rel32 (insnAddr + 7)
  | c => ByteArray.mk #[0x0F, (0x80 + c.cc).toUInt8] ++ rel32 (insnAddr + 6)

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
