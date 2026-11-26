module

public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Loop
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd

/-!
# P-256 on x86-64 with AVX512_IFMA: the odd window method's loop

`vwindowO` is `JacWinCfg.windowO` (`Impl/Weierstrass/X86_64/WinJacOdd.lean`)
with the accumulator in vectors: after the table is built, `R = P` is the
table's first entry as the accumulator (`convQPieces`, `setPieces`); each
iteration is five doublings (`dblPieces`) and the addition of the digit's
entry (`convQPieces`, `addPieces`), which the window method's own code
selects and negates into its slot (`digitO`, `select`, `negY`); then the
accumulator is put back in the words of `R` (`outPieces`, `packLaneAt`).

The selection uses `ymm0`–`ymm15` and leaves their upper halves zero, so the
accumulator is kept in the vectors' slots across it (`saveAcc`, `loadAcc`).
The window method's working space has its slots, tables and the selected
entry below `5472`; the vectors' code has what is above: its
slots from `SL + EO` (it addresses them from `rdi`, which is moved by `EO`
while it runs: `adjUp`, `adjDn`), and its constants at `EKB`.

Nothing here branches on the scalar: the additions are those of distinct
points for every scalar the window method takes
(`Proof/Weierstrass/X86_64/WinJacOddState.lean`).
-/

@[expose] public section

namespace VG.Impl.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)

/-- What `rdi` is moved by while the vectors' code runs: its slots are at `SL + EO` of the working space. -/
def EO : Nat := 448

/-- The blocks' constants, in the window method's working space. -/
def EKB : Nat := 6400

def adjUp : List Instr := [.alu .add .rdi (.imm (BitVec.ofNat 32 EO))]
def adjDn : List Instr := [.alu .sub .rdi (.imm (BitVec.ofNat 32 EO))]

/-- The accumulator, `ymm0`–`ymm19`, into the first twenty slots. -/
def saveAcc : List Instr := (List.range 20).map fun i => .evStore (cfg.smem i) (vreg i)

/-- The accumulator from the first twenty slots. -/
def loadAcc : List Instr := (List.range 20).map fun i => .evLoad (vreg i) (cfg.smem i)

/-- The registers the blocks read through: `r10` at the constants, `r9` at the mask of an entry that is
not negated, `rcx` at the words of the entry at `e` and `rdx` at those of its `Z²` and `Z³` at `z`. -/
def ptrs (e z : Nat) : List Instr :=
  [.mov .r10 (.reg .rdi), .alu .add .r10 (.imm (BitVec.ofNat 32 EKB))] ++ signPtr false ++
  [.mov .rcx (.reg .rdi), .alu .add .rcx (.imm (BitVec.ofNat 32 e)),
    .mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 z))]

/-- Iteration `j = rbx - 1`: `R = 32 R + [d_j]P`, the accumulator in `ymm0`–`ymm19` and `rdi` moved by
`EO` before and after. -/
def vstepO (K : JacWinCfg) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1), .mov32 .r11 (.imm 5)]) <|
  .seq (.loop (.block (dblPieces.flatten ++ [.alu .sub .r11 (.imm 1)])) .ne) <|
  .seq (.block (saveAcc ++ adjDn)) <|
  .seq (.block (K.digitO ++ K.select)) <|
  .seq (.block K.tc.negY) <|
  .block (ptrs K.E.x K.z2 ++ (adjUp ++ (loadAcc ++ (convQPieces.flatten ++ (addPieces.flatten ++
    [.alu .test .rbx (.reg .rbx)])))))

/-- The loop, from the table: the constants, `R = P` (the table's first entry) as the accumulator, the
iterations, and the accumulator's rows of `(Y, Z, _, X)` in the first five slots. -/
def vloopO (K : JacWinCfg) : Prog isa :=
  .seq (.block (fill kwords EKB ++ (ptrs K.tbl (K.tbl + 24 * K.M.n) ++
    ([.mov32 .rbx (.imm (BitVec.ofNat 32 (K.J - 1)))] ++ (adjUp ++ (zeroAcc ++ (convQPieces.flatten ++
      setPieces.flatten))))))) <|
  .seq (.loop (vstepO K) .ne) <|
  .block (outPieces.flatten ++ (storeOut ++ (adjDn ++ [.vop .vzeroupper])))

/-- `[k]P` into `R`, in projective coordinates, as `windowO`, with the loop in vectors. -/
def vwindowO (K : JacWinCfg) : Prog isa :=
  .seq K.buildO <| .seq (vloopO K) <|
  .seq (.block (packLaneAt (SL + EO) K.M 3 K.R.x ++ (packLaneAt (SL + EO) K.M 0 K.R.y ++
    packLaneAt (SL + EO) K.M 1 K.R.z))) <|
  .seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps)

end VG.Impl.P256.X86_64.Ifma
