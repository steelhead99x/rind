module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardFieldI
public import VerifiedGarbage.Impl.X86_64Scal

/-!
# The odd window method on x86-64, its selections woven into the additions

`windowO`'s loop, with the entry of digit `j - 1` selected while digit `j`'s
addition runs (`stepOP`): the selection loads every entry of the table, which
takes about as long as the addition but needs none of its results, while the
addition's field operations mostly wait on each other's. Its loads are spread
among the addition's operations (`selChunkO`, `ForwardField.programBI`) and
kept in vector accumulators, which the operations, of scalar code, do not
touch, until the addition is done; then they are stored to `T`, which the
addition has finished reading, and its `Y` negated for a negative digit
(`finO`). Each part of the selection computes the table's address in `rdx`
again, the only register it writes.

With AVX2 the entries are selected 32 bytes at a time (`selEntryY`); without,
16 bytes at a time with SSE2 (`selEntryX`): the mask of an entry from the
counter `xmm11` and the broadcast magnitude `xmm13` (`pcmpeqd`), as with
AVX2, so that no part of the selection needs a general-purpose register but
`rdx`. Digit `J - 2`'s entry is selected before the loop (`firstOP`), and the
last addition, digit `0`'s, selects none (`lastO`). The weaving applies to
four words (an entry of ten 16-byte pieces, five 32-byte ones), at least
three digits, and an addition of scalar code (`weaveOk`); `windowOW` falls
back to `windowO` elsewhere.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- Entry `m` (from 1) of a table at `rdx` whose entries are `st` bytes
apart, with SSE2: the mask of `xmm11 = xmm13` (both broadcasts of a
doubleword: `m` and the magnitude) in `xmm15`, `xmm11` incremented by
`xmm12` (one in every doubleword), and the entry's `np` 16-byte pieces kept
in the accumulators under the mask, through `xmm14`, as `selEntryAt` keeps
them. -/
def selEntryX (st np : Nat) (m : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm15 .xmm11), .xop (.bin .pcmpeqd .xmm15 .xmm13), .xop (.bin .paddd .xmm11 .xmm12)] ++
  (List.range np).flatMap fun c =>
    [.movdquLoad .xmm14 (tblAt (st * (m - 1) + 16 * c)), .xop (.bin .pand .xmm14 .xmm15),
      .xop (.bin .por (selAcc c) .xmm14)]

namespace JacWinCfg

variable (K : JacWinCfg)

/-- The addition's field operations. -/
def nAddO : Nat := K.addOpsO.length

/-- The entries selected before field operation `i` of the addition is done:
`16 i / nAddO`, all sixteen after the last. -/
def chunkO (i : Nat) : Nat := 16 * i / K.nAddO

/-- Entry `m` of the table at `rdx` kept in the accumulators: with AVX2 32
bytes at a time, else 16. -/
def selEntryP (m : Nat) : List Instr :=
  if K.avx2 then selEntryY K.st K.np32 (qY K.np16) m else selEntryX K.st K.np16 m

/-- After field operation `i`: `rdx = rdi + tbl`, and entries
`chunkO i + 1 … chunkO (i + 1)` kept in the accumulators. -/
def selChunkO (i : Nat) : List Instr :=
  if K.chunkO (i + 1) = K.chunkO i then [] else
  [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))] ++
  (List.range (K.chunkO (i + 1) - K.chunkO i)).flatMap fun e => K.selEntryP (K.chunkO i + e + 1)

/-- The magnitude in `r8` broadcast to `xmm13` (`ymm13` with AVX2), one to
`xmm12` and the counter (`ymm14` with AVX2, else `xmm11`), through `rcx`,
and the accumulators cleared. -/
def selSetP : List Instr :=
  if K.avx2 then
    [.vop (.vmovq .xmm13 .r8), .vop (.vpbroadcastd .l256 .xmm13 .xmm13), .mov32 .rcx (.imm 1),
      .vop (.vmovq .xmm12 .rcx), .vop (.vpbroadcastd .l256 .xmm12 .xmm12), .vop (.vmovdqa .l256 .xmm14 .xmm12)] ++
    (List.range K.np32).map fun c => .vop (.vbin .vpxor .l256 (selAcc c) (selAcc c) (selAcc c))
  else
    [.xop (.movq .xmm13 .r8), .xop (.pshufd .xmm13 .xmm13 0), .mov32 .rcx (.imm 1),
      .xop (.movq .xmm12 .rcx), .xop (.pshufd .xmm12 .xmm12 0), .xop (.bin .movdqa .xmm11 .xmm12)] ++
    (List.range K.np16).map fun c => .xop (.bin .pxor (selAcc c) (selAcc c))

/-- The accumulators stored to `T` (and the upper halves of the `ymm`
registers cleared, with AVX2). -/
def storeP : List Instr :=
  if K.avx2 then
    (List.range K.np32).map (fun c => .vmovdquStore .l256 (sc (K.T + 16 * qY K.np16 c)) (selAcc c)) ++
      [.vop .vzeroupper]
  else (List.range K.np16).map fun c => .movdquStore (sc (K.T + 16 * c)) (selAcc c)

/-- Before digit `j = rbx`'s addition: digit `j - 1`'s entry into `r8`, and
the selection set up for it. -/
def prepO : List Instr := [.alu .sub .rbx (.imm 1)] ++ K.digitO ++ [.alu .add .rbx (.imm 1)] ++ K.selSetP

/-- After digit `j = rbx`'s addition: digit `j - 1`'s entry stored to `T`, its
`Y` negated for a negative digit, and `ZF` for `j = 1`. -/
def finO : List Instr :=
  K.storeP ++ [.alu .sub .rbx (.imm 1)] ++ K.tc.negY ++ [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 1)]

/-- Iteration `j = rbx - 1` (with `rbx` counting down from `J - 1` to `2`):
`R = 32 R + [d_j]P`, digit `j`'s entry in `T`, with digit `j - 1`'s
selected meanwhile into `T`. -/
def stepOP (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) <|
  .seq (.block K.prepO) <|
  .seq (ForwardField.programBI K.M K.addOpsO K.selChunkO) <|
  .block K.finO

/-- The last iteration, `rbx = 1`: `R = 32 R + [d_0]P`, digit `0`'s entry in
`T`. -/
def lastO (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) (ForwardField.programB K.M K.addOpsO)

/-- `rbx = J - 1`, `R = P`, and digit `J - 2`'s entry in `T`. -/
def firstOP : List Instr :=
  K.firstO ++ [.alu .sub .rbx (.imm 1)] ++ K.digitO ++ K.select ++ K.tc.negY ++ [.alu .add .rbx (.imm 1)]

/-- `windowO`, its selections woven into the additions. -/
def windowOP (dbl : Pt → Prog isa) : Prog isa :=
  .seq K.buildO <| .seq (.block K.firstOP) <| .seq (.loop (K.stepOP dbl) .ne) <| .seq (K.lastO dbl) <|
  .seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps)

/-- Whether the woven selection applies: four words, at least three digits,
and an addition whose operations, forwarded or not, are of scalar code. -/
def weaveOk : Bool :=
  decide (K.M.n = 4) && decide (3 ≤ K.J) && K.addOpsO.all fun op =>
    (ForwardField.code K.M op).all scalarI && scalCode ((opCall? K.M op).getD (.block (ForwardField.code K.M op)))

/-- `windowOP` where it applies (`weaveOk`), else `windowO`. -/
def windowOW (dbl : Pt → Prog isa) : Prog isa := if K.weaveOk then K.windowOP dbl else K.windowO dbl

end JacWinCfg

end VG.Impl.Weierstrass.X86_64
