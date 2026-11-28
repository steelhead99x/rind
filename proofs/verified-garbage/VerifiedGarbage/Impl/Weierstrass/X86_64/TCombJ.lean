module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Impl.X86_64Scal

/-!
# The fixed-base comb with Booth's digits and Jacobian mixed additions

The comb of `Impl/Weierstrass/X86_64/TComb.lean`, with the same tables, but
cheaper additions: the digits are Booth's (`d_j = W_j + c_j - 2^w c_{j+1}`,
`W_j` window `j` and `c_j` bit `wj - 1` of `k`, so `|d_j| ≤ 2^(w-1)` and no
constant is added), and they are added from the bottom (`j = 0` up), with the
mixed Jacobian addition (`maddJ`: 8 products and 3 squares, against
Algorithm 5's 11 products and 2 by `b`). That formula fails for equal points;
the sum of the digits below `j` is smaller than any nonzero digit's term,
modulo the order of `G`, so they never are (the proof's `booth_ne`).

The accumulator `A` holds a Jacobian triple. Window `0` puts its entry in `A`
(`first`), the accumulator being `O`. Each later window `j = rbx` selects its
entry (the magnitude `bdigit`, `select`), negates it for a negative digit
(`bnegY`), adds it into `D`, takes the entry instead where `A` is `O`
(`Z = 0`, `nzMask`), and `A = D` unless the digit is zero (computed again).
At the end, `A = (XZ : Y : Z³)` in projective coordinates, with `Y = 1` where
`Z = 0` (`outFix`, `outOps`). Every selection is by a mask, and the windows'
order is public: the timing depends on `rdi` and the tables' address only.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- `rcx` all ones if the `n` words at `z` are not all zero, through `rax`. -/
def nzMask (n z : Nat) : List Instr :=
  .mov .rax (.mem (sc z)) :: (List.range (n - 1)).map (fun i => .alu .or .rax (.mem (sc (z + 8 * (i + 1))))) ++
  [.mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .alu .sbb .rcx (.reg .rcx)]

namespace TCombCfg

variable (K : TCombCfg)

/-- Booth's digit `rbx`'s magnitude into `rax` and `r8`: `m = W + c` (the
window, from `rcx = w rbx`, and, for `c`, bit `w rbx - 1`), the window's top
bit `s`, and `s ? 2^w - m : m`, through `rdx`. -/
def bdigit (c : Bool) : List Instr :=
  winIndex K.w ++ hornerBits K.bits K.w ++
  (if c then [.movzx8 .rdx (winByte (K.bits - 1)), .alu .add .rax (.reg .rdx)] else []) ++
  [.movzx8 .rdx (winByte (K.bits + K.w - 1)), .mov32 .r8 (.imm 0), .alu .sub .r8 (.reg .rdx),
    .alu .xor .rax (.reg .r8), .alu .sub .rax (.reg .r8),
    .alu .and .r8 (.imm (BitVec.ofNat 32 (2 ^ K.w))), .alu .add .rax (.reg .r8), .mov .r8 (.reg .rax)]

/-- `rcx` all ones if Booth's digit `rbx` is negative: minus its window's top
bit, through `rax`. -/
def bsignMask : List Instr :=
  winIndex K.w ++ [.movzx8 .rax (winByte (K.bits + K.w - 1)), .mov32 .rcx (.imm 0),
    .alu .sub .rcx (.reg .rax)]

/-- `[y] = -[y]` (through `[neg]`, with zero at `zero`) if Booth's digit
`rbx` is negative. -/
def bnegY : List Instr :=
  Mont.X86_64.sub K.M K.neg K.zero K.E.y ++ K.bsignMask ++ sel K.M.n K.E.y K.E.y K.neg

/-- The bytes of the table of bits past the scalar cleared (to `w J`, in
words). -/
def clearBits : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range K.zw).map (fun i => .store (sc (K.bits + K.kbytes + 8 * i)) .rax)

/-- Window `0`: its signed entry into `A` (the accumulator being `O`), and
`rbx = 1`. -/
def first : Prog isa :=
  .seq (.block (K.clearBits ++ [.mov32 .rbx (.imm 0)] ++ K.bdigit false ++ K.select)) <|
  .seq (.block K.bnegY) <|
  .block (copyPt K.M.n K.A K.E ++ [.mov32 .rbx (.imm 1)])

/-- Window `j = rbx`'s addition of its entry, in `E`, by `madd` (`maddJ`'s
code), then `D = E` where `A` is `O`, `A = D` unless the digit is zero, and
`fin`. -/
def tailJ (madd : Prog isa) (fin : List Instr) : Prog isa :=
  .seq madd <|
  .seq (.block (nzMask K.M.n K.A.z ++ selPt K.M.n K.D K.E K.D)) <|
  .block (K.bdigit true ++ eqMask 0 ++ selPt K.M.n K.A K.D K.A ++ fin)

/-- `rbx = j + 1` and `ZF` for `j + 1 = J`. -/
def incCmp (J : Nat) : List Instr := [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm (BitVec.ofNat 32 J))]

/-- Window `j = rbx` (`1 ≤ j < J`), then `rbx = j + 1` and `ZF` for `j + 1 = J`. -/
def stepJ : Prog isa :=
  .seq (.block (K.bdigit true ++ K.select)) <|
  .seq (.block K.bnegY) <|
  K.tailJ (fprogB K.M (maddJ K.S K.A K.E K.D)) (incCmp K.J)

/-- `Y = R mod p` where `Z = 0`: `Y` cleared there (from `zero`), then `R`'s
words or-ed in under the complemented mask, through `rax`, `rcx` and `rdx`. -/
def outFix : List Instr :=
  nzMask K.M.n K.A.z ++ sel K.M.n K.A.y K.zero K.A.y ++ .alu .xor .rcx (.imm (-1)) ::
  (List.range K.M.n).flatMap fun i =>
    [.movImm64 .rax (wordOf K.one i), .alu .and .rax (.reg .rcx), .alu .or .rax (.mem (sc (K.A.y + 8 * i))),
      .store (sc (K.A.y + 8 * i)) .rax]

/-- `A = (XZ : Y : Z³)`. -/
def outOps : List FOp := [.mul K.A.x K.A.x K.A.z, .mul K.S.t0 K.A.z K.A.z, .mul K.A.z K.S.t0 K.A.z]

/-! ### The pipelined comb

Each window's entry is selected by loading every entry of its table, which
takes about as long as the addition, but needs none of its results; the
addition's field operations mostly wait on each other's. So with `pipe`, the
entry of window `j + 1` is selected while window `j`'s addition runs: its
256-bit loads are spread among the addition's operations (`selChunk`,
`fprogBI`), and kept in the vector accumulators, which the operations, of
scalar code (`scalCode`), do not touch, until the addition's selections are
done. The operations keep nothing in registers from one to the next, so
each part of the selection computes the table's address in `rdx` again,
from the public counter `rbx`. Window `1`'s entry is selected before the loop, and the
last window, `J - 1`, selects none (`stepJ`'s addition). -/

/-- The addition's field operations. -/
def nOps : Nat := (maddJ K.S K.A K.E K.D).length

/-- The entries selected before field operation `i` of the addition is done:
`H i / nOps`, all `H` after the last. -/
def chunkLo (i : Nat) : Nat := K.H * i / K.nOps

/-- `rdx` = table `rbx + 1`'s address, from the static `tsym`'s, through `rax`
and `rcx`. -/
def selSetupNext : List Instr :=
  [.mov .rax (.reg .rbx), .alu .add .rax (.imm 1), .mov32 .rcx (.imm (BitVec.ofNat 32 K.tblBytes)), .mul .rcx,
    .leaSym .rdx K.tsym, .alu .add .rdx (.reg .rax)]

/-- After field operation `i`: the address of table `rbx + 1` in `rdx`
(the field operations keep nothing in registers, so the selection's part
computes it again), and entries `chunkLo i + 1 … chunkLo (i + 1)` of the
table kept in the accumulators under the mask of the next digit's
magnitude (`selEntryY`). -/
def selChunk (i : Nat) : List Instr :=
  if K.chunkLo (i + 1) = K.chunkLo i then [] else
  K.selSetupNext ++ (List.range (K.chunkLo (i + 1) - K.chunkLo i)).flatMap fun e =>
    selEntryY (16 * K.M.n) ((K.M.n + 1) / 2) (qY K.M.n) (K.chunkLo i + e + 1)

/-- Before window `j = rbx`'s addition: the magnitude of digit `j + 1`
(`bdigit`, `rbx` incremented around it) broadcast to `ymm13`, one to `ymm12`
and the counter `ymm14`, and the accumulators cleared (`selPassY`'s start),
through `rax`, `rcx` and `rdx`. -/
def prepNext : List Instr :=
  [.alu .add .rbx (.imm 1)] ++ K.bdigit true ++ [.alu .sub .rbx (.imm 1)] ++
  [.vop (.vmovq .xmm13 .r8), .vop (.vpbroadcastd .l256 .xmm13 .xmm13), .mov32 .rcx (.imm 1),
    .vop (.vmovq .xmm12 .rcx), .vop (.vpbroadcastd .l256 .xmm12 .xmm12), .vop (.vmovdqa .l256 .xmm14 .xmm12)] ++
  ((List.range ((K.M.n + 1) / 2)).map (fun c => .vop (.vbin .vpxor .l256 (selAcc c) (selAcc c) (selAcc c))) :
    List Instr)

/-- After window `j`'s selections: `rbx = j + 1`, the next entry stored to
`E` from the accumulators (`selPassY`'s end), its magnitude again, `selOne`
and the negation for a negative digit, and `ZF` for `j + 1 = J - 1`. -/
def finNext : List Instr :=
  [.alu .add .rbx (.imm 1)] ++
  ((List.range ((K.M.n + 1) / 2)).map (fun c => .vmovdquStore .l256 (sc (K.E.x + 16 * qY K.M.n c)) (selAcc c)) :
    List Instr) ++
  [.vop .vzeroupper] ++ K.bdigit true ++ K.selOne ++ K.bnegY ++
  [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (K.J - 1)))]

/-- Window `j = rbx` (`1 ≤ j < J - 1`) with window `j + 1`'s selection, its
entry in `E` (negated), then `rbx = j + 1` and `ZF` for `j + 1 = J - 1`. -/
def stepJP : Prog isa :=
  .seq (.block K.prepNext) <| K.tailJ (fprogBI K.M (maddJ K.S K.A K.E K.D) K.selChunk 0) K.finNext

/-- Whether the pipelined comb applies: asked for (`pipe`), with AVX2 and at
least two words (`selPassY`'s 32-byte pieces), at least three windows, and an
addition of scalar code only. -/
def pipeOk : Bool :=
  K.pipe && K.avx2 && decide (2 ≤ K.M.n) && decide (3 ≤ K.J) &&
    (maddJ K.S K.A K.E K.D).all fun op => scalCode (opProg K.M op)

/-- `[k]G` into `A`, in projective coordinates, by the pipelined comb. -/
def combJP : Prog isa :=
  .seq K.first <|
  .seq (.block (K.bdigit true ++ K.select)) <| .seq (.block K.bnegY) <|
  .seq (.loop K.stepJP .ne) <|
  .seq (K.tailJ (fprogB K.M (maddJ K.S K.A K.E K.D)) (incCmp K.J)) <|
  .seq (.block K.outFix) (fprogB K.M K.outOps)

/-- `[k]G` into `A`, in projective coordinates, a window at a time. -/
def combJ0 : Prog isa :=
  .seq K.first <| .seq (.loop K.stepJ .ne) <| .seq (.block K.outFix) (fprogB K.M K.outOps)

/-- `[k]G` into `A`, in projective coordinates: pipelined where it applies
(`pipeOk`). -/
def combJ : Prog isa := if K.pipeOk then K.combJP else K.combJ0

end TCombCfg

end VG.Impl.Weierstrass.X86_64
