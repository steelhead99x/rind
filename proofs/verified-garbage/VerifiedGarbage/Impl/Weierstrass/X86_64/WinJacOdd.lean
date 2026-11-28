module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJac

/-!
# Short Weierstrass curves on x86-64: scalar multiplication by odd 5-bit windows in Jacobian coordinates

The window method of `WinJac.lean` for an odd scalar `k < 2^(5 J - 4)`,
recoded regularly into `J` odd digits `d_j = 2 e_j - 31 ∈ [-31, 31]`, where
`e_j` is window `j` of `(k + 32^J - 1) / 2`: the 5-bit windows of
`k + 32^J - 1` read from its bit 1 (the table of bits at `bits`, one past
that of `k + 32^J - 1`). With no zero digit, and the operands of every
addition neither equal nor opposite nor `O` for `1 ≤ k < n` and
`n mod 64 < 33` (`Proof/Weierstrass/X86_64/WinJacOddState.lean`), the loop needs none of
`WinJac`'s masks.

The table holds the odd multiples `[2m - 1]P` for `m = 1 … 16`, entry `m` at
`tbl + 40 n (m - 1)` (`buildO`): `P` (`Z = 1`); then DBLU gives `2P` and `P`
sharing its `Z`, which become `D` and `T`; and `T = T + D` by ZADDU, which
leaves `D = 2P` with the sum's `Z`, gives `[3]P … [31]P`. Digit `j`'s entry
is `m = ((e_j ⊕ s) ∧ 15) + 1` with `s` all ones for `e_j < 16`
(`magnitudeO`), its `Y` negated for `e_j < 16`, the top bit of the window
clear, as `WinJac`'s.

The top digit is 1 (`e_{J-1} = 16`), so `R = P` (`firstO`); then, for
`j = J - 2` down to `0`, `R = 32 R + [d_j]P` (`stepO`): five doublings, the
entry selected and negated, and `R = R + T` in place by Jacobian addition
with `T`'s cached powers (`addOpsO`: `jacTail` reads `R`'s `X` and `Y`
before writing them, and `R`'s `Z` before its product).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- `[k] = n - [k]` if `[k]` is even, `n` words, through `[t]`, `rax`, `rcx`,
`rdx` and `r8`: `n - [k]` into `[t]`, and the mask `rcx = ([k] ∧ 1) - 1`
selecting it. -/
def oddScalar (n nv k t : Nat) : List Instr :=
  setConst n t nv ++ chainW .sub .sbb n t t k ++
    [.mov .rcx (.mem (sc k)), .alu .and .rcx (.imm 1), .alu .sub .rcx (.imm 1)] ++ sel n k k t

namespace JacWinCfg

variable (K : JacWinCfg)

/-- From the window `e` in `rax`: the entry `((e ⊕ s) ∧ 15) + 1` of its odd
digit's magnitude, `s = (e >> 4) - 1` all ones for `e < 16`, into `rax`
and `r8`, through `rdx`. -/
def magnitudeO : List Instr :=
  [.mov .rdx (.reg .rax), .shift .shr .rdx 4, .alu .sub .rdx (.imm 1), .alu .xor .rax (.reg .rdx),
    .alu .and .rax (.imm 15), .alu .add .rax (.imm 1), .mov .r8 (.reg .rax)]

/-- Digit `rbx`'s entry into `r8`, from its window as the comb reads it. -/
def digitO : List Instr := winIndex 5 ++ hornerBits K.bits 5 ++ magnitudeO

/-- The table of `[2m - 1]P`: `T = P` (`Z = 1`) into entry 1; DBLU, `T = 2 P`
and `D = P` sharing its `Z`, exchanged; then `T = T + D` by ZADDU into
entries 2 to 16 (`buildStep`, from `rbx = 1`). -/
def buildO : Prog isa :=
  .seq (.block (copyPt K.M.n K.E K.P ++ copy K.M.n K.z2 K.P.z ++ copy K.M.n (K.z2 + 8 * K.M.n) K.P.z ++
    [.mov32 .rbx (.imm 1)] ++ K.storeEntry)) <|
  .seq (ForwardField.programB K.M K.dbluOps) <|
  .seq (.block (copy K.M.n K.D.x K.E.x ++ copy K.M.n K.D.y K.E.y ++ copy K.M.n K.E.x K.S.t3 ++
    copy K.M.n K.E.y K.S.t2)) <|
  .loop K.buildStep .ne

/-- `R = R + T` in place, with `T`'s cached powers. -/
def addOpsO : List FOp := CachedJac.head K.M.n K.S K.R K.E K.z2 ++ jacTail K.S K.R K.E K.R

/-- Iteration `j = rbx - 1` (with `rbx` counting down from `J - 1`):
`R = 32 R + [d_j]P`. -/
def stepO (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) <|
  .seq (.block (K.digitO ++ K.select)) <|
  .seq (.block K.tc.negY) <|
  .seq (ForwardField.programB K.M K.addOpsO) <|
  .block [.alu .test .rbx (.reg .rbx)]

/-- `rbx = J - 1` and `R = P`, the top digit's point. -/
def firstO : List Instr := [.mov32 .rbx (.imm (BitVec.ofNat 32 (K.J - 1)))] ++ copyPt K.M.n K.R K.P

/-- `[k]P` into `R`, in projective coordinates, for the table of the bits of
`k + 32^J - 1` at `K.bits - 1`. -/
def windowO (dbl : Pt → Prog isa) : Prog isa :=
  .seq K.buildO <| .seq (.block K.firstO) <| .seq (.loop (K.stepO dbl) .ne) <|
  .seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps)

end JacWinCfg

end VG.Impl.Weierstrass.X86_64
