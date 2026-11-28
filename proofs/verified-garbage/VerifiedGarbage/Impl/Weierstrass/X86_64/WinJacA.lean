module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJac

/-!
# Short Weierstrass curves on x86-64: 5-bit windows with an affine table

The window method of `WinJac.lean`, with its table brought into affine
coordinates once it is built, so that each iteration adds the entry by the
mixed addition (`maddJ`, 8 products and 3 squares) rather than by the
Jacobian addition with the entry's cached powers (11 and 3). The code of an
iteration is then also smaller: on some processors the doubling and the
Jacobian addition together no longer fit the instruction cache.

The table is made affine by one inversion (`normA`, Montgomery's trick): the
prefix products of the entries' `Z`, `c_1 = Z_1` and `c_m = c_{m-1} Z_m`,
`c_m` in entry `m`'s `Z²` for `2 ≤ m < 16` (which the window no longer
reads) and `c_16` in `R.z`; then `inv` leaves `c_16^(p-2)` in `E.x`, from
which, for `m = 16` down to `2`, `D.x = c_m^(p-2) c_{m-1} = Z_m^(p-2)`,
`E.x = c_m^(p-2) Z_m = c_{m-1}^(p-2)`, and entry `m`'s `X`, `Y` are
multiplied by `D.x²` and `D.x³`; entry `1`'s by `E.x`'s. Then every entry's `Z`, `Z²` and `Z³` is set to Montgomery's one
(`ones`), so that the table still holds Jacobian triples with their powers,
which the first digit's entry reads as before.

The iterations (`stepA`) are those of `WinJac.lean`, but selecting only the
entry's `X` and `Y` (`selectA`, `T`'s `Z` set to one), with `D = R + T` by
the mixed addition: it is right unless `R = T` (the Jacobian addition's
exception, which the recoding rules out) or `R = O` (where `D = T`, as
before).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace JacWinCfg

variable (K : JacWinCfg)

/-- Coordinate `c` of entry `m` (from 1): `X`, `Y`, `Z`, `Z²`, `Z³`. -/
def ent (m c : Nat) : Nat := K.tbl + 8 * K.M.n * (5 * (m - 1) + c)

/-- Where the prefix product `c_m` is, `1 ≤ m ≤ 16`: `c_1 = Z_1` in entry
`1`'s `Z`, `c_16` in `R.z`, the others in entry `m`'s `Z²`. -/
def pre (m : Nat) : Nat := if m = 1 then K.ent 1 2 else if m = 16 then K.R.z else K.ent m 3

/-- `c_2 … c_16`. -/
def prodOps : List FOp := (List.range 15).map fun i => .mul (K.pre (i + 2)) (K.pre (i + 1)) (K.ent (i + 2) 2)

/-- Entry `m ≥ 2` into affine coordinates, from `c_m^(p-2)` in `E.x`:
`D.x = c_m^(p-2) c_{m-1} = Z_m^(p-2)`, `E.x = c_m^(p-2) Z_m = c_{m-1}^(p-2)`,
`X` by `D.x²` (in `D.y`) and `Y` by `D.x³` (in `D.z`). -/
def backOps (m : Nat) : List FOp :=
  [.mul K.D.x K.E.x (K.pre (m - 1)), .mul K.E.x K.E.x (K.ent m 2), .mul K.D.y K.D.x K.D.x,
    .mul (K.ent m 0) (K.ent m 0) K.D.y, .mul K.D.z K.D.y K.D.x, .mul (K.ent m 1) (K.ent m 1) K.D.z]

/-- Entries `16` down to `2`, then entry `1` (by `E.x = c_1^(p-2) = Z_1^(p-2)`). -/
def normOps : List FOp :=
  (List.range 15).flatMap (fun i => K.backOps (16 - i)) ++
    [.mul K.D.y K.E.x K.E.x, .mul (K.ent 1 0) (K.ent 1 0) K.D.y, .mul K.D.z K.D.y K.E.x,
      .mul (K.ent 1 1) (K.ent 1 1) K.D.z]

/-- Every entry's `Z`, `Z²` and `Z³` set to Montgomery's one. -/
def ones : List Instr :=
  (List.range 48).flatMap fun i => setConst K.M.n (K.ent (i / 3 + 1) (2 + i % 3)) K.one

/-- The table into affine coordinates, by one inversion: the prefix products,
`inv` (`E.x = R.z^(p-2)`), the entries' `X` and `Y`, and the powers of `Z`
one. -/
def normA (inv : Prog isa) : Prog isa :=
  .seq (fprogB K.M K.prodOps) <| .seq inv <| .seq (fprogB K.M K.normOps) (.block K.ones)

/-- An iteration's selection: `select`, but of the entry's `X` and `Y` alone
(`2n` words, the first `n` 16-byte pieces), and `T`'s `Z` set to one, which
every entry's is: the mixed addition reads neither `Z²` nor `Z³`. For
`a = 0`, `T = (0, 0, 1)`, which the iteration does not keep. -/
def selectA : List Instr :=
  [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))] ++
  (if K.avx2 then selPassY K.T 16 K.st ((K.M.n + 1) / 2) (qY K.M.n)
  else selPassAt K.T 16 K.st K.M.n (16 * ·)) ++
  setConst K.M.n K.E.z K.one

/-- Iteration `j = rbx - 1` (with `rbx` counting down from `J - 1`):
`R = 32 R + [d_j]P`, adding the affine entry by the mixed addition. -/
def stepA (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (K.dbls dbl) <|
  .seq (.block (K.tc.digit ++ K.selectA)) <|
  .seq (.block K.tc.negY) <|
  .seq (.block (fprog K.M (maddJ K.S K.R K.E K.D))) <|
  .block (nzMask K.M.n K.R.z ++ selPt K.M.n K.D K.E K.D ++
    K.tc.digit ++ eqMask 0 ++ selPt K.M.n K.R K.D K.R ++ [.alu .test .rbx (.reg .rbx)])

/-- `[k]P` into `R`, in projective coordinates, for the table of the bits of
`k + offset J` at `K.bits`, with `inv` leaving `R.z^(p-2)` in `E.x`. -/
def windowA (inv : Prog isa) (dbl : Pt → Prog isa) : Prog isa :=
  .seq K.build <| .seq (K.normA inv) <| .seq (.block K.first) <| .seq (.loop (K.stepA dbl) .ne) <|
  .seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps)

end JacWinCfg

end VG.Impl.Weierstrass.X86_64
