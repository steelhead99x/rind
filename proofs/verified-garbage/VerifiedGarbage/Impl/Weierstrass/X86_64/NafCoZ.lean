module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
public import VerifiedGarbage.Impl.Weierstrass.CoZ

/-!
# The public NAF's table by co-Z arithmetic, on x86-64

`P, 3P, …, 15P` as `Naf.table` leaves them, but by co-Z arithmetic
(`Impl/Weierstrass/CoZ.lean`): `P` (affine, its `z` Montgomery's one) into
the first entry; DBLU gives `2P` in `E` (`x`, `y`) and `P` in `R`, at
one `Z` in `R.z`; then seven times ZADDU, `R = R + 2P` with `E` the same `2P`
at the new `Z`, stored in the next entry; at the end `2P` (`E`'s `x`, `y` and
`R`'s `z`) into the ninth entry, where `Naf.table` keeps it.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass

/-- ZADDU's slots (`CoZ`): the addend in `E`, the temporaries, the sum in
`R`, two unused slots and `P`, whose `z` is one. -/
def coZσ (K : WinCfg) (i : Nat) : Nat :=
  [K.E.x, K.E.y, K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.R.x, K.R.y, K.R.z,
    K.D.x, K.D.y, K.P.x, K.P.y, K.P.z].getD i K.P.x

/-- DBLU's slots: `2P` into `E` (`x`, `y`), `P` at the same `Z` into `R`, as
ZADDU takes them. -/
def dbluσ (K : WinCfg) (i : Nat) : Nat :=
  [K.S.t4, K.S.t5, K.S.t0, K.S.t1, K.R.y, K.R.x, K.S.t2, K.S.t3, K.E.x, K.E.y, K.R.z,
    K.D.x, K.D.y, K.P.x, K.P.y, K.P.z].getD i K.P.x

def dbluOps (K : WinCfg) : List FOp := CoZ.dblu.map (CoZ.rename (dbluσ K))
def zadduOps (K : WinCfg) : List FOp := CoZ.zaddu.map (CoZ.rename (coZσ K))

/-- `R = R + 2P` by ZADDU, `E = 2P` at the new `Z`, stored in entry `rbx`
(from zero); then `rbx + 1`, compared with 8. -/
def tableCoZStep (K : WinCfg) : Prog isa :=
  .seq (fprogB K.M (zadduOps K)) <|
    .block (tableStore K ++ [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 8)])

/-- `2P` after ZADDU: `E`'s `x` and `y` at `R`'s `Z`. -/
def coZD (K : WinCfg) : Pt := ⟨K.E.x, K.E.y, K.R.z⟩

/-- `2P` into the ninth entry. -/
def coZTwice (K : WinCfg) : List Instr := copyPt K.M.n (twice K) (coZD K)

/-- The table by co-Z arithmetic (`Naf.table`'s result). -/
def tableCoZ (K : WinCfg) : Prog isa :=
  .seq (.block (copyPt K.M.n (K.tblPt 1) K.P ++ [.mov32 .rbx (.imm 1)])) <|
  .seq (fprogB K.M (dbluOps K)) <|
  .seq (.loop (tableCoZStep K) .b) (.block (coZTwice K))

end VG.Impl.Weierstrass.X86_64.Naf
