import Rind.SymCrypt.Sha3
import Mathlib.Tactic.IntervalCases

/-!
# Keccak-f[1600] on lanes

s2n-bignum's Keccak spec, `keccak_spec.ml` at the revision rind transliterates
(b4f17ee7), in which its Keccak routines' theorems are stated: the state as 25
64-bit lanes in row-major order, lane `5 * y + x` holding FIPS 202's `A[x, y]`.
`keccak_eq_KECCAK_f` proves its 24 rounds FIPS 202's `KECCAK-f[1600]`, as
SymCrypt's transliteration defines it, on the string whose bits are the lanes'
in order, each least significant bit first (FIPS 202 section 3.1.2).
-/

namespace rind.spec

open Spec Spec.SHA3
open scoped Spec.Notations

/-- `round_constants`. -/
def keccakRoundConstants : List (BitVec 64) :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
   0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
   0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
   0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
   0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
   0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- `rho8_constant`, the byte shuffle x86_64's four-way routine rotates by 8 with. -/
def keccakRho8 : List (BitVec 64) :=
  [0x0605040302010007, 0x0E0D0C0B0A09080F, 0x1615141312111017, 0x1E1D1C1B1A19181F]

/-- `rho56_constant`, the byte shuffle x86_64's four-way routine rotates by 56 with. -/
def keccakRho56 : List (BitVec 64) :=
  [0x0007060504030201, 0x080F0E0D0C0B0A09, 0x1017161514131211, 0x181F1E1D1C1B1A19]

/-- `keccak_round`: one round, its lanes named `Axy` for `A[x, y]`. HOL Light's
`^^` associates to the right, as the parentheses here do. -/
def keccakRound (RCi : BitVec 64) (Alist : List (BitVec 64)) : List (BitVec 64) :=
  let A00 := Alist[0]!
  let A10 := Alist[1]!
  let A20 := Alist[2]!
  let A30 := Alist[3]!
  let A40 := Alist[4]!
  let A01 := Alist[5]!
  let A11 := Alist[6]!
  let A21 := Alist[7]!
  let A31 := Alist[8]!
  let A41 := Alist[9]!
  let A02 := Alist[10]!
  let A12 := Alist[11]!
  let A22 := Alist[12]!
  let A32 := Alist[13]!
  let A42 := Alist[14]!
  let A03 := Alist[15]!
  let A13 := Alist[16]!
  let A23 := Alist[17]!
  let A33 := Alist[18]!
  let A43 := Alist[19]!
  let A04 := Alist[20]!
  let A14 := Alist[21]!
  let A24 := Alist[22]!
  let A34 := Alist[23]!
  let A44 := Alist[24]!
  let C0 := A00 ^^^ (A01 ^^^ (A02 ^^^ (A03 ^^^ A04)))
  let C1 := A10 ^^^ (A11 ^^^ (A12 ^^^ (A13 ^^^ A14)))
  let C2 := A20 ^^^ (A21 ^^^ (A22 ^^^ (A23 ^^^ A24)))
  let C3 := A30 ^^^ (A31 ^^^ (A32 ^^^ (A33 ^^^ A34)))
  let C4 := A40 ^^^ (A41 ^^^ (A42 ^^^ (A43 ^^^ A44)))
  let D0 := C4 ^^^ C1.rotateLeft 1
  let D1 := C0 ^^^ C2.rotateLeft 1
  let D2 := C1 ^^^ C3.rotateLeft 1
  let D3 := C2 ^^^ C4.rotateLeft 1
  let D4 := C3 ^^^ C0.rotateLeft 1
  let At00 := A00 ^^^ D0
  let At01 := A01 ^^^ D0
  let At02 := A02 ^^^ D0
  let At03 := A03 ^^^ D0
  let At04 := A04 ^^^ D0
  let At10 := A10 ^^^ D1
  let At11 := A11 ^^^ D1
  let At12 := A12 ^^^ D1
  let At13 := A13 ^^^ D1
  let At14 := A14 ^^^ D1
  let At20 := A20 ^^^ D2
  let At21 := A21 ^^^ D2
  let At22 := A22 ^^^ D2
  let At23 := A23 ^^^ D2
  let At24 := A24 ^^^ D2
  let At30 := A30 ^^^ D3
  let At31 := A31 ^^^ D3
  let At32 := A32 ^^^ D3
  let At33 := A33 ^^^ D3
  let At34 := A34 ^^^ D3
  let At40 := A40 ^^^ D4
  let At41 := A41 ^^^ D4
  let At42 := A42 ^^^ D4
  let At43 := A43 ^^^ D4
  let At44 := A44 ^^^ D4
  let B00 := At00.rotateLeft 0
  let B01 := At30.rotateLeft 28
  let B02 := At10.rotateLeft 1
  let B03 := At40.rotateLeft 27
  let B04 := At20.rotateLeft 62
  let B10 := At11.rotateLeft 44
  let B11 := At41.rotateLeft 20
  let B12 := At21.rotateLeft 6
  let B13 := At01.rotateLeft 36
  let B14 := At31.rotateLeft 55
  let B20 := At22.rotateLeft 43
  let B21 := At02.rotateLeft 3
  let B22 := At32.rotateLeft 25
  let B23 := At12.rotateLeft 10
  let B24 := At42.rotateLeft 39
  let B30 := At33.rotateLeft 21
  let B31 := At13.rotateLeft 45
  let B32 := At43.rotateLeft 8
  let B33 := At23.rotateLeft 15
  let B34 := At03.rotateLeft 41
  let B40 := At44.rotateLeft 14
  let B41 := At24.rotateLeft 61
  let B42 := At04.rotateLeft 18
  let B43 := At34.rotateLeft 56
  let B44 := At14.rotateLeft 2
  [(B00 ^^^ (~~~B10 &&& B20)) ^^^ RCi,
   B10 ^^^ (~~~B20 &&& B30),
   B20 ^^^ (~~~B30 &&& B40),
   B30 ^^^ (~~~B40 &&& B00),
   B40 ^^^ (~~~B00 &&& B10),
   B01 ^^^ (~~~B11 &&& B21),
   B11 ^^^ (~~~B21 &&& B31),
   B21 ^^^ (~~~B31 &&& B41),
   B31 ^^^ (~~~B41 &&& B01),
   B41 ^^^ (~~~B01 &&& B11),
   B02 ^^^ (~~~B12 &&& B22),
   B12 ^^^ (~~~B22 &&& B32),
   B22 ^^^ (~~~B32 &&& B42),
   B32 ^^^ (~~~B42 &&& B02),
   B42 ^^^ (~~~B02 &&& B12),
   B03 ^^^ (~~~B13 &&& B23),
   B13 ^^^ (~~~B23 &&& B33),
   B23 ^^^ (~~~B33 &&& B43),
   B33 ^^^ (~~~B43 &&& B03),
   B43 ^^^ (~~~B03 &&& B13),
   B04 ^^^ (~~~B14 &&& B24),
   B14 ^^^ (~~~B24 &&& B34),
   B24 ^^^ (~~~B34 &&& B44),
   B34 ^^^ (~~~B44 &&& B04),
   B44 ^^^ (~~~B04 &&& B14)]

/-- `keccak`: `n` rounds, round `i` with the `i`th constant. -/
def keccak : Nat → List (BitVec 64) → List (BitVec 64)
  | 0, l => l
  | n + 1, l => keccakRound keccakRoundConstants[n]! (keccak n l)

/-! ## Lanes as FIPS 202's bit strings -/

/-- A lane's bits, least significant first. -/
def lane (a : BitVec 64) : Lane := Vector.ofFn fun z => a.getLsbD z

/-- The string whose bits are the lanes', in order (FIPS 202 section 3.1.3). -/
def lanesToString (L : List (BitVec 64)) : Vector Bool b :=
  Vector.ofFn fun i => L[i.val / 64]!.getLsbD (i.val % 64)

/-- The state array of the lanes, `A[x, y]` lane `5 * y + x`. -/
def lanesToState (L : List (BitVec 64)) : State :=
  Vector.ofFn fun x => Vector.ofFn fun y => lane L[5 * y.val + x.val]!

@[simp] theorem getElem_vxor (u v : Vector Bool n) (i : Nat) (h : i < n) :
    (u ⊕ v)[i] = (u[i] != v[i]) := by
  simp [HXor.hXor, Vector.getElem_zipWith]

@[simp] theorem getElem_vand (u v : Vector Bool n) (i : Nat) (h : i < n) :
    (u &&& v)[i] = (u[i] && v[i]) := by
  simp [HAnd.hAnd, Vector.getElem_zipWith]

@[simp] theorem getElem_vnot (u : Vector Bool n) (i : Nat) (h : i < n) :
    (~~~u)[i] = !u[i] := by
  simp [Complement.complement]

@[simp] theorem getElem_lane (a : BitVec 64) (z : Nat) (h : z < 64) :
    (lane a)[z] = a.getLsbD z := by
  simp [lane, BitVec.getLsbD_eq_getElem h]

theorem lane_xor (a c : BitVec 64) : lane (a ^^^ c) = lane a ⊕ lane c := by
  ext z hz; simp only [w] at hz; simp [hz]

theorem lane_and (a c : BitVec 64) : lane (a &&& c) = lane a &&& lane c := by
  ext z hz; simp only [w] at hz; simp [hz]

theorem lane_not (a : BitVec 64) : lane (~~~a) = ~~~lane a := by
  ext z hz; simp only [w] at hz; simp [hz]

theorem lane_rotateLeft (a : BitVec 64) (k : Nat) :
    lane (a.rotateLeft k) = (lane a).rotateLeft k := by
  ext z hz
  simp only [w] at hz ⊢
  simp only [Vector.rotateLeft, show (64 = 0) = False by decide, dite_false,
    Vector.getElem_ofFn, getElem_lane _ _ hz, BitVec.getLsbD_rotateLeft]
  rw [getElem_lane _ _ (Nat.mod_lt _ (by omega))]
  split <;> rename_i h
  · congr 1; omega
  · simp only [hz, decide_true, Bool.true_and]; congr 1; omega

theorem stringToState_lanesToString (L : List (BitVec 64)) :
    stringToState (lanesToString L) = lanesToState L := by
  ext x hx y hy z hz
  simp only [w] at hz
  simp only [stringToState, lanesToString, lanesToState, Vector.getElem_ofFn, getElem_lane _ _ hz, w]
  congr 2 <;> omega

theorem stateToString_lanesToState (L : List (BitVec 64)) :
    stateToString (lanesToState L) = lanesToString L := by
  ext i hi
  simp only [b] at hi
  simp only [stateToString, lanesToString, lanesToState, Vector.getElem_ofFn, w]
  rw [getElem_lane _ _ (by omega)]
  congr 2; omega

/-- FIPS 202 section 3.2.2's Table 2, which Algorithm 2's loop computes. -/
theorem ρ_offsets :
    ρ.Offsets = #v[#v[0, 36, 3, 105, 210], #v[1, 300, 10, 45, 66], #v[190, 6, 171, 15, 253],
      #v[28, 55, 153, 21, 120], #v[91, 276, 231, 136, 78]] := by
  simp only [ρ.Offsets, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl]
  decide

set_option maxHeartbeats 4000000 in
/-- Algorithm 6's round constants, from Algorithm 5's LFSR, are s2n-bignum's. -/
theorem ι_RC (i : Nat) (hi : i < 24) : ι.RC i = lane keccakRoundConstants[i]! := by
  interval_cases i <;>
  · simp only [ι.RC, rc, Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range',
      Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
    decide +kernel

/-! ## Each step mapping on lanes -/

/-- A state's lanes, `A[x, y]` at `x y`. -/
abbrev Lanes := Fin 5 → Fin 5 → BitVec 64

/-- The state array of lanes. -/
def toState (f : Lanes) : State := Vector.ofFn fun x => Vector.ofFn fun y => lane (f x y)

/-- θ on lanes. -/
def θL (f : Lanes) : Lanes :=
  let C := fun x => f x 0 ^^^ (f x 1 ^^^ (f x 2 ^^^ (f x 3 ^^^ f x 4)))
  fun x y => f x y ^^^ (C (x - 1) ^^^ (C (x + 1)).rotateLeft 1)

/-- ρ's offsets, Table 2, modulo the lane size. -/
def ρL.offset (x y : Fin 5) : Nat :=
  (#v[#v[0, 36, 3, 41, 18], #v[1, 44, 10, 45, 2], #v[62, 6, 43, 15, 61],
    #v[28, 55, 25, 21, 56], #v[27, 20, 39, 8, 14]] : Vector (Vector Nat 5) 5)[x][y]

/-- ρ on lanes. -/
def ρL (f : Lanes) : Lanes := fun x y => (f x y).rotateLeft (ρL.offset x y)

/-- π on lanes. -/
def πL (f : Lanes) : Lanes := fun x y => f (x + 3 * y) x

/-- χ on lanes. -/
def χL (f : Lanes) : Lanes := fun x y => f x y ^^^ (~~~f (x + 1) y &&& f (x + 2) y)

/-- ι on lanes, with round constant `rc`. -/
def ιL (rc : BitVec 64) (f : Lanes) : Lanes :=
  fun x y => if x = 0 ∧ y = 0 then f x y ^^^ rc else f x y

theorem θ_toState (f : Lanes) : θ (toState f) = toState (θL f) := by
  ext x hx y hy : 2
  simp only [θ, θL, toState, Fin.getElem_fin, Vector.getElem_ofFn, lane_xor, lane_rotateLeft]
  rfl

theorem ρ_offset (x y : Fin 5) : ρ.Offsets[x.val][y.val] % w = ρL.offset x y := by
  rw [ρ_offsets]; revert x y; decide

theorem ρ_toState (f : Lanes) : ρ (toState f) = toState (ρL f) := by
  ext x hx y hy : 2
  simp only [ρ, ρL, toState, Fin.getElem_fin, Vector.getElem_ofFn, lane_rotateLeft, ρ_offset]

theorem π_toState (f : Lanes) : π (toState f) = toState (πL f) := by
  ext x hx y hy : 2
  simp only [π, πL, toState, Fin.getElem_fin, Vector.getElem_ofFn]

theorem χ_toState (f : Lanes) : χ (toState f) = toState (χL f) := by
  ext x hx y hy : 2
  simp only [χ, χL, toState, Fin.getElem_fin, Vector.getElem_ofFn, lane_xor, lane_and, lane_not]

theorem ι_toState (f : Lanes) (i : Nat) (rc : BitVec 64) (h : ι.RC i = lane rc) :
    ι (toState f) i = toState (ιL rc f) := by
  ext x hx y hy : 2
  simp only [ι, ιL, toState, Fin.getElem_fin, Vector.getElem_ofFn, h]
  split <;> simp [lane_xor]

/-- One round of FIPS 202's on the lanes' state array is s2n-bignum's. -/
theorem Rnd_lanesToState (L : List (BitVec 64)) (i : Nat) (hi : i < 24) :
    Rnd (lanesToState L) i = lanesToState (keccakRound keccakRoundConstants[i]! L) := by
  have hL : lanesToState L = toState fun x y => L[5 * y.val + x.val]! := rfl
  have hR : lanesToState (keccakRound keccakRoundConstants[i]! L) =
      toState fun x y => (keccakRound keccakRoundConstants[i]! L)[5 * y.val + x.val]! := rfl
  rw [hL, hR, Rnd, θ_toState, ρ_toState, π_toState, χ_toState,
    ι_toState _ _ _ (ι_RC i hi)]
  congr 1
  funext x y
  fin_cases x <;> fin_cases y <;> rfl

theorem foldl_Rnd_lanesToState (L : List (BitVec 64)) (n : Nat) (hn : n ≤ 24) :
    (List.range' 0 n).foldl (fun A i => Rnd A i) (lanesToState L) = lanesToState (keccak n L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_concat, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      Rnd_lanesToState _ _ (by omega), keccak, Nat.zero_add, Nat.one_mul]

/-- s2n-bignum's `keccak 24` is FIPS 202's `KECCAK-f[1600]`. -/
theorem keccak_eq_KECCAK_f (L : List (BitVec 64)) :
    lanesToString (keccak 24 L) = KECCAK_f (lanesToString L) := by
  simp only [KECCAK_f, KECCAK_p, ℓ]
  simp only [Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl,
    stringToState_lanesToString, List.foldl_attach, pure_bind]
  rw [show (12 + 2 * 6 - 24) = 0 by rfl, show [0:12 + 2 * 6].size = 24 by rfl,
    foldl_Rnd_lanesToState _ _ (by omega), stateToString_lanesToState]
  rfl

end rind.spec
