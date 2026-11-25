import Rind.P256Group
import Rind.P384Group

/-!
# The NIST curves' group law, computed

`nist.inv` picks the inverse by `Classical.choose`, and `nist.pow` adds a point
once per unit of the scalar, so neither runs on a real key. `invC`, `addC`,
and `powC` compute them, by ZMod's inverse and by doubling and adding, and the
theorems below prove each equal to its spec on the inputs the proofs pass it:
a prime field, and a point on the curve. `ecdsaSignC` and `ecdsaVerifiesC`
are FIPS 186-5's ECDSA over them, proven equal to `nist.ecdsaSign` and
`nist.ecdsaVerifies`. The spec tests (`Rind.SpecTest.Server`) run these.
-/

namespace rind.spec.nist

/-- `inv`, by ZMod's inverse. -/
def invC (p a : Nat) : Nat := if a < p then ((a : ZMod p)⁻¹).val else 0

/-- `add`, with `invC` for `inv`. -/
def addC (p : Nat) : Point → Point → Point
  | none, q => q
  | P, none => P
  | some (x1, y1), some (x2, y2) =>
    if x1 = x2 then
      if y1 = y2 ∧ y1 ≠ 0 then
        let m := (3 * (x1 ^ 2 % p) % p + (p - 3)) % p * invC p (2 * y1 % p) % p
        let x3 := sub p (m ^ 2 % p) (2 * x1 % p)
        let y3 := sub p (m * sub p x1 x3 % p) y1
        some (x3, y3)
      else none
    else
      let m := sub p y2 y1 * invC p (sub p x2 x1) % p
      let x3 := sub p (m ^ 2 % p) ((x1 + x2) % p)
      let y3 := sub p (m * sub p x1 x3 % p) y1
      some (x3, y3)

/-- `pow`, by doubling and adding from the scalar's top bit. -/
def powC (p : Nat) (P : Point) (n : Nat) : Point :=
  if n = 0 then none
  else
    let h := powC p P (n / 2)
    let d := addC p h h
    if n % 2 = 0 then d else addC p P d
termination_by n
decreasing_by omega

/-- `ecdsaSign`, over `powC`. -/
def ecdsaSignC (p n : Nat) (G : Point) (d k e : Nat) : Option (Nat × Nat) :=
  match powC p G k with
  | some (x, _) => some (x % n, (((e + x % n * d : Nat) : ZMod n) * (k : ZMod n)⁻¹).val)
  | none => none

/-- `ecdsaVerifies`, decided, over `addC` and `powC`. -/
def ecdsaVerifiesC (p n : Nat) (G Q : Point) (e r s : Nat) : Bool :=
  decide (0 < r ∧ r < n ∧ 0 < s ∧ s < n) &&
    match addC p (powC p G (((e : ZMod n) * (s : ZMod n)⁻¹).val))
        (powC p Q (((r : ZMod n) * (s : ZMod n)⁻¹).val)) with
    | some (x, _) => x % n == r
    | none => false

variable {p : Nat} [Fact p.Prime]

theorem inv_eq_invC (a : Nat) : inv p a = invC p a := by
  unfold invC
  split_ifs with h
  · have := inv_val (p := p) (a : ZMod p)
    rwa [ZMod.val_natCast_of_lt h] at this
  · unfold inv
    split_ifs with h'
    · exact absurd h'.1 h
    · rfl

theorem add_eq_addC (P Q : Point) : add p P Q = addC p P Q := by
  have h : inv p = invC p := funext inv_eq_invC
  cases P <;> cases Q <;> simp only [add, addC, h]

variable [Fact (3 < p)] {b : Nat}

theorem powC_fromM (X : (curve p b).Point) (n : Nat) : powC p (fromM X) n = fromM (n • X) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [powC]
    split_ifs with h0 h2
    · subst h0; simp [fromM]
    · simp only []
      rw [ih (n / 2) (by omega), ← add_eq_addC, fromM_add, ← add_nsmul]
      congr 2; omega
    · simp only []
      rw [ih (n / 2) (by omega)]
      simp only [← add_eq_addC, fromM_add]
      rw [← add_nsmul, ← succ_nsmul']
      congr 2; omega

/-- `powC` is `pow` on a point of the curve. -/
theorem pow_eq_powC (hb2 : (b + 2) % p ≠ 0) (hb2' : (b + (p - 2)) % p ≠ 0) {P : Point}
    (hP : OnCurve p b P) (n : Nat) : pow p P n = powC p P n := by
  obtain ⟨X, rfl⟩ : ∃ X : (curve p b).Point, fromM X = P := by
    match P, hP with
    | none, _ => exact ⟨0, rfl⟩
    | some (x, y), h => exact fromM_of_onCurve hb2 hb2' h
  rw [pow_fromM, powC_fromM]

theorem ecdsaSign_eq_ecdsaSignC (hb2 : (b + 2) % p ≠ 0) (hb2' : (b + (p - 2)) % p ≠ 0) {G : Point}
    (hG : OnCurve p b G) (n d k e : Nat) : ecdsaSign p n G d k e = ecdsaSignC p n G d k e := by
  rw [ecdsaSign, ecdsaSignC, pow_eq_powC hb2 hb2' hG]
  rcases powC p G k with _ | ⟨x, y⟩ <;> rfl

theorem ecdsaVerifies_iff (hb2 : (b + 2) % p ≠ 0) (hb2' : (b + (p - 2)) % p ≠ 0) {G Q : Point}
    (hG : OnCurve p b G) (hQ : OnCurve p b Q) (n e r s : Nat) :
    ecdsaVerifies p n G Q e r s ↔ ecdsaVerifiesC p n G Q e r s = true := by
  rw [ecdsaVerifies, ecdsaVerifiesC, pow_eq_powC hb2 hb2' hG, pow_eq_powC hb2 hb2' hQ, add_eq_addC]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h⟩
    refine ⟨⟨h1, h2, h3, h4⟩, ?_⟩
    split at h <;> simp_all
  · rintro ⟨⟨h1, h2, h3, h4⟩, h⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    split at h <;> simp_all

end rind.spec.nist
