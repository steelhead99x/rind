import Rind.X86_64.Ed25519
import Rind.X86_64.HalfSize
import Rind.Ed25519Group
open Aeneas Aeneas.Std Result rind.spec

/-!
# Ed25519 verification on x86_64, proven to s2n-bignum's contracts

x86_64 checks Ed25519 signatures with half-size scalars: `commits` checks that
`[v S mod L]B - [v]R - [u]A` is the identity, for the `u ≡ v k (mod 8L)` that
`mid::half_size::split` finds, which `Rind.X86_64.HalfSize` proves, and
`Rind.Ed25519Group`'s `half_size_iff` proves that the check accepts exactly
what `ed25519Verifies` does: RFC 8032's cofactorless equation, with the
challenge reduced mod L. That argument needs the group's orders, which HOL
Light proves and Lean does not yet, so these theorems take them as the
hypothesis `EdOrders`. The multi-scalar multiplication `commits` runs,
`low::x86_64::adx_mux::edwards25519_msm`, is Rust over s2n-bignum's point
routines that no proof covers yet
(`quest/m4/verified/ed25519-half-scalar.md`), so they also take its contract
as the hypothesis `RunsMsm`. No axiom states either.
-/

namespace rind.x86_64

/-! ## Points in projective coordinates -/

/-- HOL Light's `edwards25519_projective P (X,Y,Z)` of the twelve words `q`:
the coordinates are reduced, `Z` is not zero, and `x = X/Z` and `y = Y/Z` mod
`p`. HOL Light also requires `P`'s own coordinates to be reduced, which this
leaves to the caller (`edOnCurve P` says it): `P = (p, 1)` passes here as
`(0, 1)`. -/
def Projective (P : EdPoint) (q : List U64) : Prop :=
  wordsNat (q.take 4) < p25519 ∧ wordsNat ((q.drop 4).take 4) < p25519 ∧
    wordsNat ((q.drop 8).take 4) < p25519 ∧ wordsNat ((q.drop 8).take 4) ≠ 0 ∧
    (wordsNat (q.take 4) : Int) ≡ P.1 * wordsNat ((q.drop 8).take 4) [ZMOD p25519] ∧
    (wordsNat ((q.drop 4).take 4) : Int) ≡ P.2 * wordsNat ((q.drop 8).take 4) [ZMOD p25519]

/-- HOL Light's `edwards25519_exprojective P (X,Y,Z,W)` of the sixteen words
`q`: `Projective`, with `W = XY/Z` reduced; the same caller condition on `P`
applies. -/
def ExProjective (P : EdPoint) (q : List U64) : Prop :=
  Projective P q ∧ wordsNat ((q.drop 12).take 4) < p25519 ∧
    (wordsNat ((q.drop 12).take 4) * wordsNat ((q.drop 8).take 4) : Int) ≡
      wordsNat (q.take 4) * wordsNat ((q.drop 4).take 4) [ZMOD p25519]

/-- The contract of the multi-scalar multiplication Ed25519 verification runs,
`low::x86_64::adx_mux::edwards25519_msm`: for scalars below 2^255 and two
points of the group in extended coordinates, it writes
`[base]B + [s₀]P₀ + [s₁]P₁` in projective coordinates. No proof covers it yet,
so the theorems below take it as a hypothesis. -/
def RunsMsm : Prop :=
  ∀ (res : Std.Array U64 12#usize) (base : Std.Array U64 4#usize)
    (scalars : Std.Array (Std.Array U64 4#usize) 2#usize) (points : Std.Array (Std.Array U64 16#usize) 2#usize)
    (P₀ P₁ : EdPoint), edOnCurve P₀ → edOnCurve P₁ →
    ExProjective P₀ points.val[0]!.val → ExProjective P₁ points.val[1]!.val →
    wordsNat base.val < 2 ^ 255 → wordsNat scalars.val[0]!.val < 2 ^ 255 →
    wordsNat scalars.val[1]!.val < 2 ^ 255 →
    low.x86_64.adx_mux.edwards25519_msm res base scalars points ⦃ r =>
      Projective (edMul (edMul (edPow edB (wordsNat base.val)) (edPow P₀ (wordsNat scalars.val[0]!.val)))
        (edPow P₁ (wordsNat scalars.val[1]!.val))) r.val ⦄

theorem int_prime_p : Prime (p25519 : Int) := Nat.prime_iff_prime_int.mp p25519_prime

/-- A number below `p` that `p` divides is zero. -/
theorem eq_of_dvd_sub {a b : Int} (ha0 : 0 ≤ a) (ha : a < p25519) (hb0 : 0 ≤ b) (hb : b < p25519)
    (h : (p25519 : Int) ∣ a - b) : a = b := by
  obtain ⟨c, hc⟩ := h
  have : c = 0 := by
    by_contra hc0
    rcases lt_or_gt_of_ne hc0 with h' | h' <;> nlinarith
  subst this; omega

/-- The identity is `(0 : Z : Z)`: a point of the group in projective
coordinates is the identity exactly when `X = 0` and `Y = Z`. -/
theorem projective_id {P : EdPoint} (hP : edOnCurve P) {q : List U64} (h : Projective P q) :
    (wordsNat (q.take 4) = 0 ∧ wordsNat ((q.drop 4).take 4) = wordsNat ((q.drop 8).take 4)) ↔ P = edId := by
  obtain ⟨x, y⟩ := P
  obtain ⟨hx0, hx1, hy0, hy1, -⟩ := hP
  obtain ⟨hX, hY, hZ, hZ0, hXc, hYc⟩ := h
  generalize wordsNat (q.take 4) = X at *
  generalize wordsNat ((q.drop 4).take 4) = Y at *
  generalize wordsNat ((q.drop 8).take 4) = Z at *
  simp only at *
  have hpZ : ¬ (p25519 : Int) ∣ Z := by
    intro ⟨c, hc⟩
    have : c = 0 := by
      by_contra hc0
      rcases lt_or_gt_of_ne hc0 with h' | h' <;> nlinarith [show (0 : Int) < p25519 by decide]
    subst this; omega
  simp only [edId, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, hYZ⟩
    subst hYZ
    have h1 : (p25519 : Int) ∣ x * Y := by
      have := hXc.symm.dvd; simpa using this
    have h2 : (p25519 : Int) ∣ (y - 1) * Y := by
      have := hYc.symm.dvd; rw [show (y - 1) * (Y : Int) = -(Y - y * Y) by ring]; exact (dvd_neg).mpr this
    refine ⟨?_, ?_⟩
    · rcases int_prime_p.dvd_or_dvd h1 with h | h
      · exact (eq_of_dvd_sub hx0 hx1 (le_refl 0) (by decide) (by simpa using h))
      · exact absurd h hpZ
    · rcases int_prime_p.dvd_or_dvd h2 with h | h
      · exact eq_of_dvd_sub hy0 hy1 (by norm_num) (by decide) h
      · exact absurd h hpZ
  · rintro ⟨rfl, rfl⟩
    have hp : (0 : Int) < p25519 := by decide
    refine ⟨?_, ?_⟩
    · have h := hXc.dvd
      have := eq_of_dvd_sub (a := 0) (b := (X : Int)) (le_refl 0) hp (by positivity) (by exact_mod_cast hX)
        (by simpa using h)
      omega
    · have h := hYc.dvd
      have := eq_of_dvd_sub (a := (Z : Int)) (b := (Y : Int)) (by positivity) (by exact_mod_cast hZ)
        (by positivity) (by exact_mod_cast hY) (by simpa using h)
      omega

/-! ## `commits` -/

@[step]
theorem extended_spec (h : Runs) (p : Std.Array U64 8#usize) (P : EdPoint) (hP : edOnCurve P)
    (hp : pairNat p.val = edModEncodePair P) :
    mid.ed25519.EdwardsPoint.extended p ⦃ q => ExProjective P q.val ⦄ := by
  unfold mid.ed25519.EdwardsPoint.extended
  step*
  have hp8 : p.val.length = 8 := p.property
  have ht4 : t1.val.length = 4 := t1.property
  have hq : (index_mut_back1 s7).val = p.val ++ [1#u64, 0#u64, 0#u64, 0#u64] ++ t1.val := by
    have hz : (Std.Array.repeat 16#usize 0#u64).val = [] ++ List.replicate 16 0#u64 := by simp [Std.Array.repeat]
    rw [s5_post2, s7_post, s6_post, out2_post, Std.Array.set_val_eq, s2_post2, s4_post, s3_post,
      Std.Array.val_to_slice, hz, setSlice!_at [] _ _ 0 rfl (by simp [hp8])]
    have hr : List.drop p.val.length (List.replicate 16 0#u64) =
        [0#u64, 0#u64, 0#u64, 0#u64] ++ List.replicate 4 0#u64 := by rw [hp8]; rfl
    rw [List.nil_append, hr, List.set_append_right _ _ (by simp [hp8]), hp8]
    rw [show (8#usize).val - 8 = 0 from rfl,
      show ([0#u64, 0#u64, 0#u64, 0#u64] ++ List.replicate 4 0#u64).set 0 1#u64 =
        [1#u64, 0#u64, 0#u64, 0#u64] ++ List.replicate 4 0#u64 from rfl,
      ← List.append_assoc, Std.Array.val_to_slice,
      setSlice!_at _ _ _ 12 (by simp [hp8]) (by simp [ht4])]
    simp [ht4]
  have key : ∃ a b : Std.Array U64 4#usize, wordsNat t1.val = wordsNat a.val * wordsNat b.val % p25519 ∧
      a.val = s.val ∧ b.val = s1.val := ⟨_, _, t1_post, by simp_all, by simp_all⟩
  obtain ⟨a0, b0, ht, ha, hb⟩ := key
  have hx : wordsNat a0.val = edModEncode P.1 := by
    rw [ha, s_post, Std.Array.val_to_slice]
    have := congrArg Prod.fst hp; simpa [pairNat, edModEncodePair, List.slice] using this
  have hy : wordsNat b0.val = edModEncode P.2 := by
    rw [hb, s1_post, Std.Array.val_to_slice]
    have := congrArg Prod.snd hp
    have hd : (p.val.drop 4).take 4 = p.val.drop 4 := List.take_of_length_le (by simp [hp8])
    simpa [pairNat, edModEncodePair, hd] using this
  have hX1 : wordsNat (p.val.take 4) = edModEncode P.1 := congrArg Prod.fst hp
  have hY1 : wordsNat ((p.val.drop 4).take 4) = edModEncode P.2 := congrArg Prod.snd hp
  obtain ⟨hx0, hx1, hy0, hy1, -⟩ := hP
  have cx := edModEncode_of_onCurve _ hx0 hx1
  have cy := edModEncode_of_onCurve _ hy0 hy1
  have e1 : (p.val ++ [1#u64, 0#u64, 0#u64, 0#u64] ++ t1.val).take 4 = p.val.take 4 := by
    simp [List.take_append, hp8]
  have e2 : ((p.val ++ [1#u64, 0#u64, 0#u64, 0#u64] ++ t1.val).drop 4).take 4 = (p.val.drop 4).take 4 := by
    simp [List.drop_append, hp8]
  have e3 : ((p.val ++ [1#u64, 0#u64, 0#u64, 0#u64] ++ t1.val).drop 8).take 4 = [1#u64, 0#u64, 0#u64, 0#u64] := by
    simp [hp8]
  have e4 : ((p.val ++ [1#u64, 0#u64, 0#u64, 0#u64] ++ t1.val).drop 12).take 4 = t1.val := by
    simp [List.drop_append, hp8, ht4]
  have w1 : wordsNat [1#u64, 0#u64, 0#u64, 0#u64] = 1 := by decide
  have hpp : (0 : Nat) < p25519 := by decide
  unfold ExProjective Projective
  rw [hq, e1, e2, e3, e4, w1, ht, hx, hy, hX1, hY1]
  refine ⟨⟨edModEncode_lt _, edModEncode_lt _, by decide, by decide, ?_, ?_⟩, Nat.mod_lt _ hpp, ?_⟩
  · rw [cx]; simp
  · rw [cy]; simp
  · push_cast; rw [cx, cy, mul_one]; exact Int.mod_modEq _ _

/-- `commits`'s identity test on the words of `(X : Y : Z)`: `X = 0` and
`Y = Z`. -/
theorem id_words (q : List U64) (hl : q.length = 12) :
    ((q[0]! ||| q[1]! ||| q[2]! ||| q[3]!) = 0#u64 ∧ q[4]! = q[8]! ∧ q[5]! = q[9]! ∧ q[6]! = q[10]! ∧
        q[7]! = q[11]!) ↔
      (wordsNat (q.take 4) = 0 ∧ wordsNat ((q.drop 4).take 4) = wordsNat ((q.drop 8).take 4)) := by
  match q, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], _ =>
    simp only [List.take, List.drop, wordsNat, List.map, Nat.ofDigits, Nat.cast_id,
      List.getElem!_cons_zero, List.getElem!_cons_succ, UScalar.eq_equiv, UScalar.val_or]
    have b : ∀ x : U64, x.val < 2 ^ 64 := fun x => x.hBounds
    have := b a0; have := b a1; have := b a2; have := b a3; have := b a4; have := b a5
    have := b a6; have := b a7; have := b a8; have := b a9; have := b a10; have := b a11
    simp only [Nat.or_eq_zero_iff, show (0#u64).val = 0 from rfl]
    omega

/-- The coordinates `negate` writes for a point of the group are its
negation's, as s2n-bignum writes them. -/
theorem neg_encode (A : EdPoint) (hA : edOnCurve A) :
    edModEncodePair (edNeg A) = ((p25519 - edModEncode A.1) % p25519, edModEncode A.2) := by
  rw [← neg_decode A hA]
  have hp : (0 : Nat) < p25519 := by decide
  have h1 : (p25519 - edModEncode A.1) % p25519 < p25519 := Nat.mod_lt _ hp
  have h2 := edModEncode_lt A.2
  have e (n : Nat) (hn : n < p25519) : edModEncode ((n : Int) % p25519) = n := by
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hn)]
    exact_mod_cast edModEncode_of_onCurve n (by positivity) (by exact_mod_cast hn)
  simp only [edModEncodePair, edModDecodePair, Prod.mk.injEq]
  exact ⟨e _ h1, e _ h2⟩

/-- The point `commits` multiplies by `u`: `A` if `u` is negative, `-A`
otherwise. -/
theorem select_spec (h : Runs) (b : Bool) (pt : Std.Array U64 8#usize) (A : EdPoint) (hA : edOnCurve A)
    (hp : pairNat pt.val = edModEncodePair A) :
    (if b then mid.ed25519.EdwardsPoint.extended pt
      else do
        let ep ← mid.ed25519.EdwardsPoint.negate pt
        mid.ed25519.EdwardsPoint.extended ep) ⦃ a => ExProjective (if b then A else edNeg A) a.val ⦄ := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step with negate_spec pt (by rw [hp]; exact (edModEncode_lt _).le) as ⟨ep, hep⟩
    have hn : pairNat ep.val = edModEncodePair (edNeg A) := by rw [hep, hp, neg_encode A hA]; rfl
    exact extended_spec h ep _ (edOnCurve_neg A hA) hn
  · simpa using extended_spec h pt A hA hp

open Classical in
/-- `commits` accepts exactly when `r` encodes `[s]B - [k]A`, for a point `A`
of the group and `k` below `L`. -/
theorem commits_spec (h : Runs) (hm : RunsMsm) (ho : EdOrders) (pt : Std.Array U64 8#usize) (A : EdPoint) (hA : edOnCurve A)
    (hp : pairNat pt.val = edModEncodePair A) (r : Std.Array U8 32#usize) (k s : Std.Array U64 4#usize)
    (hk : wordsNat k.val < n25519) :
    mid.ed25519.commits pt r k s ⦃ b =>
      b = true ↔ leNat r.val = edEncode (edMul (edPow (edNeg A) (wordsNat k.val)) (edPow edB (wordsNat s.val))) ⦄ := by
  have hX : edOnCurve (edMul (edPow (edNeg A) (wordsNat k.val)) (edPow edB (wordsNat s.val))) :=
    edOnCurve_mul (edOnCurve_pow (edOnCurve_neg A hA) _) (edOnCurve_pow edOnCurve_B _)
  unfold mid.ed25519.commits
  step with decompress_from_spec h r as ⟨r1, hr1⟩
  by_cases hv : edValidEncode (leNat r.val)
  swap
  · simp only [hv, ↓reduceIte] at hr1
    subst hr1
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro he
    exact hv ⟨_, hX, he.symm⟩
  simp only [hv, ↓reduceIte] at hr1
  obtain ⟨r2, rfl, hr2⟩ := hr1
  obtain ⟨hR, hRe⟩ := edDecode_spec _ hv
  generalize edDecode (leNat r.val) = R at hR hRe hr2
  simp only
  step with HalfSize.split_spec k (lt_trans hk (by decide)) as ⟨sp, hsu, hsv, hsv128, hsu255⟩
  step with madd_spec h sp.v s _ as ⟨vs, hvs⟩
  step with select_spec h sp.u_negative pt A hA hp as ⟨a1, ha1⟩
  step with negate_spec r2 (by rw [hr2]; exact (edModEncode_lt _).le) as ⟨ep, hep⟩
  have hn : pairNat ep.val = edModEncodePair (edNeg R) := by rw [hep, hr2, neg_encode R hR]; rfl
  step with extended_spec h ep _ (edOnCurve_neg R hR) hn as ⟨a2, ha2⟩
  have hsel : edOnCurve (if sp.u_negative then A else edNeg A) := by
    split
    · exact hA
    · exact edOnCurve_neg A hA
  have hz : wordsNat (Std.Array.repeat 4#usize 0#u64).val = 0 := by decide
  rw [hz, add_zero] at hvs
  have hvsl : wordsNat vs.val < 2 ^ 255 := by rw [hvs]; exact lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  step with hm (Std.Array.repeat 12#usize 0#u64) vs (Std.Array.make 2#usize [sp.v, sp.u])
    (Std.Array.make 2#usize [a2, a1]) (edNeg R) _ (edOnCurve_neg R hR) hsel (by simpa using ha2)
    (by simpa using ha1) hvsl (by simp; omega) (by simpa using hsu255) as ⟨q1, hq1⟩
  simp only [Std.Array.make] at hq1
  rw [hvs] at hq1
  have hvL : wordsNat sp.v.val < n25519 := lt_trans hsv128 (by decide)
  have hQ := edOnCurve_mul (edOnCurve_mul (edOnCurve_pow edOnCurve_B (wordsNat sp.v.val * wordsNat s.val % n25519))
    (edOnCurve_pow (edOnCurve_neg R hR) (wordsNat sp.v.val)))
    (edOnCurve_pow hsel (wordsNat sp.u.val))
  have hfin := (id_words q1.val q1.property).trans ((projective_id hQ hq1).trans
    ((half_size_iff ho A R hA hR (wordsNat s.val) (wordsNat k.val) _ _ sp.u_negative hsu hsv hvL).trans
      (show R = edMul (edPow (edNeg A) (wordsNat k.val)) (edPow edB (wordsNat s.val)) ↔
          leNat r.val = edEncode (edMul (edPow (edNeg A) (wordsNat k.val)) (edPow edB (wordsNat s.val))) from
        ⟨fun he => by rw [← hRe, he], fun he => edEncode_inj hR hX (by rw [hRe, he])⟩)))
  have hl : q1.val.length = 12 := q1.property
  simp (disch := omega) only [getElem!_pos] at hfin
  rw [← hfin]
  step*

/-! ## Verification -/

open Classical in
/-- `verify_rind` with the point `A`, a point of the group, and the key's
bytes `vk.bytes`: `ed25519Verifies`, rind's cofactorless check with the
challenge reduced mod L. -/
theorem verify_rind_spec (h : Runs) (hmsm : RunsMsm) (ho : EdOrders) (hs : RunsSha512) (vk : mid.ed25519.VerifyingKey)
    (pt : mid.ed25519.EdwardsPoint) (A : EdPoint) (hA : edOnCurve A) (hp : pairNat pt.val = edModEncodePair A)
    (sig : Std.Array U8 64#usize) (msg : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    mid.ed25519.VerifyingKey.verify_rind vk pt sig msg ⦃ b =>
      b = decide (ed25519Verifies A vk.bytes.val msg.val sig.val) ⦄ := by
  unfold mid.ed25519.VerifyingKey.verify_rind
  have hsig : sig.val.length = 64 := sig.property
  step*
  all_goals
    have hs2 : s2.val = sig.val.drop 32 := by simp_all [Array.val_to_slice]
    have hr : r_sig.val = sig.val.take 32 := by simp_all [Array.val_to_slice]
    rw [hs2] at o_post
  · have hS : ¬ leNat (sig.val.drop 32) < n25519 := by
      intro hS
      simp only [hS, ↓reduceIte] at o_post
      obtain ⟨_, h1, _⟩ := o_post
      simp_all
    have hn : ¬ ed25519Verifies A vk.bytes.val msg.val sig.val := fun ⟨_, h, _⟩ => hS h
    simp [hn]
  · have hos : o = some s3 := by assumption
    have hS : leNat (sig.val.drop 32) < n25519 := by
      by_contra hS
      simp only [hS, ↓reduceIte] at o_post
      simp_all
    simp only [hS, ↓reduceIte] at o_post
    obtain ⟨S, hSo, hSv⟩ := o_post
    rw [hos, Option.some.injEq] at hSo
    subst hSo
    have h2 : a.val = r_sig.val := by simp_all
    apply WP.spec_mono (commits_spec h hmsm ho pt A hA hp a k1 s3 (by rw [k1_post]; exact Nat.mod_lt _ (by decide)))
    intro b hb
    have hiff : leNat a.val = edEncode (edMul (edPow (edNeg A) (wordsNat k1.val)) (edPow edB (wordsNat s3.val))) ↔
        ed25519Verifies A vk.bytes.val msg.val sig.val := by
      rw [h2, hr, k1_post, k_post, hSv, s4_post, Array.val_to_slice, hr]
      exact ⟨fun he => ⟨hsig, hS, he⟩, fun he => he.2.2⟩
    exact Bool.eq_iff_iff.mpr (by simpa using hb.trans hiff)

open Classical in
/-- `verify` with a key that runs rind's own arithmetic on the point `A`, a
point of the group, and whose bytes are `vk.bytes`: `ed25519Verifies`, rind's cofactorless check
with the challenge reduced mod L. -/
theorem mid_verify_spec (h : Runs) (hmsm : RunsMsm) (ho : EdOrders) (hs : RunsSha512) (vk : mid.ed25519.VerifyingKey) (A : EdPoint)
    (hA : edOnCurve A) (hp : HoldsPoint vk A)
    (sig : Std.Array U8 64#usize) (msg : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    mid.ed25519.VerifyingKey.verify vk sig msg ⦃ r =>
      r = if ed25519Verifies A vk.bytes.val msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  obtain ⟨pt, hpath, hp⟩ := hp
  unfold mid.ed25519.VerifyingKey.verify
  rw [hpath]
  step with verify_rind_spec h hmsm ho hs vk pt A hA hp sig msg hm as ⟨b, hb⟩
  split <;> simp_all

open Classical in
theorem high_verify_spec (h : Runs) (hmsm : RunsMsm) (ho : EdOrders) (hs : RunsSha512) (vk : high.ed25519.Ed25519VerifyingKey) (A : EdPoint)
    (hA : edOnCurve A) (hp : HoldsPoint vk A) (sig msg : Slice U8)
    (hm : msg.length + 64 < 2 ^ 64) :
    high.ed25519.Ed25519VerifyingKey.verify vk sig msg ⦃ r =>
      r = if ed25519Verifies A (mid.ed25519.VerifyingKey.bytes vk).val msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold high.ed25519.Ed25519VerifyingKey.verify
  step
  step with try_from_shared_spec 64#usize sig as ⟨r, hr⟩
  by_cases hl : sig.length = 64
  · simp only [hl, ↓reduceIte] at hr
    obtain ⟨a, rfl, ha⟩ := hr
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch]
    step*
    step with mid_verify_spec h hmsm ho hs vk A hA hp a msg hm as ⟨r, hr⟩
    rw [hr, ha]
  · simp only [hl, ↓reduceIte] at hr
    obtain ⟨e, rfl⟩ := hr
    have hn : ¬ ed25519Verifies A (mid.ed25519.VerifyingKey.bytes vk).val msg.val sig.val := fun ⟨h64, _⟩ => hl h64
    simp [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      high.ed25519.Ed25519VerifyingKey.verify.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hn]

open Classical in
/-- Verification with a key pair's public key: `ed25519Verifies`, rind's
cofactorless check with the challenge reduced mod L, with its seed's public
key, whose point is the base point times its secret scalar. -/
theorem ed25519_key_pair_verify (h : Runs) (hmsm : RunsMsm) (ho : EdOrders) (hs : RunsSha512) (kp : high.signature.ed25519.KeyPair)
    (seed : List U8) (hkp : KeyPairOf kp seed) (msg sig : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    (do
      let pk ← high.signature.ed25519.KeyPair.public_key kp
      high.signature.ed25519.PublicKey.verify pk msg sig) ⦃ r =>
      r = if ed25519Verifies (edPow edB (ed25519Scalar seed)) (ed25519PublicKey seed) msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold high.signature.ed25519.KeyPair.public_key high.signature.ed25519.PublicKey.verify
  obtain ⟨⟨-, -, hkb, hkpt⟩, hpub⟩ := hkp
  simp only [bind_ok]
  have hb : (mid.ed25519.VerifyingKey.bytes kp.«public»).val = ed25519PublicKey seed := by rw [hpub]; exact hkb
  rw [← hb]
  exact high_verify_spec h hmsm ho hs kp.«public» _ (edOnCurve_pow edOnCurve_B _) (by rw [hpub]; exact hkpt) sig msg hm

open Classical in
/-- An Ed25519 public key parsed from its encoding: refused unless it is 32
bytes, refused if its y-coordinate is one of libsodium's small-order list,
refused unless it encodes a point of the group, and otherwise its
verification is `ed25519Verifies`, rind's cofactorless check with the
challenge reduced mod L, with that point, for messages under 2⁶⁴ - 64 bytes. -/
theorem ed25519_public_key_new (h : Runs) (hmsm : RunsMsm) (ho : EdOrders) (hs : RunsSha512) (hi : NoCurveIfma) (key : Slice U8) :
    high.signature.ed25519.PublicKey.new key ⦃ r =>
      if key.length ≠ 32 then r = .Err (.KeyRejected .WrongLength)
      else if leNat key.val % 2 ^ 255 ∈ edSmallOrderY then r = .Err (.KeyRejected .SmallOrder)
      else if edValidEncode (leNat key.val) then
        ∃ pk, r = .Ok pk ∧ ∀ msg sig : Slice U8, msg.length + 64 < 2 ^ 64 →
          high.signature.ed25519.PublicKey.verify pk msg sig ⦃ v =>
            v = if ed25519Verifies (edDecode (leNat key.val)) key.val msg.val sig.val then
              (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄
      else r = .Err (.KeyRejected .NotOnCurve) ⦄ := by
  unfold high.signature.ed25519.PublicKey.new
  step with high_from_bytes_spec h hs hi key as ⟨r, hr⟩
  split_ifs at hr ⊢ with hl hso hv
  · subst hr; simp [core.result.Result.map]
  · subst hr; simp [core.result.Result.map]
  · obtain ⟨vk, rfl, hvb, hvp⟩ := hr
    simp only [core.result.Result.map, P.Insts.CoreOpsFunctionFnOnceTupleEd25519VerifyingKeyPublicKey.call_once,
      high.signature.ed25519.PublicKey.constructor, bind_ok, WP.spec_ok]
    refine ⟨_, rfl, fun msg sig hm => ?_⟩
    simp only [high.signature.ed25519.PublicKey.verify]
    have := high_verify_spec h hmsm ho hs vk _ (edDecode_spec _ hv).1 hvp sig msg hm
    rwa [hvb] at this
  · subst hr; simp [core.result.Result.map]

end rind.x86_64
