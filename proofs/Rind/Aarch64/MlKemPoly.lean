import Rind.Aarch64.MlKemRoutines
import Rind.Aarch64.MlKemGeneric
open Aeneas Aeneas.Std Result rind.spec Spec Spec.MLKEM rind.spec.mlkem rind.spec.s2n

/-!
# ML-KEM's polynomial vectors on aarch64

What `mid::mlkem`'s operations on `Coeffs` compute, in FIPS 203's terms, over
`MlKemRoutines`' specs of the routines they call. Each `Coeffs` holds an
array of polynomials, which a set's `Params` impl names and the translation
leaves abstract: `IsArray` states the `FixedArray` impl the array types have,
which Aeneas does not translate. ML-KEM-768 is the set the ✓ covers, so a
vector has three polynomials and a matrix nine, row by row.
-/

namespace rind.aarch64

namespace MlKemPoly

open MlKemCoding MlKemRoutines MlKemGeneric

abbrev Poly := Std.Array I16 256#usize

/-- `inst` is `[T; n]`'s `FixedArray` impl: its slices are the array's. -/
structure IsArray {T : Type} {n : Usize} (inst : mid.mlkem.FixedArray (Std.Array T n) T) : Prop where
  as_ref : inst.coreconvertAsRefSelfSliceInst = Array.Insts.CoreConvertAsRefSlice T n
  as_mut : inst.coreconvertAsMutSelfSliceInst = Array.Insts.CoreConvertAsMutSlice T n
  filled : ∀ v, inst.filled v = ok (Std.Array.repeat n v)
  clone : ∀ a, inst.corecloneCloneInst.clone a = ok a

/-- Each of `v`'s first `n` polynomials holds `F`'s, each coefficient in `[lo, hi]`. -/
def VHolds (lo hi : ℤ) (n : ℕ) (v : List Poly) (F : ℕ → Polynomial) : Prop :=
  ∀ j < n, Holds lo hi 256 (v[j]!).val (F j)

/-- A loop over `0..n` whose body changes only the slice element its index
names, as `Q` relates the element before and after, given `Pre` held of it
before. -/
theorem slice_loop {α : Type} [Inhabited α] (n : ℕ) (Pre Q : ℕ → α → α → Prop)
    (body : core.ops.range.Range Usize × Slice α →
      Result (ControlFlow (core.ops.range.Range Usize × Slice α) (Slice α)))
    (hbody : ∀ (it : core.ops.range.Range Usize) (s : Slice α), it.end.val = n → it.start.val ≤ n →
      s.length = n → (it.start.val < n → Pre it.start.val (s.val[it.start.val]!) (s.val[it.start.val]!)) →
      body (it, s) ⦃ r => match r with
        | .done y => it.start.val = n ∧ y = s
        | .cont x => x.1.end.val = n ∧ x.1.start.val = it.start.val + 1 ∧ it.start.val < n ∧
            x.2.length = n ∧ Q it.start.val (s.val[it.start.val]!) (x.2.val[it.start.val]!) ∧
            ∀ j, j ≠ it.start.val → x.2.val[j]! = s.val[j]! ⦄)
    (s0 : Slice α) (hn : s0.length = n) (hpre : ∀ j < n, Pre j (s0.val[j]!) (s0.val[j]!))
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    loop body (it, s0) ⦃ y => y.length = n ∧ ∀ j < n, Q j (s0.val[j]!) (y.val[j]!) ⦄ := by
  apply WP.spec_mono (range_loop n (fun i (s : Slice α) => s.length = n ∧
      (∀ j < i, Q j (s0.val[j]!) (s.val[j]!)) ∧ ∀ j, i ≤ j → s.val[j]! = s0.val[j]!) body ?_
    it s0 he (by omega) ⟨hn, fun j hj => by omega, fun j _ => rfl⟩)
  · intro y ⟨hl, hq, _⟩
    exact ⟨hl, hq⟩
  · intro it' s he' hs' ⟨hl, hq, hrest⟩
    apply WP.spec_mono (hbody it' s he' hs' hl (fun hlt => by
      rw [hrest _ le_rfl]; exact hpre _ hlt))
    rintro (x | y) h
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      refine ⟨h1, h2, h3, h4, fun j hj => ?_, fun j hj => ?_⟩
      · by_cases hjj : j = it'.start.val
        · subst hjj
          rw [← hrest _ le_rfl]
          exact h5
        · rw [h6 j hjj]
          exact hq j (by omega)
      · rw [h6 j (by omega)]
        exact hrest j (by omega)
    · obtain ⟨h1, rfl⟩ := h
      exact ⟨hl, by rw [← h1]; exact hq, fun j hj => hrest j (by omega)⟩

theorem set_getElem!_self {α : Type} [Inhabited α] (s : Slice α) (i : Usize) (x : α) (hi : i.val < s.length) :
    (s.set i x).val[i.val]! = x := by
  rw [Slice.set_val_eq]
  exact getElem!_set_self _ _ _ hi

theorem set_getElem!_ne {α : Type} [Inhabited α] (s : Slice α) (i : Usize) (x : α) (j : ℕ)
    (hj : j ≠ i.val) : (s.set i x).val[j]! = s.val[j]! := by
  rw [Slice.set_val_eq]
  exact getElem!_set_ne _ _ _ _ (Ne.symm hj)

theorem set_length {α : Type} (s : Slice α) (i : Usize) (x : α) : (s.set i x).length = s.length := by
  simp [Slice.length, Slice.set_val_eq]

/-- `Coeffs::zero`: every coefficient zero. -/
theorem zero_eq {n : Usize} {D : Type} (inst : mid.mlkem.FixedArray (Std.Array Poly n) Poly)
    (hi : IsArray inst) (d : mid.mlkem.Domain D) :
    mid.mlkem.Coeffs.zero inst d = ok (Std.Array.repeat n (Std.Array.repeat 256#usize 0#i16), ()) := by
  unfold mid.mlkem.Coeffs.zero
  simp [hi.filled]
  rfl

theorem zero1_eq {D : Type} (d : mid.mlkem.Domain D) :
    mid.mlkem.CoeffsArrayI16256D.zero d = ok (Std.Array.repeat 256#usize 0#i16, ()) := rfl

theorem ntt_loop_spec (n : ℕ) (F : ℕ → Polynomial) (polys : Slice Poly) (hl : polys.length = n)
    (h : ∀ j < n, Holds (-8191) 8191 256 (polys.val[j]!).val (F j))
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    mid.mlkem.CoeffsVNormal.ntt_loop it polys ⦃ y =>
      y.length = n ∧ ∀ j < n, Holds (-23594) 23594 256 (y.val[j]!).val (NTT (F j)) ⦄ := by
  unfold mid.mlkem.CoeffsVNormal.ntt_loop
  apply WP.spec_mono (slice_loop (α := Poly) n (fun j a _ => Holds (-8191) 8191 256 a.val (F j))
    (fun j _ b => Holds (-23594) 23594 256 b.val (NTT (F j))) _ ?_ polys hl h it hs he)
  · intro y hy
    exact hy
  · intro it s he hs hl hpre
    simp only
    unfold mid.mlkem.CoeffsVNormal.ntt_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨a, back', ha, hb⟩
      subst hb
      step with mlkem_ntt_spec a (F it.start.val) (by rw [ha, ← getElem!_pos]; exact hpre (by omega))
        as ⟨a1, ha1⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl,
        by rw [set_getElem!_self _ _ _ (by omega)]; exact ha1, fun j hj => set_getElem!_ne _ _ _ _ hj⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

theorem zero1_spec {D : Type} (d : mid.mlkem.Domain D) :
    mid.mlkem.CoeffsArrayI16256D.zero d ⦃ r => r.1 = Std.Array.repeat 256#usize 0#i16 ⦄ := by
  unfold mid.mlkem.CoeffsArrayI16256D.zero
  exact (WP.spec_ok _).2 rfl

/-- `Coeffs::ntt`: FIPS 203's `NTT` of each polynomial, of coefficients below
`2 ^ 13` in magnitude. -/
theorem ntt_spec {n : Usize} (inst : mid.mlkem.FixedArray (Std.Array Poly n) Poly) (hi : IsArray inst)
    (v : Std.Array Poly n) (F : ℕ → Polynomial) (h : VHolds (-8191) 8191 n.val v.val F) :
    mid.mlkem.CoeffsVNormal.ntt inst (v, ()) ⦃ r =>
      VHolds (-23594) 23594 n.val r.1.val (fun j => NTT (F j)) ⦄ := by
  unfold mid.mlkem.CoeffsVNormal.ntt
  rw [hi.as_mut]
  step as ⟨polys, back, hpv, hpl, hback⟩
  step with ntt_loop_spec n.val F polys hpl (fun j hj => by rw [hpv]; exact h j hj)
      { start := 0#usize, «end» := Slice.len polys } rfl (by rw [Slice.len_val]; exact hpl)
    as ⟨polys1, hl1, hq1⟩
  apply (WP.spec_ok _).2
  intro j hj
  rw [hback _ hl1]
  exact hq1 j hj

/-! ## Base multiplication -/

theorem add_get (f g : Polynomial) (p : ℕ) (hp : p < 256) : (f + g)[p]! = f[p]! + g[p]! := by
  rw [getElem!_pos (f + g) p hp, getElem!_pos f p hp, getElem!_pos g p hp]
  show (Vector.zipWith (· + ·) f g)[p] = _
  simp

/-- The scalar product of three polynomials' NTTs, as FIPS 203 sums it. -/
def dot3 (X Y : ℕ → Polynomial) : Polynomial :=
  MultiplyNTTs (X 0) (Y 0) + MultiplyNTTs (X 1) (Y 1) + MultiplyNTTs (X 2) (Y 2)

theorem dite_true' {α : Type} {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := by
  simp [h]

theorem flat_length {T : Type} {n : Usize} : ∀ l : List (Std.Array T n),
    (l.flatMap (·.val)).length = l.length * n.val
  | [] => by simp
  | a :: t => by
    rw [List.flatMap_cons, List.length_append, flat_length t, a.property, List.length_cons, Nat.succ_mul]
    omega

theorem flat_getElem! {T : Type} [Inhabited T] {n : Usize} : ∀ (l : List (Std.Array T n)) (j p : ℕ),
    j < l.length → p < n.val → (l.flatMap (·.val))[n.val * j + p]! = (l[j]!).val[p]!
  | [], j, p, hj, _ => by simp at hj
  | a :: t, 0, p, _, hp => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
      List.getElem!_append_left _ _ _ (by rw [a.property]; exact hp), List.getElem!_cons_zero]
  | a :: t, j + 1, p, hj, hp => by
    rw [List.flatMap_cons, List.getElem!_append_right _ _ _ (by rw [a.property, Nat.mul_succ]; omega),
      a.property, show n.val * (j + 1) + p - n.val = n.val * j + p by rw [Nat.mul_succ]; omega,
      List.getElem!_cons_succ]
    exact flat_getElem! t j p (by simp at hj; omega) hp

theorem coeff_flat {n : Usize} (w : ℕ) (hn : n.val = w) (l : List (Std.Array I16 n)) (j p : ℕ)
    (hj : j < l.length) (hp : p < w) :
    coeff ((l.flatMap (·.val)).drop (w * j)) p = ((l[j]!).val[p]!).val := by
  unfold coeff
  rw [List.getElem!_drop, ← hn, flat_getElem! l j p hj (by omega)]

theorem as_flattened_spec {T : Type} {N : Usize} (s : Slice (Std.Array T N))
    (h : s.length * N.val ≤ Usize.max) :
    core.slice.SliceArray.as_flattened s ⦃ r => r.val = s.val.flatMap (·.val) ⦄ := by
  simp only [core.slice.SliceArray.as_flattened]
  rw [dite_true' ((by rw [flat_length]; exact h))]
  exact (WP.spec_ok _).2 (Slice.from_val _ _)

theorem try_from_ok {T : Type} (N : Usize) (s : Slice T) (h : s.length = N.val) :
    core.array.TryFromSharedArraySlice.try_from N s = ok (.Ok (Std.Array.from s.val h)) := by
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dite_true' ((by scalar_tac))]

theorem N_eq : mid.mlkem.N = 256#usize := by unfold mid.mlkem.N; rfl

/-- `basemul` of three polynomials each: the sum of their `MultiplyNTTs`
products times `2 ^ -16`, of a first factor at most `2 ^ 12` in magnitude,
given the second's mulcache. -/
theorem basemul_spec (r : Poly) (a b : Slice Poly) (bt : Slice (Std.Array I16 128#usize))
    (X Y : ℕ → Polynomial) (ha : a.length = 3) (hb : b.length = 3) (hbt : bt.length = 3)
    (hX : VHolds (-4096) 4096 3 a.val X)
    (hY : ∀ j < 3, ∀ p < 256, ((((b.val[j]!).val[p]!).val : ℤ) : Zq) = (Y j)[p]!)
    (hT : ∀ j < 3, CacheHolds (bt.val[j]!).val (Y j)) :
    mid.mlkem.basemul r a b bt ⦃ r' => ∀ p < 256,
      (2 : Zq) ^ 16 * ((r'.val[p]!).val : Zq) = (dot3 X Y)[p]! ⦄ := by
  unfold mid.mlkem.basemul
  have ha' : a.val.length = 3 := ha
  have hb' : b.val.length = 3 := hb
  have hbt' : bt.val.length = 3 := hbt
  have hm : (3 : ℕ) * 256 ≤ Usize.max := by scalar_tac
  have hm' : (3 : ℕ) * 128 ≤ Usize.max := by scalar_tac
  step with as_flattened_spec a (by rw [ha]; exact hm) as ⟨a1, ha1⟩
  step with as_flattened_spec b (by rw [hb]; exact hm) as ⟨b1, hb1⟩
  step with as_flattened_spec bt (by rw [hbt]; exact hm') as ⟨bt1, hbt1⟩
  have la : a1.length = 768 := by
    show a1.val.length = _; rw [ha1, flat_length, ha']; rfl
  have lb : b1.length = 768 := by
    show b1.val.length = _; rw [hb1, flat_length, hb']; rfl
  have lt : bt1.length = 384 := by
    show bt1.val.length = _; rw [hbt1, flat_length, hbt']; rfl
  rw [N_eq]
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = 3 := by
    rw [hi2, hi1, Slice.len_val, lt]
  simp only [hi2v]
  rw [try_from_ok 768#usize a1 la, try_from_ok 768#usize b1 lb, try_from_ok 384#usize bt1 lt]
  simp only [core.result.Result.unwrap, bind_ok]
  have hA : ∀ j < 3, ∀ p < 256, coeff (a1.val.drop (256 * j)) p = (((a.val[j]!).val[p]!).val) :=
    fun j hj p hp => by rw [ha1]; exact coeff_flat 256 rfl a.val j p (by rw [ha']; exact hj) hp
  have hB : ∀ j < 3, ∀ p < 256, coeff (b1.val.drop (256 * j)) p = (((b.val[j]!).val[p]!).val) :=
    fun j hj p hp => by rw [hb1]; exact coeff_flat 256 rfl b.val j p (by rw [hb']; exact hj) hp
  have hBT : ∀ j < 3, ∀ p < 128, coeff (bt1.val.drop (128 * j)) p = (((bt.val[j]!).val[p]!).val) :=
    fun j hj p hp => by rw [hbt1]; exact coeff_flat 128 rfl bt.val j p (by rw [hbt']; exact hj) hp
  have hx : ∀ j < 3, poly (coeff (a1.val.drop (256 * j))) = X j := fun j hj =>
    poly_coeff _ _ fun p hp => by
      have := hA j hj p hp; unfold coeff at this; rw [this]; exact (hX j hj p hp).2.2
  have hy : ∀ j < 3, poly (coeff (b1.val.drop (256 * j))) = Y j := fun j hj =>
    poly_coeff _ _ fun p hp => by
      have := hB j hj p hp; unfold coeff at this; rw [this]; exact hY j hj p hp
  have hc : ∀ j < 3, ∀ i < 128, ((coeff (bt1.val.drop (128 * j)) i : ℤ) : Zq) =
      ((mulcache (coeff (b1.val.drop (256 * j))) i : ℤ) : Zq) := fun j hj i hi => by
    rw [hBT j hj i hi, mulcache_eq _ _ hi, hy j hj]
    exact hT j hj i hi
  have hbound : ∀ i < 768, |(a1.val[i]!).val| ≤ 4096 := by
    intro i hi
    have := hA (i / 256) (by omega) (i % 256) (by omega)
    unfold coeff at this
    rw [List.getElem!_drop, show 256 * (i / 256) + i % 256 = i by omega] at this
    rw [this]
    exact abs_le.2 ⟨(hX _ (by omega) _ (by omega)).1, (hX _ (by omega) _ (by omega)).2.1⟩
  apply WP.spec_mono (mlkem_basemul_k3_axiom r (Std.Array.from a1.val la) (Std.Array.from b1.val lb)
    (Std.Array.from bt1.val lt) (by rw [Std.Array.from_val]; exact hbound))
  intro r' hr' p hp
  simp only [Std.Array.from_val] at hr'
  have hx0 := hx 0 (by omega)
  have hx1 := hx 1 (by omega)
  have hx2 := hx 2 (by omega)
  have hy0 := hy 0 (by omega)
  have hy1 := hy 1 (by omega)
  have hy2 := hy 2 (by omega)
  simp only [Nat.mul_zero, List.drop_zero, Nat.mul_one, show 256 * 2 = 512 by rfl] at hx0 hx1 hx2 hy0 hy1 hy2
  rw [dot3, add_get _ _ _ hp, add_get _ _ _ hp]
  obtain ⟨i, hi, rfl | rfl⟩ : ∃ i < 128, p = 2 * i ∨ p = 2 * i + 1 := ⟨p / 2, by omega, by omega⟩
  · have hc0 := hc 0 (by omega) i hi
    have hc1 := hc 1 (by omega) i hi
    have hc2 := hc 2 (by omega) i hi
    simp only [Nat.mul_zero, List.drop_zero, Nat.mul_one, show 128 * 2 = 256 by rfl,
      show 256 * 2 = 512 by rfl] at hc0 hc1 hc2
    rw [cast_of_modEq (hr' i hi).1, basemul3Even_eq _ _ _ _ _ _ _ _ _ i hi hc0 hc1 hc2,
      hx0, hx1, hx2, hy0, hy1, hy2]
  · rw [cast_of_modEq (hr' i hi).2, basemul3Odd_eq _ _ _ _ _ _ i hi, hx0, hx1, hx2, hy0, hy1, hy2]

/-! ## Per-polynomial loops -/

/-- `a`'s values are congruent to `F`'s coefficients. -/
def Congr (a : List I16) (F : Polynomial) : Prop := ∀ p < 256, ((a[p]!).val : Zq) = F[p]!

/-- `a`'s values times Montgomery's factor `2 ^ 16` are `F`'s coefficients. -/
def Mont (a : List I16) (F : Polynomial) : Prop := ∀ p < 256, (2 : Zq) ^ 16 * ((a[p]!).val : Zq) = F[p]!

theorem Holds.congr {lo hi : ℤ} {a : List I16} {F : Polynomial} (h : Holds lo hi 256 a F) : Congr a F :=
  fun p hp => (h p hp).2.2

theorem array_length {T : Type} {n : Usize} (s : Slice T) (a : Std.Array T n) (h : s.val = a.val) :
    s.length = n.val := by
  show s.val.length = _
  rw [h]
  exact a.property

theorem mul_cache_loop_spec (n : ℕ) (F : ℕ → Polynomial) (polys : Slice Poly)
    (out : Slice (Std.Array I16 128#usize)) (hl : out.length = n) (hp : polys.length = n)
    (h : ∀ j < n, Congr (polys.val[j]!).val (F j))
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    mid.mlkem.CoeffsVNtt.mul_cache_loop it out polys ⦃ y =>
      y.length = n ∧ ∀ j < n, CacheHolds (y.val[j]!).val (F j) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.mul_cache_loop
  apply WP.spec_mono (slice_loop (α := Std.Array I16 128#usize) n (fun _ _ _ => True)
    (fun j _ b => CacheHolds b.val (F j)) _ ?_ out hl (fun _ _ => trivial) it hs he)
  · intro y hy
    exact hy
  · intro it s he hs hl' _
    simp only
    unfold mid.mlkem.CoeffsVNtt.mul_cache_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨a, back', ha, hb⟩
      subst hb
      step as ⟨x, hx⟩
      step with mlkem_mulcache_compute_spec a x (F it.start.val)
          (by rw [hx, ← getElem!_pos]; exact h _ (by omega))
        as ⟨a1, ha1⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl',
        by rw [set_getElem!_self _ _ _ (by omega)]; exact ha1, fun j hj => set_getElem!_ne _ _ _ _ hj⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

/-- `Coeffs::mul_cache`: each polynomial's mulcache. -/
theorem mul_cache_spec {n : Usize} {Enc : Type}
    (vec : mid.mlkem.Vector (Std.Array Poly n) (Std.Array (Std.Array I16 128#usize) n) Enc)
    (h1 : IsArray vec.FixedArraySelfArrayI16256Inst) (h2 : IsArray vec.FixedArraySelf_MulCacheArrayI16128Inst)
    (v : Std.Array Poly n) (F : ℕ → Polynomial) (h : ∀ j < n.val, Congr (v.val[j]!).val (F j)) :
    mid.mlkem.CoeffsVNtt.mul_cache vec (v, ()) ⦃ r =>
      ∀ j < n.val, CacheHolds (r.1.val[j]!).val (F j) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.mul_cache
  simp only [h2.filled, h2.as_mut, h1.as_ref, bind_ok]
  step as ⟨out, back, hov, hol, hback⟩
  step as ⟨polys, hpv⟩
  step with mul_cache_loop_spec n.val F polys out hol (array_length polys v hpv)
      (fun j hj => by rw [hpv]; exact h j hj)
      { start := 0#usize, «end» := Slice.len out } rfl (by rw [Slice.len_val]; exact hol)
    as ⟨out1, hl1, hq1⟩
  apply (WP.spec_ok _).2
  intro j hj
  rw [hback _ hl1]
  exact hq1 j hj

theorem inverse_ntt_loop_spec (n : ℕ) (G : ℕ → Polynomial) (polys : Slice Poly) (hl : polys.length = n)
    (h : ∀ j < n, Mont (polys.val[j]!).val (G j))
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    mid.mlkem.CoeffsVNtt.inverse_ntt_loop it polys ⦃ y =>
      y.length = n ∧ ∀ j < n, Holds (-26624) 26624 256 (y.val[j]!).val (NTTInv (G j)) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.inverse_ntt_loop
  apply WP.spec_mono (slice_loop (α := Poly) n (fun j a _ => Mont a.val (G j))
    (fun j _ b => Holds (-26624) 26624 256 b.val (NTTInv (G j))) _ ?_ polys hl h it hs he)
  · intro y hy
    exact hy
  · intro it s he hs hl hpre
    simp only
    unfold mid.mlkem.CoeffsVNtt.inverse_ntt_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨a, back', ha, hb⟩
      subst hb
      step with mlkem_intt_spec a (G it.start.val) (by rw [ha, ← getElem!_pos]; exact hpre (by omega))
        as ⟨a1, ha1⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl,
        by rw [set_getElem!_self _ _ _ (by omega)]; exact ha1, fun j hj => set_getElem!_ne _ _ _ _ hj⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

/-- `Coeffs::inverse_ntt`: FIPS 203's `NTTInv` of each `G j`, of coefficients
`G j` times `2 ^ -16`. -/
theorem inverse_ntt_spec {n : Usize} {MC Enc : Type} (vec : mid.mlkem.Vector (Std.Array Poly n) MC Enc)
    (hi : IsArray vec.FixedArraySelfArrayI16256Inst)
    (v : Std.Array Poly n) (G : ℕ → Polynomial) (h : ∀ j < n.val, Mont (v.val[j]!).val (G j)) :
    mid.mlkem.CoeffsVNtt.inverse_ntt vec (v, ()) ⦃ r =>
      VHolds (-26624) 26624 n.val r.1.val (fun j => NTTInv (G j)) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.inverse_ntt
  rw [hi.as_mut]
  step as ⟨polys, back, hpv, hpl, hback⟩
  step with inverse_ntt_loop_spec n.val G polys hpl (fun j hj => by rw [hpv]; exact h j hj)
      { start := 0#usize, «end» := Slice.len polys } rfl (by rw [Slice.len_val]; exact hpl)
    as ⟨polys1, hl1, hq1⟩
  apply (WP.spec_ok _).2
  intro j hj
  rw [hback _ hl1]
  exact hq1 j hj

/-- `Coeffs::dot_and_inverse_ntt`: `NTTInv` of the scalar product, given the
second vector's mulcache. -/
theorem dot_and_inverse_ntt_spec {Enc : Type}
    (vec : mid.mlkem.Vector (Std.Array Poly 3#usize) (Std.Array (Std.Array I16 128#usize) 3#usize) Enc)
    (h1 : IsArray vec.FixedArraySelfArrayI16256Inst) (h2 : IsArray vec.FixedArraySelf_MulCacheArrayI16128Inst)
    (x y : Std.Array Poly 3#usize) (yc : Std.Array (Std.Array I16 128#usize) 3#usize) (X Y : ℕ → Polynomial)
    (hx : VHolds (-4096) 4096 3 x.val X) (hy : ∀ j < 3, Congr (y.val[j]!).val (Y j))
    (hc : ∀ j < 3, CacheHolds (yc.val[j]!).val (Y j)) :
    mid.mlkem.CoeffsVNtt.dot_and_inverse_ntt vec (x, ()) (y, ()) (yc, ()) ⦃ r =>
      Holds (-26624) 26624 256 r.1.val (NTTInv (dot3 X Y)) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.dot_and_inverse_ntt mid.mlkem.CoeffsArrayI16256Ntt.inverse_ntt
  simp only [h1.as_ref, h2.as_ref, zero1_eq]
  apply spec_bind_ok
  step as ⟨s1, hs1⟩
  step as ⟨s2, hs2⟩
  step as ⟨s3, hs3⟩
  step with basemul_spec _ s1 s2 s3 X Y (array_length s1 x hs1) (array_length s2 y hs2)
      (array_length s3 yc hs3) (by rw [hs1]; exact hx) (by rw [hs2]; exact hy) (by rw [hs3]; exact hc)
    as ⟨a1, ha1⟩
  step with mlkem_intt_spec a1 (dot3 X Y) ha1 as ⟨a2, ha2⟩
  exact (WP.spec_ok _).2 ha2

theorem reduce_loop_spec (n : ℕ) (F : ℕ → Polynomial) (polys : Slice Poly) (hl : polys.length = n)
    (h : ∀ j < n, Congr (polys.val[j]!).val (F j))
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    mid.mlkem.Coeffs.reduce_in_place_loop it polys ⦃ y =>
      y.length = n ∧ ∀ j < n, Holds 0 3328 256 (y.val[j]!).val (F j) ⦄ := by
  unfold mid.mlkem.Coeffs.reduce_in_place_loop
  apply WP.spec_mono (slice_loop (α := Poly) n (fun j a _ => Congr a.val (F j))
    (fun j _ b => Holds 0 3328 256 b.val (F j)) _ ?_ polys hl h it hs he)
  · intro y hy
    exact hy
  · intro it s he hs hl hpre
    simp only
    unfold mid.mlkem.Coeffs.reduce_in_place_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨a, back', ha, hb⟩
      subst hb
      step with mlkem_reduce_spec a (F it.start.val) (by rw [ha, ← getElem!_pos]; exact hpre (by omega))
        as ⟨a1, ha1⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl,
        by rw [set_getElem!_self _ _ _ (by omega)]; exact ha1, fun j hj => set_getElem!_ne _ _ _ _ hj⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

/-- `Coeffs::reduce_in_place`: each coefficient reduced into `[0, q)`. -/
theorem reduce_in_place_spec {n : Usize} {D : Type} (inst : mid.mlkem.FixedArray (Std.Array Poly n) Poly)
    (hi : IsArray inst) (d : mid.mlkem.Domain D)
    (v : Std.Array Poly n) (F : ℕ → Polynomial) (h : ∀ j < n.val, Congr (v.val[j]!).val (F j)) :
    mid.mlkem.Coeffs.reduce_in_place inst d (v, ()) ⦃ r => VHolds 0 3328 n.val r.1.val F ⦄ := by
  unfold mid.mlkem.Coeffs.reduce_in_place
  rw [hi.as_mut]
  step as ⟨polys, back, hpv, hpl, hback⟩
  step with reduce_loop_spec n.val F polys hpl (fun j hj => by rw [hpv]; exact h j hj)
      { start := 0#usize, «end» := Slice.len polys } rfl (by rw [Slice.len_val]; exact hpl)
    as ⟨polys1, hl1, hq1⟩
  apply (WP.spec_ok _).2
  intro j hj
  rw [hback _ hl1]
  exact hq1 j hj

/-- The 12-bit decoding of 384 bytes. -/
abbrev decode12 (b : Std.Array U8 384#usize) : Polynomial :=
  ByteDecode (toVec (32 * 12) b.val b.property) (by omega)

theorem from_bytes_loop_spec (n : ℕ) (bytes : Slice (Std.Array U8 384#usize)) (polys : Slice Poly)
    (hl : polys.length = n) (hb : bytes.length = n)
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    mid.mlkem.CoeffsVNtt.from_bytes_loop it polys bytes ⦃ y =>
      y.length = n ∧ ∀ j < n, Holds 0 3328 256 (y.val[j]!).val (decode12 (bytes.val[j]!)) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.from_bytes_loop
  apply WP.spec_mono (slice_loop (α := Poly) n (fun _ _ _ => True)
    (fun j _ b => Holds 0 3328 256 b.val (decode12 (bytes.val[j]!))) _ ?_ polys hl
    (fun _ _ => trivial) it hs he)
  · intro y hy
    exact hy
  · intro it s he hs hl _
    simp only
    unfold mid.mlkem.CoeffsVNtt.from_bytes_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨a, back', ha, hb'⟩
      subst hb'
      step as ⟨x, hx⟩
      step with mlkem_frombytes_spec a x as ⟨a2, ha2⟩
      step as ⟨a3, back2, ha3, hb2⟩
      subst hb2
      have ha3' : a3 = a2 := by
        rw [ha3, ← getElem!_pos, set_getElem!_self _ _ _ (by omega)]
      subst ha3'
      step with mlkem_reduce_spec a3 _ (Holds.congr ha2) as ⟨a4, ha4⟩
      have hx' : x = bytes.val[it.start.val]! := by rw [hx, ← getElem!_pos]
      subst hx'
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length, set_length]; exact hl,
        by rw [set_getElem!_self _ _ _ (by rw [set_length]; omega)]; exact ha4, fun j hj => ?_⟩
      rw [set_getElem!_ne _ _ _ _ hj, set_getElem!_ne _ _ _ _ hj]
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

/-- `Coeffs::from_bytes`: FIPS 203's `ByteDecode_12` of each 384 bytes, each
coefficient in `[0, q)`. -/
theorem from_bytes_spec {n : Usize} {MC : Type}
    (vec : mid.mlkem.Vector (Std.Array Poly n) MC (Std.Array (Std.Array U8 384#usize) n))
    (h1 : IsArray vec.FixedArraySelfArrayI16256Inst) (h3 : IsArray vec.FixedArraySelf_EncodedArrayU8384Inst)
    (bytes : Std.Array (Std.Array U8 384#usize) n) :
    mid.mlkem.CoeffsVNtt.from_bytes vec bytes ⦃ r =>
      VHolds 0 3328 n.val r.1.val (fun j => decode12 (bytes.val[j]!)) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.from_bytes
  simp only [zero_eq _ h1, h1.as_mut, h3.as_ref]
  apply spec_bind_ok
  step as ⟨polys, back, hpv, hpl, hback⟩
  step as ⟨b1, hb1⟩
  step with from_bytes_loop_spec n.val b1 polys hpl (array_length b1 bytes hb1)
      { start := 0#usize, «end» := Slice.len polys } rfl (by rw [Slice.len_val]; exact hpl)
    as ⟨polys1, hl1, hq1⟩
  apply (WP.spec_ok _).2
  intro j hj
  rw [hback _ hl1, ← hb1]
  exact hq1 j hj

theorem to_bytes_loop_spec (n : ℕ) (F : ℕ → Polynomial) (polys : Slice Poly)
    (out : Slice (Std.Array U8 384#usize)) (hl : out.length = n) (hp : polys.length = n)
    (h : ∀ j < n, Holds 0 3328 256 (polys.val[j]!).val (F j))
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    mid.mlkem.CoeffsVNtt.to_bytes_loop it out polys ⦃ y =>
      y.length = n ∧ ∀ j < n, toVec (32 * 12) (y.val[j]!).val (y.val[j]!).property = ByteEncode 12 (F j) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.to_bytes_loop
  apply WP.spec_mono (slice_loop (α := Std.Array U8 384#usize) n (fun _ _ _ => True)
    (fun j _ b => toVec (32 * 12) b.val b.property = ByteEncode 12 (F j)) _ ?_ out hl
    (fun _ _ => trivial) it hs he)
  · intro y hy
    exact hy
  · intro it s he hs hl' _
    simp only
    unfold mid.mlkem.CoeffsVNtt.to_bytes_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨a, back', ha, hb⟩
      subst hb
      step as ⟨x, hx⟩
      step with mlkem_tobytes_spec a x (F it.start.val) (by rw [hx, ← getElem!_pos]; exact h _ (by omega))
        as ⟨a1, ha1⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl',
        by rw [set_getElem!_self _ _ _ (by omega)]; exact ha1, fun j hj => set_getElem!_ne _ _ _ _ hj⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

/-- `Coeffs::to_bytes`: FIPS 203's `ByteEncode_12` of each polynomial, of
coefficients in `[0, q)`. -/
theorem to_bytes_spec {n : Usize} {MC : Type}
    (vec : mid.mlkem.Vector (Std.Array Poly n) MC (Std.Array (Std.Array U8 384#usize) n))
    (h1 : IsArray vec.FixedArraySelfArrayI16256Inst) (h3 : IsArray vec.FixedArraySelf_EncodedArrayU8384Inst)
    (v : Std.Array Poly n) (F : ℕ → Polynomial) (h : VHolds 0 3328 n.val v.val F) :
    mid.mlkem.CoeffsVNtt.to_bytes vec (v, ()) ⦃ r =>
      ∀ j < n.val, toVec (32 * 12) (r.val[j]!).val (r.val[j]!).property = ByteEncode 12 (F j) ⦄ := by
  unfold mid.mlkem.CoeffsVNtt.to_bytes
  simp only [h3.filled, h3.as_mut, h1.as_ref, bind_ok]
  step as ⟨out, back, hov, hol, hback⟩
  step as ⟨polys, hpv⟩
  step with to_bytes_loop_spec n.val F polys out hol (array_length polys v hpv)
      (fun j hj => by rw [hpv]; exact h j hj)
      { start := 0#usize, «end» := Slice.len out } rfl (by rw [Slice.len_val]; exact hol)
    as ⟨out1, hl1, hq1⟩
  intro j hj
  have : (back out1).val[j]! = out1.val[j]! := by rw [hback _ hl1]
  rw [this]
  exact hq1 j hj

/-! ## Coefficient-wise sums -/

theorem ite_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem bmod16 (x : ℤ) (h1 : -32768 ≤ x) (h2 : x ≤ 32767) : Int.bmod x (2 ^ IScalarTy.I16.numBits) = x := by
  have : (2 : ℕ) ^ IScalarTy.I16.numBits = 65536 := rfl
  rw [this]
  unfold Int.bmod
  dsimp only
  split <;> omega

theorem sub_get (f g : Polynomial) (p : ℕ) (hp : p < 256) : (f - g)[p]! = f[p]! - g[p]! := by
  rw [getElem!_pos (f - g) p hp, getElem!_pos f p hp, getElem!_pos g p hp]
  show (Vector.zipWith (· - ·) f g)[p] = _
  simp

theorem array_set_getElem! (a : Poly) (i : Usize) (x : I16) (p : ℕ) (hi : i.val < 256) :
    (a.set i x).val[p]! = if p = i.val then x else a.val[p]! := by
  rw [Std.Array.set_val_eq]
  split_ifs with h
  · subst h
    exact getElem!_set_self _ _ _ (by simp [hi])
  · exact getElem!_set_ne _ _ _ _ (Ne.symm h)

/-- The loop of `Coeffs::sub`: each coefficient's difference, wrapping. -/
theorem sub_loop_spec (a t : Poly)
    (hb : ∀ p < 256, -32768 ≤ (a.val[p]!).val - (t.val[p]!).val ∧ (a.val[p]!).val - (t.val[p]!).val ≤ 32767)
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = 256) :
    mid.mlkem.CoeffsArrayI16256Normal.sub_loop it (a, ()) (t, ()) ⦃ r =>
      ∀ p < 256, (r.1.val[p]!).val = (a.val[p]!).val - (t.val[p]!).val ⦄ := by
  unfold mid.mlkem.CoeffsArrayI16256Normal.sub_loop
  apply WP.spec_mono (range_loop 256 (fun c (s : mid.mlkem.Coeffs Poly mid.mlkem.Normal) =>
    ∀ p < 256, (s.1.val[p]!).val = if p < c then (a.val[p]!).val - (t.val[p]!).val else (a.val[p]!).val)
    _ ?_ it (a, ()) he (by omega) (fun p hp => by simp [hs]))
  · intro r hr p hp
    rw [hr p hp, ite_pos (hp)]
  · intro it s he hs hinv
    simp only
    unfold mid.mlkem.CoeffsArrayI16256Normal.sub_loop.body
    obtain ⟨sa, pd⟩ := s
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨z, hz⟩
      step as ⟨a2, ha2⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, fun p hp => ?_⟩
      rw [ha2, array_set_getElem! _ _ _ _ (by omega)]
      split_ifs with h1 h2 h2
      · subst h1
        rw [hz, core.num.I16.wrapping_sub_val_eq, hx, hy, ← getElem!_pos, ← getElem!_pos]
        have := hinv it.start.val hp
        rw [ite_neg ((by omega))] at this
        rw [this]
        exact bmod16 _ (hb _ hp).1 (hb _ hp).2
      · omega
      · rw [hinv p hp, ite_pos ((by omega))]
      · rw [hinv p hp, ite_neg ((by omega))]
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = 256 := by omega
      rw [this] at hinv
      exact hinv

/-- `Coeffs::sub`: the difference, reduced into `[0, q)`, of polynomials
whose coefficients' differences fit an `i16`. -/
theorem sub_spec (a t : Poly) (F G : Polynomial) (ha : Congr a.val F) (ht : Congr t.val G)
    (hb : ∀ p < 256, -32768 ≤ (a.val[p]!).val - (t.val[p]!).val ∧ (a.val[p]!).val - (t.val[p]!).val ≤ 32767) :
    mid.mlkem.CoeffsArrayI16256Normal.sub (a, ()) (t, ()) ⦃ r => Holds 0 3328 256 r.1.val (F - G) ⦄ := by
  unfold mid.mlkem.CoeffsArrayI16256Normal.sub
  rw [N_eq]
  apply WP.spec_bind (sub_loop_spec a t hb { start := 0#usize, «end» := 256#usize } rfl rfl)
  intro r1 hr1
  obtain ⟨r1, pd⟩ := r1
  step with mlkem_reduce_spec r1 (F - G) (fun p hp => by
      rw [hr1 p hp, sub_get _ _ _ hp, ← ha p hp, ← ht p hp]; push_cast; rfl) as ⟨r2, hr2⟩
  exact (WP.spec_ok _).2 hr2

/-- The loop of `Coeffs::add` on one polynomial: each coefficient's sum, wrapping. -/
theorem add_loop_spec (a t : Poly)
    (hb : ∀ p < 256, -32768 ≤ (a.val[p]!).val + (t.val[p]!).val ∧ (a.val[p]!).val + (t.val[p]!).val ≤ 32767)
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = 256) :
    mid.mlkem.CoeffsArrayI16256Normal.add_loop it (a, ()) t ⦃ r =>
      ∀ p < 256, (r.1.val[p]!).val = (a.val[p]!).val + (t.val[p]!).val ⦄ := by
  unfold mid.mlkem.CoeffsArrayI16256Normal.add_loop
  apply WP.spec_mono (range_loop 256 (fun c (s : mid.mlkem.Coeffs Poly mid.mlkem.Normal) =>
    ∀ p < 256, (s.1.val[p]!).val = if p < c then (a.val[p]!).val + (t.val[p]!).val else (a.val[p]!).val)
    _ ?_ it (a, ()) he (by omega) (fun p hp => by simp [hs]))
  · intro r hr p hp
    rw [hr p hp, ite_pos (hp)]
  · intro it s he hs hinv
    simp only
    unfold mid.mlkem.CoeffsArrayI16256Normal.add_loop.body
    obtain ⟨sa, pd⟩ := s
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨z, hz⟩
      step as ⟨a2, ha2⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, fun p hp => ?_⟩
      rw [ha2, array_set_getElem! _ _ _ _ (by omega)]
      split_ifs with h1 h2 h2
      · subst h1
        rw [hz, core.num.I16.wrapping_add_val_eq, hx, hy, ← getElem!_pos, ← getElem!_pos]
        have := hinv it.start.val hp
        rw [ite_neg ((by omega))] at this
        rw [this]
        exact bmod16 _ (hb _ hp).1 (hb _ hp).2
      · omega
      · rw [hinv p hp, ite_pos ((by omega))]
      · rw [hinv p hp, ite_neg ((by omega))]
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = 256 := by omega
      rw [this] at hinv
      exact hinv

/-- `Coeffs::add` on one polynomial: each coefficient's sum, of polynomials
whose coefficients' sums fit an `i16`. -/
theorem add1_spec (a t : Poly)
    (hb : ∀ p < 256, -32768 ≤ (a.val[p]!).val + (t.val[p]!).val ∧ (a.val[p]!).val + (t.val[p]!).val ≤ 32767) :
    mid.mlkem.CoeffsArrayI16256Normal.add (a, ()) t ⦃ r =>
      ∀ p < 256, (r.1.val[p]!).val = (a.val[p]!).val + (t.val[p]!).val ⦄ := by
  unfold mid.mlkem.CoeffsArrayI16256Normal.add
  rw [N_eq]
  exact add_loop_spec a t hb { start := 0#usize, «end» := 256#usize } rfl rfl

end MlKemPoly

end rind.aarch64
