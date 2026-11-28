import Rind.Aarch64.MlKemPke
import Rind.Aarch64.MlKemCbd
open Aeneas Aeneas.Std Result rind.spec Spec Spec.MLKEM rind.spec.mlkem rind.spec.s2n

/-!
# K-PKE's encryption on aarch64

`Decoded::kpke_encrypt` for ML-KEM-768, over `MlKemPoly`'s vector specs and
`MlKemCbd`'s noise: given a decoded encapsulation key whose `t̂` and
transposed matrix are FIPS 203's, it is `K-PKE.Encrypt`.
-/

namespace rind.aarch64

namespace MlKemEncrypt

open MlKemCoding MlKemRoutines MlKemGeneric MlKemPoly MlKemPke
open MlKemCbd (cbd2 get2 sample_poly_cbd_spec try_from_mut_spec unwrap_mut_spec toVec_toList)

/-! ## The matrix-vector product -/

theorem rank9 : mid.mlkem.rank 9#usize = ok 3#usize := by
  unfold mid.mlkem.rank; rfl

theorem mul_and_inverse_ntt_loop_spec {Enc : Type}
    (vec : mid.mlkem.Vector (Std.Array Poly 3#usize) (Std.Array (Std.Array I16 128#usize) 3#usize) Enc)
    (h1 : IsArray vec.FixedArraySelfArrayI16256Inst) (h2 : IsArray vec.FixedArraySelf_MulCacheArrayI16128Inst)
    (mat : mid.mlkem.FixedArray (Std.Array Poly 9#usize) Poly)
    (a : Slice Poly) (ha : a.length = 9) (y : Std.Array Poly 3#usize)
    (yc : Std.Array (Std.Array I16 128#usize) 3#usize) (A : ℕ → ℕ → Polynomial) (Y : ℕ → Polynomial)
    (hA : ∀ i < 3, ∀ j < 3, Holds (-4096) 4096 256 (a.val[3 * i + j]!).val (A i j))
    (hy : ∀ j < 3, Congr (y.val[j]!).val (Y j)) (hc : ∀ j < 3, CacheHolds (yc.val[j]!).val (Y j))
    (rows : Slice Poly) (hl : rows.length = 3)
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = 3) :
    mid.mlkem.CoeffsMNtt.mul_and_inverse_ntt_loop mat vec it (y, ()) (yc, ()) a 3#usize rows ⦃ r =>
      r.length = 3 ∧ ∀ i < 3, Mont (r.val[i]!).val (dot3 (A i) Y) ⦄ := by
  unfold mid.mlkem.CoeffsMNtt.mul_and_inverse_ntt_loop
  apply WP.spec_mono (slice_loop (α := Poly) 3 (fun _ _ _ => True)
    (fun i _ b => Mont b.val (dot3 (A i) Y)) _ ?_ rows hl (fun _ _ => trivial) it hs he)
  · intro r hr
    exact hr
  · intro it s he hs hl _
    simp only
    unfold mid.mlkem.CoeffsMNtt.mul_and_inverse_ntt_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only [h1.as_ref, h2.as_ref]
      step as ⟨r0, back, hr0, hback⟩
      subst hback
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨s, hs1, hs2⟩
      step as ⟨s1, hs1'⟩
      step as ⟨s2, hs2'⟩
      have hsl : s.length = 3 := by scalar_tac
      have hsv : ∀ j < 3, s.val[j]! = a.val[3 * it.start.val + j]! := by
        intro j hj
        rw [hs1, List.getElem!_slice _ _ _ _ ⟨by scalar_tac, by scalar_tac⟩]
        congr 1
        scalar_tac
      step with basemul_spec r0 s s1 s2 (A it.start.val) Y hsl (array_length s1 y hs1')
          (array_length s2 yc hs2') (fun j hj => by rw [hsv j hj]; exact hA _ (by omega) j hj)
          (fun j hj p hp => by rw [hs1']; exact hy j hj p hp) (by rw [hs2']; exact hc) as ⟨a2, ha2⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl,
        by rw [set_getElem!_self _ _ _ (by omega)]; exact ha2, fun j hj => set_getElem!_ne _ _ _ _ hj⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

/-- `Coeffs::mul_and_inverse_ntt`: row `i`'s `NTTInv` of the scalar product of
the matrix's row `i` and `y`, given `y`'s mulcache. -/
theorem mul_and_inverse_ntt_spec {Enc : Type}
    (vec : mid.mlkem.Vector (Std.Array Poly 3#usize) (Std.Array (Std.Array I16 128#usize) 3#usize) Enc)
    (h1 : IsArray vec.FixedArraySelfArrayI16256Inst) (h2 : IsArray vec.FixedArraySelf_MulCacheArrayI16128Inst)
    (mat : mid.mlkem.FixedArray (Std.Array Poly 9#usize) Poly) (hm : IsArray mat)
    (a : Std.Array Poly 9#usize) (y : Std.Array Poly 3#usize)
    (yc : Std.Array (Std.Array I16 128#usize) 3#usize) (A : ℕ → ℕ → Polynomial) (Y : ℕ → Polynomial)
    (hA : ∀ i < 3, ∀ j < 3, Holds (-4096) 4096 256 (a.val[3 * i + j]!).val (A i j))
    (hy : ∀ j < 3, Congr (y.val[j]!).val (Y j)) (hc : ∀ j < 3, CacheHolds (yc.val[j]!).val (Y j)) :
    mid.mlkem.CoeffsMNtt.mul_and_inverse_ntt mat vec (a, ()) (y, ()) (yc, ()) ⦃ r =>
      VHolds (-26624) 26624 3 r.1.val (fun i => NTTInv (dot3 (A i) Y)) ⦄ := by
  unfold mid.mlkem.CoeffsMNtt.mul_and_inverse_ntt
  simp only [zero_eq _ h1, hm.as_ref, h1.as_mut]
  apply spec_bind_ok
  step as ⟨sl, has⟩
  have hal : sl.length = 9 := array_length sl a has
  have hk : mid.mlkem.rank (Slice.len sl) = ok 3#usize := by
    unfold mid.mlkem.rank
    rw [Slice.len_val, hal]
    rfl
  rw [hk]
  apply spec_bind_ok
  step as ⟨rows, back, hrv, hrl, hback⟩
  step with mul_and_inverse_ntt_loop_spec vec h1 h2 mat sl hal y yc A Y (by rw [has]; exact hA) hy hc rows
      hrl { start := 0#usize, «end» := 3#usize } rfl rfl as ⟨rows1, hl1, hq1⟩
  apply WP.spec_mono (inverse_ntt_spec vec h1 (back rows1) (fun i => dot3 (A i) Y)
    (fun i hi => by rw [hback _ hl1]; exact hq1 i hi))
  intro r hr
  exact hr

/-! ## Vector sums -/

theorem vadd_inner_spec (polys terms : Slice Poly) (i : Usize) (hi : i.val < polys.length)
    (ht : i.val < terms.length)
    (hb : ∀ p < 256, -32768 ≤ ((polys.val[i.val]!).val[p]!).val + ((terms.val[i.val]!).val[p]!).val ∧
      ((polys.val[i.val]!).val[p]!).val + ((terms.val[i.val]!).val[p]!).val ≤ 32767)
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = 256) :
    mid.mlkem.CoeffsVNormal.add_loop0_loop0 it polys terms i ⦃ r =>
      r.length = polys.length ∧ (∀ j, j ≠ i.val → r.val[j]! = polys.val[j]!) ∧
      ∀ p < 256, ((r.val[i.val]!).val[p]!).val =
        ((polys.val[i.val]!).val[p]!).val + ((terms.val[i.val]!).val[p]!).val ⦄ := by
  unfold mid.mlkem.CoeffsVNormal.add_loop0_loop0
  apply WP.spec_mono (range_loop 256 (fun c (s : Slice Poly) =>
    s.length = polys.length ∧ (∀ j, j ≠ i.val → s.val[j]! = polys.val[j]!) ∧
    ∀ p < 256, ((s.val[i.val]!).val[p]!).val = if p < c then
      ((polys.val[i.val]!).val[p]!).val + ((terms.val[i.val]!).val[p]!).val
      else ((polys.val[i.val]!).val[p]!).val) _ ?_ it polys he (by omega)
    ⟨rfl, fun _ _ => rfl, fun p hp => by simp [hs]⟩)
  · intro r ⟨hl, hne, hr⟩
    exact ⟨hl, hne, fun p hp => by rw [hr p hp, ite_eq_left hp]⟩
  · intro it s he hs' ⟨hl, hne, hinv⟩
    simp only
    unfold mid.mlkem.CoeffsVNormal.add_loop0_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨x, hx⟩
      step as ⟨x1, hx1⟩
      step as ⟨y, hy⟩
      step as ⟨y1, hy1⟩
      step as ⟨z, hz⟩
      step as ⟨a2, back, ha2, hback⟩
      step as ⟨a3, ha3⟩
      subst hback
      have hxs : x = s.val[i.val]! := by rw [hx, ← getElem!_pos]
      have ha2s : a2 = s.val[i.val]! := by rw [ha2, ← getElem!_pos]
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl,
        fun j hj => by rw [set_getElem!_ne _ _ _ _ hj]; exact hne j hj, fun p hp => ?_⟩
      rw [set_getElem!_self _ _ _ (by omega), ha3, MlKemPoly.array_set_getElem! _ _ _ _ (by omega)]
      split_ifs with h1 h2 h2
      · subst h1
        rw [hz, core.num.I16.wrapping_add_val_eq, hx1, hy1, ← getElem!_pos, ← getElem!_pos, hxs, hy,
          ← getElem!_pos]
        have := hinv it.start.val hp
        rw [ite_eq_right (by omega)] at this
        rw [this]
        exact bmod16 _ (hb _ hp).1 (hb _ hp).2
      · omega
      · rw [ha2s, hinv p hp, ite_eq_left (by omega)]
      · rw [ha2s, hinv p hp, ite_eq_right (by omega)]
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = 256 := by omega
      rw [this] at hinv
      exact ⟨hl, hne, hinv⟩

theorem vadd_loop_spec (n : ℕ) (polys terms : Slice Poly) (hl : polys.length = n) (ht : terms.length = n)
    (hb : ∀ j < n, ∀ p < 256, -32768 ≤ ((polys.val[j]!).val[p]!).val + ((terms.val[j]!).val[p]!).val ∧
      ((polys.val[j]!).val[p]!).val + ((terms.val[j]!).val[p]!).val ≤ 32767)
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    mid.mlkem.CoeffsVNormal.add_loop0 it polys terms ⦃ r => r.length = n ∧ ∀ j < n, ∀ p < 256,
      ((r.val[j]!).val[p]!).val = ((polys.val[j]!).val[p]!).val + ((terms.val[j]!).val[p]!).val ⦄ := by
  unfold mid.mlkem.CoeffsVNormal.add_loop0
  apply WP.spec_mono (slice_loop (α := Poly) n
    (fun j a _ => ∀ p < 256, -32768 ≤ (a.val[p]!).val + ((terms.val[j]!).val[p]!).val ∧
      (a.val[p]!).val + ((terms.val[j]!).val[p]!).val ≤ 32767)
    (fun j a b => ∀ p < 256, (b.val[p]!).val = (a.val[p]!).val + ((terms.val[j]!).val[p]!).val)
    _ ?_ polys hl hb it hs he)
  · intro r hr
    exact hr
  · intro it s he hs' hl' hpre
    simp only
    unfold mid.mlkem.CoeffsVNormal.add_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      rw [N_eq]
      step with vadd_inner_spec s terms it.start (by omega) (by omega) (hpre (by omega))
          { start := 0#usize, «end» := 256#usize } rfl rfl as ⟨s1, hl1, hne1, hv1⟩
      exact ⟨by rw [he1]; exact he, hst, by omega, by rw [hl1]; exact hl', hv1, hne1⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

/-- `Coeffs::add`: each coefficient's sum, of vectors whose coefficients' sums
fit an `i16`. -/
theorem vadd_spec {n : Usize} (inst : mid.mlkem.FixedArray (Std.Array Poly n) Poly) (hi : IsArray inst)
    (u e : Std.Array Poly n)
    (hb : ∀ j < n.val, ∀ p < 256, -32768 ≤ ((u.val[j]!).val[p]!).val + ((e.val[j]!).val[p]!).val ∧
      ((u.val[j]!).val[p]!).val + ((e.val[j]!).val[p]!).val ≤ 32767) :
    mid.mlkem.CoeffsVNormal.add inst (u, ()) (e, ()) ⦃ r => ∀ j < n.val, ∀ p < 256,
      ((r.1.val[j]!).val[p]!).val = ((u.val[j]!).val[p]!).val + ((e.val[j]!).val[p]!).val ⦄ := by
  unfold mid.mlkem.CoeffsVNormal.add
  simp only [hi.as_mut, hi.as_ref]
  step as ⟨polys, back, hpv, hpl, hback⟩
  step as ⟨terms, htv⟩
  step with vadd_loop_spec n.val polys terms hpl (array_length terms e htv)
      (fun j hj => by rw [hpv, htv]; exact hb j hj)
      { start := 0#usize, «end» := Slice.len polys } rfl (by rw [Slice.len_val]; exact hpl)
    as ⟨polys1, hl1, hq1⟩
  apply (WP.spec_ok _).2
  intro j hj p hp
  rw [hback _ hl1, hq1 j hj p hp, hpv, htv]

/-! ## The ciphertext's compression -/

theorem sub_setSlice!_self (l X : List U8) (off len : ℕ) (hX : X.length = len) (h : off + len ≤ l.length) :
    sub (l.setSlice! off X) off len = X := by
  subst hX
  apply List.ext_getElem (by rw [sub_length _ _ _ (by simp; omega)])
  intro k h1 h2
  rw [← getElem!_pos _ k h1, ← getElem!_pos _ k h2, sub_getElem! _ _ _ _ h2,
    List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem sub_setSlice!_prefix (l X : List U8) (off off' len : ℕ) (h : off' + len ≤ off)
    (h2 : off' + len ≤ l.length) : sub (l.setSlice! off X) off' len = sub l off' len := by
  apply List.ext_getElem (by rw [sub_length _ _ _ (by simp; omega), sub_length _ _ _ h2])
  intro k h1 h3
  have hk : k < len := by rw [sub_length _ _ _ h2] at h3; exact h3
  rw [← getElem!_pos _ k h1, ← getElem!_pos _ k h3, sub_getElem! _ _ _ _ hk, sub_getElem! _ _ _ _ hk,
    List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]

theorem split3 (l : List U8) (h : l.length = 960) :
    l = sub l (320 * 0) 320 ++ sub l (320 * 1) 320 ++ sub l (320 * 2) 320 := by
  have h3 : sub l (320 * 2) 320 = l.drop 640 := List.take_of_length_le (by simp; omega)
  have h2 : sub l (320 * 1) 320 ++ l.drop 640 = l.drop 320 := by
    rw [show (640 : ℕ) = 320 + 320 from rfl, ← List.drop_drop]
    exact List.take_append_drop _ _
  rw [h3, List.append_assoc, h2]
  simp [sub, List.take_append_drop]

/-- `len` bytes of `l` from `off` are `B`'s. -/
def BytesAt (l : List U8) (off len : ℕ) (B : 𝔹 len) : Prop := bv (sub l off len) = B.toList

theorem compress_d10_vector_spec (out : Slice U8) (hl : out.length = 960) (polys : Slice Poly)
    (hp : polys.length = 3) (F : ℕ → Polynomial) (h : VHolds 0 3328 3 polys.val F) :
    mid.mlkem.compress_d10_vector out polys ⦃ r => r.length = 960 ∧
      ∀ j < 3, BytesAt r.val (320 * j) 320 (ByteEncode 10 (Polynomial.Compress 10 (F j))) ⦄ := by
  unfold mid.mlkem.compress_d10_vector
  apply WP.spec_mono (range_loop 3 (fun i (s : Slice U8) => s.length = 960 ∧
    ∀ j < i, BytesAt s.val (320 * j) 320 (ByteEncode 10 (Polynomial.Compress 10 (F j)))) _ ?_
    { start := 0#usize, «end» := Slice.len polys } out (by rw [Slice.len_val]; exact hp) (by simp)
    ⟨hl, fun j hj => absurd hj (by simp)⟩)
  · intro r hr
    exact hr
  · intro it s he hs ⟨hsl, hinv⟩
    simp only
    unfold mid.mlkem.compress_d10_vector_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨s1, back, hs1, hs1l, hback⟩
      step with try_from_mut_spec 320#usize s1 (by rw [hs1l, hi2, hi1]; simp) as ⟨r1, tback, hr1, htback⟩
      subst hr1
      step with unwrap_mut_spec core.fmt.DebugTryFromSliceError _ as ⟨a1, uback, ha1, huback⟩
      subst ha1
      step as ⟨a, ha⟩
      step with mlkem_compress_d10_spec _ a (F it.start.val)
          (by rw [ha, ← getElem!_pos]; exact h _ (by omega)) as ⟨out2, hout2⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, ?_, fun j hj => ?_⟩
      · rw [hback, Slice.setSlice!_length]; exact hsl
      · have hv : (tback (uback out2)).val = out2.val := by rw [huback]; exact htback out2
        unfold BytesAt
        rw [hback, Slice.setSlice!_val, hv, hi1]
        by_cases hjt : j = it.start.val
        · subst hjt
          have hsl' : s.val.length = 960 := hsl
          rw [sub_setSlice!_self _ _ _ 320 out2.property (by omega)]
          rw [← toVec_toList (32 * 10) out2.val out2.property, hout2]
        · have hsl' : s.val.length = 960 := hsl
          rw [sub_setSlice!_prefix _ _ _ _ _ (by omega) (by omega)]
          exact hinv j (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = 3 := by omega
      rw [this] at hinv
      exact ⟨hsl, hinv⟩

/-! ## `K-PKE.Encrypt` -/

/-- The decoded encapsulation key holds `t̂`'s polynomials `T` and the
transposed matrix's `A`, row by row, each coefficient in `[0, q)`. -/
structure DecodedHolds {X : Type} (d : mid.mlkem.Decoded X Vec Mat EkBytes CtBytes DkBytes Cache Enc)
    (T : ℕ → Polynomial) (A : ℕ → ℕ → Polynomial) : Prop where
  t_hat : VHolds 0 3328 3 d.t_hat_coeffs.1.val T
  mat : ∀ i < 3, ∀ j < 3, Holds 0 3328 256 (d.transpose_a_hat.1.val[3 * i + j]!).val (A i j)

/-- A K-PKE ciphertext of ML-KEM-768: `ByteEncode_10(Compress_10(u_j))` for
each `j`, then `ByteEncode_4(Compress_4(v))`. -/
def ctBytes (U : ℕ → Polynomial) (V : Polynomial) : List Byte :=
  (ByteEncode 10 (Polynomial.Compress 10 (U 0))).toList ++ (ByteEncode 10 (Polynomial.Compress 10 (U 1))).toList ++
    (ByteEncode 10 (Polynomial.Compress 10 (U 2))).toList ++ (ByteEncode 4 (Polynomial.Compress 4 V)).toList

/-- `K-PKE.Encrypt`'s `u` and `v`, as rind computes them, from `t̂`'s polynomials
`T`, the transposed matrix's `A`, the message `m`, and the randomness `r`. -/
def encU (A : ℕ → ℕ → Polynomial) (r : Std.Array U8 32#usize) (i : ℕ) : Polynomial :=
  NTTInv (dot3 (A i) (fun j => NTT (cbd2 r j))) + cbd2 r (3 + i)

def encV (T : ℕ → Polynomial) (m r : Std.Array U8 32#usize) : Polynomial :=
  NTTInv (dot3 T (fun j => NTT (cbd2 r j))) + cbd2 r 6 +
    Polynomial.Decompress 1 (ByteDecode (toVec (32 * 1) m.val m.property))

theorem ETA2_eq : mid.mlkem.ETA2 = 2#usize := by unfold mid.mlkem.ETA2; rfl

/-- `kpke_encrypt` writes the ciphertext of rind's `u` and `v`. -/
theorem kpke_encrypt_spec (h : RunsSha3) {X : Type}
    (P : mid.mlkem.Params X Vec Mat EkBytes CtBytes DkBytes Cache Enc) (hP : Is768 P)
    (d : mid.mlkem.Decoded X Vec Mat EkBytes CtBytes DkBytes Cache Enc) (T : ℕ → Polynomial)
    (A : ℕ → ℕ → Polynomial) (hd : DecodedHolds d T A) (m : mid.mlkem.Message)
    (r : mid.mlkem.KpkeRandomness) :
    mid.mlkem.Decoded.kpke_encrypt P d m r ⦃ c => bv c.val = ctBytes (encU A r) (encV T m r) ⦄ := by
  unfold mid.mlkem.Decoded.kpke_encrypt
  simp only [zero_eq _ hP.vec, hP.vec.as_mut, hP.vec.as_ref, hP.ct.filled, hP.ct.as_mut, hP.ETA1, hP.K, hP.DU,
    hP.DV, ETA2_eq]
  have h0 : (0#u8).val = 0 := rfl
  generalize Std.Array.repeat 3#usize (Std.Array.repeat 256#usize 0#i16) = z
  apply spec_bind_ok
  -- `y`'s noise, polynomials 0 to 2.
  step as ⟨s, back, hsv, hsl, hback⟩
  step as ⟨s1, back1, hs1v, hback1⟩
  have hs1l : s1.length = 0 := by simp [Slice.length, hs1v, Std.Array.empty]
  refine WP.spec_bind (sample_poly_cbd_spec h r 0#u8 s s1 (by rw [hsl, hs1l]; scalar_tac)) ?_
  rintro ⟨s2, s2'⟩ ⟨hl2, -, hq2⟩
  -- `e_1` and `e_2`'s, polynomials 3 to 6.
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = 3 := by rw [hi2, UScalar.cast_val_eq]; simp
  step as ⟨s3, back3, hs3v, hs3l, hback3⟩
  step as ⟨s4, back4, hs4v, hback4⟩
  have hs4l : s4.length = 1 := by simp [Slice.length, hs4v]
  refine WP.spec_bind (sample_poly_cbd_spec h r i2 s3 s4 (by rw [hs3l, hs4l, hi2v]; scalar_tac)) ?_
  rintro ⟨s5, s6⟩ ⟨hl5, hl6, hq5⟩
  have hy : VHolds (-2) 2 3 (back s2).val (cbd2 r) := by
    intro j hj
    rw [hback s2 (by rw [hl2, hsl])]
    have := hq2 j (by rw [hsl, hs1l]; exact hj)
    unfold get2 at this
    rw [ite_eq_left (by rw [hl2, hsl]; exact hj), h0, Nat.zero_add] at this
    exact this
  have he1 : VHolds (-2) 2 3 (back3 s5).val (fun j => cbd2 r (3 + j)) := by
    intro j hj
    rw [hback3 s5 (by rw [hl5, hs3l])]
    have := hq5 j (by rw [hs3l, hs4l]; omega)
    unfold get2 at this
    rw [ite_eq_left (by rw [hl5, hs3l]; exact hj), hi2v] at this
    exact this
  have he2 : Holds (-2) 2 256 ((back4 s6).val[0]!).val (cbd2 r 6) := by
    have hl6' : s6.val.length = (1#usize).val := by
      show s6.length = _
      rw [hl6, hs4l]
      rfl
    rw [hback4, Std.Array.from_slice_val _ _ hl6']
    have := hq5 3 (by rw [hs3l, hs4l]; omega)
    unfold get2 at this
    rw [ite_eq_right (by rw [hl5, hs3l]; omega), hl5, hs3l, hi2v] at this
    exact this
  -- `ŷ` and its mulcache.
  refine WP.spec_bind (ntt_spec _ hP.vec (back s2) (cbd2 r)
    (fun j hj => Holds.mono (hy j hj) (by norm_num) (by norm_num))) ?_
  rintro ⟨yh, pdy⟩ hyh
  refine WP.spec_bind (mul_cache_spec P.VectorInst hP.vec hP.cache yh _ (fun j hj => Holds.congr (hyh j hj))) ?_
  rintro ⟨yc, pdc⟩ hyc
  -- `u`.
  refine WP.spec_bind (mul_and_inverse_ntt_spec P.VectorInst hP.vec hP.cache P.FixedArraySelf_MatrixArrayI16256Inst
    hP.mat d.transpose_a_hat.1 yh yc A _ (fun i hi j hj => Holds.mono (hd.mat i hi j hj) (by norm_num) (by norm_num))
    (fun j hj => Holds.congr (hyh j hj)) hyc) ?_
  rintro ⟨cu, pdcu⟩ hcu
  dsimp only at hcu
  refine WP.spec_bind (vadd_spec _ hP.vec cu (back3 s5) (fun j hj p hp => by
    obtain ⟨a1, a2, -⟩ := hcu j hj p hp
    obtain ⟨b1, b2, -⟩ := he1 j hj p hp
    constructor <;> omega)) ?_
  rintro ⟨u, pdu⟩ hu
  dsimp only at hu
  refine WP.spec_bind (reduce_in_place_spec _ hP.vec _ u (encU A r) (fun j hj p hp => by
    rw [hu j hj p hp, encU, add_get _ _ p hp, ← (hcu j hj p hp).2.2, ← (he1 j hj p hp).2.2]
    push_cast
    rfl)) ?_
  rintro ⟨u1, pdu1⟩ hu1
  dsimp only at hu1
  -- `v`.
  refine WP.spec_bind (from_message_bits_spec m) ?_
  rintro ⟨mu, pdm⟩ hmu
  dsimp only at hmu
  refine WP.spec_bind (dot_and_inverse_ntt_spec P.VectorInst hP.vec hP.cache d.t_hat_coeffs.1 yh yc T _
    (fun j hj => Holds.mono (hd.t_hat j hj) (by norm_num) (by norm_num)) (fun j hj => Holds.congr (hyh j hj)) hyc) ?_
  rintro ⟨cv, pdcv⟩ hcv
  dsimp only at hcv
  step as ⟨a1, ha1⟩
  have ha1' : a1 = (back4 s6).val[0]! := by rw [ha1, getElem!_pos]
  rw [← ha1'] at he2
  refine WP.spec_bind (add1_spec cv a1 (fun p hp => by
    obtain ⟨x1, x2, -⟩ := hcv p hp
    obtain ⟨y1, y2, -⟩ := he2 p hp
    constructor <;> omega)) ?_
  rintro ⟨c2, pdc2⟩ hc2
  dsimp only at hc2
  refine WP.spec_bind (add1_spec c2 mu (fun p hp => by
    obtain ⟨x1, x2, -⟩ := hcv p hp
    obtain ⟨y1, y2, -⟩ := he2 p hp
    obtain ⟨z1, z2, -⟩ := hmu p hp
    rw [hc2 p hp]
    constructor <;> omega)) ?_
  rintro ⟨v, pdv⟩ hv
  dsimp only at hv
  refine WP.spec_bind (mlkem_reduce_spec v (encV T m r) (fun p hp => by
    rw [hv p hp, hc2 p hp, encV, add_get _ _ p hp, add_get _ _ p hp, ← (hcv p hp).2.2, ← (he2 p hp).2.2,
      ← (hmu p hp).2.2]
    push_cast
    rfl)) ?_
  intro a4 ha4
  -- The ciphertext.
  step as ⟨s7, back7, hs7v, hs7l, hback7⟩
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  have hi5v : i5.val = 960 := by rw [hi5, hi4]
  step as ⟨c_1, c_2, sback, hr1, hr2, hr3, hr4, hr5⟩
  split <;> try (exfalso; scalar_tac)
  step as ⟨s8, hs8⟩
  refine WP.spec_bind (compress_d10_vector_spec c_1 (by rw [hr1, hi5v]) s8 (array_length s8 u1 hs8) (encU A r)
    (by rw [hs8]; exact hu1)) ?_
  rintro c_11 ⟨hc11l, hc11⟩
  split <;> try (exfalso; scalar_tac)
  have hc2l : c_2.length = (128#usize).val := by rw [hr2, hs7l, hi5v]; rfl
  step with try_from_mut_spec 128#usize c_2 hc2l as ⟨r1, tback, hr1, htback⟩
  subst hr1
  step with unwrap_mut_spec core.fmt.DebugTryFromSliceError _ as ⟨a5, uback, ha5, huback⟩
  subst ha5
  refine WP.spec_bind (mlkem_compress_d4_spec _ _ (encV T m r) ha4) ?_
  intro c4 hc4
  apply (WP.spec_ok _).2
  rw [huback]
  have hl' : (tback (.Ok c4)).length = 128 := by
    show (tback (.Ok c4)).val.length = _
    rw [htback c4, c4.property]
    rfl
  obtain ⟨hcv1, hcl⟩ := hr5 c_11 (tback (.Ok c4)) (by rw [hc11l, hi5v]) (by rw [hl', hs7l, hi5v])
  have hcl' : (sback (c_11, tback (.Ok c4))).length = (1088#usize).val := by rw [hcl, hs7l]; rfl
  rw [hback7 _ hcl', hcv1, htback c4]
  have hc11l' : c_11.val.length = 960 := by show c_11.length = _; rw [hc11l]
  have hu0 := hc11 0 (by norm_num)
  have hu1 := hc11 1 (by norm_num)
  have hu2 := hc11 2 (by norm_num)
  unfold BytesAt at hu0 hu1 hu2
  unfold ctBytes
  rw [split3 c_11.val hc11l']
  simp only [bv, List.map_append] at hu0 hu1 hu2 ⊢
  rw [hu0, hu1, hu2]
  rw [← hc4, toVec_toList]
  rfl

/-! ## FIPS 203's `K-PKE.Encrypt`

`K-PKE.Encrypt` for ML-KEM-768, unrolled to `ctBytes`. Its loops' bounds
proofs and `update`'s index proofs mention the loop state, so they are
rewritten to proof-free forms (`upd`, `setIfInBounds`) before the loops
unroll, and each `getElem` is rewritten whole rather than under its bound. -/

open scoped Spec.Notations

theorem toList3 {α : Type} (v : Vector α 3) : v.toList = [v[0], v[1], v[2]] := by
  obtain ⟨⟨l⟩, hl⟩ := v
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp at hl
  rfl

theorem encode_compress3 (d : ℕ) (u : PolyVector q (k .ML_KEM_768)) (h1 : 1 ≤ d ∧ d < 12)
    (hd : 1 ≤ d ∧ d ≤ 12) :
    (PolyVector.ByteEncode d (PolyVector.Compress d u h1) hd).toList =
      (ByteEncode d (Polynomial.Compress d u[0] h1) hd).toList ++
        (ByteEncode d (Polynomial.Compress d u[1] h1) hd).toList ++
        (ByteEncode d (Polynomial.Compress d u[2] h1) hd).toList := by
  have h := toList3 ((PolyVector.Compress d u h1).map (fun x => ByteEncode d x hd))
  unfold PolyVector.ByteEncode
  simp only [Vector.toList, Vector.flatten, Array.toList_flatten, Array.toList_map, List.map_map] at h ⊢
  rw [h]
  simp [PolyVector.Compress, Vector.getElem_map]

theorem hmul_eq (M : PolyMatrix q (k .ML_KEM_768)) (v : PolyVector q (k .ML_KEM_768)) :
    @HMul.hMul _ _ _ (@instHMulPolyMatrixQPolyVector (k .ML_KEM_768)) M v = PolyMatrix.MulVectorNTT M v := rfl

theorem mulVec3 (M : PolyMatrix q (k .ML_KEM_768)) (v : PolyVector q (k .ML_KEM_768)) (i : ℕ) (hi : i < 3) :
    (PolyMatrix.MulVectorNTT M v)[i] =
      MultiplyNTTs (M ⟨i, hi⟩ 0) v[0] + MultiplyNTTs (M ⟨i, hi⟩ 1) v[1] + MultiplyNTTs (M ⟨i, hi⟩ 2) v[2] := by
  unfold PolyMatrix.MulVectorNTT
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size, k, List.range'_succ,
    List.range'_zero, List.forIn'_cons, List.forIn'_nil, pure_bind, Nat.zero_add, Nat.reduceAdd, Id.run_pure]
  interval_cases i <;> simp [PolyVector.set, PolyVector.zero, Polynomial.zero_add]

theorem add_getElem {kk : K} (v w : PolyVector q kk) (i : ℕ) (hi : i < kk) : (v + w)[i] = v[i] + w[i] := by
  show (Vector.ofFn fun i => v[i] + w[i])[i] = _
  simp

theorem nttinv_getElem {kk : K} (v : PolyVector q kk) (i : ℕ) (hi : i < kk) :
    (PolyVector.NTTInv v)[i] = NTTInv v[i] := Vector.getElem_map _ _

theorem ntt_getElem {kk : K} (v : PolyVector q kk) (i : ℕ) (hi : i < kk) :
    (PolyVector.NTT v)[i] = NTT v[i] := Vector.getElem_map _ _

/-- `M` with entry `(i, j)` set to `val`, without `update`'s bounds proofs. -/
def upd {kk : K} {mm : ℕ} (M : PolyMatrix mm kk) (i j : ℕ) (val : Polynomial mm) : PolyMatrix mm kk :=
  fun a b => if a.val = i ∧ b.val = j then val else M a b

theorem upd_same {kk : K} {mm : ℕ} (M : PolyMatrix mm kk) (i j : ℕ) (val : Polynomial mm) (a b : Fin kk)
    (h : a.val = i ∧ b.val = j) : upd M i j val a b = val := by
  unfold upd; rw [ite_eq_left h]

theorem upd_ne {kk : K} {mm : ℕ} (M : PolyMatrix mm kk) (i j : ℕ) (val : Polynomial mm) (a b : Fin kk)
    (h : ¬(a.val = i ∧ b.val = j)) : upd M i j val a b = M a b := by
  unfold upd; rw [ite_eq_right h]

theorem update_eq {kk : K} {mm : ℕ} (M : PolyMatrix mm kk) (i j : ℕ) (val : Polynomial mm) (hi : i < kk)
    (hj : j < kk) : M.update i j val hi hj = upd M i j val := by
  funext a b
  unfold PolyMatrix.update upd
  simp only [Matrix.updateRow_apply]
  by_cases ha : a = ⟨i, hi⟩
  · subst ha
    by_cases hb : b.val = j <;> simp [hb]
  · have : a.val ≠ i := fun h => ha (Fin.ext h)
    simp [ha, this]

theorem set_eq {kk : K} {mm : ℕ} (v : PolyVector mm kk) (i : ℕ) (f : Polynomial mm) (h : i < kk) :
    v.set i f h = v.setIfInBounds i f := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_setIfInBounds hj]
  simp only [PolyVector.set, Vector.getElem_set]

/-- The size of the spec's `[0:k]`: unfolding `k` itself would rewrite it in
types too, which leaves terms `simp` cannot check. -/
theorem size768 : (((k .ML_KEM_768 : K) : ℕ) - 0 + 1 - 1) / 1 = 3 := rfl

theorem vget! {α : Type} [Inhabited α] {n : ℕ} (v : Vector α n) (i : ℕ) (h : i < n) : v[i]! = v[i] :=
  getElem!_pos v i h

theorem append_eq {α : Type} {m n : ℕ} (a : Vector α m) (b : Vector α n) : Vector.append a b = a ++ b := rfl

/-- `K-PKE.Encrypt` for ML-KEM-768, with `t̂` and `Â` read from `ek`. -/
theorem encrypt_eq (ek : 𝔹 1184) (m r : 𝔹 32) :
    (K_PKE.Encrypt .ML_KEM_768 ek m r).toList =
      ctBytes (fun i => NTTInv (dot3 (fun j => SampleNTT (slice ek 1152 32 ‖ #v[(i : Byte)] ‖ #v[(j : Byte)]))
          (fun j => NTT (SamplePolyCBD (PRF η₂ r (j : Byte))))) + SamplePolyCBD (PRF η₂ r ((3 + i : ℕ) : Byte)))
        (NTTInv (dot3 (fun j => (PolyVector.ByteDecode (k := k .ML_KEM_768) 12 (slice ek 0 1152))[j]!)
            (fun j => NTT (SamplePolyCBD (PRF η₂ r (j : Byte))))) + SamplePolyCBD (PRF η₂ r ((6 : ℕ) : Byte)) +
          Polynomial.Decompress 1 (ByteDecode (m.cast (by omega)))) := by
  unfold K_PKE.Encrypt
  simp only [update_eq, set_eq, innerProductNTT_768]
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size, size768, List.range'_succ,
    List.range'_zero, List.forIn'_cons, List.forIn'_nil, pure_bind, Nat.zero_add, Nat.reduceAdd]
  simp only [Id.run, Vector.toList_cast, append_eq, Vector.toList_append, encode_compress3]
  simp (disch := decide) only [add_getElem, nttinv_getElem, ntt_getElem]
  rw [hmul_eq, mulVec3 _ _ 0 (by decide), mulVec3 _ _ 1 (by decide), mulVec3 _ _ 2 (by decide)]
  simp (disch := decide) only [ntt_getElem]
  simp only [Matrix.transpose_apply]
  simp (disch := decide) only [upd_same, upd_ne, Vector.getElem_setIfInBounds]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  unfold ctBytes dot3
  simp (disch := decide) only [vget!]
  rfl

/-- `kpke_encrypt` is FIPS 203's `K-PKE.Encrypt` for ML-KEM-768, given a decoded
key whose `t̂` and transposed matrix are those `ek` encodes. -/
theorem kpke_encrypt_fips (h : RunsSha3) {X : Type}
    (P : mid.mlkem.Params X Vec Mat EkBytes CtBytes DkBytes Cache Enc) (hP : Is768 P)
    (d : mid.mlkem.Decoded X Vec Mat EkBytes CtBytes DkBytes Cache Enc) (ek : 𝔹 1184)
    (hd : DecodedHolds d (fun j => (PolyVector.ByteDecode (k := k .ML_KEM_768) 12 (slice ek 0 1152))[j]!)
      (fun i j => SampleNTT (slice ek 1152 32 ‖ #v[(i : Byte)] ‖ #v[(j : Byte)])))
    (m : mid.mlkem.Message) (r : mid.mlkem.KpkeRandomness) :
    mid.mlkem.Decoded.kpke_encrypt P d m r ⦃ c =>
      toVec 1088 c.val c.property =
        K_PKE.Encrypt .ML_KEM_768 ek (toVec 32 m.val m.property) (toVec 32 r.val r.property) ⦄ := by
  apply WP.spec_mono (kpke_encrypt_spec h P hP d _ _ hd m r)
  intro c hc
  apply Vector.toList_inj.mp
  rw [toVec_toList, hc, encrypt_eq]
  rfl

end MlKemEncrypt

end rind.aarch64
