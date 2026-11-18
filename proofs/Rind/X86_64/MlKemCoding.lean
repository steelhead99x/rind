import Rind.X86_64.Funs
import Rind.X86_64.Blockwise
import Rind.MlKemCoding
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.spec Spec Spec.MLKEM rind.spec.mlkem

namespace rind.x86_64

namespace MlKemCoding

/-- A counted loop: its body, run from an index below `n` on a state the
invariant holds of, either continues to the next index, never past `n`, with a
state it holds of, or stops with a result `post` holds of. Stopping may come
before `n`: this states only that every result meets `post`, so a proof that
needs the loop to run to `n` shows it separately. -/
theorem range_loop' {σ τ : Type} (n : ℕ) (inv : ℕ → σ → Prop) (post : τ → Prop)
    (body : core.ops.range.Range Usize × σ → Result (ControlFlow (core.ops.range.Range Usize × σ) τ))
    (hbody : ∀ (it : core.ops.range.Range Usize) (s : σ), it.end.val = n → it.start.val ≤ n →
      inv it.start.val s →
      body (it, s) ⦃ r => match r with
        | .done y => post y
        | .cont x => x.1.end.val = n ∧ x.1.start.val = it.start.val + 1 ∧ it.start.val < n ∧
            inv x.1.start.val x.2 ⦄)
    (it : core.ops.range.Range Usize) (s : σ) (he : it.end.val = n) (hs : it.start.val ≤ n)
    (hinv : inv it.start.val s) :
    loop body (it, s) ⦃ y => post y ⦄ := by
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => x.1.end.val = n ∧ x.1.start.val ≤ n ∧ inv x.1.start.val x.2)
  · rintro ⟨it, s⟩ ⟨he, hs, hinv⟩
    apply WP.spec_mono (hbody it s he hs hinv)
    rintro (x | y) h
    · obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨⟨h1, by omega, h4⟩, by simp only; omega⟩
    · exact h
  · exact ⟨he, hs, hinv⟩

theorem range_loop {σ : Type} (n : ℕ) (inv : ℕ → σ → Prop)
    (body : core.ops.range.Range Usize × σ → Result (ControlFlow (core.ops.range.Range Usize × σ) σ))
    (hbody : ∀ (it : core.ops.range.Range Usize) (s : σ), it.end.val = n → it.start.val ≤ n →
      inv it.start.val s →
      body (it, s) ⦃ r => match r with
        | .done y => inv n y
        | .cont x => x.1.end.val = n ∧ x.1.start.val = it.start.val + 1 ∧ it.start.val < n ∧
            inv x.1.start.val x.2 ⦄)
    (it : core.ops.range.Range Usize) (s : σ) (he : it.end.val = n) (hs : it.start.val ≤ n)
    (hinv : inv it.start.val s) :
    loop body (it, s) ⦃ y => inv n y ⦄ := by
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => x.1.end.val = n ∧ x.1.start.val ≤ n ∧ inv x.1.start.val x.2)
  · rintro ⟨it, s⟩ ⟨he, hs, hinv⟩
    apply WP.spec_mono (hbody it s he hs hinv)
    rintro (x | y) h
    · obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨⟨h1, by omega, h4⟩, by simp only; omega⟩
    · exact h
  · exact ⟨he, hs, hinv⟩

theorem getElem!_set_self {α : Type _} [Inhabited α] (l : List α) (i : ℕ) (x : α) (h : i < l.length) :
    (l.set i x)[i]! = x := by
  simp [h]

theorem getElem!_set_ne {α : Type _} [Inhabited α] (l : List α) (i j : ℕ) (x : α) (h : i ≠ j) :
    (l.set i x)[j]! = l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

/-- `l`, of `n` bytes, as SymCrypt's byte string. -/
def toVec (n : ℕ) (l : List U8) (h : l.length = n) : 𝔹 n := ⟨(bv l).toArray, by simp [bv_length, h]⟩

/-- Bit `k` of `l`, in FIPS 203's `BytesToBits` order. -/
theorem bit_toVec (n : ℕ) (l : List U8) (h : l.length = n) (k : ℕ) :
    bit (toVec n l h) k = (l[k / 8]!).val.testBit (k % 8) := by
  unfold bit toVec
  by_cases hk : k / 8 < l.length
  · have : ((⟨(bv l).toArray, by simp [bv_length, h]⟩ : 𝔹 n)[k / 8]!) = (l[k / 8]!).bv := by
      rw [getElem!_pos _ _ (by omega)]
      simp only [Vector.getElem_mk, List.getElem_toArray, bv, List.getElem_map]
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rfl
    rw [this]
    rfl
  · have h1 : ((⟨(bv l).toArray, by simp [bv_length, h]⟩ : 𝔹 n)[k / 8]!) = 0 := by
      rw [getElem!_neg _ _ (by omega)]
      rfl
    have h2 : l[k / 8]! = 0#u8 := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [h1, h2]
    simp

/-- Bit `k` of the number little-endian bytes encode is bit `k % 8` of byte
`k / 8`. -/
theorem leNat_testBit : ∀ (l : List U8) (k : ℕ),
    (leNat l).testBit k = (l[k / 8]!).val.testBit (k % 8)
  | [], k => by
    have : ([] : List U8)[k / 8]! = 0#u8 := rfl
    rw [this]
    simp [leNat]
  | b :: l, k => by
    have e : leNat (b :: l) = 2 ^ 8 * leNat l + b.val := by
      simp only [leNat, List.map_cons, Nat.ofDigits_cons]
      ring
    have hb : b.val < 2 ^ 8 := by scalar_tac
    rw [e, Nat.testBit_two_pow_mul_add _ hb]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · rw [leNat_testBit l (k - 8)]
      obtain ⟨c, rfl⟩ : ∃ c, k = c + 8 := ⟨k - 8, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right _ (by norm_num), Nat.add_mod_right]
      rfl

/-- The low `d` bits of a number, as the sum of each times its power of two. -/
theorem mod_two_pow_eq_sum (x : ℕ) : ∀ d : ℕ, x % 2 ^ d = ∑ t : Fin d, (x.testBit t).toNat * 2 ^ t.val
  | 0 => by simp [Nat.mod_one]
  | d + 1 => by
    rw [Fin.sum_univ_castSucc, Nat.mod_pow_succ, mod_two_pow_eq_sum x d, Nat.toNat_testBit]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring

/-- The value `decompress` writes for the `D`-bit field `y`: FIPS 203's
`Decompress_D`, as `Decompress_val` states it. -/
def decompVal (D y : ℕ) : ℕ := (y * 3329 + 2 ^ (D - 1)) / 2 ^ D

theorem decompVal_lt (D y : ℕ) (hD : 1 ≤ D ∧ D ≤ 11) (hy : y < 2 ^ D) : decompVal D y < 3329 := by
  unfold decompVal
  obtain ⟨c, rfl⟩ : ∃ c, D = c + 1 := ⟨D - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h1 : 2 ^ c ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.div_lt_iff_lt_mul (by positivity), pow_succ] at *
  nlinarith

/-- `Decompress_d(ByteDecode_d(B))`'s coefficient `p`, from a number `x`
whose low `d` bits are `B`'s from bit `p * d`. -/
theorem decompress_field {d : ℕ} (B : 𝔹 (32 * d)) (hd : 1 ≤ d ∧ d ≤ 11) (p : ℕ) (hp : p < 256) (x : ℕ)
    (hx : ∀ t < d, x.testBit t = bit B (p * d + t)) :
    (Polynomial.Decompress d (ByteDecode B (by omega)) (by omega))[p]! = ((decompVal d (x % 2 ^ d) : ℕ) : Zq) := by
  unfold Polynomial.Decompress
  rw [Vector.getElem!_map_eq _ _ _ hp, Decompress_val, ByteDecode_get _ _ _ hp]
  have hm : m d = 2 ^ d := by simp [m]; omega
  have hsum : (∑ j : Fin d, (bit B (p * d + j)).toNat * 2 ^ j.val) = x % 2 ^ d := by
    rw [mod_two_pow_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hx j j.isLt]
  rw [hsum]
  have hval : (((x % 2 ^ d : ℕ) : ZMod (m d))).val = x % 2 ^ d := by
    rw [ZMod.val_natCast, hm, Nat.mod_mod]
  rw [hval, decompVal, Nat.mul_comm]

theorem decompress_inner_spec (D i : Usize) (bits : U128) (hD : 1 ≤ D.val ∧ D.val ≤ 11) (hi : i.val < 32)
    (iter : core.ops.range.Range Usize) (out : Array I16 256#usize)
    (he : iter.end.val = 8) (hs : iter.start.val = 0) :
    mid.mlkem.decompress_loop0_loop0 D iter out i bits ⦃ r =>
      (∀ p, 8 * i.val ≤ p → p < 8 * i.val + 8 →
        (r.val[p]!).val = (decompVal D.val (bits.val / 2 ^ (D.val * (p - 8 * i.val)) % 2 ^ D.val) : ℤ)) ∧
      ∀ p, ¬ (8 * i.val ≤ p ∧ p < 8 * i.val + 8) → r.val[p]! = out.val[p]! ⦄ := by
  unfold mid.mlkem.decompress_loop0_loop0
  apply range_loop 8 (fun j (o : Array I16 256#usize) =>
    (∀ p, 8 * i.val ≤ p → p < 8 * i.val + j →
      (o.val[p]!).val = (decompVal D.val (bits.val / 2 ^ (D.val * (p - 8 * i.val)) % 2 ^ D.val) : ℤ)) ∧
    ∀ p, ¬ (8 * i.val ≤ p ∧ p < 8 * i.val + j) → o.val[p]! = out.val[p]!) _ _ iter out he (by omega)
  · rw [hs]
    exact ⟨fun p h1 h2 => by omega, fun p _ => rfl⟩
  · intro it o he hs hinv
    simp only
    unfold mid.mlkem.decompress_loop0_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have hD1 := hD.1
      have hD2 := hD.2
      have hpow : 2 ^ D.val ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) hD2
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2, _⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4, _⟩
      have hi4v : i4.val = 2 ^ D.val := by
        rw [hi4, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt (by simp [U32.size, U32.numBits]; omega)]
      have hpos : 1 ≤ 2 ^ D.val := Nat.one_le_two_pow
      step as ⟨i5, hi5, _⟩
      step as ⟨y, hy, _⟩
      have hyv : y.val = bits.val / 2 ^ (D.val * it.start.val) % 2 ^ D.val := by
        rw [hy, UScalar.val_and, hi5, hi4v, Nat.and_two_pow_sub_one_eq_mod, hi3, UScalar.cast_val_eq, hi2,
          hi1, Nat.shiftRight_eq_div_pow]
        exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by simp [UScalarTy.numBits]; omega))
      have hylt : y.val < 2 ^ D.val := by rw [hyv]; exact Nat.mod_lt _ (by positivity)
      step as ⟨i6, hi6⟩
      have hi6v : i6.val = 3329 := by rw [hi6]; simp [mid.mlkem.Q]
      have hprod : y.val * i6.val ≤ 2 ^ 11 * 3329 := by rw [hi6v]; exact Nat.mul_le_mul_right _ (by omega)
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8, _⟩
      step as ⟨i9, hi9, _⟩
      have hpow' : 2 ^ (D.val - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hi9v : i9.val = 2 ^ (D.val - 1) := by
        rw [hi9, hi8, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt (by simp [U32.size, U32.numBits]; omega)]
      step as ⟨i10, hi10⟩
      step as ⟨i11, hi11, _⟩
      have hi11v : i11.val = decompVal D.val y.val := by
        rw [hi11, hi10, hi7, hi9v, hi6v, Nat.shiftRight_eq_div_pow, decompVal]
      have hlt11 := decompVal_lt D.val y.val hD hylt
      step as ⟨i12, hi12⟩
      step as ⟨i13, hi13⟩
      step as ⟨i14, hi14⟩
      have hi14v : i14.val = (decompVal D.val y.val : ℤ) := by
        rw [hi14, UScalar.hcast_val_eq, hi11v]
        exact Int.bmod_eq_of_le (by simp) (by simp; omega)
      step as ⟨a, ha⟩
      obtain ⟨hin, hout⟩ := hinv
      have hidx : i13.val = 8 * i.val + it.start.val := by rw [hi13, hi12]
      have hlen : 8 * i.val + it.start.val < o.val.length := by simp; omega
      refine ⟨by rw [he1]; exact he, hst, by omega, fun p h1 h2 => ?_, fun p hp => ?_⟩
      · rw [ha, Array.set_val_eq, hidx]
        by_cases hp : p = 8 * i.val + it.start.val
        · subst hp
          rw [getElem!_set_self _ _ _ hlen, hi14v, hyv,
            show 8 * i.val + it.start.val - 8 * i.val = it.start.val by omega]
        · rw [getElem!_set_ne _ _ _ _ (Ne.symm hp)]
          exact hin p h1 (by omega)
      · rw [ha, Array.set_val_eq, hidx, getElem!_set_ne _ _ _ _ (by omega)]
        exact hout p (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val = 8 := by omega
      rw [this] at hinv
      exact hinv

/-- The first `n` coefficients of `a` are those of `f`, each in `[lo, hi]`. -/
def Holds (lo hi : ℤ) (n : ℕ) (a : List I16) (f : Polynomial) : Prop :=
  ∀ p < n, lo ≤ (a[p]!).val ∧ (a[p]!).val ≤ hi ∧ (((a[p]!).val : ℤ) : Zq) = f[p]!

/-- `u128::from_le_bytes` reads its bytes as a little-endian number. -/
theorem val_of_fromLEBytes128 (a : List U8) (i : U128) {h}
    (hi : i.bv = (BitVec.fromLEBytes (a.map U8.bv)).cast h) : i.val = leNat a := by
  show i.bv.toNat = _
  rw [hi, BitVec.toNat_cast, toNat_fromLEBytes]
  simp [leNat, List.map_map, Function.comp_def]

/-- Bit `D * j + t` of the bytes from `D * i` is bit `t` of the `D`-bit field
`8 * i + j`. -/
theorem chunk_bit (D i j t : ℕ) (bytes : List U8) :
    (bytes[D * i + (D * j + t) / 8]!).val.testBit ((D * j + t) % 8) =
      (bytes[((8 * i + j) * D + t) / 8]!).val.testBit (((8 * i + j) * D + t) % 8) := by
  have : (8 * i + j) * D + t = (D * j + t) + (D * i) * 8 := by ring
  rw [this, Nat.add_mul_div_right _ _ (by norm_num), Nat.add_mul_mod_self_right, Nat.add_comm (D * i)]

theorem decompress_loop_spec (D : Usize) {L : Usize} (hD : 1 ≤ D.val ∧ D.val ≤ 11)
    (bytes : Array U8 L) (hlen : bytes.val.length = 32 * D.val)
    (iter : core.ops.range.Range Usize) (out : Array I16 256#usize)
    (he : iter.end.val = 32) (hs : iter.start.val = 0) :
    mid.mlkem.decompress_loop0 D iter bytes out ⦃ r =>
      Holds 0 3328 256 r.val
        (Polynomial.Decompress D.val (ByteDecode (toVec (32 * D.val) bytes.val hlen) (by omega)) (by omega)) ⦄ := by
  unfold mid.mlkem.decompress_loop0
  apply WP.spec_mono (range_loop 32 (fun i (o : Array I16 256#usize) => Holds 0 3328 (8 * i) o.val
    (Polynomial.Decompress D.val (ByteDecode (toVec (32 * D.val) bytes.val hlen) (by omega)) (by omega)))
    _ _ iter out he (by omega) (by rw [hs]; intro p hp; omega))
  · intro r hr
    exact hr
  · intro it o he hs hinv
    simp only
    unfold mid.mlkem.decompress_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have hD1 := hD.1
      have hD2 := hD.2
      have hi32 : it.start.val < 32 := by omega
      have hprod : D.val * it.start.val + D.val ≤ 32 * D.val := by nlinarith
      step as ⟨s, back, hs1, hs2, hback⟩
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨s1, hs1v, hs1l⟩
      step as ⟨s2, hs2v⟩
      · rw [hs2, hs1l, hi2]; omega
      step as ⟨bits2, hbits2⟩
      have hbv : bits2.val = leNat (back s2).val := val_of_fromLEBytes128 _ _ hbits2
      step with decompress_inner_spec D it.start bits2 hD hi32 { start := 0#usize, «end» := 8#usize } o rfl rfl as ⟨out1, hin1, hout1⟩
      refine ⟨by rw [he1]; exact he, hst, hi32, ?_⟩
      rw [hst]
      intro p hp
      by_cases hp8 : p < 8 * it.start.val
      · rw [hout1 p (by omega)]
        exact hinv p hp8
      · have hv := hin1 p (by omega) (by omega)
        have hmod : bits2.val / 2 ^ (D.val * (p - 8 * it.start.val)) % 2 ^ D.val < 2 ^ D.val :=
          Nat.mod_lt _ (by positivity)
        have hlt := decompVal_lt D.val _ hD hmod
        refine ⟨by rw [hv]; positivity, by rw [hv]; omega, ?_⟩
        rw [hv, Int.cast_natCast]
        symm
        apply decompress_field _ hD p (by omega)
        intro t ht
        obtain ⟨j, rfl⟩ : ∃ j, p = 8 * it.start.val + j := ⟨p - 8 * it.start.val, by omega⟩
        have hj : j < 8 := by omega
        rw [Nat.add_sub_cancel_left, Nat.testBit_div_two_pow, hbv, leNat_testBit, hback, hs2v,
          Array.repeat_val, bit_toVec, ← chunk_bit]
        have hk : (D.val * j + t) / 8 < D.val := by
          rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith
        have hts : bytes.to_slice.val = bytes.val := by simp [Array.to_slice]
        have hs1len : s1.val.length = D.val := by
          rw [show s1.val.length = s1.length from rfl, hs1l, hi2]; omega
        rw [Nat.add_comm t, List.getElem!_setSlice!_middle _ _ _ _ ⟨Nat.zero_le _, by omega, by simp; omega⟩,
          hs1v, Nat.sub_zero, hts,
          List.getElem!_slice _ _ _ _ ⟨by rw [hlen, hi2, hi1]; exact hprod, by omega⟩, hi1]
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val = 32 := by omega
      rw [this] at hinv
      exact hinv

/-- `decompress::<D, L>` writes FIPS 203's `Decompress_D(ByteDecode_D(bytes))`,
each coefficient in `[0, q)`, for `D` from 1 to 11 and `L = 32 * D` bytes. -/
theorem decompress_spec (D : Usize) {L : Usize} (hD : 1 ≤ D.val ∧ D.val ≤ 11) (hL : L.val = 32 * D.val)
    (bytes : Array U8 L) (out : Array I16 256#usize) :
    mid.mlkem.decompress D bytes out ⦃ r =>
      Holds 0 3328 256 r.val
        (Polynomial.Decompress D.val
          (ByteDecode (toVec (32 * D.val) bytes.val (by rw [← hL]; exact bytes.property)) (by omega))
          (by omega)) ⦄ := by
  unfold mid.mlkem.decompress
  have hD2 := hD.2
  step as ⟨x, hx⟩
  step as ⟨i, hi⟩
  have hiv : L = i := by
    apply UScalar.eq_of_val_eq
    rw [hL, hi]
    simp [Usize.wrapping_mul]
    exact (Nat.mod_eq_of_lt (by rw [← hx]; scalar_tac)).symm
  simp only [massert, hiv, ite_true, bind_ok]
  step as ⟨i1, hi1⟩
  have h8 : i1.val = 32 := by rw [hi1]; simp [mid.mlkem.N]
  exact decompress_loop_spec D hD bytes _ _ out h8 rfl

/-- `ct_select_i16` on a bit: the half modulus if it is set, and zero if not,
as `Decompress_1` takes it. -/
theorem ct_select_half_spec (b : U8) (hb : b.val ≤ 1) :
    low.generic.ct_copy.ct_select_i16 b 1665#i16 0#i16 ⦃ r => r.val = (decompVal 1 b.val : ℤ) ⦄ := by
  have hb' : b = 0#u8 ∨ b = 1#u8 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h
    · left; exact UScalar.eq_of_val_eq h
    · right; exact UScalar.eq_of_val_eq h
  unfold low.generic.ct_copy.ct_select_i16 core.hint.black_box core.num.I32.wrapping_neg
  rcases hb' with rfl | rfl
  · simp [decompVal, lift]
    step as ⟨i3, hv, hbv⟩
    have h3 : i3 = 0#i32 := by
      apply IScalar.eq_of_val_eq; rw [hv]; decide
    subst h3
    decide
  · simp [decompVal, lift]
    step as ⟨i3, hv, hbv⟩
    have h3 : i3 = (-1)#i32 := by
      apply IScalar.eq_of_val_eq; rw [hv]; decide
    subst h3
    decide

set_option maxRecDepth 100000 in
/-- The multiply and shift `compress_1` divides by: `Compress_1`'s rounded
quotient, for each coefficient. -/
theorem compress_1_exact : ∀ v < 3329, (2 * v + 1665) * 80635 / 2 ^ 28 % 2 = (2 * (2 ^ 1 * v) + 3329) / (2 * 3329) % 2 := by
  intro v hv
  have e : (2 : ℕ) ^ 28 = 268435456 := by norm_num
  rw [e]
  rcases Nat.lt_or_ge v 833 with h | h
  · have h1 : (2 * v + 1665) * 80635 / 268435456 = 0 := by omega
    have h2 : (2 * (2 ^ 1 * v) + 3329) / (2 * 3329) = 0 := by omega
    rw [h1, h2]
  rcases Nat.lt_or_ge v 2497 with h' | h'
  · have h1 : (2 * v + 1665) * 80635 / 268435456 = 1 := by omega
    have h2 : (2 * (2 ^ 1 * v) + 3329) / (2 * 3329) = 1 := by omega
    rw [h1, h2]
  · have h1 : (2 * v + 1665) * 80635 / 268435456 = 2 := by omega
    have h2 : (2 * (2 ^ 1 * v) + 3329) / (2 * 3329) = 2 := by omega
    rw [h1, h2]

theorem Q_HALF_spec : mid.mlkem.Q_HALF ⦃ r => r = 1665#i16 ⦄ := by
  unfold mid.mlkem.Q_HALF
  simp only [mid.mlkem.Q]
  step as ⟨i, hi⟩
  step as ⟨r, hr⟩
  apply IScalar.eq_of_val_eq
  rw [hr, hi]
  decide

theorem from_message_inner_spec (i : Usize) (hi : i.val < 32) (m : mid.mlkem.Message)
    (r : mid.mlkem.Coeffs (Array I16 256#usize) mid.mlkem.Normal)
    (iter : core.ops.range.Range Usize) (he : iter.end.val = 8) (hs : iter.start.val = 0) :
    mid.mlkem.CoeffsArrayI16256Normal.from_message_bits_loop0_loop0 iter m r i ⦃ s =>
      s.1 = m ∧
      (∀ p, 8 * i.val ≤ p → p < 8 * i.val + 8 →
        (s.2.1.val[p]!).val = (decompVal 1 ((m.val[i.val]!).val / 2 ^ (p - 8 * i.val) % 2 ^ 1) : ℤ)) ∧
      ∀ p, ¬ (8 * i.val ≤ p ∧ p < 8 * i.val + 8) → s.2.1.val[p]! = r.1.val[p]! ⦄ := by
  unfold mid.mlkem.CoeffsArrayI16256Normal.from_message_bits_loop0_loop0
  apply range_loop 8 (fun j (s : mid.mlkem.Message × mid.mlkem.Coeffs (Array I16 256#usize) mid.mlkem.Normal) =>
    s.1 = m ∧
    (∀ p, 8 * i.val ≤ p → p < 8 * i.val + j →
      (s.2.1.val[p]!).val = (decompVal 1 ((m.val[i.val]!).val / 2 ^ (p - 8 * i.val) % 2 ^ 1) : ℤ)) ∧
    ∀ p, ¬ (8 * i.val ≤ p ∧ p < 8 * i.val + j) → s.2.1.val[p]! = r.1.val[p]!) _ _ iter (m, r) he (by omega)
  · rw [hs]
    exact ⟨rfl, fun p h1 h2 => by omega, fun p _ => rfl⟩
  · intro it s he hs hinv
    obtain ⟨m', a, pd⟩ := s
    obtain ⟨hm, hin, hout⟩ := hinv
    simp only at hm hin hout
    subst hm
    simp only
    unfold mid.mlkem.CoeffsArrayI16256Normal.from_message_bits_loop0_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2, _⟩
      step as ⟨i3, hi3⟩
      have hi3v : i3.val = (m'.val[i.val]!).val / 2 ^ it.start.val % 2 ^ 1 := by
        have h1 : (1#u8).val = 2 ^ 1 - 1 := by decide
        have hget : m'.val[i.val]! = i1 := by
          rw [hi1]; exact getElem!_pos m'.val i.val (by scalar_tac)
        rw [hget, hi3, UScalar.val_and, hi2, Nat.shiftRight_eq_div_pow, h1, Nat.and_two_pow_sub_one_eq_mod]
      step with Q_HALF_spec as ⟨i4, hi4⟩
      subst hi4
      step with ct_select_half_spec as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      step as ⟨a1, ha1⟩
      have hidx : i7.val = 8 * i.val + it.start.val := by rw [hi7, hi6]; omega
      have hlen : 8 * i.val + it.start.val < a.val.length := by simp; omega
      refine ⟨by rw [he1]; exact he, hst, by omega, fun p h1 h2 => ?_, fun p hp => ?_⟩
      · rw [ha1, Array.set_val_eq, hidx]
        by_cases hp : p = 8 * i.val + it.start.val
        · subst hp
          rw [getElem!_set_self _ _ _ hlen, hi5, hi3v,
            show 8 * i.val + it.start.val - 8 * i.val = it.start.val by omega]
        · rw [getElem!_set_ne _ _ _ _ (Ne.symm hp)]
          exact hin p h1 (by omega)
      · rw [ha1, Array.set_val_eq, hidx, getElem!_set_ne _ _ _ _ (by omega)]
        exact hout p (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val = 8 := by omega
      rw [this] at hin hout
      exact ⟨trivial, hin, hout⟩

theorem from_message_loop_spec (m : mid.mlkem.Message)
    (r : mid.mlkem.Coeffs (Array I16 256#usize) mid.mlkem.Normal)
    (iter : core.ops.range.Range Usize) (he : iter.end.val = 32) (hs : iter.start.val = 0) :
    mid.mlkem.CoeffsArrayI16256Normal.from_message_bits_loop0 iter m r ⦃ s =>
      Holds 0 3328 256 s.1.val
        (Polynomial.Decompress 1 (ByteDecode (toVec (32 * 1) m.val m.property) (by omega)) (by omega)) ⦄ := by
  have final : ∀ a : Array I16 256#usize,
      (∀ p, p < 8 * 32 → (a.val[p]!).val = (decompVal 1 ((m.val[p / 8]!).val / 2 ^ (p % 8) % 2 ^ 1) : ℤ)) →
      Holds 0 3328 256 a.val
        (Polynomial.Decompress 1 (ByteDecode (toVec (32 * 1) m.val m.property) (by omega)) (by omega)) := by
    intro a h p hp
    have hv := h p (by omega)
    have hlt := decompVal_lt 1 ((m.val[p / 8]!).val / 2 ^ (p % 8) % 2 ^ 1) (by omega)
      (Nat.mod_lt _ (by norm_num))
    refine ⟨by rw [hv]; positivity, by rw [hv]; omega, ?_⟩
    rw [hv, decompress_field (d := 1) _ (by omega) p hp ((m.val[p / 8]!).val / 2 ^ (p % 8))]
    · simp
    · intro t ht
      obtain rfl : t = 0 := by omega
      rw [bit_toVec, Nat.testBit_div_two_pow]
      simp
  unfold mid.mlkem.CoeffsArrayI16256Normal.from_message_bits_loop0
  apply range_loop' 32 (fun j (s : mid.mlkem.Message × mid.mlkem.Coeffs (Array I16 256#usize) mid.mlkem.Normal) =>
    s.1 = m ∧ ∀ p, p < 8 * j →
      (s.2.1.val[p]!).val = (decompVal 1 ((m.val[p / 8]!).val / 2 ^ (p % 8) % 2 ^ 1) : ℤ)) _ _ _ iter (m, r) he
    (by omega)
  · rw [hs]
    exact ⟨rfl, fun p h => by omega⟩
  · intro it s he hs hinv
    obtain ⟨m', r'⟩ := s
    obtain ⟨hm, hin⟩ := hinv
    simp only at hm hin
    subst hm
    simp only
    unfold mid.mlkem.CoeffsArrayI16256Normal.from_message_bits_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step with from_message_inner_spec as ⟨m1, r1, hsm, hsin, hsout⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, hsm, fun p hp => ?_⟩
      rw [hst] at hp
      by_cases hlo : 8 * it.start.val ≤ p
      · rw [hsin p hlo (by omega), show p / 8 = it.start.val by omega,
          show p - 8 * it.start.val = p % 8 by omega]
      · rw [hsout p (by omega)]
        exact hin p (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val = 32 := by omega
      rw [this] at hin
      exact final _ hin

theorem spec_bind_ok {α β : Type} (x : α) (f : α → Result β) (P : β → Prop) (h : f x ⦃ P ⦄) :
    (do let r ← ok x; f r) ⦃ P ⦄ := by
  simpa using h

/-- `from_message_bits` is FIPS 203's `Decompress_1(ByteDecode_1(m))`, each
coefficient in `[0, q)`. -/
theorem from_message_bits_spec (m : mid.mlkem.Message) :
    mid.mlkem.CoeffsArrayI16256Normal.from_message_bits m ⦃ r =>
      Holds 0 3328 256 r.1.val
        (Polynomial.Decompress 1 (ByteDecode (toVec (32 * 1) m.val m.property) (by omega)) (by omega)) ⦄ := by
  unfold mid.mlkem.CoeffsArrayI16256Normal.from_message_bits mid.mlkem.CoeffsArrayI16256D.zero
  apply spec_bind_ok (Array.repeat 256#usize 0#i16, ())
  exact from_message_loop_spec m _ { start := 0#usize, «end» := 32#usize } rfl rfl

/-- `compress_1` is FIPS 203's `Compress_1`, of a coefficient in `[0, q)`. -/
theorem compress_1_spec (x : I16) (h0 : 0 ≤ x.val) (h1 : x.val < 3329) :
    mid.mlkem.compress_1 x ⦃ r => r.val = (2 * (2 ^ 1 * x.val.toNat) + 3329) / (2 * 3329) % 2 ⦄ := by
  unfold mid.mlkem.compress_1 low.ct.into_public
  have hle : 0#i16 ≤ x := by scalar_tac
  have hlt : x < mid.mlkem.Q := by simp [mid.mlkem.Q]; scalar_tac
  apply spec_bind_ok x
  simp only [massert, hle, hlt, ite_true]
  step as ⟨i, hi⟩
  step as ⟨x1, hx1, _⟩
  step with Q_HALF_spec as ⟨i1, hi1⟩
  subst hi1
  step as ⟨i2, hi2⟩
  step as ⟨x2, hx2⟩
  step as ⟨x3, hx3⟩
  step as ⟨x4, hx4, _⟩
  step as ⟨i3, hi3⟩
  have hv : (x.val.toNat : ℤ) = x.val := Int.toNat_of_nonneg h0
  have hvlt : x.val.toNat < 3329 := by omega
  generalize x.val.toNat = v at hv hvlt ⊢
  have hiv : i.val = v := by
    rw [hi, IScalar.hcast_val_eq, ← hv]
    simp [UScalarTy.numBits]
    omega
  have hi2v : i2.val = 1665 := by
    rw [hi2]; decide
  have hx1v : x1.val = 2 * v := by
    rw [hx1, hiv, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by simp [U64.size, U64.numBits]; omega)]
    omega
  have hx2v : x2.val = 2 * v + 1665 := by
    rw [hx2, core.num.U64.wrapping_add_val_eq, hx1v, hi2v]
    exact Nat.mod_eq_of_lt (by simp [U64.size, U64.numBits]; omega)
  have hx3v : x3.val = (2 * v + 1665) * 80635 := by
    rw [hx3, core.num.U64.wrapping_mul_val_eq, hx2v, show (80635#u64).val = 80635 by decide]
    exact Nat.mod_eq_of_lt (by simp [U64.size, U64.numBits]; omega)
  have hi3v : i3.val = (2 * v + 1665) * 80635 / 2 ^ 28 % 2 := by
    have h1 : (1#u64).val = 2 ^ 1 - 1 := by decide
    rw [hi3, UScalar.val_and, hx4, hx3v, Nat.shiftRight_eq_div_pow, h1, Nat.and_two_pow_sub_one_eq_mod]
  rw [UScalar.cast_val_eq, hi3v, compress_1_exact v hvlt]
  exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)

theorem spec_bind_ret {α : Type} (x : Result α) (P : α → Prop) (h : x ⦃ P ⦄) :
    (do let r ← x; ok r) ⦃ P ⦄ := by
  step with h as ⟨r, hr⟩
  exact hr

/-- `Compress_1` of coefficient `p` of `a`, as a number. -/
def comp1 (a : List I16) (p : ℕ) : ℕ := (2 * (2 ^ 1 * (a[p]!).val.toNat) + 3329) / (2 * 3329) % 2

theorem to_message_inner_spec (self : mid.mlkem.Coeffs (Array I16 256#usize) mid.mlkem.Normal)
    (hself : ∀ p < 256, 0 ≤ (self.1.val[p]!).val ∧ (self.1.val[p]!).val < 3329)
    (i : Usize) (hi : i.val < 32) (byte : U8) (hbyte : byte.val = 0)
    (iter : core.ops.range.Range Usize) (he : iter.end.val = 8) (hs : iter.start.val = 0) :
    mid.mlkem.CoeffsArrayI16256Normal.to_message_bits_loop0_loop0 iter self i byte ⦃ r =>
      r.1 = self ∧ ∀ t, r.2.val.testBit t = (decide (t < 8) && (comp1 self.1.val (8 * i.val + t)).testBit 0) ⦄ := by
  unfold mid.mlkem.CoeffsArrayI16256Normal.to_message_bits_loop0_loop0
  apply range_loop' 8 (fun j (b : U8) =>
    ∀ t, b.val.testBit t = (decide (t < j) && (comp1 self.1.val (8 * i.val + t)).testBit 0)) _ _ _ iter byte he
    (by omega)
  · rw [hs, hbyte]
    intro t
    simp
  · intro it b he hs hinv
    simp only
    unfold mid.mlkem.CoeffsArrayI16256Normal.to_message_bits_loop0_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      obtain ⟨a, pd⟩ := self
      simp only at hself hinv ⊢
      step as ⟨i3, hi3⟩
      have hidx : i2.val = 8 * i.val + it.start.val := by rw [hi2, hi1]; omega
      have hget : a.val[8 * i.val + it.start.val]! = i3 := by
        rw [hi3]; simp only [hidx]; exact getElem!_pos a.val _ (by simp; omega)
      have hr := hself (8 * i.val + it.start.val) (by omega)
      rw [hget] at hr
      step with compress_1_spec as ⟨i4, hi4⟩
      step as ⟨i5, hi5, _⟩
      step as ⟨b1, hb1⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, fun t => ?_⟩
      have hi4' : i4.val = comp1 a.val (8 * i.val + it.start.val) := by rw [hi4, comp1, hget]
      have hc : comp1 a.val (8 * i.val + it.start.val) < 2 := Nat.mod_lt _ (by norm_num)
      have hpow : 2 ^ it.start.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hi5v : i5.val = comp1 a.val (8 * i.val + it.start.val) * 2 ^ it.start.val := by
        rw [hi5, hi4', Nat.shiftLeft_eq]
        exact Nat.mod_eq_of_lt (by
          simp [U8.size, U8.numBits]
          calc _ ≤ 1 * 2 ^ 7 := Nat.mul_le_mul (by omega) hpow
            _ < 256 := by norm_num)
      rw [hb1, UScalar.val_or, Nat.testBit_or, hinv t, hi5v, hst]
      rcases Nat.lt_or_ge t it.start.val with h | h
      · have : (comp1 a.val (8 * i.val + it.start.val) * 2 ^ it.start.val).testBit t = false := by
          rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp; omega
        simp [this, h, show t < it.start.val + 1 by omega]
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · subst h'
          have : (comp1 a.val (8 * i.val + it.start.val) * 2 ^ it.start.val).testBit it.start.val =
              (comp1 a.val (8 * i.val + it.start.val)).testBit 0 := by
            rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp
          simp [this]
        · have : (comp1 a.val (8 * i.val + it.start.val) * 2 ^ it.start.val).testBit t = false := by
            rw [Nat.mul_comm, Nat.testBit_two_pow_mul]
            simp only [ge_iff_le, h, decide_true, Bool.true_and]
            exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (t - it.start.val) := Nat.pow_le_pow_right (by norm_num) (by omega)))
          simp [this, show ¬ t < it.start.val by omega, show ¬ t < it.start.val + 1 by omega]
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val = 8 := by omega
      rw [this] at hinv
      exact ⟨trivial, hinv⟩

/-- `to_message_bits` is FIPS 203's `ByteEncode_1(Compress_1(f))`, of a
polynomial `f` with coefficients in `[0, q)`. -/
theorem to_message_bits_spec (self : mid.mlkem.Coeffs (Array I16 256#usize) mid.mlkem.Normal) (f : Polynomial)
    (hself : Holds 0 3328 256 self.1.val f) :
    mid.mlkem.CoeffsArrayI16256Normal.to_message_bits self ⦃ r =>
      toVec (32 * 1) r.val r.property = ByteEncode 1 (Polynomial.Compress 1 f (by omega)) (by omega) ⦄ := by
  have hrange : ∀ p < 256, 0 ≤ (self.1.val[p]!).val ∧ (self.1.val[p]!).val < 3329 := fun p hp => by
    obtain ⟨h0, h1, _⟩ := hself p hp
    exact ⟨h0, by omega⟩
  have final : ∀ a : Array U8 32#usize,
      (∀ i' < 32, ∀ t, (a.val[i']!).val.testBit t = (decide (t < 8) && (comp1 self.1.val (8 * i' + t)).testBit 0)) →
      toVec (32 * 1) a.val a.property = ByteEncode 1 (Polynomial.Compress 1 f (by omega)) (by omega) := by
    intro a h
    apply eq_of_bit
    intro k hk
    rw [bit_toVec, h (k / 8) (by omega), ByteEncode_bit _ _ k (by omega)]
    obtain ⟨h0, h1, hf⟩ := hself k (by omega)
    simp only [Nat.div_one, Nat.mod_one, show k % 8 < 8 by omega, decide_true, Bool.true_and,
      show 8 * (k / 8) + k % 8 = k by omega]
    unfold Polynomial.Compress
    rw [Vector.getElem!_map_eq _ _ _ (by omega), Compress_val, ← hf]
    have hval : ((((self.1.val[k]!).val : ℤ) : Zq)).val = (self.1.val[k]!).val.toNat := by
      rw [← Int.toNat_of_nonneg h0, Int.cast_natCast, ZMod.val_natCast, Int.toNat_natCast]
      exact Nat.mod_eq_of_lt (by rw [show q = 3329 from rfl]; omega)
    rw [hval, ZMod.val_natCast]
    simp [comp1, m, q]
  unfold mid.mlkem.CoeffsArrayI16256Normal.to_message_bits
  simp only
  apply spec_bind_ret
  · unfold mid.mlkem.CoeffsArrayI16256Normal.to_message_bits_loop0
    apply range_loop' 32 (fun j (s : mid.mlkem.Coeffs (Array I16 256#usize) mid.mlkem.Normal × Array U8 32#usize) =>
      s.1 = self ∧ ∀ i' < j, ∀ t,
        (s.2.val[i']!).val.testBit t = (decide (t < 8) && (comp1 self.1.val (8 * i' + t)).testBit 0))
      (fun a : Array U8 32#usize => toVec (32 * 1) a.val a.property =
        ByteEncode 1 (Polynomial.Compress 1 f (by omega)) (by omega)) _ _
      { start := 0#usize, «end» := 32#usize } (self, Array.repeat 32#usize 0#u8) rfl (by decide)
    · exact ⟨rfl, fun i' h => by simp at h⟩
    · intro it s he hs hinv
      obtain ⟨self', a⟩ := s
      obtain ⟨hm, hin⟩ := hinv
      simp only at hm hin
      subst hm
      simp only
      unfold mid.mlkem.CoeffsArrayI16256Normal.to_message_bits_loop0.body
      step as ⟨o', it1, ho, he1⟩
      split_ifs at ho with hlt
      · obtain ⟨rfl, hst⟩ := ho
        simp only
        step with to_message_inner_spec as ⟨self1, byte, hs1, hbyte⟩
        step as ⟨a1, ha1⟩
        refine ⟨by rw [he1]; exact he, hst, by omega, hs1, fun i' hi' t => ?_⟩
        rw [ha1, Array.set_val_eq]
        by_cases hp : i' = it.start.val
        · subst hp
          rw [getElem!_set_self _ _ _ (by simp; omega)]
          exact hbyte t
        · rw [getElem!_set_ne _ _ _ _ (Ne.symm hp)]
          exact hin i' (by omega) t
      · obtain ⟨rfl, hst⟩ := ho
        simp only [WP.spec_ok]
        have : it.start.val = 32 := by omega
        rw [this] at hin
        exact final _ hin

end MlKemCoding

end rind.x86_64
