import Rind.X86_64.RsaBytes
import Rind.X86_64.VgRsa
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's public operation on AVX-512 IFMA

On a CPU whose AVX-512 IFMA check passes, `RsaPublicKey::public_op` runs
pyca/verified-garbage's public operation for 2048-, 3072-, and 4096-bit
moduli with `e = 65537`, through `public_op_ifma`, which `VgRsa.lean`'s
axiom states. This proves `public_op_ifma`'s glue: the key's precomputed
words, the exponent's and the input's bytes, and the result's words.
-/

namespace rind.x86_64

/-! ## `VG.Spec.Rsa`'s encodings, as rind's -/

theorem vg_os2ip_map_bv (l : List U8) : VG.Spec.Rsa.os2ip (l.map (·.bv)) = beNat l :=
  os2ip_bv l

theorem vg_i2osp_length (x k : Nat) : (VG.Spec.Rsa.i2osp x k).length = k := by
  simp [VG.Spec.Rsa.i2osp]

theorem vg_i2osp_succ (x k : Nat) :
    VG.Spec.Rsa.i2osp x (k + 1) = VG.Spec.Rsa.i2osp (x / 256) k ++ [BitVec.ofNat 8 x] := by
  simp only [VG.Spec.Rsa.i2osp, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
    congr 3
    omega
  · simp

theorem vg_os2ip_append_one (l : List VG.Byte) (b : VG.Byte) :
    VG.Spec.Rsa.os2ip (l ++ [b]) = 256 * VG.Spec.Rsa.os2ip l + b.toNat := by
  simp [VG.Spec.Rsa.os2ip, List.foldl_append]

/-- I2OSP then OS2IP gives back a number below `256^k`. -/
theorem vg_os2ip_i2osp (x k : Nat) (h : x < 256 ^ k) : VG.Spec.Rsa.os2ip (VG.Spec.Rsa.i2osp x k) = x := by
  induction k generalizing x with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    rw [vg_i2osp_succ, vg_os2ip_append_one, ih _ (by rw [pow_succ] at h; omega)]
    simp only [BitVec.toNat_ofNat]
    omega

theorem vg_powMod (a e m : Nat) : VG.Spec.Rsa.powMod a e m = a ^ e % m := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [VG.Spec.Rsa.powMod]
    split
    · subst_vars; simp
    · rename_i he
      simp only
      rw [ih _ (by omega)]
      have hsplit : a ^ e = a ^ (e / 2) * a ^ (e / 2) * a ^ (e % 2) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      split
      · rename_i h2
        rw [hsplit, h2, pow_zero, mul_one, ← Nat.mul_mod]
      · rename_i h2
        have h1 : e % 2 = 1 := by omega
        rw [hsplit, h1, pow_one, Nat.mul_mod (a ^ (e / 2) * a ^ (e / 2)), Nat.mul_mod (a ^ (e / 2))]
        simp [Nat.mul_mod]

/-- `toWords` reads back the words of `wordsNat`. -/
theorem vg_toWords_wordsNat (l : List U64) : VG.Spec.Rsa.toWords (wordsNat l) l.length = l.map (·.bv) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [VG.Spec.Rsa.toWords, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.cons.injEq] at ih ⊢
    refine ⟨?_, ?_⟩
    · rw [wordsNat_cons]; apply BitVec.eq_of_toNat_eq
      simp [UScalar.bv_toNat, Nat.add_mul_mod_self_left]
    · rw [← ih]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, wordsNat_cons]
      congr 1
      rw [show 64 * (i + 1) = 64 + 64 * i by ring, pow_add, ← Nat.div_div_eq_div_mul]
      congr 1
      rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by simpa using a.hBounds), Nat.zero_add]

/-! ## `to_bytes_fixed` and `from_secret_bytes` -/

/-- Word `q` of `l` is `wordsNat l`'s digit `q` in base `2^64`. -/
theorem word_val (l : List U64) (q : Nat) (hq : q < l.length) :
    l[q]!.val = wordsNat l / 2 ^ (64 * q) % 2 ^ 64 := by
  have h := wordsNat_take_drop l q
  have hlen : (l.take q).length = q := by simp; omega
  rw [hlen, List.drop_eq_getElem_cons hq, wordsNat_cons] at h
  have hA := wordsNat_lt' (l.take q)
  rw [hlen] at hA
  rw [h, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simpa using l[q].hBounds)]
  simp [getElem!_pos l q hq]

/-- Byte `r` of digit `q` in base `2^64` is digit `8q + r` in base 256. -/
theorem byte_of_word (X q r : Nat) (hr : r < 8) :
    X / 2 ^ (64 * q) % 2 ^ 64 / 2 ^ (8 * r) % 256 = X / 256 ^ (8 * q + r) % 256 := by
  rw [show (2 : Nat) ^ 64 = 2 ^ (8 * r) * 2 ^ (64 - 8 * r) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)),
    Nat.div_div_eq_div_mul, ← pow_add, show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]
  congr 3
  ring

/-- `to_bytes_fixed`'s loop, with the low `i` bytes written at the back of
`out`. -/
theorem to_bytes_fixed_loop_spec {N : Usize} (self : low.posint.PosInt N) (out0 : Slice U8) (len : Usize)
    (hN : len.val ≤ 8 * N.val) (iter : core.ops.range.Range Usize)
    (hend : iter.end = len) (hstart : iter.start.val ≤ len.val) (out : Slice U8)
    (hinv : out.length = len.val ∧ out.val.take (len.val - iter.start.val) = out0.val.take (len.val - iter.start.val) ∧
      beNat (out.val.drop (len.val - iter.start.val)) = wordsNat self.words.val % 256 ^ iter.start.val) :
    low.posint.PosInt.to_bytes_fixed_loop iter self out len ⦃ o =>
      o.length = len.val ∧ beNat o.val = wordsNat self.words.val % 256 ^ len.val ⦄ := by
  unfold low.posint.PosInt.to_bytes_fixed_loop
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x : core.ops.range.Range Usize × low.posint.PosInt N × Slice U8 => x.1.end = len ∧
      x.1.start.val ≤ len.val ∧ x.2.1 = self ∧ x.2.2.length = len.val ∧
      x.2.2.val.take (len.val - x.1.start.val) = out0.val.take (len.val - x.1.start.val) ∧
      beNat (x.2.2.val.drop (len.val - x.1.start.val)) = wordsNat self.words.val % 256 ^ x.1.start.val)
  · rintro ⟨it, s0, o⟩ ⟨he, hs, rfl, hol, hot, hov⟩
    simp only at he hs hol hot hov
    unfold low.posint.PosInt.to_bytes_fixed_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have hev : it.end.val = len.val := by rw [he]
      have : it.start.val = len.val := by
        split at hop
        · simp at hop
        · omega
      rw [this, Nat.sub_self, List.drop_zero] at hov
      simp only [WP.spec_ok]
      exact ⟨hol, hov⟩
    | some i =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      have hev : it.end.val = len.val := by rw [he]
      have hwl : s0.words.val.length = N.val := by simp
      step as ⟨i1, hi1⟩
      have hi1N : i1 < N := by scalar_tac
      rw [ite_eq_left hi1N]
      step*
      have hj : i6.val = len.val - (it.start.val + 1) := by omega
      have hoL : o.val.length = len.val := hol
      have hsv : s.val = o.val.set i6.val i7 := by rw [s_post]; simp
      have hbyte : i7.val = wordsNat s0.words.val / 256 ^ it.start.val % 256 := by
        rw [i7_post, UScalar.cast_val_eq, i4_post, x_post, Nat.shiftRight_eq_div_pow, i3_post, i2_post]
        have hw := word_val s0.words.val i1.val (by scalar_tac)
        rw [getElem!_pos _ _ (by scalar_tac)] at hw
        rw [hw, hi1]
        simp only [UScalarTy.U8_numBits_eq]
        rw [show (2 : Nat) ^ 8 = 256 by norm_num, byte_of_word _ _ _ (Nat.mod_lt _ (by norm_num)),
          Nat.div_add_mod]
      have hdrop : (o.val.set i6.val i7).drop i6.val = i7 :: o.val.drop (i6.val + 1) := by
        rw [List.drop_set, ite_eq_right (lt_irrefl _), Nat.sub_self, List.drop_eq_getElem_cons (by omega)]
        rfl
      have h1e : iter1.end.val = it.end.val := by rw [hend1]
      refine ⟨by rw [hend1, he], by omega, ?_, ?_, ?_, by omega⟩
      · show s.val.length = _
        rw [hsv, List.length_set, hoL]
      · rw [hst, ← hj, hsv, List.take_set_of_le (le_refl _)]
        have := congrArg (List.take i6.val) hot
        simp only [List.take_take] at this
        rwa [Nat.min_eq_left (by omega)] at this
      · rw [hst, ← hj, hsv, hdrop, show i7 :: o.val.drop (i6.val + 1) = [i7] ++ o.val.drop (i6.val + 1) from rfl,
          beNat_append, show i6.val + 1 = len.val - it.start.val by omega, hov, List.length_drop, hoL,
          show len.val - (len.val - it.start.val) = it.start.val by omega, Nat.mod_pow_succ]
        simp only [beNat, leNat, List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
          List.map_nil, Nat.ofDigits_singleton]
        rw [hbyte]
        ring
  · exact ⟨hend, hstart, rfl, hinv⟩


/-- `to_bytes_fixed` writes the low `out.length` bytes of the value,
big-endian, for an `out` no wider than the value's words. -/
theorem to_bytes_fixed_spec {N : Usize} (self : low.posint.PosInt N) (out : Slice U8)
    (hN : out.length ≤ 8 * N.val) :
    low.posint.PosInt.to_bytes_fixed self out ⦃ o =>
      o.length = out.length ∧ beNat o.val = wordsNat self.words.val % 256 ^ out.length ⦄ := by
  unfold low.posint.PosInt.to_bytes_fixed
  exact to_bytes_fixed_loop_spec self out out.len hN _ rfl (by simp) out
    ⟨rfl, rfl, by simp [beNat, leNat, Nat.mod_one]⟩

/-- Setting word `q` adds its change, at its place. -/
theorem wordsNat_set (l : List U64) (q : Nat) (v : U64) (hq : q < l.length) :
    wordsNat (l.set q v) + l[q].val * 2 ^ (64 * q) = wordsNat l + v.val * 2 ^ (64 * q) := by
  have hs : l.set q v = l.take q ++ v :: l.drop (q + 1) := by
    rw [List.set_eq_take_append_cons_drop, ite_eq_left hq]
  have hl : l = l.take q ++ l[q] :: l.drop (q + 1) := by
    conv_lhs => rw [← List.take_append_drop q l, List.drop_eq_getElem_cons hq]
  have hlen : (l.take q).length = q := by simp; omega
  conv_rhs => rw [hl]
  rw [hs, wordsNat_append, wordsNat_append, wordsNat_cons, wordsNat_cons, hlen]
  ring

set_option maxHeartbeats 1000000 in
/-- `from_secret_bytes`'s loop, with the low `i` bytes read: the words hold
the number they encode. -/
theorem from_secret_bytes_loop2_spec {N : Usize} (bytes : Slice U8) (len : Usize) (hlen : bytes.length = len.val)
    (hN : len.val ≤ 8 * N.val) (iter : core.ops.range.Range Usize) (hend : iter.end = len)
    (hstart : iter.start.val ≤ len.val) (r : low.posint.PosInt N)
    (hinv : wordsNat r.words.val = beNat (bytes.val.drop (len.val - iter.start.val))) :
    low.posint.PosInt.from_secret_bytes_loop2 iter bytes r len ⦃ o =>
      o.used = r.used ∧ wordsNat o.words.val = beNat bytes.val ⦄ := by
  unfold low.posint.PosInt.from_secret_bytes_loop2
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x : core.ops.range.Range Usize × low.posint.PosInt N => x.1.end = len ∧
      x.1.start.val ≤ len.val ∧ x.2.used = r.used ∧
      wordsNat x.2.words.val = beNat (bytes.val.drop (len.val - x.1.start.val)))
  · rintro ⟨it, r1⟩ ⟨he, hs, hu, hv⟩
    simp only at he hs hu hv
    have hev : it.end.val = len.val := by rw [he]
    unfold low.posint.PosInt.from_secret_bytes_loop2.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have : it.start.val = len.val := by
        split at hop
        · simp at hop
        · omega
      rw [this, Nat.sub_self, List.drop_zero] at hv
      simp only [WP.spec_ok]
      exact ⟨hu, hv⟩
    | some i =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      have hwl : r1.words.val.length = N.val := by simp
      have h1e : iter1.end.val = it.end.val := by rw [hend1]
      step*
      have hbl : bytes.val.length = len.val := hlen
      set st := it.start.val with hstv
      set V := wordsNat r1.words.val
      have hVlt : V < 2 ^ (64 * (st / 8) + 8 * (st % 8)) := by
        have := beNat_lt (bytes.val.drop (len.val - st))
        rw [List.length_drop, hbl, show len.val - (len.val - st) = st by omega,
          show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] at this
        rw [show 64 * (st / 8) + 8 * (st % 8) = 8 * st by omega, hv]; exact this
      have hblt : bytes.val[i2.val].val < 2 ^ 8 := by have := (bytes.val[i2.val]).hBounds; simpa using this
      have hb : i4.val = bytes.val[i2.val].val := by
        rw [i4_post, i3_post, UScalar.cast_val_eq]
        apply Nat.mod_eq_of_lt
        have := hblt
        simp only [UScalarTy.U64_numBits_eq]
        omega
      have hi7 : i7.val = bytes.val[i2.val].val * 2 ^ (8 * (st % 8)) := by
        rw [i7_post, Nat.shiftLeft_eq, hb, i6_post, i5_post]
        apply Nat.mod_eq_of_lt
        calc bytes.val[i2.val].val * 2 ^ (8 * (st % 8)) < 2 ^ 8 * 2 ^ (8 * (st % 8)) :=
              Nat.mul_lt_mul_of_pos_right hblt (by positivity)
          _ = 2 ^ (8 + 8 * (st % 8)) := by rw [← pow_add]
          _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ U64.size := by simp [U64.size, U64.numBits]
      have hi9 : i9.val = V / 2 ^ (64 * (st / 8)) := by
        have hw := word_val r1.words.val i8.val (by scalar_tac)
        rw [getElem!_pos _ _ (by scalar_tac)] at hw
        rw [i9_post, hw, i8_post]
        apply Nat.mod_eq_of_lt
        calc V / 2 ^ (64 * (st / 8)) < 2 ^ (8 * (st % 8)) := by
              rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; rwa [Nat.add_comm]
          _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hi9lt : i9.val < 2 ^ (8 * (st % 8)) := by
        rw [hi9, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; rwa [Nat.add_comm]
      have hi10 : i10.val = i9.val + bytes.val[i2.val].val * 2 ^ (8 * (st % 8)) := by
        rw [i10_post, UScalar.val_or, hi7, ← Nat.shiftLeft_eq, Nat.lor_comm,
          ← Nat.shiftLeft_add_eq_or_of_lt hi9lt, Nat.add_comm]
      have hset := wordsNat_set r1.words.val i8.val i10 (by scalar_tac)
      have ha : wordsNat a.val = V + bytes.val[i2.val].val * 256 ^ st := by
        rw [a_post]
        simp only [Std.Array.set_val_eq]
        have h9 : (r1.words.val)[i8.val]'(by scalar_tac) = i9 := by rw [i9_post]
        rw [h9, hi10, i8_post] at hset
        have hp : (256 : Nat) ^ st = 2 ^ (8 * (st % 8)) * 2 ^ (64 * (st / 8)) := by
          rw [← pow_add, show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]; congr 1; omega
        rw [hp, ← Nat.mul_assoc]
        rw [Nat.add_mul] at hset
        rw [i8_post]
        show _ = wordsNat r1.words.val + _
        omega
      refine ⟨by rw [hend1, he], by omega, hu, ?_, by omega⟩
      have hd : bytes.val.drop i2.val = bytes.val[i2.val] :: bytes.val.drop (i2.val + 1) :=
        List.drop_eq_getElem_cons _
      have hdrop : bytes.val.drop (len.val - iter1.start.val) =
          [bytes.val[i2.val]] ++ bytes.val.drop (len.val - st) := by
        rw [show len.val - iter1.start.val = i2.val by omega, hd, show i2.val + 1 = len.val - st by omega]
        rfl
      have hdl : (bytes.val.drop (len.val - st)).length = st := by
        rw [List.length_drop, hbl]; omega
      rw [ha, hv, hdrop, beNat_append, hdl]
      simp only [beNat, leNat, List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
        List.map_nil, Nat.ofDigits_singleton]
      ring
  · exact ⟨hend, hstart, rfl, hinv⟩

/-- `from_secret_bytes` reads big-endian bytes no wider than its words as the
number they encode, in `⌈len / 8⌉` words. -/
theorem from_secret_bytes_spec (bytes : Slice U8) (hN : bytes.length ≤ 1024) :
    low.posint.PosInt.from_secret_bytes 128#usize bytes ⦃ r => ∃ p, r = .Ok p ∧
      p.used.val = (bytes.length + 7) / 8 ∧ wordsNat p.words.val = beNat bytes.val ⦄ := by
  unfold low.posint.PosInt.from_secret_bytes low.posint.PosInt.zero
  step as ⟨i1, hi1⟩
  have hbl : bytes.length = bytes.val.length := rfl
  have hle : ¬ (Slice.len bytes > i1) := by
    intro h; have : (Slice.len bytes).val > i1.val := h; simp at this; omega
  simp only [hle, ↓reduceIte]
  step with from_secret_bytes_loop2_spec bytes (Slice.len bytes) (by simp) (by simp; omega)
    { start := 0#usize, «end» := Slice.len bytes } rfl (by simp)
    { words := Array.repeat 128#usize 0#u64, used := 0#usize }
    (by rw [Array.repeat_val, wordsNat_replicate_zero]; simp [beNat, leNat]) as ⟨r1, hu, hv⟩
  unfold core.num.Usize.div_ceil
  simp only [show ¬ (8#usize).val = 0 by decide, _root_.dite_false, bind_ok, WP.spec_ok]
  refine ⟨_, rfl, ?_, hv⟩
  rw [UScalar.ofNatCore_val_eq]
  simp

theorem len_bits_spec (p : RsaInt) (hu : p.used.val ≤ 128) :
    low.posint.PosInt.len_bits p ⦃ r => r.val = (wordsNat (lowWords p p.used)).size ⦄ := by
  unfold low.posint.PosInt.len_bits low.posint.PosInt.as_words
  step*
  rw [r_post, s_post]
  simp [lowWords, List.slice, Array.val_to_slice]

/-- The modulus's length in bytes is RFC 8017's `k`. -/
theorem modulus_len_bytes_spec (key : mid.rsa_pub.RsaPublicKey) (hinv : PubKeyInv key) :
    mid.rsa_pub.RsaPublicKey.modulus_len_bytes key ⦃ r =>
      r.val = octetLen (wordsNat (lowWords key.n key.n.used)) ⦄ := by
  obtain ⟨-, hk, -, -, -, -, -, -, hs2, -⟩ := hinv
  unfold mid.rsa_pub.RsaPublicKey.modulus_len_bytes low.posint.PosInt.len_bytes
  step with len_bits_spec key.n hk as ⟨b, hb⟩
  step*
  rw [r_post, i1_post, core.num.Usize.wrapping_add_val_eq, hb, octetLen]
  congr 1
  rw [Nat.mod_eq_of_lt]
  · rfl
  rw [← hb] at hs2 ⊢
  have : (7#usize).val = 7 := rfl
  have : 2 ^ 32 ≤ UScalar.size UScalarTy.Usize := by
    simp only [UScalar.size, UScalarTy.numBits]
    cases System.Platform.numBits_eq <;> simp_all
  omega

/-- `k` bytes hold any number below the modulus. -/
theorem lt_octetLen (N x : Nat) (hx : x < N) : x < 256 ^ octetLen N := by
  calc x < N := hx
    _ < 2 ^ N.size := Nat.lt_size_self N
    _ ≤ 2 ^ (8 * octetLen N) := Nat.pow_le_pow_right (by norm_num) (by unfold octetLen; omega)
    _ = 256 ^ octetLen N := by rw [pow_mul]; norm_num

/-- `RsaIfma::check`'s CPU check returns, whichever features it finds. -/
def IfmaCheckReturns : Prop := ∃ t, low.x86_64.cpu.HaveAvx512ForRsa.check = ok t

/-- `RsaIfma::check` returns a token only for the exponent 65537 and a
2048-, 3072-, or 4096-bit modulus, on a CPU whose check returns. -/
theorem rsa_ifma_check_spec (key : mid.rsa_pub.RsaPublicKey) (hinv : PubKeyInv key)
    (hcpu : IfmaCheckReturns) :
    low.x86_64.rsa_ifma.RsaIfma.check key.n key.e ⦃ o => o.isSome → key.e.val = 65537 ∧
      (octetLen (wordsNat (lowWords key.n key.n.used)) = 256 ∨
        octetLen (wordsNat (lowWords key.n key.n.used)) = 384 ∨
        octetLen (wordsNat (lowWords key.n key.n.used)) = 512) ⦄ := by
  obtain ⟨t, ht⟩ := hcpu
  have hlen := modulus_len_bytes_spec key hinv
  unfold mid.rsa_pub.RsaPublicKey.modulus_len_bytes at hlen
  unfold low.x86_64.rsa_ifma.RsaIfma.check
  split
  · simp
  · rename_i he
    have he' : key.e.val = 65537 := by simpa using he
    step with hlen as ⟨i, hi⟩
    rw [ht]
    split <;> (cases t <;> simp_all [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual])

/-- `public_op_ifma` raises `c`, below the modulus, to the exponent 65537
modulo a 2048-, 3072-, or 4096-bit modulus by pyca/verified-garbage's
public operation. -/
theorem public_op_ifma_spec (key : mid.rsa_pub.RsaPublicKey) (hinv : PubKeyInv key)
    (ifma : low.x86_64.rsa_ifma.RsaIfma) (he : key.e.val = 65537)
    (hk : octetLen (wordsNat (lowWords key.n key.n.used)) = 256 ∨
      octetLen (wordsNat (lowWords key.n key.n.used)) = 384 ∨
      octetLen (wordsNat (lowWords key.n key.n.used)) = 512)
    (c : RsaInt) (hc : wordsNat c.words.val < wordsNat (lowWords key.n key.n.used)) :
    mid.rsa_pub.RsaPublicKey.public_op_ifma key ifma c ⦃ r => ∃ m, r = .Ok m ∧
      m.used = key.n.used ∧
      wordsNat (lowWords m key.n.used) =
        wordsNat c.words.val ^ key.e.val % wordsNat (lowWords key.n key.n.used) ⦄ := by
  have hinv' := hinv
  obtain ⟨hk2, hku, hodd, -, hmont, -, -, hs1, hs2, htop⟩ := hinv'
  unfold mid.rsa_pub.RsaPublicKey.public_op_ifma low.posint.PosInt.as_words
    low.posint.PosInt.as_words_with_len_of
  step with modulus_len_bytes_spec key hinv as ⟨k, hkv⟩
  have hkle : k.val ≤ 512 := by rcases hk with h | h | h <;> omega
  have heq : key.e = 65537#u64 := by scalar_tac
  have hlz : core.num.U64.leading_zeros key.e = 47#u32 := by rw [heq]; decide
  have hbe : key.e.bv.toBEBytes = [0#8, 0#8, 0#8, 0#8, 0#8, 1#8, 0#8, 1#8] := by
    rw [heq]; simp [BitVec.toBEBytes, BitVec.toLEBytes]
  rw [hlz]
  step*
  case h => simp only [Slice.length] at *; scalar_tac
  simp only [lift, bind_ok]
  step*
  step with to_bytes_fixed_spec c s6 (by scalar_tac) as ⟨s7, hs7l, hs7v⟩
  -- The modulus `N` of `w` words and `k` bytes.
  generalize hN : wordsNat (lowWords key.n key.n.used) = N at *
  have hNw : N < 2 ^ (64 * key.n.used.val) := by
    have := wordsNat_lt' (lowWords key.n key.n.used); rwa [lowWords_length _ hku, hN] at this
  have hsz1 := Nat.size_le.mpr hNw
  have hsz2 := Nat.lt_size.mpr htop
  have hw : (k.val + 7) / 8 = key.n.used.val := by rw [hkv, octetLen]; omega
  have hNk : N < 256 ^ k.val := by
    rw [hkv]
    calc N < 2 ^ N.size := Nat.lt_size_self N
      _ ≤ 2 ^ (8 * octetLen N) := Nat.pow_le_pow_right (by norm_num) (by unfold octetLen; omega)
      _ = 256 ^ octetLen N := by rw [pow_mul]; norm_num
  have hCk : wordsNat c.words.val < 256 ^ k.val := lt_trans hc hNk
  have he1v : e1.val.map (·.bv) = [1#8, 0#8, 1#8] := by
    have hi3 : i3.val = 5 := by rw [i3_post]; scalar_tac
    rw [e1_post, Array.val_to_slice, e_post, hbe, hi3]; rfl
  have he1l : e1.length = 3 := by
    have := congrArg List.length he1v; simpa using this
  step as ⟨s8, index_mut_back3, s8_post, s8_post1, s8_post2⟩
  step as ⟨s9, s9_post, s9_post1⟩
  step as ⟨s10, s10_post, s10_post1⟩
  have hsv : s.val = lowWords key.n key.n.used := by
    rw [s_post]; simp [lowWords, List.slice, Array.val_to_slice]
  have hs4v : s4.val = lowWords key.montifier key.n.used := by
    rw [s4_post]; simp [lowWords, List.slice, Array.val_to_slice]
  have hsl : (Slice.len s).val = key.n.used.val := by rw [Slice.len_val]; exact s_post1
  have hs9 : s9.val = lowWords key.n key.n.used ++ lowWords key.montifier key.n.used := by
    have hsl' : s.val.length = key.n.used.val := s_post1
    have hs4l : s4.val.length = key.n.used.val := s4_post1
    have hr : (Array.repeat 256#usize 0#u64).val.length = 256 := by
      rw [Array.repeat_val, List.length_replicate]; rfl
    have h1 := take_setSlice! (Array.repeat 256#usize 0#u64).val s.val 0 (by omega)
    rw [List.take_zero, List.nil_append, zero_add, hsl'] at h1
    have hl0 : ((Array.repeat 256#usize 0#u64).val.setSlice! 0 s.val).length = 256 := by
      rw [List.length_setSlice!, hr]
    have h2 := take_setSlice! ((Array.repeat 256#usize 0#u64).val.setSlice! 0 s.val) s4.val key.n.used.val
      (by omega)
    rw [hs4l, h1] at h2
    rw [s9_post, Array.val_to_slice, s3_post2, s1_post2, s5_post, s2_post, i_post, hsl, List.slice,
      Nat.sub_zero, List.drop_zero, two_mul, h2, hsv, hs4v]
  have hs7l' : s7.val.length = k.val := by rw [← s6_post1]; exact hs7l
  have hs10 : s10.val = s7.val := by
    have hr : (Array.repeat 1024#usize 0#u8).val.length = 1024 := by
      rw [Array.repeat_val, List.length_replicate]; rfl
    have := take_setSlice! (Array.repeat 1024#usize 0#u8).val s7.val 0 (by omega)
    rw [List.take_zero, List.nil_append, zero_add] at this
    rw [s10_post, Array.val_to_slice, s6_post2, List.slice, Nat.sub_zero, List.drop_zero, ← hs7l', this]
  have hC : beNat s10.val = wordsNat c.words.val := by
    rw [hs10, hs7v, s6_post1, Nat.mod_eq_of_lt hCk]
  -- pyca/verified-garbage's precondition, and its result.
  have hk256 : 256 ≤ k.val := by rcases hk with h | h | h <;> omega
  have hk8 : VG.Spec.Rsa.lenValid s8.length := by
    unfold VG.Spec.Rsa.lenValid; rw [s8_post1]; omega
  have hpre9 : s9.length = VG.Spec.Rsa.precomputedWords s8.length := by
    unfold VG.Spec.Rsa.precomputedWords VG.Spec.Rsa.modulusWords
    rw [s9_post1, s8_post1, i_post, hsl]; omega
  have hmv : VG.Spec.Rsa.modulusValid N k.val = true := by
    simp only [VG.Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨⟨hodd, Nat.lt_size.mp (by omega)⟩, Nat.size_le.mp hs2⟩, ?_⟩
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← pow_mul]
    exact Nat.lt_size.mp (by rw [hkv]; unfold octetLen; omega)
  have hpc : VG.Spec.Rsa.publicPrecompute (VG.Spec.Rsa.i2osp N k.val) = some (s9.val.map (·.bv)) := by
    unfold VG.Spec.Rsa.publicPrecompute
    simp only [vg_os2ip_i2osp N k.val hNk, vg_i2osp_length, hmv, ↓reduceIte, Option.some.injEq]
    rw [show VG.Spec.Rsa.modulusWords k.val = key.n.used.val by unfold VG.Spec.Rsa.modulusWords; omega,
      hs9, List.map_append, ← vg_toWords_wordsNat (lowWords key.n key.n.used),
      ← vg_toWords_wordsNat (lowWords key.montifier key.n.used), lowWords_length _ hku,
      lowWords_length _ hku, hN, hmont]
  have hpo : VG.Spec.Rsa.publicOpChecked (VG.Spec.Rsa.i2osp N k.val) (e1.val.map (·.bv))
      (s10.val.map (·.bv)) =
      some (VG.Spec.Rsa.i2osp (wordsNat c.words.val ^ 65537 % N) k.val) := by
    have he65537 : VG.Spec.Rsa.os2ip [1#8, 0#8, 1#8] = 65537 := by decide
    simp only [VG.Spec.Rsa.publicOpChecked, VG.Spec.Rsa.publicOp, VG.Spec.Rsa.encrypt, he1v, he65537,
      show VG.Spec.Rsa.exponentValid 65537 = true by decide, ↓reduceIte, vg_os2ip_i2osp N k.val hNk,
      vg_i2osp_length, hmv, vg_os2ip_map_bv, hC, hc, Option.map_some, vg_powMod]
  step with rsa_ifma_public_spec ifma s8 s9 e1 s10 hk8 hpre9 (by rw [s10_post1, s8_post1])
    (by omega) (by rw [he1l, s8_post1]; omega) as ⟨b, s11, hW⟩
  have hW' := hW (VG.Spec.Rsa.i2osp N k.val) (by rw [vg_i2osp_length, s8_post1]) hpc
  rw [hpo] at hW'
  obtain ⟨rfl, hs11⟩ := hW'
  simp only [↓reduceIte]
  have hs11l : s11.val.length = k.val := by
    have := congrArg List.length hs11; rwa [List.length_map, vg_i2osp_length] at this
  have hR : wordsNat c.words.val ^ 65537 % N < N := Nat.mod_lt _ (by omega)
  step as ⟨s12, s12_post, s12_post1⟩
  have hs12 : s12.val = s11.val := by
    have hr : (Array.repeat 1024#usize 0#u8).val.length = 1024 := by
      rw [Array.repeat_val, List.length_replicate]; rfl
    have := take_setSlice! (Array.repeat 1024#usize 0#u8).val s11.val 0 (by omega)
    rw [List.take_zero, List.nil_append, zero_add] at this
    rw [s12_post, Array.val_to_slice, s8_post2, List.slice, Nat.sub_zero, List.drop_zero, ← hs11l, this]
  have hs12v : beNat s12.val = wordsNat c.words.val ^ 65537 % N := by
    rw [hs12, ← vg_os2ip_map_bv, hs11, vg_os2ip_i2osp _ _ (lt_trans hR hNk)]
  apply WP.spec_mono (from_secret_bytes_spec s12 (by rw [s12_post1]; omega))
  rintro r ⟨m, rfl, hmu, hmv'⟩
  refine ⟨m, rfl, ?_, ?_⟩
  · rw [UScalar.eq_equiv, hmu, s12_post1, hw]
  · rw [lowWords, wordsNat_take_mod, hmv', hs12v, he, Nat.mod_eq_of_lt (lt_trans hR hNw)]

/-- RSAVP1: `public_op` raises `c` to the public exponent modulo the
modulus, or refuses a `c` not below it. -/
theorem public_op_spec (key : mid.rsa_pub.RsaPublicKey) (hinv : PubKeyInv key)
    (hP : MontProducts key.n.used.val) (hifma : IfmaCheckReturns) (c : RsaInt) (hcu : c.used.val ≤ 128)
    (hcz : wordsNat (c.words.val.drop c.used.val) = 0) :
    mid.rsa_pub.RsaPublicKey.public_op key c ⦃ r => match r with
      | .Ok m => wordsNat (lowWords c c.used) < wordsNat (lowWords key.n key.n.used) ∧
          m.used = key.n.used ∧
          wordsNat (lowWords m key.n.used) =
            wordsNat (lowWords c c.used) ^ key.e.val % wordsNat (lowWords key.n key.n.used)
      | .Err _ => wordsNat (lowWords key.n key.n.used) ≤ wordsNat (lowWords c c.used) ⦄ := by
  have hinv' := hinv
  obtain ⟨hk2, hk, hodd, hn0, hmont, he, he3, _⟩ := hinv'
  unfold mid.rsa_pub.RsaPublicKey.public_op
  step with less_than_spec c key.n hcu hk as ⟨b, hb⟩
  unfold low.ct.into_public
  simp only [bind_ok]
  split
  · rename_i hlt
    rw [hb] at hlt
    have hlt : wordsNat (lowWords c c.used) < wordsNat (lowWords key.n key.n.used) := by simpa using hlt
    have hNR : wordsNat (lowWords key.n key.n.used) < 2 ^ (64 * key.n.used.val) := by
      have := wordsNat_lt' (lowWords key.n key.n.used); rwa [lowWords_length _ hk] at this
    have hR : Nat.Coprime (2 ^ (64 * key.n.used.val)) (wordsNat (lowWords key.n key.n.used)) :=
      coprime_two_pow_odd hodd _
    -- `expand` keeps `c`'s value, which its words above `used` hold none of.
    unfold low.posint.PosInt.expand
    simp only [bind_ok]
    have hcw : wordsNat c.words.val = wordsNat (lowWords c c.used) := by
      rw [wordsNat_take_drop c.words.val c.used, hcz, Nat.mul_zero, Nat.add_zero]; rfl
    have hc1 : wordsNat (lowWords ({ c with used := key.n.used } : RsaInt) key.n.used) =
        wordsNat (lowWords c c.used) := by
      simp only [lowWords]; rw [wordsNat_take_mod, hcw]
      exact Nat.mod_eq_of_lt (lt_trans hlt hNR)
    -- With the exponent 65537 and a 2048-, 3072-, or 4096-bit modulus, on a
    -- CPU with AVX-512 IFMA, pyca/verified-garbage's public operation.
    step with rsa_ifma_check_spec key hinv hifma as ⟨o, ho⟩
    cases o
    case some ifma =>
      obtain ⟨he', hk'⟩ := ho rfl
      apply WP.spec_mono (public_op_ifma_spec key hinv ifma he' hk' _ (by rw [hcw]; exact hlt))
      rintro r ⟨m, rfl, hmu, hmv⟩
      exact ⟨hlt, hmu, by rw [hmv, hcw]⟩
    -- Otherwise, square-and-multiply.
    -- `to_montgomery` takes `c` to `c·R`.
    unfold low.posint.PosInt.to_montgomery low.posint.PosInt.mont_mul low.posint.PosInt.zero
    step with mont_neg_inverse_spec key.n (by omega) hk hodd as ⟨n0', hn0'⟩
    have hmlt : wordsNat (lowWords key.montifier key.n.used) < wordsNat (lowWords key.n key.n.used) := by
      rw [hmont]; exact Nat.mod_lt _ (by omega)
    step with mont_mul_into_spec _ key.montifier _ key.n n0' hP hk
      (mont_args_of _ _ key.n n0' hk hk2 hodd hn0' (by rw [hc1]; exact hlt) hmlt) as ⟨cm, hcmu, hcmr, _⟩
    obtain ⟨hcmN, hcmv⟩ := mont_result_of hcmr
    rw [lowWords_length _ hk, hc1, hmont] at hcmv
    have hcmC : wordsNat (lowWords cm key.n.used) ≡
        wordsNat (lowWords c c.used) * 2 ^ (64 * key.n.used.val) [MOD wordsNat (lowWords key.n key.n.used)] := by
      apply mont_cancel hR
      refine hcmv.trans ?_
      unfold Nat.ModEq
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      congr 1; ring
    step as ⟨a, ha⟩
    subst ha
    step with ilog2_spec key.e (by omega) as ⟨L, hL⟩
    step as ⟨iter, hiter⟩
    have hL1 : 1 ≤ L.val := by
      rw [hL]; exact Nat.le_log2 (by omega) |>.mpr (by omega)
    have hL64 : L.val < 64 := by
      rw [hL]; exact (Nat.log2_lt (by omega)).mpr (by have := key.e.hBounds; simpa using this)
    step with public_op_loop_spec key.n key.e key.n0 _ a hP hk hk2 hodd hn0 he (by rw [hc1]; exact hlt)
      hcmN (by rw [hc1]; exact hcmC) iter (by rw [hiter]; rfl) (by rw [hiter]; exact hL64) a _ true
      (by
        rw [hiter]
        simp only [ExpInv, ↓reduceIte, show L.val ≠ 0 by omega]
        refine ⟨hcmu, hcmN, ?_⟩
        rw [hL, div_pow_log2 _ (by omega), pow_one, hc1]
        exact hcmC) as ⟨a1, b3, in_a, hres⟩
    simp only [ExpInv, ↓reduceIte, hc1] at hres
    obtain ⟨hu, hN, hv⟩ := hres
    split <;> rename_i hin <;> simp only [hin, ↓reduceIte] at hu hN hv <;> simp only [WP.spec_ok] <;>
      exact ⟨hlt, hu, (Nat.mod_eq_of_lt hN).symm.trans hv⟩
  · rename_i hge
    rw [hb] at hge
    simp only [WP.spec_ok]
    simpa using hge

end rind.x86_64
