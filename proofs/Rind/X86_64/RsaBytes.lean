import Rind.X86_64.RsaPublic
import Rind.X86_64.Blockwise
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's integer encodings on x86_64

`PosInt::from_bytes` is RFC 8017's OS2IP, and `PosInt::to_bytes` with
`i2osp` its I2OSP.
-/

namespace rind.x86_64

theorem os2ip_bv (l : List U8) : os2ip (bv l) = beNat l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    simp only [bv, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [os2ip, List.foldl_append, ← os2ip, ih, beNat_append]
    simp [beNat, leNat, Nat.mul_comm]

theorem beNat_zeros (l : List U8) (h : ∀ x ∈ l, x = 0#u8) : beNat l = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [show a :: t = [a] ++ t from rfl, beNat_append, ih (fun x hx => h x (by simp [hx]))]
    simp [h a (by simp), beNat, leNat]

/-- Leading zeros add nothing. -/
theorem beNat_drop_zeros (l : List U8) (n : Nat) (h : ∀ x ∈ l.take n, x = 0#u8) :
    beNat (l.drop n) = beNat l := by
  conv_rhs => rw [← List.take_append_drop n l, beNat_append, beNat_zeros _ h]
  simp

theorem trim_leading_zeroes_spec (bytes : Slice U8) :
    low.posint.trim_leading_zeroes bytes ⦃ s =>
      beNat s.val = beNat bytes.val ∧ s.length ≤ bytes.length ∧ (0 < s.length → s.val[0]! ≠ 0#u8) ⦄ := by
  unfold low.posint.trim_leading_zeroes low.posint.trim_leading_zeroes_loop
  step with loop.spec_decr_nat (fun st : Usize => bytes.length - st.val)
    (fun st : Usize => st.val ≤ bytes.length ∧ ∀ x ∈ bytes.val.take st.val, x = 0#u8)
    (fun st : Usize => st.val ≤ bytes.length ∧ (∀ x ∈ bytes.val.take st.val, x = 0#u8) ∧
      (st.val < bytes.length → bytes.val[st.val]! ≠ 0#u8)) as ⟨start, hle, hz, hnz⟩
  · intro st ⟨hle, hz⟩
    unfold low.posint.trim_leading_zeroes_loop.body
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro x hx
      rw [start1_post, List.take_add_one] at hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hz x hx
      · simp [List.getElem?_eq_getElem (by scalar_tac : st.val < bytes.val.length)] at hx
        rw [hx, ← i1_post]; assumption
    · refine ⟨hle, hz, fun _ => ?_⟩
      rw [getElem!_pos _ _ (by scalar_tac), ← i1_post]
      assumption
  · exact ⟨by simp, by simp⟩
  · step*
    refine ⟨?_, by scalar_tac, fun h => ?_⟩
    · rw [s_post]; exact beNat_drop_zeros _ _ hz
    · rw [s_post, List.getElem!_drop, Nat.add_zero]
      apply hnz
      have : s.length = bytes.length - start.val := by scalar_tac
      omega

/-- A number whose first byte is nonzero is at least `256` to the rest's
length. -/
theorem beNat_ge_of_head (l : List U8) (h : 0 < l.length) (h0 : l[0]! ≠ 0#u8) :
    256 ^ (l.length - 1) ≤ beNat l := by
  obtain ⟨x, t, rfl⟩ : ∃ x t, l = x :: t := by
    cases l with
    | nil => simp at h
    | cons x t => exact ⟨x, t, rfl⟩
  have hx : 1 ≤ x.val := by
    by_contra hc
    apply h0
    simp only [List.getElem!_cons_zero]
    rw [UScalar.eq_equiv]; simp; omega
  rw [show x :: t = [x] ++ t from rfl, beNat_append, List.length_append, List.length_singleton,
    Nat.add_sub_cancel_left]
  have h1 : beNat [x] = x.val := by simp [beNat, leNat]
  rw [h1]
  have : 256 ^ t.length ≤ x.val * 256 ^ t.length := Nat.le_mul_of_pos_left _ hx
  omega

theorem set_append_replicate {α : Type} (ws : List α) (n : Nat) (z x : α) (hn : 1 ≤ n) :
    (ws ++ List.replicate n z).set ws.length x = (ws ++ [x]) ++ List.replicate (n - 1) z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [List.replicate_succ, List.set_append_right]

theorem take_eq_take_append_slice {α : Type} (l : List α) (a e : Nat) (hae : a ≤ e) :
    l.take e = l.take a ++ l.slice a e := by
  have := slice_append_slice l 0 a e (by omega) hae
  simp only [List.slice_zero_j] at this
  exact this.symm

/-- What `from_bytes`'s word loop keeps, with `i` words read from the back of
`b`: they are the words below `i`, the rest are zero, and `b` reads as the
bytes left over, then those words. -/
def FromBytesInv (b : List U8) (i : Nat) (r : RsaInt) : Prop :=
  r.used.val = 0 ∧ ∃ ws : List U64, ws.length = i ∧ r.words.val = ws ++ List.replicate (128 - i) 0#u64 ∧
    beNat b = beNat (b.take (b.length - 8 * i)) * 2 ^ (64 * i) + wordsNat ws

theorem from_bytes_loop0_spec (b : Slice U8) (hlen : b.length ≤ 1024)
    (iter : core.ops.range.Range Usize) (hend : iter.end.val = b.length / 8)
    (hstart : iter.start.val ≤ iter.end.val) (r : RsaInt) (hinv : FromBytesInv b.val iter.start.val r) :
    low.posint.PosInt.from_bytes_loop0 iter b r ⦃ r' => FromBytesInv b.val (b.length / 8) r' ⦄ := by
  unfold low.posint.PosInt.from_bytes_loop0
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x => x.1.end = iter.end ∧ x.1.start.val ≤ x.1.end.val ∧ FromBytesInv b.val x.1.start.val x.2)
  · rintro ⟨it, r1⟩ ⟨he, hs, hinv⟩
    simp only at he hs hinv
    unfold low.posint.PosInt.from_bytes_loop0.body
    step as ⟨o, iter1, ho, hend1⟩
    cases o with
    | none =>
      have h2 : it.end.val = iter.end.val := by rw [he]
      have : it.start.val = b.length / 8 := by
        split at ho
        · simp at ho
        · omega
      rw [this] at hinv
      simpa using hinv
    | some i =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at ho
      simp only [hlt, ↓reduceIte, Option.some.injEq] at ho
      obtain ⟨rfl, hst⟩ := ho
      obtain ⟨hu, ws, hwl, hws, hval⟩ := hinv
      have h2 : it.end.val = iter.end.val := by rw [he]
      have hi : it.start.val < b.length / 8 := by omega
      have hbl : b.len.val = b.length := rfl
      have hbL : b.length = b.val.length := rfl
      step as ⟨i2, hi2⟩
      step as ⟨e, he1, he2⟩
      step as ⟨i3, hi3, hi3'⟩
      step as ⟨sl, hsl, hsl'⟩
      step as ⟨r2, hr2⟩
      cases r2 with
      | Err _ => exfalso; simp at hr2; scalar_tac
      | Ok a =>
        obtain ⟨haval, halen⟩ := hr2
        step as ⟨a', ha'⟩
        simp only [core.result.Result.Ok.injEq] at ha'
        subst ha'
        step as ⟨w, hw⟩
        have hwv : w.val = beNat sl.val := by rw [← haval]; exact val_of_fromBEBytes _ w hw
        step as ⟨nw, hnw⟩
        have h3 : iter1.end.val = it.end.val := by rw [hend1]
        refine ⟨by rw [hend1, he], by omega, ⟨hu, ws ++ [w], by simp [hwl, hst], ?_, ?_⟩, by omega⟩
        · rw [hnw, Array.set_val_eq, hws, ← hwl, set_append_replicate _ _ _ _ (by omega)]
          simp only [List.append_assoc, List.cons_append, List.nil_append, hwl, hst]
          rw [Nat.sub_sub]
        · have hsplit := take_eq_take_append_slice b.val i3.val e.val (by omega)
          have hsl8 : sl.val.length = 8 := by simpa [Slice.length] using hsl'.trans (by omega)
          rw [hst, wordsNat_append, hwl, show (b.val.length - 8 * (it.start.val + 1)) = i3.val by omega]
          rw [show b.val.length - 8 * it.start.val = e.val by omega,
            hsplit, beNat_append, ← hsl, hsl8] at hval
          rw [hval, show wordsNat [w] = w.val by simp [wordsNat], hwv]
          rw [show (256 : Nat) ^ 8 = 2 ^ 64 by norm_num]
          ring
  · exact ⟨rfl, hstart, hinv⟩

theorem from_bytes_loop1_spec (b : Slice U8) (iter : core.ops.range.Range Usize)
    (hend : iter.end.val < 8) (hle : iter.end.val ≤ b.length) (hstart : iter.start.val ≤ iter.end.val)
    (top : U64) (htop : top.val = beNat (b.val.take iter.start.val)) :
    low.posint.PosInt.from_bytes_loop1 iter b top ⦃ t => t.val = beNat (b.val.take iter.end.val) ⦄ := by
  unfold low.posint.PosInt.from_bytes_loop1
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x => x.1.end = iter.end ∧ x.1.start.val ≤ x.1.end.val ∧ x.2.val = beNat (b.val.take x.1.start.val))
  · rintro ⟨it, t⟩ ⟨he, hs, ht⟩
    simp only at he hs ht
    have h2 : it.end.val = iter.end.val := by rw [he]
    unfold low.posint.PosInt.from_bytes_loop1.body
    step as ⟨o, iter1, ho, hend1⟩
    cases o with
    | none =>
      have : it.start.val = iter.end.val := by
        split at ho
        · simp at ho
        · omega
      rw [this] at ht
      simpa using ht
    | some i =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at ho
      simp only [hlt, ↓reduceIte, Option.some.injEq] at ho
      obtain ⟨rfl, hst⟩ := ho
      have h3 : iter1.end.val = it.end.val := by rw [hend1]
      have hbL : b.length = b.val.length := rfl
      have htlt : t.val < 2 ^ 56 := by
        rw [ht]
        have := beNat_lt (b.val.take it.start.val)
        calc _ < 256 ^ (b.val.take it.start.val).length := this
          _ ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by simp; omega)
          _ = 2 ^ 56 := by norm_num
      step*
      refine ⟨by rw [hend1, he], by omega, ?_, by omega⟩
      rw [hst, List.take_add_one, beNat_append, ← ht]
      have hi1 : i1.val = t.val * 256 := by
        rw [i1_post, Nat.shiftLeft_eq, Nat.mod_eq_of_lt] <;> simp [U64.size, U64.numBits] <;> try omega
      have hi3 : i3.val = i2.val := by
        rw [i3_post, UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by have := i2.hBounds; simp at this ⊢; omega)
      have htop1 : top1.val = t.val * 256 + i2.val := by
        rw [top1_post, UScalar.val_or, hi1, hi3, show t.val * 256 = t.val <<< 8 by rw [Nat.shiftLeft_eq],
          ← Nat.shiftLeft_add_eq_or_of_lt (by have := i2.hBounds; simpa using this)]
      rw [List.getElem?_eq_getElem (by omega)]
      simp [beNat, leNat, htop1, i2_post]
  · exact ⟨rfl, hstart, htop⟩

/-- Up to 1024 bytes read below `2^8192`. -/
theorem beNat_lt_8192 (l : List U8) (h : l.length ≤ 1024) : beNat l < 2 ^ 8192 :=
  calc beNat l < 256 ^ l.length := beNat_lt l
    _ ≤ 256 ^ 1024 := Nat.pow_le_pow_right (by norm_num) h
    _ = 2 ^ 8192 := by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← pow_mul]

/-- OS2IP: `from_bytes` reads big-endian bytes encoding a number below
`2^8192` as that number, with no words set above its length, and its top
word nonzero. -/
theorem posint_from_bytes_spec (bytes : Slice U8) (hlen : beNat bytes.val < 2 ^ 8192) :
    low.posint.PosInt.from_bytes 128#usize bytes ⦃ r => ∃ p, r = .Ok p ∧ p.used.val ≤ 128 ∧
      wordsNat (p.words.val.drop p.used.val) = 0 ∧ wordsNat (lowWords p p.used) = beNat bytes.val ∧
      (p.used.val = 0 ∨ 2 ^ (64 * (p.used.val - 1)) ≤ beNat bytes.val) ⦄ := by
  unfold low.posint.PosInt.from_bytes low.posint.PosInt.zero
  step with trim_leading_zeroes_spec as ⟨b1, hb1v, hb1l, hb1h⟩
  have hbL : b1.length = b1.val.length := rfl
  have hb1ge : 0 < b1.length → 2 ^ (8 * (b1.length - 1)) ≤ beNat bytes.val := fun h => by
    rw [← hb1v, pow_mul]
    exact beNat_ge_of_head _ (by omega) (hb1h h)
  -- Trimmed of its leading zeros, a number below `2^8192` takes at most 1024 bytes.
  have hlen : b1.length ≤ 1024 := by
    by_contra hc
    have := lt_of_le_of_lt (hb1ge (by omega)) hlen
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    omega
  step*
  have hfull : full.val = b1.length / 8 := by rw [full_post]; rfl
  step with from_bytes_loop0_spec b1 (by omega) { start := 0#usize, «end» := full } hfull (by scalar_tac)
    { words := Array.repeat 128#usize 0#u64, used := 0#usize } ⟨by first | rfl | scalar_tac, [], rfl, by simp, by simp [wordsNat_nil]⟩ as ⟨r1, hr1⟩
  obtain ⟨hu, ws, hwl, hws, hval⟩ := hr1
  step as ⟨i4, hi4⟩
  have hi4' : i4.val = b1.length % 8 := by rw [hi4]; rfl
  step with from_bytes_loop1_spec b1 { start := 0#usize, «end» := i4 } (by simp; omega) (by simp; omega)
    (by scalar_tac) 0#u64 (by simp [beNat, leNat]) as ⟨top, htop⟩
  rw [show b1.val.length - 8 * (b1.length / 8) = i4.val by omega, ← htop] at hval
  have hz : wordsNat (List.replicate (128 - b1.length / 8) 0#u64) = 0 := wordsNat_replicate_zero _
  split
  · rename_i hne
    have htop0 : top.val ≠ 0 := by
      intro h0; apply absurd hne; simp [UScalar.eq_equiv, h0]
    have hf128 : full.val < 128 := by
      by_contra hc
      have : i4.val = 0 := by omega
      rw [this] at htop; simp [beNat, leNat] at htop; omega
    unfold low.posint.PosInt.push_word
    split
    · rename_i h; rw [UScalar.eq_equiv] at h; simp at h; omega
    step as ⟨nw, hnw⟩
    step as ⟨u1, hu1⟩
    step*
    have hfw : full.val = ws.length := by rw [hfull, hwl]
    have hnwv : nw.val = (ws ++ [top]) ++ List.replicate (128 - ws.length - 1) 0#u64 := by
      rw [hnw, Array.set_val_eq, hws, hfw, ← hwl, set_append_replicate _ _ _ _ (by omega)]
    have hu1' : u1.val = (ws ++ [top]).length := by simp [hu1, hfw]
    refine ⟨_, rfl, by scalar_tac, ?_, ?_, Or.inr ?_⟩
    · simp only [hnwv, hu1', List.drop_left]
      exact wordsNat_replicate_zero _
    · simp only [lowWords, hnwv, hu1', List.take_left]
      rw [wordsNat_append, ← hb1v, hval, hwl]
      simp [wordsNat]; ring
    · have hi4p : 0 < i4.val := by
        by_contra hc
        have : i4.val = 0 := by omega
        rw [this] at htop; simp [beNat, leNat] at htop; omega
      have := hb1ge (by omega)
      rw [hu1', List.length_append, List.length_singleton, Nat.add_sub_cancel, ← hfw]
      calc 2 ^ (64 * full.val) ≤ 2 ^ (8 * (b1.length - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := this
  · rename_i heq
    have htop0 : top.val = 0 := by simpa [UScalar.eq_equiv] using heq
    simp only [WP.spec_ok]
    refine ⟨_, rfl, by scalar_tac, ?_, ?_, ?_⟩
    · simp only [hws, show full.val = ws.length by rw [hfull, hwl], List.drop_left]
      exact hz
    · simp only [lowWords, hws, show full.val = ws.length by rw [hfull, hwl], List.take_left]
      rw [← hb1v, hval, htop0]; simp
    · rcases Nat.eq_zero_or_pos full.val with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ?_
        have := hb1ge (by omega)
        calc 2 ^ (64 * (full.val - 1)) ≤ 2 ^ (8 * (b1.length - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ _ := this

/-- `from_bytes` refuses a number of `2^8192` or more, too long for its
words. -/
theorem posint_from_bytes_long_spec (bytes : Slice U8) (hlen : 2 ^ 8192 ≤ beNat bytes.val) :
    low.posint.PosInt.from_bytes 128#usize bytes ⦃ r => ∃ err, r = .Err err ⦄ := by
  unfold low.posint.PosInt.from_bytes
  step with trim_leading_zeroes_spec as ⟨b1, hb1v, hb1l, hb1h⟩
  have : 1024 < b1.length := by
    by_contra hc
    have := beNat_lt_8192 b1.val (by have : b1.length = b1.val.length := rfl; omega)
    omega
  step*

/-- `to_bytes`'s loop, with `i` words written at the back of `out`'s first
`8 used` bytes: those bytes read as the low `i` words. -/
theorem to_bytes_loop_spec {N : Usize} (words : Std.Array U64 N) (req : Usize) (out0 : Slice U8)
    (iter : core.ops.range.Range Usize) (hreq : req.val = 8 * iter.end.val) (hlen : out0.length = req.val)
    (hN : iter.end.val ≤ N.val) (hstart : iter.start.val ≤ iter.end.val) (out : Slice U8)
    (hinv : out.length = req.val ∧ ∃ L : List U8, L.length = 8 * iter.start.val ∧
      out.val = out0.val.take (req.val - 8 * iter.start.val) ++ L ∧
      beNat L = wordsNat (words.val.take iter.start.val)) :
    low.posint.PosInt.to_bytes_loop iter words req out ⦃ o =>
      o.length = req.val ∧ beNat o.val = wordsNat (words.val.take iter.end.val) ⦄ := by
  unfold low.posint.PosInt.to_bytes_loop
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x : core.ops.range.Range Usize × Slice U8 => x.1.end = iter.end ∧ x.1.start.val ≤ x.1.end.val ∧
      x.2.length = req.val ∧ ∃ L : List U8, L.length = 8 * x.1.start.val ∧
      x.2.val = out0.val.take (req.val - 8 * x.1.start.val) ++ L ∧
      beNat L = wordsNat (words.val.take x.1.start.val))
  · rintro ⟨it, o⟩ ⟨he, hs, hol, L, hL, ho, hLv⟩
    simp only at he hs hol hL ho hLv
    have h2 : it.end.val = iter.end.val := by rw [he]
    unfold low.posint.PosInt.to_bytes_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have : it.start.val = iter.end.val := by
        split at hop
        · simp at hop
        · omega
      rw [this] at hLv hL ho
      simp only [WP.spec_ok]
      refine ⟨hol, ?_⟩
      rw [ho, show req.val - 8 * iter.end.val = 0 by omega]
      simpa using hLv
    | some i =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      have h3 : iter1.end.val = it.end.val := by rw [hend1]
      have hwl : words.val.length = N.val := by simp
      have hoL : o.length = o.val.length := rfl
      have h0L : out0.length = out0.val.length := rfl
      step as ⟨i1, hi1⟩
      step as ⟨e, he1⟩
      step as ⟨i2, hi2⟩
      step as ⟨s, back, hs1, hs2, hback⟩
      step as ⟨w, hw⟩
      step as ⟨a1, ha1⟩
      step as ⟨s1, hs1v⟩
      step as ⟨s2, hs2v⟩
      have hbl : s1.val.length = 8 := by simp [hs1v, ha1]
      have hs1' : s1.val = w.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8) := by simp [hs1v, ha1]
      refine ⟨by rw [hend1, he], by omega, by simp [hback, hs2v]; omega,
        ⟨s1.val ++ L, by simp [hbl, hL, hst]; ring, ?_, ?_⟩, by omega⟩
      · rw [hback, hs2v]
        rw [Slice.setSlice!_val]
        have hsplit := take_eq_take_append_slice out0.val i2.val e.val (by omega)
        have hA : (out0.val.take i2.val).length = i2.val := by simp; omega
        have hset := setSlice!_append (out0.val.take i2.val) (out0.val.slice i2.val e.val) L s1.val
          (by rw [hbl, length_slice _ _ _ (by omega)]; omega)
        rw [hA] at hset
        rw [ho, show req.val - 8 * it.start.val = e.val by omega, hsplit, hset, hst,
          show req.val - 8 * (it.start.val + 1) = i2.val by omega]
        simp
      · rw [beNat_append, hLv, hL, hst, List.take_add_one, wordsNat_append,
          List.getElem?_eq_getElem (by omega)]
        rw [hs1', beNat_toBEBytes, hw]
        simp [wordsNat, List.length_take, hwl, show min it.start.val N.val = it.start.val by omega]
        rw [show (256 : Nat) ^ (8 * it.start.val) = 2 ^ (64 * it.start.val) by
          rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]; ring_nf]
        ring
  · exact ⟨rfl, hstart, hinv⟩

/-- `to_bytes` writes a number of at most `N` words as `8 used` big-endian
bytes, given room for them. -/
theorem to_bytes_spec {N : Usize} (p : low.posint.PosInt N) (out : Slice U8) (hN : p.used.val ≤ N.val)
    (hlen : 8 * p.used.val ≤ out.length) :
    low.posint.PosInt.to_bytes p out ⦃ r _ => ∃ s, r = .Ok s ∧ s.length = 8 * p.used.val ∧
      beNat s.val = wordsNat (p.words.val.take p.used.val) ⦄ := by
  unfold low.posint.PosInt.to_bytes
  step as ⟨req, hreq⟩
  have hle : req ≤ out.length := by scalar_tac
  simp only [core.slice.Slice.get_mut, core.slice.index.SliceIndexRangeToUsizeSlice.get_mut, hle, ↓reduceIte]
  have hl0 : (Slice.from (out.val.slice 0 req.val) (by scalar_tac) : Slice U8).length = req.val := by
    simp [Slice.length]; scalar_tac
  step with to_bytes_loop_spec p.words req _ { start := 0#usize, «end» := p.used } (by simp [hreq]; ring) hl0
    (by simpa using hN) (by simp) _ ⟨hl0, [], by simp, by simp, by simp [beNat, leNat, wordsNat_nil]⟩
    as ⟨o, hol, hov⟩
  exact ⟨o, rfl, by omega, hov⟩

theorem usize_saturating_sub_val (x y : Usize) :
    (core.num.Usize.saturating_sub x y).val = x.val - y.val := by
  have := x.hBounds
  simp only [core.num.Usize.saturating_sub, UScalar.saturating_sub, UScalar.val, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  simp only [UScalar.val] at this
  omega

theorem beNat_pos (l : List U8) (h : ∃ x ∈ l, x ≠ 0#u8) : 0 < beNat l := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    rw [show a :: t = [a] ++ t from rfl, beNat_append]
    by_cases ha : a = 0#u8
    · have : ∃ x ∈ t, x ≠ 0#u8 := by
        obtain ⟨x, hx, hx0⟩ := h
        simp at hx; rcases hx with rfl | hx
        · exact absurd ha hx0
        · exact ⟨x, hx, hx0⟩
      have := ih this; positivity
    · have : 0 < a.val := by
        rcases Nat.eq_zero_or_pos a.val with h0 | h0
        · exact absurd (by simpa [UScalar.eq_equiv] using h0) ha
        · exact h0
      have : beNat [a] = a.val := by simp [beNat, leNat]
      have : 0 < 256 ^ t.length := by positivity
      nlinarith

/-- `i2osp`'s loop: whether the excess bytes read so far are all zero. -/
theorem i2osp_loop_spec (excess : Slice U8) (iter : core.ops.range.Range Usize)
    (hend : iter.end.val = excess.length) (hstart : iter.start.val ≤ iter.end.val) (any : U8)
    (hany : any.val = 0 ↔ ∀ x ∈ excess.val.take iter.start.val, x = 0#u8) :
    high.rsa.i2osp_loop iter excess any ⦃ a => a.val = 0 ↔ ∀ x ∈ excess.val, x = 0#u8 ⦄ := by
  unfold high.rsa.i2osp_loop
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x : core.ops.range.Range Usize × U8 => x.1.end = iter.end ∧ x.1.start.val ≤ x.1.end.val ∧
      (x.2.val = 0 ↔ ∀ y ∈ excess.val.take x.1.start.val, y = 0#u8))
  · rintro ⟨it, a⟩ ⟨he, hs, ha⟩
    simp only at he hs ha
    have h2 : it.end.val = iter.end.val := by rw [he]
    have hbL : excess.length = excess.val.length := rfl
    unfold high.rsa.i2osp_loop.body
    step as ⟨o, iter1, ho, hend1⟩
    cases o with
    | none =>
      have : it.start.val = excess.length := by
        split at ho
        · simp at ho
        · omega
      simp only [WP.spec_ok]
      rw [ha, this, hbL, List.take_length]
    | some i =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at ho
      simp only [hlt, ↓reduceIte, Option.some.injEq] at ho
      obtain ⟨rfl, hst⟩ := ho
      have h3 : iter1.end.val = it.end.val := by rw [hend1]
      step as ⟨b, hb⟩
      step as ⟨a1, ha1⟩
      refine ⟨by rw [hend1, he], by omega, ?_, by omega⟩
      rw [ha1, UScalar.val_or, Nat.or_eq_zero_iff, ha, hst, List.take_add_one,
        List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩ y (hy | rfl)
        · exact h1 y hy
        · rw [← hb]; simpa [UScalar.eq_equiv] using h2
      · intro h
        refine ⟨fun y hy => h y (Or.inl hy), ?_⟩
        have := h _ (Or.inr rfl)
        rw [← hb] at this
        simpa [UScalar.eq_equiv] using this
  · exact ⟨rfl, hstart, hany⟩

/-- I2OSP: `i2osp` writes `x` to all of `out` if it fits in that many bytes,
and refuses it otherwise. -/
theorem i2osp_spec (x : RsaInt) (out : Slice U8) (hu : x.used.val ≤ 128) :
    high.rsa.i2osp x out ⦃ r out' =>
      (wordsNat (lowWords x x.used) < 256 ^ out.length →
        r = .Ok () ∧ out'.length = out.length ∧ beNat out'.val = wordsNat (lowWords x x.used)) ∧
      (256 ^ out.length ≤ wordsNat (lowWords x x.used) → r = .Err .WrongLength) ⦄ := by
  unfold high.rsa.i2osp
  step as ⟨s, _p, hs⟩
  have hsl : s.length = 1024 := by
    simp only [Slice.length, hs, Array.repeat_val, List.length_replicate]; rfl
  step with to_bytes_spec x s (by simpa using hu) (by omega) as ⟨r, _q, val, hr, hvl, hvv⟩
  subst hr
  simp only [core.result.Result.Insts.CoreOpsTry.branch]
  have hsat := usize_saturating_sub_val val.len out.len
  have hvL : val.length = val.val.length := rfl
  have hoL : out.length = out.val.length := rfl
  simp only [lift]
  step as ⟨excess, bytes1, hel, hbl, hev, hbv⟩
  · rw [hsat]; simp
  rw [hsat] at hel hbl hev hbv
  simp only [Slice.len_val] at hel hbl hev hbv
  step with i2osp_loop_spec excess { start := 0#usize, «end» := excess.len } (by simp) (by simp)
    0#u8 (by simp) as ⟨any, hany⟩
  simp only [low.ct.into_public, bind_ok]
  have hX : wordsNat (lowWords x x.used) = beNat val.val := by rw [hvv]; rfl
  rw [hX]
  have hsplit : beNat val.val = beNat excess.val * 256 ^ bytes1.length + beNat bytes1.val := by
    rw [← beNat_append, hev, hbv, List.take_append_drop]
  have hbl' : bytes1.length = min val.length out.length := by rw [hbl]; omega
  split
  · rename_i hne
    simp only [WP.spec_ok]
    have hne' : any.val ≠ 0 := by
      intro h0
      have : any = 0#u8 := by rw [UScalar.eq_equiv]; simpa using h0
      simp [this] at hne
    have hnz : ∃ y ∈ excess.val, y ≠ 0#u8 := by
      by_contra hc; push_neg at hc; exact hne' (hany.mpr hc)
    have hpos := beNat_pos _ hnz
    have hbo : bytes1.length = out.length := by
      have : 0 < excess.val.length := by
        obtain ⟨y, hy, _⟩ := hnz; exact List.length_pos_of_mem hy
      have : excess.length = excess.val.length := rfl
      omega
    refine ⟨fun hlt => ?_, fun _ => rfl⟩
    exfalso
    rw [hsplit, hbo] at hlt
    have := Nat.mul_le_mul_right (256 ^ out.length) hpos
    omega
  · rename_i heq
    have hz : any.val = 0 := by simpa [UScalar.eq_equiv] using heq
    have hall := hany.mp hz
    have hex0 : beNat excess.val = 0 := beNat_zeros _ hall
    have hlt : beNat val.val < 256 ^ out.length := by
      rw [hsplit, hex0, zero_mul, zero_add]
      calc beNat bytes1.val < 256 ^ bytes1.val.length := beNat_lt _
        _ ≤ 256 ^ out.length := Nat.pow_le_pow_right (by norm_num) (by
          have : bytes1.length = bytes1.val.length := rfl; omega)
    step as ⟨i7, hi7⟩
    step as ⟨zv, vs, bk, hz1, hz2, hz3, hz4, hback⟩
    step as ⟨zeroes1, hzl, hzv⟩
    · simp
    have hb7 : bytes1.length = out.length - i7.val := by
      have : bytes1.len.val = bytes1.length := rfl
      have : out.len.val = out.length := rfl
      omega
    step as ⟨value1, hval1⟩
    have hbk := hback zeroes1 value1 (by rw [hzl, hz1]) (by rw [hval1, hb7])
    refine ⟨fun _ => ⟨hbk.2, ?_⟩, fun hge => absurd hlt (by omega)⟩
    rw [hbk.1, hzv, hval1, beNat_append, beNat_zeros _ (by simp), zero_mul, zero_add, hsplit, hex0,
      zero_mul, zero_add]

/-- I2OSP writes a number as the bytes it was read from. -/
theorem i2osp_beNat (L : List U8) : i2osp (beNat L) L.length = some (bv L) := by
  unfold i2osp
  rw [ite_cond_eq_true _ _ (eq_true (beNat_lt L))]
  congr 1
  induction L with
  | nil => rfl
  | cons a t ih =>
    have hP : 0 < 256 ^ t.length := by positivity
    have hB := beNat_lt t
    have hcons : beNat (a :: t) = a.val * 256 ^ t.length + beNat t := by
      rw [show a :: t = [a] ++ t from rfl, beNat_append]; simp [beNat, leNat]
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, bv, List.map_cons, ← bv, ← ih, hcons]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl),
        Nat.mul_div_cancel _ hP, Nat.div_eq_of_lt hB, Nat.add_zero]
      have := a.hBounds
      simp only [UScalar.val] at this ⊢
      exact Nat.mod_eq_of_lt (by simpa using this)
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_reverse, List.mem_range] at hi
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      have hpow : 256 ^ t.length = 256 ^ i * (256 * 256 ^ (t.length - i - 1)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      rw [hpow, show a.val * (256 ^ i * (256 * 256 ^ (t.length - i - 1))) + beNat t =
        beNat t + (a.val * (256 * 256 ^ (t.length - i - 1))) * 256 ^ i by ring,
        Nat.add_mul_div_right _ _ (by positivity)]
      rw [show a.val * (256 * 256 ^ (t.length - i - 1)) = 2 ^ 8 * (a.val * 256 ^ (t.length - i - 1)) by ring,
        Nat.add_mul_mod_self_left]

theorem take_set_succ {α : Type} (l : List α) (j : Nat) (x : α) (hj : j < l.length) :
    (l.set j x).take (j + 1) = l.take j ++ [x] := by
  rw [List.take_set, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.set_append_right _ _ (by simp)]
  simp [show j - min j l.length = 0 by omega]

/-- `encode_pkcs1_sig`'s padding loop: the bytes it has reached are the
encoding's header and as much of its `0xff` run. -/
theorem encode_pkcs1_sig_loop_spec (iter : core.ops.range.Range Usize) (out : Slice U8)
    (h2 : 2 ≤ iter.start.val) (hstart : iter.start.val ≤ iter.end.val) (hend : iter.end.val ≤ out.length)
    (hinv : out.val.take iter.start.val = [0#u8, 1#u8] ++ List.replicate (iter.start.val - 2) 255#u8) :
    high.pkcs1.encode_pkcs1_sig_loop iter out ⦃ o => o.length = out.length ∧
      o.val.take iter.end.val = [0#u8, 1#u8] ++ List.replicate (iter.end.val - 2) 255#u8 ⦄ := by
  unfold high.pkcs1.encode_pkcs1_sig_loop
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x : core.ops.range.Range Usize × Slice U8 => x.1.end = iter.end ∧ 2 ≤ x.1.start.val ∧
      x.1.start.val ≤ x.1.end.val ∧ x.2.length = out.length ∧
      x.2.val.take x.1.start.val = [0#u8, 1#u8] ++ List.replicate (x.1.start.val - 2) 255#u8)
  · rintro ⟨it, o⟩ ⟨he, h2', hs, hol, ho⟩
    simp only at he h2' hs hol ho
    have h2e : it.end.val = iter.end.val := by rw [he]
    unfold high.pkcs1.encode_pkcs1_sig_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have : it.start.val = iter.end.val := by
        split at hop
        · simp at hop
        · omega
      simp only [WP.spec_ok]
      rw [this] at ho
      exact ⟨hol, ho⟩
    | some i =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      have h3 : iter1.end.val = it.end.val := by rw [hend1]
      have hoL : o.length = o.val.length := rfl
      step as ⟨o1, ho1⟩
      refine ⟨by rw [hend1, he], by omega, by omega, by rw [ho1]; simpa using hol, ?_, by omega⟩
      rw [ho1, Slice.set_val_eq, hst, take_set_succ _ _ _ (by omega), ho,
        show it.start.val + 1 - 2 = (it.start.val - 2) + 1 by omega, List.replicate_succ']
      simp
  · exact ⟨rfl, h2, hstart, rfl, hinv⟩

theorem setSlice!_end {α : Type _} (r s : List α) (i : Nat) (hs : i + s.length = r.length) :
    r.setSlice! i s = r.take i ++ s := by
  rw [← take_setSlice! r s i (by omega), List.take_of_length_le (by simp; omega)]

/-- EMSA-PKCS1-v1_5-ENCODE, given `T = digest_info ++ hash` and room for it. -/
theorem encode_pkcs1_sig_spec (out digest_info hash : Slice U8)
    (hroom : digest_info.length + hash.length + 11 ≤ out.length) :
    high.pkcs1.encode_pkcs1_sig out digest_info hash ⦃ o =>
      o.val = [0#u8, 1#u8] ++ List.replicate (out.length - (digest_info.length + hash.length) - 3) 255#u8 ++
        [0#u8] ++ digest_info.val ++ hash.val ⦄ := by
  unfold high.pkcs1.encode_pkcs1_sig
  have hoL : out.length = out.val.length := rfl
  have hdL : digest_info.length = digest_info.val.length := rfl
  have hhL : hash.length = hash.val.length := rfl
  step as ⟨tl, htl⟩
  step as ⟨i2, hi2⟩
  step*
  have hdl : digest_info.len.val = digest_info.length := rfl
  have hhl : hash.len.val = hash.length := rfl
  have hol : out.len.val = out.length := rfl
  have hsl : s.length = out.length := by rw [s_post, out1_post]; simp
  have hs2 : s.val.take 2 = [0#u8, 1#u8] := by
    rw [s_post, Slice.set_val_eq, show (2 : Nat) = (1#usize).val + 1 from rfl,
      take_set_succ _ _ _ (by simp [out1_post]; omega), out1_post, Slice.set_val_eq,
      show (1#usize).val = (0#usize).val + 1 from rfl, take_set_succ _ _ _ (by simp; omega)]
    simp
  step with encode_pkcs1_sig_loop_spec { start := 2#usize, «end» := i3 } s (by simp) (by simp; omega)
    (by show i3.val ≤ s.length; omega) (by simpa using hs2) as ⟨out2, ho2l, ho2⟩
  step as ⟨i4, hi4⟩
  step as ⟨out3, ho3⟩
  step as ⟨i6, hi6⟩
  step as ⟨s1, back, hs1, hs1l, hback⟩
  step as ⟨s2, hs2v⟩
  · rw [hs1l]; omega
  step as ⟨i8, hi8⟩
  have e1 : (back s2).length = (back s2).val.length := rfl
  have e2 : out2.length = out2.val.length := rfl
  have hb2l : (back s2).length = out.length := by
    rw [e1, hback, hs2v]; simp [ho3]; omega
  step as ⟨s3, back1, hs3, hs3l, hback1⟩
  step as ⟨s4, hs4v⟩
  · rw [hs3l, hb2l]; omega
  rw [hback1, hs4v, setSlice!_end _ _ _ (by omega), hback, hs2v, Slice.setSlice!_val, show i8.val = t_start.val + digest_info.val.length by omega,
    take_setSlice! _ _ _ (by simp [ho3]; omega), ho3, Slice.set_val_eq,
    show t_start.val = i4.val + 1 by omega, take_set_succ _ _ _ (by omega), show i4.val = i3.val by omega, ho2,
    show i3.val - 2 = out.length - (digest_info.length + hash.length) - 3 by omega]

end rind.x86_64
