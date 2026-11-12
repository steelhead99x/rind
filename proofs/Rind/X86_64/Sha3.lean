import Rind.X86_64.KeccakDispatch
import Rind.X86_64.Blockwise
import Rind.X86_64.Sha512
import Rind.Sha3
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.spec

/-!
# The SHA-3 sponge, proven from rind's Rust to FIPS 202

`Rind.Sha3` states FIPS 202's sponge over bytes and proves it SymCrypt's
transliteration of the standard. This file proves rind's Rust sponge,
`mid::sha3`, computes it, over the Keccak-f routines
`Rind.X86_64.KeccakDispatch` specifies from s2n-bignum's contracts.
`admin/prove` writes the aarch64 proof from this file by renaming the target.
-/

namespace rind.x86_64

/-! ## The state's bytes -/

/-- Lanes' bytes, little-endian. -/
abbrev sbl (L : List U64) : List Byte := stateBytes (L.map (·.bv))

theorem ext_getElem! {α : Type} [Inhabited α] {l1 l2 : List α} (h : l1.length = l2.length)
    (h' : ∀ i, i < l1.length → l1[i]! = l2[i]!) : l1 = l2 :=
  List.ext_getElem h fun i h1 h2 => by
    have := h' i h1
    rwa [getElem!_pos l1 i h1, getElem!_pos l2 i h2] at this

theorem length_sbl (L : List U64) : (sbl L).length = 8 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [sbl, stateBytes, List.map_cons, List.flatMap_cons, List.length_append,
      BitVec.toLEBytes_length, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem sbl_testBit (L : List U64) (j t : Nat) (ht : t < 8) :
    (sbl L)[j]!.toNat.testBit t = (L[j / 8]!).bv[8 * (j % 8) + t]! := by
  rw [sbl, stateBytes, testBit_flatMap_toLEBytes _ _ _ ht]
  by_cases h : j / 8 < L.length
  · rw [getElem!_pos (L.map (·.bv)) (j / 8) (by simpa using h), getElem!_pos L _ h, List.getElem_map]
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
      List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- XORing `w` into lane `k` XORs into the state's bytes the bytes `B` that
`w` holds from byte `sh` of the lane on, zero elsewhere. -/
theorem sbl_set_xor (L : List U64) (k : Nat) (hk : k < L.length) (x : U64) (w : BitVec 64)
    (hx : x.bv = (L[k]!).bv ^^^ w) (sh : Nat) (B : List Byte) (hB : sh + B.length ≤ 8)
    (hw : ∀ m t, m < 8 → t < 8 → w[8 * m + t]! =
      if sh ≤ m ∧ m < sh + B.length then B[m - sh]!.toNat.testBit t else false) :
    sbl (L.set k x) = xorAt (sbl L) (8 * k + sh) B := by
  apply ext_getElem! (by simp [length_sbl])
  intro j hj
  rw [length_sbl, List.length_set] at hj
  rw [getElem!_xorAt _ _ _ _ (by rw [length_sbl]; omega)]
  apply Spec.Byte.ext_testBit
  intro t ht
  rw [sbl_testBit _ _ _ ht]
  by_cases hjk : j / 8 = k
  · rw [hjk, getElem!_pos _ k (by simpa using hk), List.getElem_set_self, hx, BitVec.getElem!_eq_testBit_toNat,
      BitVec.toNat_xor, Nat.testBit_xor, ← BitVec.getElem!_eq_testBit_toNat,
      ← BitVec.getElem!_eq_testBit_toNat, hw (j % 8) t (by omega) ht]
    have hc : (8 * k + sh ≤ j ∧ j < 8 * k + sh + B.length) ↔
        (sh ≤ j % 8 ∧ j % 8 < sh + B.length) := by omega
    by_cases hin : sh ≤ j % 8 ∧ j % 8 < sh + B.length
    · rw [ite_eq_left hin, ite_eq_left (hc.2 hin), testBit_xor_byte, sbl_testBit _ _ _ ht, hjk,
        show j - (8 * k + sh) = j % 8 - sh by omega]
    · rw [ite_eq_right hin, ite_eq_right (fun h => hin (hc.1 h)), sbl_testBit _ _ _ ht, hjk]
      simp
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjk),
      ← List.getElem!_eq_getElem?_getD, ite_eq_right (by omega), sbl_testBit _ _ _ ht]

/-! ## `partial_lane`, `add_bytes` -/

theorem toLEBytes_fromLEBytes (l : List Byte) (h : l.length = 8) :
    ((BitVec.fromLEBytes l).cast (by rw [h]) : BitVec 64).toLEBytes = l := by
  apply ext_getElem! (by simp [h])
  intro i hi
  simp only [BitVec.toLEBytes_length] at hi
  apply Spec.Byte.ext_testBit
  intro t ht
  have := BitVec.toLEBytes_getElem!_testBit ((BitVec.fromLEBytes l).cast (by rw [h]) : BitVec 64)
    i t ht
  simp only [Byte.testBit] at this
  rw [this, BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!,
    show (8 * i + t) / 8 = i by omega, show (8 * i + t) % 8 = t by omega]

/-- `partial_lane` puts `bytes` in a lane's low bytes. -/
theorem partial_lane_spec (bytes : Slice U8) (h : bytes.length ≤ 8) :
    mid.sha3.partial_lane bytes ⦃ r => ∀ m t, m < 8 → t < 8 →
      r.bv[8 * m + t]! = if m < bytes.length then (bv bytes.val)[m]!.toNat.testBit t else false ⦄ := by
  unfold mid.sha3.partial_lane
  step*
  intro m t hm ht
  have hfl := core.num.U64.from_le_bytes.step_spec (index_mut_back s1)
  simp only [lift, WP.spec_ok] at hfl
  rw [hfl, BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!, show (8 * m + t) / 8 = m by omega,
    show (8 * m + t) % 8 = t by omega, s_post2, s1_post]
  rw [getElem!_pos _ m (by simp [hm]), List.getElem_map, ← getElem!_pos]
  by_cases hmb : m < bytes.length
  · rw [ite_eq_left hmb, List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by simpa using hmb, by simp; omega⟩,
      bv, getElem!_pos _ m (by simpa using hmb), List.getElem_map, ← getElem!_pos]
    rfl
  · rw [ite_eq_right hmb, List.getElem!_setSlice!_suffix _ _ _ _ (by simp [Slice.length] at hmb ⊢; omega)]
    have hz : (Array.repeat 8#usize 0#u8).val[m]! = 0#u8 := by
      rw [getElem!_pos _ m (by simp [hm])]; interval_cases m <;> rfl
    rw [hz]; simp [Byte.testBit]

@[simp] theorem xorAt_nil (S : List Byte) (off : Nat) : xorAt S off [] = S := by
  apply ext_getElem! (by simp)
  intro i hi
  rw [getElem!_xorAt S off [] i (by simpa using hi), ite_eq_right (by simp)]

theorem getElem!_append_if {α : Type} [Inhabited α] (l1 l2 : List α) (i : Nat) :
    (l1 ++ l2)[i]! = if i < l1.length then l1[i]! else l2[i - l1.length]! := by
  simp only [List.getElem!_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega)]

/-- XORing two runs of bytes in turn, the second just after the first. -/
theorem xorAt_xorAt (S : List Byte) (off : Nat) (B1 B2 : List Byte) :
    xorAt (xorAt S off B1) (off + B1.length) B2 = xorAt S off (B1 ++ B2) := by
  apply ext_getElem! (by simp)
  intro i hi
  simp only [length_xorAt] at hi
  rw [getElem!_xorAt _ _ _ _ (by simpa using hi), getElem!_xorAt _ _ _ _ hi,
    getElem!_xorAt _ _ _ _ hi, getElem!_append_if, List.length_append]
  by_cases h1 : off ≤ i ∧ i < off + B1.length
  · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_right h1]
    by_cases h2 : off + B1.length ≤ i ∧ i < off + B1.length + B2.length
    · rw [ite_eq_left h2, ite_eq_left (by omega), ite_eq_right (by omega), show i - (off + B1.length) =
        i - off - B1.length by omega]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- XORing a second run, if any, just after the first. -/
theorem xorAt_xorAt' (S : List Byte) (off o2 : Nat) (B1 B2 : List Byte)
    (h : B2 ≠ [] → o2 = off + B1.length) :
    xorAt (xorAt S off B1) o2 B2 = xorAt S off (B1 ++ B2) := by
  by_cases hB : B2 = []
  · subst hB; simp
  · rw [h hB, xorAt_xorAt]

/-- `as_chunks`: chunk `i` is the `i`-th run of `N`, and the rest follows them. -/
theorem as_chunks_spec {T : Type} [Inhabited T] (N : Usize) (s : Slice T) (hN : 0 < N.val) :
    core.slice.Slice.as_chunks N s ⦃ c r =>
      c.val.length = s.length / N.val ∧
      (∀ i, i < c.val.length → (c.val[i]!).val = (s.val.drop (i * N.val)).take N.val) ∧
      r.val = s.val.drop (s.length / N.val * N.val) ⦄ := by
  simp only [core.slice.Slice.as_chunks, show ¬(N.val = 0) by omega, ↓reduceIte, WP.spec_ok]
  refine ⟨by simp, ?_, by simp⟩
  intro i hi
  simp only [Slice.from_val, List.length_ofFn] at hi
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem setSlice!_set {α : Type} [Inhabited α] (L w : List α) (first c : Nat) (x : α)
    (_h : first + w.length ≤ L.length) (hc : c < w.length) :
    L.setSlice! first (w.set c x) = (L.setSlice! first w).set (first + c) x := by
  apply ext_getElem! (by simp)
  intro j hj
  simp only [List.length_setSlice!] at hj
  rw [List.getElem!_eq_getElem?_getD (l := (L.setSlice! first w).set (first + c) x),
    List.getElem?_set]
  by_cases hjc : first + c = j
  · subst hjc
    rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by simp; omega, by omega⟩]
    simp [show first + c - first = c by omega, hc, hj]
  · rw [ite_eq_right hjc, ← List.getElem!_eq_getElem?_getD]
    by_cases hin : first ≤ j ∧ j < first + w.length
    · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨hin.1, by simp; omega, hj⟩,
        List.getElem!_setSlice!_middle _ _ _ _ ⟨hin.1, by omega, hj⟩,
        List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega),
        ← List.getElem!_eq_getElem?_getD]
    · rw [List.getElem!_setSlice!_same _ _ _ _ (by simp; omega),
        List.getElem!_setSlice!_same _ _ _ _ (by omega)]

theorem setSlice!_slice {α : Type} [Inhabited α] (L : List α) (a b : Nat) (h : a ≤ b ∧ b ≤ L.length) :
    L.setSlice! a (L.slice a b) = L := by
  apply ext_getElem! (by simp)
  intro j hj
  simp only [List.length_setSlice!] at hj
  by_cases hin : a ≤ j ∧ j < b
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨hin.1, by simp [List.slice]; omega, hj⟩]
    simp only [List.slice, List.getElem!_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ite_eq_left (by omega), show a + (j - a) = j by omega]
  · rw [List.getElem!_setSlice!_same _ _ _ _ (by simp [List.slice]; omega)]

/-- The whole lanes' loop of `add_bytes` XORs lane `i` of `P` into state lane
`first + i`, through the view `L.setSlice! first`. -/
theorem add_bytes_loop_spec (L : List U64) (hL : L.length = 25) (first nl : Nat)
    (hfirst : first + nl ≤ 25) (P : List U8) (hP : 8 * nl ≤ P.length)
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Std.Array U8 8#usize)))
    (hsl : iter.iter.slice.val.length = nl)
    (hel : ∀ i, i < nl → (iter.iter.slice.val[i]!).val = (P.drop (8 * i)).take 8)
    (hi : iter.iter.i = iter.count.val) (hk : iter.count.val ≤ nl)
    (w : Slice U64) (hw : w.length = nl)
    (hst : sbl (L.setSlice! first w.val) = xorAt (sbl L) (8 * first) (bv (P.take (8 * iter.count.val)))) :
    mid.sha3.add_bytes_loop iter w ⦃ w' =>
      w'.length = nl ∧ sbl (L.setSlice! first w'.val) = xorAt (sbl L) (8 * first) (bv (P.take (8 * nl))) ⦄ := by
  unfold mid.sha3.add_bytes_loop
  apply loop.spec_decr_nat (fun x => nl - x.1.count.val)
    (fun x => x.1.iter.slice.val.length = nl ∧
      (∀ i, i < nl → (x.1.iter.slice.val[i]!).val = (P.drop (8 * i)).take 8) ∧
      x.1.iter.i = x.1.count.val ∧ x.1.count.val ≤ nl ∧ x.2.length = nl ∧
      sbl (L.setSlice! first x.2.val) = xorAt (sbl L) (8 * first) (bv (P.take (8 * x.1.count.val))))
  · rintro ⟨it, w⟩ ⟨hsl, hel, hi, hk, hw, hst⟩
    simp only at hsl hel hi hk hw hst ⊢
    unfold mid.sha3.add_bytes_loop.body
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next]
    split
    · rename_i hlt
      have hlt' : it.count.val < nl := by
        have : it.iter.slice.len.val = nl := by simp [Slice.len, hsl]
        omega
      step*
      have hc : it.iter.slice[it.iter.i] = it.iter.slice.val[it.count.val]! := by
        rw [getElem!_pos _ _ (by omega)]; simp only [hi]; rfl
      have hwl : w.val.length = nl := hw
      have hcl : ∀ a : Std.Array U8 8#usize, (bv a.val).length = 8 := fun a => by simp [bv]
      refine ⟨hsl, hel, by omega, by omega, by simp [s_post, Slice.length, hw], ?_, by omega⟩
      rw [s_post, Slice.set_val_eq, setSlice!_set _ _ _ _ _ (by rw [hL]; omega) (by omega),
        sbl_set_xor _ (first + it.count.val) (by simp [hL]; omega) i3 i1.bv
          (by refine i3_post1.trans ?_
              rw [i2_post, List.getElem!_setSlice!_middle _ _ _ _
            ⟨by omega, by omega, by simp [hL]; omega⟩, show first + it.count.val - first =
            it.count.val by omega, getElem!_pos w.val _ (by omega)])
          0 (bv (it.iter.slice.val[it.count.val]!).val) (by rw [Nat.zero_add, hcl])
          (by
            intro m t hm ht
            rw [i1_post, hc, BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!,
              show (8 * m + t) / 8 = m by omega, show (8 * m + t) % 8 = t by omega,
              ite_eq_left ⟨Nat.zero_le _, by rw [Nat.zero_add, hcl]; omega⟩, Nat.sub_zero]
            rfl),
        hst, Nat.add_zero, show 8 * (first + it.count.val) = 8 * first + (bv (P.take (8 * it.count.val))).length by
          simp [bv]; omega,
        xorAt_xorAt, hel _ hlt', x_post, show 8 * (it.count.val + 1) = 8 * it.count.val + 8 by ring,
        List.take_add, bv, bv, bv, List.map_append]
    · rename_i hlt
      have hk' : it.count.val = nl := by
        have : it.iter.slice.len.val = nl := by simp [Slice.len, hsl]
        omega
      rw [hk'] at hst
      simpa [WP.spec_ok] using ⟨hw, hst⟩
  · exact ⟨hsl, hel, hi, hk, hw, hst⟩

/-- `add_bytes` XORs `bytes` into the state's bytes from `offset`. -/
theorem add_bytes_spec (s : Std.Array U64 25#usize) (off : Usize) (bytes : Slice U8)
    (h : off.val + bytes.length ≤ 200) :
    mid.sha3.add_bytes s off bytes ⦃ r => sbl r.val = xorAt (sbl s.val) off.val (bv bytes.val) ⦄ := by
  unfold mid.sha3.add_bytes
  step*
  have hlead : lead.val = min ((8 - off.val % 8) % 8) bytes.length := by
    rw [lead_post, core.cmp.impls.OrdUsize.min_val, i1_post, i_post, shift_post]; rfl
  have hbl : (bv bytes.val).length = bytes.length := by simp [bv, Slice.length]
  have hsl : s.val.length = 25 := by simp
  -- The head, up to the next lane boundary.
  have hhead : (if b = true then ok s else do
      let i3 ← mid.sha3.partial_lane head
      let i4 ← 8#usize * shift
      let i5 ← i3 <<< i4
      let i6 ← s.index_usize lane
      let i7 ← lift (i6 ^^^ i5)
      s.update lane i7) ⦃ s1 => sbl s1.val = xorAt (sbl s.val) off.val (bv head.val) ⦄ := by
    by_cases hb : b = true
    · have : head.val = [] := by
        have := b_post ▸ hb; simpa [Slice.length] using this
      simp [hb, this, bv, WP.spec_ok]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hne : head.length ≠ 0 := by intro h0; exact hb (b_post ▸ h0)
      have hsh : 0 < off.val % 8 := by
        by_contra h0; apply hne; rw [head_post, hlead]; simp; omega
      have hhl : head.length ≤ 8 - off.val % 8 := by rw [head_post, hlead]; omega
      step with partial_lane_spec head (by omega) as ⟨i3, hi3⟩
      step*
      have hhb : (bv head.val).length = head.length := by simp [bv, Slice.length]
      have hx7 : i7.bv = (s.val[lane.val]!).bv ^^^ i5.bv := by
        simp only [i7_post1, i6_post, getElem!_pos s.val lane.val (by omega)]
      have hw5 : ∀ m t, m < 8 → t < 8 → i5.bv[8 * m + t]! =
          if shift.val ≤ m ∧ m < shift.val + (bv head.val).length then
            (bv head.val)[m - shift.val]!.toNat.testBit t else false := by
        intro m t hm ht
        simp only [i5_post1, i4_post]
        by_cases hm' : shift.val ≤ m
        · rw [BitVec.getElem!_shiftLeft_eq _ _ _ ⟨by omega, by omega⟩,
            show 8 * m + t - 8 * shift.val = 8 * (m - shift.val) + t by omega,
            hi3 (m - shift.val) t (by omega) ht, hhb]
          by_cases hc : m - shift.val < head.length
          · rw [ite_eq_left hc, ite_eq_left ⟨hm', by omega⟩]
          · rw [ite_eq_right hc, ite_eq_right (by omega)]
        · rw [BitVec.getElem!_shiftLeft_false _ _ _ (Or.inl (by omega)), ite_eq_right (by omega)]
      rw [s1_post, Std.Array.set_val_eq, sbl_set_xor s.val lane.val (by omega) i7 i5.bv hx7
        shift.val (bv head.val) (by omega) hw5, show 8 * lane.val + shift.val = off.val by omega]
  step with hhead as ⟨s1, hs1⟩
  have hdc : core.num.Usize.div_ceil off 8#usize ⦃ r => r.val = (off.val + 7) / 8 ⦄ := by
    simp [core.num.Usize.div_ceil, WP.spec_ok]
  step with hdc as ⟨first, hfirst⟩
  step with as_chunks_spec 8#usize bytes1 (by decide) as ⟨lanes, tail, hll, hle, htail⟩
  have hs1l : s1.val.length = 25 := by simp
  have hll' : lanes.val.length = bytes1.length / 8 := by simpa using hll
  have hal : bytes1.length ≠ 0 → off.val + lead.val = 8 * first.val := by
    intro hne; rw [hfirst, hlead]; omega
  have hfl : first.val + lanes.val.length ≤ 25 := by
    by_cases hb1 : bytes1.length = 0
    · rw [hll', hb1]; omega
    · have := hal hb1; rw [hll']; omega
  step*
  have hwl : whole.length = lanes.val.length := by rw [whole_post1, i4_post]; simp [Slice.len]
  have hst0 : sbl (s1.val.setSlice! first.val whole.val) =
      xorAt (sbl s1.val) (8 * first.val) (bv (bytes1.val.take (8 * (0#usize : Usize).val))) := by
    rw [whole_post, setSlice!_slice _ _ _ (by rw [i4_post]; simp [Slice.len]; omega)]
    simp [bv]
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
  have hP : 8 * lanes.val.length ≤ bytes1.val.length := by
    rw [hll']; simp only [Slice.length]; omega
  step with add_bytes_loop_spec s1.val hs1l first.val lanes.val.length hfl bytes1.val hP
    { iter := { slice := lanes, i := 0 }, count := 0#usize } rfl (by
      intro i hi; rw [hle i hi, Nat.mul_comm]) rfl (by simp) whole hwl
    hst0 as ⟨w1, hw1l, hw1⟩
  have hhl : (bv head.val).length = lead.val := by simp [bv, ← head_post, Slice.length]
  have hTl : (bv (bytes1.val.take (8 * lanes.val.length))).length = 8 * lanes.val.length := by
    rw [bv, List.length_map, List.length_take]; omega
  have hcomb : sbl (index_mut_back w1).val =
      xorAt (sbl s.val) off.val (bv head.val ++ bv (bytes1.val.take (8 * lanes.val.length))) := by
    rw [whole_post2, hw1, hs1, xorAt_xorAt' _ _ _ _ _ (by
      intro hne
      have : bytes1.length ≠ 0 := by
        intro h0; apply hne; simp [bv, Slice.length] at h0 ⊢; simp [h0]
      rw [hhl, hal this])]
  have htl : tail.val.length = bytes1.length - 8 * lanes.val.length := by
    rw [htail, hll']; simp only [Slice.length]; simp; omega
  have hsplit : bv bytes.val = bv head.val ++ bv (bytes1.val.take (8 * lanes.val.length)) ++ bv tail.val := by
    rw [htail, hll', head_post2, head_post3, show bytes1.length / 8 * 8 = 8 * (bytes1.length / 8) by ring]
    simp only [bv, ← List.map_append, List.append_assoc, List.take_append_drop]
  step*
  · have ht0 : tail.val = [] := by
      have := b1_post ▸ (by assumption : b1 = true); simpa [Slice.length] using this
    rw [hcomb, hsplit, ht0]; simp [bv]
  · have hne : tail.length ≠ 0 := by
      intro h0; apply (by assumption : ¬b1 = true); exact b1_post ▸ h0
    step with partial_lane_spec tail (by simp only [Slice.length] at hne ⊢; omega) as ⟨i6, hi6⟩
    step*
    have hi8 : i8.val = first.val + lanes.val.length := by rw [i8_post]; simp [Slice.len]
    have htl' : tail.length = tail.val.length := rfl
    have hb1ne : bytes1.length ≠ 0 := by omega
    have hal' := hal hb1ne
    have hk : i8.val < 25 := by rw [hi8, hll']; omega
    have hx : i10.bv = ((index_mut_back w1).val[i8.val]!).bv ^^^ i6.bv := by
      simp only [i10_post1, i9_post, getElem!_pos (index_mut_back w1).val i8.val (by simp; omega)]
    have hbt : (bv tail.val).length = tail.length := by simp [bv, Slice.length]
    have hw : ∀ m t, m < 8 → t < 8 → i6.bv[8 * m + t]! =
        if 0 ≤ m ∧ m < 0 + (bv tail.val).length then (bv tail.val)[m - 0]!.toNat.testBit t
        else false := by
      intro m t hm ht
      rw [hi6 m t hm ht, hbt, Nat.zero_add, Nat.sub_zero]
      by_cases hc : m < tail.length
      · rw [ite_eq_left hc, ite_eq_left ⟨Nat.zero_le _, hc⟩]
      · rw [ite_eq_right hc, ite_eq_right (by omega)]
    rw [r_post, Std.Array.set_val_eq, sbl_set_xor _ i8.val (by simp; omega) i10 i6.bv hx 0
      (bv tail.val) (by rw [hbt]; omega) hw, hcomb, xorAt_xorAt' _ _ _ _ _ (fun _ => by
        simp only [List.length_append, hhl, hTl]; omega), hsplit, List.append_assoc]

/-! ## `store_bytes` -/

theorem getElem!_sbl (L : List U64) (j : Nat) :
    (sbl L)[j]! = (L[j / 8]!).bv.toLEBytes[j % 8]! := by
  apply Spec.Byte.ext_testBit
  intro t ht
  rw [sbl_testBit _ _ _ ht]
  have := BitVec.toLEBytes_getElem!_testBit (L[j / 8]!).bv (j % 8) t ht
  simp only [Byte.testBit] at this
  rw [this]

theorem getElem!_bv (l : List U8) (j : Nat) : (bv l)[j]! = (l[j]!).bv := by
  simp only [bv, List.getElem!_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

/-- `store_bytes` writes the state's first bytes. -/
theorem store_bytes_spec (s : Std.Array U64 25#usize) (output : Slice U8) (h : output.length ≤ 200) :
    mid.sha3.store_bytes s output ⦃ r =>
      r.length = output.length ∧ bv r.val = (sbl s.val).take output.length ⦄ := by
  unfold mid.sha3.store_bytes mid.sha3.store_bytes_loop
  apply loop.spec_decr_nat (fun x => output.length - x.2.val)
    (fun x => x.1.length = output.length ∧ x.2.val ≤ output.length ∧
      (x.2.val % 8 = 0 ∨ x.2.val = output.length) ∧
      ∀ j, j < x.2.val → (bv x.1.val)[j]! = (sbl s.val)[j]!)
  · rintro ⟨out, done⟩ ⟨hl, hd, hd8, hpre⟩
    simp only at hl hd hd8 hpre ⊢
    unfold mid.sha3.store_bytes_loop.body
    have hlen : out.len.val = output.length := by rw [← hl]; rfl
    have hol : out.val.length = output.length := hl
    have hoL : output.length = output.val.length := rfl
    have hs25 : s.val.length = 25 := by simp
    simp only []
    split
    · rename_i hlt
      have hdl : done.val < output.length := by
        have : done.val < out.len.val := hlt
        omega
      step*
      · rw [s1_post1, s2_post1, i3_post]
        omega
      · have hn : n.val = min 8 (output.length - done.val) := by
          rw [n_post, core.cmp.impls.OrdUsize.min_val, i2_post, hlen]; rfl
        have hd0 : done.val % 8 = 0 := by omega
        refine ⟨by rw [s1_post2]; simp [hl], by omega, by omega, ?_, by omega⟩
        intro j hj
        rw [s1_post2, Slice.setSlice!_val, s3_post]
        by_cases hjd : j < done.val
        · rw [getElem!_bv, List.getElem!_setSlice!_prefix _ _ _ _ hjd, ← getElem!_bv, hpre j hjd]
        · have hs2l : s2.val.length = n.val := s2_post1
          have hi5 : s.val[i4.val]! = i5 := by rw [i5_post, getElem!_pos s.val i4.val (by omega)]
          rw [getElem!_bv, List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by omega⟩,
            s2_post, getElem!_sbl, show j / 8 = i4.val by omega, show j % 8 = j - done.val by omega,
            hi5]
          simp only [List.slice, List.drop_zero, Array.val_to_slice, a_post]
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
            List.getElem?_map, List.getElem?_eq_getElem (by simp; omega),
            List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
          rfl
    · rename_i hnd
      have hdl : done.val = output.length := by
        have : ¬ done.val < out.len.val := hnd
        omega
      simp only [WP.spec_ok]
      refine ⟨hl, ?_⟩
      apply ext_getElem! (by
        rw [bv, List.length_map, List.length_take, length_sbl, hs25]; omega)
      intro j hj
      rw [bv, List.length_map] at hj
      rw [hpre j (by omega), List.getElem!_eq_getElem?_getD (l := List.take _ _), List.getElem?_take,
        ite_eq_left (by omega), ← List.getElem!_eq_getElem?_getD]
  · exact ⟨rfl, by simp, by simp, by simp⟩

/-! ## Keccak-f on the state's bytes -/

theorem length_stateBytes (L : List (BitVec 64)) : (stateBytes L).length = 8 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [stateBytes, List.flatMap_cons, List.length_append, BitVec.toLEBytes_length,
      List.length_cons] at ih ⊢
    rw [ih]; ring

theorem stateLanes_stateBytes (L : List (BitVec 64)) (hL : L.length = 25) :
    stateLanes (stateBytes L) = L := by
  apply List.ext_getElem (by simp [stateLanes, hL])
  intro i h1 h2
  simp only [stateLanes, List.getElem_map]
  rw [BitVec.eq_iff]
  intro p hp
  rw [BitVec.getElem!_setWidth _ _ _ hp, BitVec.fromLEBytes_getElem!, List.getElem!_eq_getElem?_getD,
    List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop, ← List.getElem!_eq_getElem?_getD]
  have := testBit_flatMap_toLEBytes L (8 * i + p / 8) (p % 8) (by omega)
  rw [← stateBytes] at this
  simp only [Byte.testBit, List.getElem_range]
  rw [this, show (8 * i + p / 8) / 8 = i by omega, show 8 * ((8 * i + p / 8) % 8) + p % 8 = p by omega,
    getElem!_pos L i (by omega)]

theorem keccakF_sbl (a r : Std.Array U64 25#usize) (h : lanes r = keccak 24 (lanes a)) :
    sbl r.val = keccakF (sbl a.val) := by
  rw [keccakF, sbl, stateLanes_stateBytes _ (by simp)]
  exact congrArg stateBytes h

@[simp] theorem length_sbl_array (a : Std.Array U64 25#usize) : (sbl a.val).length = 200 := by
  rw [length_sbl]; simp

/-! ## Squeezing, `SqueezingSponge::squeeze` -/

theorem div_block (R c k : Nat) (_hR : 0 < R) (h1 : R * c ≤ k) (h2 : k < R * c + R) :
    k / R = c ∧ k % R = k - R * c := by
  have hd : k / R = c := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; exact h1
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; exact h2
  refine ⟨hd, ?_⟩
  have := Nat.mod_add_div k R
  rw [hd] at this
  omega

theorem iterate_keccakF_succ (c : Nat) (S : List Byte) :
    keccakF^[c] (keccakF S) = keccakF^[c + 1] S := by
  rw [Function.iterate_succ_apply]

theorem ceil_div_eq (R L c : Nat) (hR : 0 < R) (h1 : L ≤ R * c) (h2 : c = 0 ∨ R * (c - 1) < L) :
    (L + R - 1) / R = c := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; rw [Nat.mul_zero] at h1
    rw [show L = 0 by omega]; exact Nat.div_eq_of_lt (by omega)
  · have h2' : R * (c - 1) < L := by rcases h2 with h2 | h2 <;> omega
    have key : R * (c - 1) + R = R * c := by
      rw [← Nat.mul_succ]; congr 1; omega
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega

/-- The squeeze loop: block `c` of the output after `c + 1` Keccak-fs. -/
theorem squeeze_loop_spec (h : RunsSha3) {R : Usize} (hR : 0 < R.val ∧ R.val ≤ 200) (S0 : List Byte)
    (L : Nat) (self : mid.sha3.SqueezingSponge R) (output : Slice U8) (done : Usize) (c : Nat)
    (hl : output.length = L) (hd : done.val = min (R.val * c) L) (hc : c = 0 ∨ R.val * (c - 1) < L)
    (hs : sbl self.s.val = keccakF^[c] S0)
    (hpre : ∀ k, k < done.val → (bv output.val)[k]! = (keccakF^[k / R.val + 1] S0)[k % R.val]!) :
    mid.sha3.SqueezingSponge.squeeze_loop self output done ⦃ r =>
      r.2.length = L ∧
      (∀ k, k < L → (bv r.2.val)[k]! = (keccakF^[k / R.val + 1] S0)[k % R.val]!) ∧
      sbl r.1.s.val = keccakF^[(L + R.val - 1) / R.val] S0 ⦄ := by
  unfold mid.sha3.SqueezingSponge.squeeze_loop
  apply loop.spec_decr_nat (fun x => L - x.2.2.val)
    (fun x => ∃ c, x.2.1.length = L ∧ x.2.2.val = min (R.val * c) L ∧ (c = 0 ∨ R.val * (c - 1) < L) ∧
      sbl x.1.s.val = keccakF^[c] S0 ∧
      ∀ k, k < x.2.2.val → (bv x.2.1.val)[k]! = (keccakF^[k / R.val + 1] S0)[k % R.val]!)
  · rintro ⟨self, out, done⟩ ⟨c, hl, hd, hc, hs, hpre⟩
    simp only at hl hd hc hs hpre ⊢
    unfold mid.sha3.SqueezingSponge.squeeze_loop.body
    have hlen : out.len.val = L := by rw [← hl]; rfl
    have hol : out.val.length = L := hl
    simp only []
    split
    · rename_i hlt
      have hdl : done.val < L := by
        have : done.val < out.len.val := hlt
        omega
      have hdc : done.val = R.val * c := by
        rcases Nat.le_total (R.val * c) L with h' | h' <;> simp [h'] at hd <;> omega
      step as ⟨i2, i2_post, i2_post1⟩
      step as ⟨n, n_post⟩
      have hn : n.val = min R.val (L - done.val) := by
        rw [n_post, core.cmp.impls.OrdUsize.min_val, i2_post, hlen]
      step with keccak_f1600_spec h self.s as ⟨a, ha⟩
      have hsa : sbl a.val = keccakF^[c + 1] S0 := by
        rw [keccakF_sbl self.s a ha, hs, Function.iterate_succ_apply']
      step as ⟨i3, hi3⟩
      step as ⟨sl, back, hsl, hsll, hback⟩
      step with store_bytes_spec a sl (by rw [hsll]; omega) as ⟨s1, hs1l, hs1⟩
      have hRc : R.val * (c + 1) = R.val * c + R.val := Nat.mul_succ _ _
      refine ⟨⟨c + 1, by rw [hback]; simp [hl], by rw [hi3, hn, hRc]; omega,
        Or.inr (by rw [Nat.add_sub_cancel]; omega), hsa, ?_⟩, by omega⟩
      intro k hk
      rw [hback, Slice.setSlice!_val]
      by_cases hkd : k < done.val
      · rw [getElem!_bv, List.getElem!_setSlice!_prefix _ _ _ _ hkd, ← getElem!_bv, hpre k hkd]
      · have hs1v : s1.val.length = sl.length := hs1l
        rw [getElem!_bv, List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by omega⟩,
          ← getElem!_bv, hs1, List.getElem!_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
          ← List.getElem!_eq_getElem?_getD, hsa]
        obtain ⟨hk1, hk2⟩ := div_block R.val c k hR.1 (by omega) (by omega)
        rw [hk1, hk2, hdc]
    · rename_i hnd
      have hdl : done.val = L := by
        have : ¬ done.val < out.len.val := hnd
        omega
      simp only [WP.spec_ok]
      refine ⟨hl, by rw [← hdl]; exact hpre, ?_⟩
      rw [hs, ceil_div_eq R.val L c hR.1 (by omega) hc]
  · exact ⟨c, hl, hd, hc, hs, hpre⟩

/-- `squeeze` writes FIPS 202's output from a state owing its Keccak-f, and
leaves the state as many Keccak-fs on as it took blocks. -/
theorem squeeze_spec (h : RunsSha3) {R : Usize} (hR : 0 < R.val ∧ R.val ≤ 200)
    (self : mid.sha3.SqueezingSponge R) (output : Slice U8) :
    mid.sha3.SqueezingSponge.squeeze self output ⦃ r =>
      r.2.length = output.length ∧
      bv r.2.val = squeeze R.val output.length (keccakF (sbl self.s.val)) ∧
      sbl r.1.s.val = keccakF^[(output.length + R.val - 1) / R.val] (sbl self.s.val) ⦄ := by
  unfold mid.sha3.SqueezingSponge.squeeze
  step with sha3_assert_held_spec h
  apply WP.spec_mono (squeeze_loop_spec h hR (sbl self.s.val) output.length self output 0#usize 0
    rfl (by simp) (Or.inl rfl) (by simp) (by simp))
  rintro r ⟨h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  apply ext_getElem! (by simp [bv, squeeze]; exact h1)
  intro k hk
  rw [bv, List.length_map] at hk
  have hk' : k < output.length := by rw [← h1]; exact hk
  rw [h2 k hk', squeeze, getElem!_pos _ k (by simp; omega), List.getElem_map, List.getElem_range,
    iterate_keccakF_succ]

/-- Squeezing on: the output past `c` whole blocks is the output of the state
`c` Keccak-fs on. -/
theorem squeeze_append (R c n : Nat) (hR : 0 < R) (T : List Byte) :
    squeeze R (R * c + n) T = squeeze R (R * c) T ++ squeeze R n (keccakF^[c] T) := by
  apply ext_getElem! (by simp [squeeze])
  intro k hk
  simp only [squeeze, List.length_map, List.length_range] at hk
  rw [getElem!_append_if]
  simp only [squeeze, List.length_map, List.length_range]
  by_cases hkc : k < R * c
  · rw [ite_eq_left hkc, getElem!_pos _ k (by simp; omega), getElem!_pos _ k (by simp; omega)]
    simp
  · rw [ite_eq_right hkc, getElem!_pos _ k (by simp; omega), getElem!_pos _ (k - R * c) (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [← Function.iterate_add_apply]
    have h1 : k / R = (k - R * c) / R + c := by
      conv_lhs => rw [show k = (k - R * c) + R * c by omega]
      rw [Nat.add_mul_div_left _ _ hR]
    have h2 : k % R = (k - R * c) % R := by
      conv_lhs => rw [show k = (k - R * c) + R * c by omega]
      exact Nat.add_mul_mod_self_left _ _ _
    rw [h1, h2]

/-! ## Absorbing, `Sponge::absorb` -/

/-- The all-zero state. -/
abbrev zeros : List Byte := List.replicate 200 0

theorem blocks_single (R : Nat) (hR : 0 < R) (B : List Byte) (hB : B.length = R) :
    rind.spec.blocks R B = [B] := by
  rw [blocks_eq_map R hR, hB, Nat.div_self hR]
  simp [← hB]

theorem blocks_short (R : Nat) (hR : 0 < R) (r : List Byte) (hr : r.length < R) :
    rind.spec.blocks R r = [] := by
  rw [blocks_eq_map R hR, Nat.div_eq_of_lt hr]
  rfl

theorem absorb_append_block (R : Nat) (hR : 0 < R) (S P B : List Byte) (hP : P.length % R = 0)
    (hB : B.length = R) : absorb R S (P ++ B) = keccakF (xorAt (absorb R S P) 0 B) := by
  simp only [absorb]
  rw [blocks_append hR _ _ hP, blocks_single R hR B hB, List.foldl_append]
  rfl

theorem absorb_append_short (R : Nat) (hR : 0 < R) (S P r : List Byte) (hP : P.length % R = 0)
    (hr : r.length < R) : absorb R S (P ++ r) = absorb R S P := by
  simp only [absorb]
  rw [blocks_append hR _ _ hP, blocks_short R hR r hr, List.append_nil]

/-- A sponge state that has absorbed `m`: its whole blocks `P` permuted in, and
the `used` bytes after them XORed in. -/
def SpongeAbsorbed (R : Nat) (s : Std.Array U64 25#usize) (used : Nat) (m : List Byte) : Prop :=
  ∃ P r, m = P ++ r ∧ P.length % R = 0 ∧ r.length < R ∧ used = r.length ∧
    sbl s.val = xorAt (absorb R zeros P) 0 r

theorem sbl_zero : sbl (Std.Array.repeat 25#usize 0#u64).val = zeros := by
  apply ext_getElem! (by simp [length_sbl])
  intro j hj
  rw [length_sbl] at hj; simp at hj
  apply Spec.Byte.ext_testBit
  intro t ht
  rw [sbl_testBit _ _ _ ht, getElem!_pos zeros j (by simp; omega), List.getElem_replicate]
  have : (Std.Array.repeat 25#usize 0#u64).val[j / 8]! = 0#u64 := by
    have hr : (Std.Array.repeat 25#usize 0#u64).val = List.replicate 25 0#u64 := rfl
    rw [hr, getElem!_pos _ (j / 8) (by simp; omega), List.getElem_replicate]
  rw [this]
  simp

/-- `Sponge::new` has absorbed nothing. -/
theorem sponge_new_spec (R : Usize) (hR : 0 < R.val) (PAD : U8) :
    mid.sha3.Sponge.new R PAD ⦃ sp => SpongeAbsorbed R.val sp.s sp.used.val [] ⦄ := by
  unfold mid.sha3.Sponge.new
  simp only [WP.spec_ok]
  refine ⟨[], [], rfl, by simp, by simpa using hR, rfl, ?_⟩
  rw [sbl_zero]
  simp [absorb, blocks_nil]

/-- The absorb loop permutes in block after block. -/
theorem absorb_loop_spec (h : RunsSha3) {R : Usize} (hR : 0 < R.val ∧ R.val ≤ 200) (m1 : List Byte)
    (hm1 : m1.length % R.val = 0) (P : List U8) (nb : Nat) (hP : R.val * nb ≤ P.length)
    (iter : core.slice.iter.Iter (Std.Array U8 R)) (hsl : iter.slice.val.length = nb)
    (hel : ∀ i, i < nb → (iter.slice.val[i]!).val = (P.drop (i * R.val)).take R.val)
    (hi : iter.i ≤ nb) (a : Std.Array U64 25#usize)
    (ha : sbl a.val = absorb R.val zeros (m1 ++ bv (P.take (iter.i * R.val)))) :
    mid.sha3.Sponge.absorb_loop iter a ⦃ r =>
      sbl r.val = absorb R.val zeros (m1 ++ bv (P.take (nb * R.val))) ⦄ := by
  unfold mid.sha3.Sponge.absorb_loop
  apply loop.spec_decr_nat (fun x => nb - x.1.i)
    (fun x => x.1.slice.val.length = nb ∧
      (∀ i, i < nb → (x.1.slice.val[i]!).val = (P.drop (i * R.val)).take R.val) ∧ x.1.i ≤ nb ∧
      sbl x.2.val = absorb R.val zeros (m1 ++ bv (P.take (x.1.i * R.val))))
  · rintro ⟨it, a⟩ ⟨hsl, hel, hi, ha⟩
    simp only at hsl hel hi ha ⊢
    unfold mid.sha3.Sponge.absorb_loop.body
    simp only [core.slice.iter.IteratorSliceIter.next]
    split
    · rename_i hlt
      have hlt' : it.i < nb := by
        have : it.i < it.slice.len.val := hlt
        simpa [Slice.len, hsl] using this
      have hblk : (it.slice[it.i]'hlt).val = (P.drop (it.i * R.val)).take R.val := by
        rw [← hel it.i hlt', getElem!_pos it.slice.val it.i (by omega)]; rfl
      have hbl : (it.slice[it.i]'hlt).val.length = R.val := by simp
      simp only [bind_ok]
      step as ⟨sl, hsl'⟩
      step with add_bytes_spec a 0#usize sl (by simp [Slice.length, hsl', hbl]; omega) as ⟨a1, ha1⟩
      step with keccak_f1600_spec h a1 as ⟨a2, ha2⟩
      refine ⟨hsl, hel, by omega, ?_, by omega⟩
      have hRi : R.val * (it.i + 1) ≤ P.length := by
        have := Nat.mul_le_mul_left R.val (show it.i + 1 ≤ nb by omega); omega
      have hRi' : it.i * R.val + R.val ≤ P.length := by
        rw [show it.i * R.val + R.val = R.val * (it.i + 1) by ring]; exact hRi
      rw [keccakF_sbl a1 a2 ha2, ha1, ha,
        ← absorb_append_block R.val hR.1 _ _ _ (by
          rw [List.length_append, bv, List.length_map, List.length_take,
            Nat.min_eq_left (by omega), Nat.add_mod, hm1, Nat.mul_mod_left]; simp)
        (by simp [bv, hsl', hbl]),
        hsl', Array.val_to_slice, hblk, List.append_assoc, bv, bv, bv, ← List.map_append,
        ← List.take_add, show it.i * R.val + R.val = (it.i + 1) * R.val by ring]
    · rename_i hnd
      have hi' : it.i = nb := by
        have : ¬ it.i < it.slice.len.val := hnd
        simp [Slice.len, hsl] at this; omega
      rw [← hi']
      simpa [WP.spec_ok] using ha
  · exact ⟨hsl, hel, hi, ha⟩

/-- `Sponge::absorb` absorbs `bytes` after what the sponge has absorbed. -/
theorem sponge_absorb_spec (h : RunsSha3) {R : Usize} {PAD : U8} (hR : 0 < R.val ∧ R.val ≤ 200)
    (sp : mid.sha3.Sponge R PAD) (m : List Byte) (hm : SpongeAbsorbed R.val sp.s sp.used.val m)
    (bytes : Slice U8) :
    mid.sha3.Sponge.absorb sp bytes ⦃ sp' =>
      SpongeAbsorbed R.val sp'.s sp'.used.val (m ++ bv bytes.val) ⦄ := by
  obtain ⟨P0, r0, hm, hP0, hr0, hu, hs⟩ := hm
  have hbl : (bv bytes.val).length = bytes.length := by simp [bv, Slice.length]
  unfold mid.sha3.Sponge.absorb
  step as ⟨room, hroom⟩
  split
  · rename_i hlt
    have hlt' : bytes.length < room.val := hlt
    step with add_bytes_spec sp.s sp.used bytes (by omega) as ⟨a, ha⟩
    step as ⟨u, hu'⟩
    refine ⟨P0, r0 ++ bv bytes.val, by rw [hm, List.append_assoc], hP0,
      by rw [List.length_append, hbl]; omega, by rw [hu', List.length_append, hbl, hu]; rfl, ?_⟩
    rw [ha, hs, hu, ← xorAt_xorAt, Nat.zero_add]
  · rename_i hge
    have hge' : room.val ≤ bytes.length := by
      have : ¬ bytes.len.val < room.val := hge
      exact Nat.le_of_not_lt this
    step with sha3_new_secret_spec h as ⟨e⟩
    step as ⟨head, bytes1, hhl, hb1l, hhv, hb1v⟩
    step with add_bytes_spec sp.s sp.used head (by omega) as ⟨a, ha⟩
    step with keccak_f1600_spec h a as ⟨a1, ha1⟩
    have hhb : (bv head.val).length = room.val := by simp [bv, Slice.length] at hhl ⊢; exact hhl
    have hblk : (r0 ++ bv head.val).length = R.val := by
      rw [List.length_append, hhb]; omega
    have hsa1 : sbl a1.val = absorb R.val zeros (P0 ++ (r0 ++ bv head.val)) := by
      rw [keccakF_sbl a a1 ha1, ha, hs, hu, xorAt_xorAt' _ 0 _ _ _ (fun _ => by simp),
        absorb_append_block R.val hR.1 _ _ _ hP0 hblk]
    step with as_chunks_spec R bytes1 hR.1 as ⟨blocks, rest, hnb, hbe, hrest⟩
    step as ⟨iter, hit, hit0⟩
    have hm1 : (P0 ++ (r0 ++ bv head.val)).length % R.val = 0 := by
      rw [List.length_append, hblk, Nat.add_mod, hP0, Nat.mod_self]; simp
    have hnbR : R.val * blocks.val.length ≤ bytes1.val.length := by
      rw [hnb, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    step with absorb_loop_spec h hR _ hm1 bytes1.val blocks.val.length hnbR iter
      (by rw [hit]) (by rw [hit]; exact hbe) (by omega) a1 (by rw [hit0, hsa1]; simp [bv])
      as ⟨a2, ha2⟩
    have hrl : rest.val.length < R.val := by
      have e1 := Nat.div_add_mod' bytes1.length R.val
      have e2 := Nat.mod_lt bytes1.length hR.1
      have e3 : bytes1.val.length = bytes1.length := rfl
      rw [hrest, List.length_drop]; omega
    step with add_bytes_spec a2 0#usize rest (by simp [Slice.length]; omega) as ⟨a3, ha3⟩
    refine ⟨P0 ++ (r0 ++ bv head.val) ++ bv (bytes1.val.take (blocks.val.length * R.val)),
      bv rest.val, ?_, ?_, by simpa [bv] using hrl, by simp [bv, Slice.len], ?_⟩
    · rw [hm, hrest, hhv, hb1v, hnb]
      simp only [bv, List.append_assoc]
      rw [← List.map_append, ← List.map_append, List.take_append_drop, List.take_append_drop]
    · have hT : (bv (bytes1.val.take (blocks.val.length * R.val))).length =
          blocks.val.length * R.val := by
        rw [bv, List.length_map, List.length_take]
        exact Nat.min_eq_left (by rw [Nat.mul_comm]; exact hnbR)
      rw [List.length_append, hT, Nat.add_mod, hm1, Nat.mul_mod_left]; simp
    · rw [ha3, ha2]

/-! ## Padding, `Sponge::padded_state` -/

theorem getElem!_replicate_zero (n k : Nat) : (List.replicate n (0 : Byte))[k]! = 0 := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- The last block's padding XORed into the state is the message's tail, the
pad byte after it, and the top bit of the block's last byte, in turn. -/
theorem xorAt_keccakPad (R : Nat) (hR : 0 < R ∧ R ≤ 200) (d : Byte) (A r : List Byte)
    (hA : A.length = 200) (hr : r.length < R) :
    xorAt A 0 (keccakPad R d r) = xorAt (xorAt (xorAt A 0 r) r.length [d]) (R - 1) [0x80] := by
  have hK : (keccakPad R d r).length = R := by
    rw [length_keccakPad R hR.1, Nat.mod_eq_of_lt hr]; omega
  apply ext_getElem! (by simp)
  intro i hi
  simp only [length_xorAt] at hi
  rw [getElem!_xorAt _ _ _ _ hi, getElem!_xorAt _ _ _ _ (by simp; omega),
    getElem!_xorAt _ _ _ _ (by simp; omega), getElem!_xorAt _ _ _ _ hi, hK]
  have hY : ∀ k, (r ++ d :: List.replicate (R - r.length - 1) 0)[k]! =
      if k < r.length then r[k]! else if k = r.length then d else 0 := by
    intro k
    rw [getElem!_append_if]
    split
    · rfl
    · split
      · rename_i h; rw [h, Nat.sub_self]; rfl
      · rw [show k - r.length = (k - r.length - 1) + 1 by omega, List.getElem!_cons_succ,
          getElem!_replicate_zero]
  have hKi : ∀ k, k < R → (keccakPad R d r)[k]! =
      if k = R - 1 then (r ++ d :: List.replicate (R - r.length - 1) 0)[k]! ^^^ 0x80
      else (r ++ d :: List.replicate (R - r.length - 1) 0)[k]! := by
    intro k hk
    simp only [keccakPad, Nat.mod_eq_of_lt hr]
    rw [getElem!_xorAt _ _ _ _ (by simp; omega)]
    by_cases h' : k = R - 1
    · rw [ite_eq_left ⟨by omega, by simp; omega⟩, ite_eq_left h',
        show k - (r.length + (R - r.length) - 1) = 0 by omega,
        show R - r.length - 1 = R - r.length - 1 from rfl]
      rfl
    · rw [ite_eq_right (by simp; omega), ite_eq_right h']
  have e1 : (r.length ≤ i ∧ i < r.length + 1) ↔ i = r.length := by omega
  have e2 : (R - 1 ≤ i ∧ i < R - 1 + 1) ↔ i = R - 1 := by omega
  by_cases hiR : i < R
  · simp only [List.length_singleton, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, e1, e2,
      hiR, ite_true]
    rw [hKi i hiR, hY]
    split_ifs <;> subst_vars <;> simp_all [BitVec.xor_assoc]
  · simp only [List.length_singleton, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, e1, e2,
      hiR, ite_false]
    split_ifs <;> first | omega | rfl

theorem xorAt_append_left (X Y : List Byte) (o : Nat) (B : List Byte) :
    xorAt (X ++ Y) (X.length + o) B = X ++ xorAt Y o B := by
  apply ext_getElem! (by simp)
  intro i hi
  simp only [length_xorAt, List.length_append] at hi
  rw [getElem!_xorAt (X ++ Y) (X.length + o) B i (by simp; omega),
    getElem!_append_if X (xorAt Y o B) i, getElem!_append_if X Y i]
  by_cases h : i < X.length
  · simp only [h, ite_true]
    rw [ite_eq_right (by omega)]
  · simp only [h, ite_false]
    rw [getElem!_xorAt Y o B (i - X.length) (by omega)]
    by_cases h2 : X.length + o ≤ i ∧ i < X.length + o + B.length
    · rw [ite_eq_left h2, ite_eq_left (show o ≤ i - X.length ∧ i - X.length < o + B.length by omega),
        show i - (X.length + o) = i - X.length - o by omega]
    · rw [ite_eq_right h2, ite_eq_right (show ¬(o ≤ i - X.length ∧ i - X.length < o + B.length) by omega)]

theorem keccakPad_append (R : Nat) (hR : 0 < R) (d : Byte) (P r : List Byte) (hP : P.length % R = 0)
    (hr : r.length < R) : keccakPad R d (P ++ r) = P ++ keccakPad R d r := by
  have hm : (P ++ r).length % R = r.length % R := by
    rw [List.length_append, Nat.add_mod, hP, Nat.zero_add, Nat.mod_mod]
  simp only [keccakPad, hm, List.append_assoc]
  rw [List.length_append, Nat.add_assoc, Nat.add_sub_assoc (by rw [Nat.mod_eq_of_lt hr]; omega),
    xorAt_append_left, Nat.add_sub_assoc (by rw [Nat.mod_eq_of_lt hr]; omega)]

theorem length_absorb (R : Nat) (S P : List Byte) (hS : S.length = 200) :
    (absorb R S P).length = 200 := by
  simp only [absorb]
  generalize rind.spec.blocks R P = l
  induction l generalizing S with
  | nil => exact hS
  | cons x l ih => rw [List.foldl_cons]; exact ih _ (by simp)

/-- The padded message's absorbing ends on the last block's padding. -/
theorem absorb_keccakPad (R : Nat) (hR : 0 < R ∧ R ≤ 200) (d : Byte) (P r : List Byte)
    (hP : P.length % R = 0) (hr : r.length < R) :
    absorb R zeros (keccakPad R d (P ++ r)) =
      keccakF (xorAt (xorAt (xorAt (absorb R zeros P) 0 r) r.length [d]) (R - 1) [0x80]) := by
  rw [keccakPad_append R hR.1 d P r hP hr, absorb_append_block R hR.1 _ _ _ hP (by
      rw [length_keccakPad R hR.1, Nat.mod_eq_of_lt hr]; omega),
    xorAt_keccakPad R hR d _ r (length_absorb R _ P (by simp)) hr]

/-- `padded_state` is the state whose Keccak-f ends absorbing the padded message. -/
theorem padded_state_spec {R : Usize} {PAD : U8} (hR : 8 ≤ R.val ∧ R.val < 200 ∧ R.val % 8 = 0)
    (sp : mid.sha3.Sponge R PAD) (m : List Byte) (hm : SpongeAbsorbed R.val sp.s sp.used.val m) :
    mid.sha3.Sponge.padded_state sp ⦃ s =>
      keccakF (sbl s.val) = absorb R.val zeros (keccakPad R.val PAD.bv m) ⦄ := by
  obtain ⟨P, r, rfl, hP, hr, hu, hs⟩ := hm
  unfold mid.sha3.Sponge.padded_state
  step as ⟨sl, hsl⟩
  have hsl' : sl.val = [PAD] := by rw [hsl]; rfl
  step with add_bytes_spec sp.s sp.used sl (by simp [Slice.length, hsl']; omega) as ⟨s1, hs1⟩
  step*
  have hi2 : i2.val < 25 := by omega
  have hx : i4.bv = (s1.val[i2.val]!).bv ^^^ i.bv := by
    simp only [i4_post1, i3_post, getElem!_pos s1.val i2.val (by simp; omega)]
  have hw : ∀ m t, m < 8 → t < 8 → i.bv[8 * m + t]! =
      if 7 ≤ m ∧ m < 7 + [(0x80 : Byte)].length then [(0x80 : Byte)][m - 7]!.toNat.testBit t
      else false := by
    intro m t hm ht
    simp only [i_post1]
    interval_cases m <;> interval_cases t <;> rfl
  have hbv : bv sl.val = [PAD.bv] := by rw [hsl']; rfl
  rw [s_post, Std.Array.set_val_eq, sbl_set_xor _ i2.val (by simp; omega) i4 i.bv hx 7 [0x80]
    (by simp) hw, hs1, hs, hu, hbv, absorb_keccakPad R.val ⟨by omega, by omega⟩ PAD.bv P r hP hr,
    show 8 * i2.val + 7 = R.val - 1 by omega]

/-! ## SHA-3, `Sha3Context` -/

/-- A SHA-3 context that has hashed `m`. -/
def Sha3Hashed {R OUT : Usize} (c : mid.sha3.Sha3Context R OUT) (m : List U8) : Prop :=
  SpongeAbsorbed R.val c.sponge.s c.sponge.used.val (bv m)

/-- `Sha3Context::new` has hashed nothing. -/
theorem sha3ctx_new_spec (R OUT : Usize) (hR : R.val = 200 - 2 * OUT.val) (hR0 : 0 < R.val) :
    mid.sha3.Sha3Context.new R OUT ⦃ c => Sha3Hashed c [] ⦄ := by
  unfold mid.sha3.Sha3Context.new
  step*
  all_goals try scalar_tac
  step with sponge_new_spec R hR0 6#u8 as ⟨sp, hsp⟩
  exact hsp

/-- `update` adds `bytes` to what the context has hashed. -/
theorem sha3ctx_update_spec (h : RunsSha3) {R OUT : Usize} (hR : 0 < R.val ∧ R.val ≤ 200)
    (c : mid.sha3.Sha3Context R OUT) (m : List U8) (hc : Sha3Hashed c m) (bytes : Slice U8) :
    mid.sha3.Sha3Context.update c bytes ⦃ c' => Sha3Hashed c' (m ++ bytes.val) ⦄ := by
  unfold mid.sha3.Sha3Context.update
  step with sponge_absorb_spec h hR c.sponge (bv m) hc bytes as ⟨sp, hsp⟩
  simpa [Sha3Hashed, bv] using hsp

/-- `finish` is FIPS 202's sponge on what the context has hashed. -/
theorem sha3ctx_finish_spec (h : RunsSha3) {R OUT : Usize}
    (hR : 8 ≤ R.val ∧ R.val < 200 ∧ R.val % 8 = 0) (c : mid.sha3.Sha3Context R OUT) (m : List U8)
    (hc : Sha3Hashed c m) :
    mid.sha3.Sha3Context.finish c ⦃ d => bv d.val = sponge R.val sha3Pad (bv m) OUT.val ⦄ := by
  unfold mid.sha3.Sha3Context.finish
  step with padded_state_spec hR c.sponge (bv m) hc as ⟨a, ha⟩
  simp only [mid.sha3.SqueezingSponge.new, bind_ok]
  step with Std.Array.to_slice_mut_spec (Array.repeat OUT 0#u8) as ⟨sl, back, hsl, hback⟩
  step with squeeze_spec (R := R) h ⟨by omega, by omega⟩ { s := a } sl as ⟨ss, out, hol, hout, _⟩
  have hsll : sl.length = OUT.val := by simp [Slice.length, hsl]
  rw [hback, Std.Array.from_slice_val _ _ (by rw [← hsll]; exact hol), hout, hsll]
  simp only [ha, sponge]
  rfl

/-! ## The digest API, `high::digest`, through the modelled dispatch -/

/-- What each SHA-3 algorithm of the digest API computes. -/
def sha3Family : high.digest.Algorithm → Option (List Byte → List Byte)
  | .SHA3_256 => some sha3_256
  | .SHA3_384 => some sha3_384
  | .SHA3_512 => some sha3_512
  | _ => none

/-- A digest context of `algorithm`, a SHA-3, that has hashed `m`. -/
def Sha3ContextHashed (c : high.digest.Context) (algorithm : high.digest.Algorithm) (m : List U8) :
    Prop :=
  match c, algorithm with
  | .Sha3_256 hs, .SHA3_256 => Sha3Hashed hs.context m
  | .Sha3_384 hs, .SHA3_384 => Sha3Hashed hs.context m
  | .Sha3_512 hs, .SHA3_512 => Sha3Hashed hs.context m
  | _, _ => False

/-- `Context::new` starts a context that has hashed nothing. -/
theorem sha3_context_new (algorithm : high.digest.Algorithm) (f : List Byte → List Byte)
    (hf : sha3Family algorithm = some f) :
    high.digest.Context.new algorithm ⦃ c => Sha3ContextHashed c algorithm [] ⦄ := by
  cases algorithm <;> simp only [sha3Family, reduceCtorEq] at hf <;>
    simp only [high.digest.Context.new, high.digest.Algorithm.start, high.digest.Hashing.start]
  · simp only [high.digest.Sha3_256Context.Insts.RindHighDigestVariant.NEW,
      high.digest.Sha3_256Context.Insts.RindHighDigestVariant.state]
    step with sha3ctx_new_spec 136#usize 32#usize rfl (by decide) as ⟨c, hc⟩
    simpa [Sha3ContextHashed] using hc
  · simp only [high.digest.Sha3_384Context.Insts.RindHighDigestVariant.NEW,
      high.digest.Sha3_384Context.Insts.RindHighDigestVariant.state]
    step with sha3ctx_new_spec 104#usize 48#usize rfl (by decide) as ⟨c, hc⟩
    simpa [Sha3ContextHashed] using hc
  · simp only [high.digest.Sha3_512Context.Insts.RindHighDigestVariant.NEW,
      high.digest.Sha3_512Context.Insts.RindHighDigestVariant.state]
    step with sha3ctx_new_spec 72#usize 64#usize rfl (by decide) as ⟨c, hc⟩
    simpa [Sha3ContextHashed] using hc

/-- `Context::update` adds `data` to what the context has hashed. -/
theorem sha3_context_update (h : RunsSha3) (c : high.digest.Context)
    (algorithm : high.digest.Algorithm) (m : List U8) (data : Slice U8)
    (hc : Sha3ContextHashed c algorithm m) :
    high.digest.Context.update c data ⦃ c' => Sha3ContextHashed c' algorithm (m ++ data.val) ⦄ := by
  unfold high.digest.Context.update high.digest.State.update high.digest.Hashing.update
  cases c <;> cases algorithm <;> simp only [Sha3ContextHashed] at hc ⊢
  · simp only [high.digest.Sha3_256Context.Insts.RindHighHashHashContext.update]
    step with sha3ctx_update_spec h (by decide) _ _ hc data as ⟨c', hc'⟩
    simpa [Sha3ContextHashed] using hc'
  · simp only [high.digest.Sha3_384Context.Insts.RindHighHashHashContext.update]
    step with sha3ctx_update_spec h (by decide) _ _ hc data as ⟨c', hc'⟩
    simpa [Sha3ContextHashed] using hc'
  · simp only [high.digest.Sha3_512Context.Insts.RindHighHashHashContext.update]
    step with sha3ctx_update_spec h (by decide) _ _ hc data as ⟨c', hc'⟩
    simpa [Sha3ContextHashed] using hc'

/-- `Context::finish` returns the digest of what the context has hashed, and
leaves the context as `Context::new` makes it. -/
theorem sha3_context_finish (h : RunsSha3) (c : high.digest.Context)
    (algorithm : high.digest.Algorithm) (f : List Byte → List Byte)
    (hf : sha3Family algorithm = some f) (m : List U8) (hc : Sha3ContextHashed c algorithm m) :
    (do
      let (d, c) ← high.digest.Context.finish c
      let b ← high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d
      ok (b, c)) ⦃ r => bv r.1.val = f (bv m) ∧ Sha3ContextHashed r.2 algorithm [] ⦄ := by
  unfold high.digest.Context.finish high.digest.State.finish high.digest.Hashing.finish
  step with sha3_new_secret_spec h as ⟨e⟩
  cases c <;> cases algorithm <;>
    simp only [Sha3ContextHashed, sha3Family, Option.some.injEq] at hc hf ⊢ <;> subst hf
  · simp only [high.digest.Sha3_256Context.Insts.RindHighHashHashContext.finish, high.digest.SHA3_256, bind_ok]
    step with sha3ctx_finish_spec h (by decide) _ _ hc as ⟨d, hd⟩
    step as ⟨sl, hsl⟩
    have hl : sl.length = 32 := by simp [hsl]
    step with digest_new_as_ref' .SHA3_256 sl 32#usize rfl (by simp [hl]) (by simp [hl]) as ⟨dg, hdg⟩
    simp only [high.digest.Sha3_256Context.Insts.RindHighDigestVariant.NEW]
    step with sha3ctx_new_spec 136#usize 32#usize rfl (by decide) as ⟨c0, hc0⟩
    step with hdg as ⟨b, hb⟩
    refine ⟨?_, by simpa using hc0⟩
    rw [hb, hsl, Array.val_to_slice, hd]
    rfl
  · simp only [high.digest.Sha3_384Context.Insts.RindHighHashHashContext.finish, high.digest.SHA3_384, bind_ok]
    step with sha3ctx_finish_spec h (by decide) _ _ hc as ⟨d, hd⟩
    step as ⟨sl, hsl⟩
    have hl : sl.length = 48 := by simp [hsl]
    step with digest_new_as_ref' .SHA3_384 sl 48#usize rfl (by simp [hl]) (by simp [hl]) as ⟨dg, hdg⟩
    simp only [high.digest.Sha3_384Context.Insts.RindHighDigestVariant.NEW]
    step with sha3ctx_new_spec 104#usize 48#usize rfl (by decide) as ⟨c0, hc0⟩
    step with hdg as ⟨b, hb⟩
    refine ⟨?_, by simpa using hc0⟩
    rw [hb, hsl, Array.val_to_slice, hd]
    rfl
  · simp only [high.digest.Sha3_512Context.Insts.RindHighHashHashContext.finish, high.digest.SHA3_512, bind_ok]
    step with sha3ctx_finish_spec h (by decide) _ _ hc as ⟨d, hd⟩
    step as ⟨sl, hsl⟩
    have hl : sl.length = 64 := by simp [hsl]
    step with digest_new_as_ref' .SHA3_512 sl 64#usize rfl (by simp [hl]) (by simp [hl]) as ⟨dg, hdg⟩
    simp only [high.digest.Sha3_512Context.Insts.RindHighDigestVariant.NEW]
    step with sha3ctx_new_spec 72#usize 64#usize rfl (by decide) as ⟨c0, hc0⟩
    step with hdg as ⟨b, hb⟩
    refine ⟨?_, by simpa using hc0⟩
    rw [hb, hsl, Array.val_to_slice, hd]
    rfl

/-- Updating a context with each chunk in turn adds their concatenation. -/
theorem sha3_context_updates (h : RunsSha3) (algorithm : high.digest.Algorithm)
    (chunks : List (Slice U8)) (c : high.digest.Context) (m : List U8)
    (hc : Sha3ContextHashed c algorithm m) :
    chunks.foldlM high.digest.Context.update c ⦃ c' =>
      Sha3ContextHashed c' algorithm (m ++ chunks.flatMap (·.val)) ⦄ := by
  induction chunks generalizing c m with
  | nil =>
    show (ok c : Result _) ⦃ c' => Sha3ContextHashed c' algorithm (m ++ []) ⦄
    simpa [WP.spec_ok] using hc
  | cons x xs ih =>
    simp only [List.foldlM_cons, List.flatMap_cons]
    step with sha3_context_update h c algorithm m x hc as ⟨c', hc'⟩
    apply WP.spec_mono (ih c' _ hc')
    intro r hr
    simpa [List.append_assoc] using hr

/-- SHA-3 through a context: `Context::new`, an `update` with each of `chunks`
in turn, and `finish` return FIPS 202's hash of their concatenation, for a
message of any length, and leave the context fresh. -/
theorem sha3_family_context (h : RunsSha3) (algorithm : high.digest.Algorithm)
    (f : List Byte → List Byte) (hf : sha3Family algorithm = some f) (chunks : List (Slice U8)) :
    (do
      let c ← high.digest.Context.new algorithm
      let c ← chunks.foldlM high.digest.Context.update c
      let (d, c) ← high.digest.Context.finish c
      let b ← high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d
      ok (b, c)) ⦃ r =>
      bv r.1.val = f (bv (chunks.flatMap (·.val))) ∧ Sha3ContextHashed r.2 algorithm [] ⦄ := by
  step with sha3_context_new algorithm f hf as ⟨c, hc⟩
  step with sha3_context_updates h algorithm chunks c [] hc as ⟨c', hc'⟩
  simpa using sha3_context_finish h c' algorithm f hf _ hc'

/-- The digest API's SHA-3 algorithms hash as FIPS 202 does, in SymCrypt's spec. -/
theorem sha3Family_fips202 :
    sha3Family .SHA3_256 = some (fun M => (Spec.SHA3.sha3_256 (toB M)).toList) ∧
    sha3Family .SHA3_384 = some (fun M => (Spec.SHA3.sha3_384 (toB M)).toList) ∧
    sha3Family .SHA3_512 = some (fun M => (Spec.SHA3.sha3_512 (toB M)).toList) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [sha3Family, Option.some.injEq] <;> funext M
  · exact sha3_256_eq M
  · exact sha3_384_eq M
  · exact sha3_512_eq M

/-- SHA-3 in one call: `digest`'s bytes are FIPS 202's hash of `data`. -/
theorem sha3_family_digest (h : RunsSha3) (algorithm : high.digest.Algorithm)
    (f : List Byte → List Byte) (hf : sha3Family algorithm = some f) (data : Slice U8) :
    (do
      let d ← high.digest.digest algorithm data
      high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d) ⦃ b =>
      bv b.val = f (bv data.val) ⦄ := by
  unfold high.digest.digest high.digest.Algorithm.hash high.digest.one_shot
  step with sha3_new_secret_spec h as ⟨e⟩
  cases algorithm <;> simp only [sha3Family, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  · simp only [high.digest.Sha3_256Context.Insts.RindHighDigestVariant.NEW,
      high.digest.Sha3_256Context.Insts.RindHighHashHashContext.update,
      high.digest.Sha3_256Context.Insts.RindHighHashHashContext.finish, high.digest.SHA3_256, bind_ok]
    step with sha3ctx_new_spec 136#usize 32#usize rfl (by decide) as ⟨c0, hc0⟩
    step with sha3ctx_update_spec h (by decide) _ _ hc0 data as ⟨c1, hc1⟩
    step with sha3ctx_finish_spec h (by decide) _ _ hc1 as ⟨d, hd⟩
    step as ⟨sl, hsl⟩
    have hl : sl.length = 32 := by simp [hsl]
    apply WP.spec_mono (digest_new_as_ref .SHA3_256 sl 32#usize rfl (by simp [hl]) (by simp [hl]))
    intro b hb
    rw [hb, hsl, Array.val_to_slice, hd, List.nil_append]
    rfl
  · simp only [high.digest.Sha3_384Context.Insts.RindHighDigestVariant.NEW,
      high.digest.Sha3_384Context.Insts.RindHighHashHashContext.update,
      high.digest.Sha3_384Context.Insts.RindHighHashHashContext.finish, high.digest.SHA3_384, bind_ok]
    step with sha3ctx_new_spec 104#usize 48#usize rfl (by decide) as ⟨c0, hc0⟩
    step with sha3ctx_update_spec h (by decide) _ _ hc0 data as ⟨c1, hc1⟩
    step with sha3ctx_finish_spec h (by decide) _ _ hc1 as ⟨d, hd⟩
    step as ⟨sl, hsl⟩
    have hl : sl.length = 48 := by simp [hsl]
    apply WP.spec_mono (digest_new_as_ref .SHA3_384 sl 48#usize rfl (by simp [hl]) (by simp [hl]))
    intro b hb
    rw [hb, hsl, Array.val_to_slice, hd, List.nil_append]
    rfl
  · simp only [high.digest.Sha3_512Context.Insts.RindHighDigestVariant.NEW,
      high.digest.Sha3_512Context.Insts.RindHighHashHashContext.update,
      high.digest.Sha3_512Context.Insts.RindHighHashHashContext.finish, high.digest.SHA3_512, bind_ok]
    step with sha3ctx_new_spec 72#usize 64#usize rfl (by decide) as ⟨c0, hc0⟩
    step with sha3ctx_update_spec h (by decide) _ _ hc0 data as ⟨c1, hc1⟩
    step with sha3ctx_finish_spec h (by decide) _ _ hc1 as ⟨d, hd⟩
    step as ⟨sl, hsl⟩
    have hl : sl.length = 64 := by simp [hsl]
    apply WP.spec_mono (digest_new_as_ref .SHA3_512 sl 64#usize rfl (by simp [hl]) (by simp [hl]))
    intro b hb
    rw [hb, hsl, Array.val_to_slice, hd, List.nil_append]
    rfl

/-! ## SHAKE, as ML-KEM calls it

`Sponge::finish` and `SqueezingSponge::squeeze` serve ML-KEM's J (SHAKE256),
`SqueezingSponge4xShake128` its matrix sampling (SHAKE128, four at once), and
`shake256_batch` its CBD sampling (SHAKE256, up to four at once). `shake128_eq`
and `shake256_eq` restate each as FIPS 202's. -/

/-- A sponge that has squeezed `k` blocks of FIPS 202's sponge at rate `R` on
`M` padded with `d`: the Keccak-f it owes yields block `k`. -/
def Squeezing {R : Usize} (s : mid.sha3.SqueezingSponge R) (d : Byte) (M : List Byte) (k : Nat) :
    Prop :=
  keccakF (sbl s.s.val) = keccakF^[k] (absorb R.val zeros (keccakPad R.val d M))

/-- `Sponge::finish` has squeezed nothing of the sponge on what it absorbed. -/
theorem sponge_finish_spec {R : Usize} {PAD : U8} (hR : 8 ≤ R.val ∧ R.val < 200 ∧ R.val % 8 = 0)
    (sp : mid.sha3.Sponge R PAD) (m : List Byte) (hm : SpongeAbsorbed R.val sp.s sp.used.val m) :
    mid.sha3.Sponge.finish sp ⦃ ss => Squeezing ss PAD.bv m 0 ⦄ := by
  unfold mid.sha3.Sponge.finish
  step with padded_state_spec hR sp m hm as ⟨a, ha⟩
  simpa [mid.sha3.SqueezingSponge.new, WP.spec_ok, Squeezing] using ha

theorem length_squeeze (R n : Nat) (S : List Byte) : (squeeze R n S).length = n := by
  simp [squeeze]

/-- `SqueezingSponge::squeeze` writes the sponge's next bytes, and has then
squeezed each block it read from. -/
theorem squeezing_squeeze_spec (h : RunsSha3) {R : Usize} (hR : 0 < R.val ∧ R.val ≤ 200)
    (s : mid.sha3.SqueezingSponge R) (d : Byte) (M : List Byte) (k : Nat) (hs : Squeezing s d M k)
    (output : Slice U8) :
    mid.sha3.SqueezingSponge.squeeze s output ⦃ r =>
      r.2.length = output.length ∧
      bv r.2.val = (sponge R.val d M (R.val * k + output.length)).drop (R.val * k) ∧
      Squeezing r.1 d M (k + (output.length + R.val - 1) / R.val) ⦄ := by
  apply WP.spec_mono (squeeze_spec h hR s output)
  rintro ⟨s', out⟩ ⟨hl, hout, hst⟩
  unfold Squeezing at hs ⊢
  refine ⟨hl, ?_, ?_⟩
  · rw [hout, hs, sponge, squeeze_append _ _ _ hR.1, List.drop_left' (length_squeeze _ _ _)]
  · simp only at hst ⊢
    rw [hst, ← Function.iterate_succ_apply' keccakF, Function.iterate_succ_apply, hs,
      ← Function.iterate_add_apply, Nat.add_comm]

theorem xorAt_append_zeros (S : List Byte) (o : Nat) (B : List Byte) (k : Nat) :
    xorAt S o (B ++ List.replicate k 0) = xorAt S o B := by
  apply ext_getElem! (by simp)
  intro i hi
  simp only [length_xorAt] at hi
  rw [getElem!_xorAt _ _ _ _ hi, getElem!_xorAt _ _ _ _ hi, List.length_append,
    List.length_replicate, getElem!_append_if]
  by_cases h1 : o ≤ i ∧ i < o + B.length
  · rw [ite_eq_left ⟨h1.1, by omega⟩, ite_eq_left h1, ite_eq_left (by omega)]
  · rw [ite_eq_right h1]
    by_cases h2 : o ≤ i ∧ i < o + (B.length + k)
    · rw [ite_eq_left h2, ite_eq_right (by omega), getElem!_replicate_zero]; exact BitVec.xor_zero
    · rw [ite_eq_right h2]

/-- `padded_block` is the state whose Keccak-f absorbs `M`, of a single block,
which `input` holds before the pad byte `d` and zeros. -/
theorem padded_block_spec (R : Usize) (hR : 48 ≤ R.val ∧ R.val < 200 ∧ R.val % 8 = 0)
    (input : Std.Array U8 40#usize) (d : Byte) (M : List Byte) (hM : M.length < 40)
    (hin : bv input.val = M ++ d :: List.replicate (39 - M.length) 0) :
    mid.sha3.padded_block R input ⦃ s =>
      keccakF (sbl s.val) = absorb R.val zeros (keccakPad R.val d M) ⦄ := by
  unfold mid.sha3.padded_block
  step as ⟨sl, hsl⟩
  step with add_bytes_spec _ 0#usize sl (by simp [Slice.length, hsl]) as ⟨s1, hs1⟩
  step*
  have hi2 : i2.val < 25 := by omega
  have hx : i4.bv = (s1.val[i2.val]!).bv ^^^ i.bv := by
    simp only [i4_post1, i3_post, getElem!_pos s1.val i2.val (by simp; omega)]
  have hw : ∀ m t, m < 8 → t < 8 → i.bv[8 * m + t]! =
      if 7 ≤ m ∧ m < 7 + [(0x80 : Byte)].length then [(0x80 : Byte)][m - 7]!.toNat.testBit t
      else false := by
    intro m t hm ht
    simp only [i_post1]
    interval_cases m <;> interval_cases t <;> rfl
  have h0 := absorb_keccakPad R.val ⟨by omega, by omega⟩ d [] M rfl (by omega)
  rw [List.nil_append] at h0
  rw [h0, s_post, Std.Array.set_val_eq, sbl_set_xor _ i2.val (by simp; omega) i4 i.bv hx 7 [0x80]
    (by simp) hw, hs1, hsl, Array.val_to_slice, hin, sbl_zero,
    show 8 * i2.val + 7 = R.val - 1 by omega, show d :: List.replicate (39 - M.length) 0 =
      [d] ++ List.replicate (39 - M.length) 0 from rfl, ← List.append_assoc, xorAt_append_zeros,
    ← xorAt_xorAt, Nat.zero_add]
  simp [absorb, blocks_nil]

theorem array_set_getElem! {α : Type} [Inhabited α] {n : Usize} (a : Std.Array α n) (i : Usize)
    (x : α) (j : Nat) (hi : i.val < a.length) :
    (a.set i x).val[j]! = if j = i.val then x else a.val[j]! := by
  rw [Std.Array.set_val_eq, List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split
  · subst_vars; simp
  · rw [ite_eq_right (by omega), ← List.getElem!_eq_getElem?_getD]

/-- The byte after a message of `padded_block`'s input is its pad byte. -/
theorem pad_byte_at (input : Std.Array U8 40#usize) (d : Byte) (M : List Byte)
    (hin : bv input.val = M ++ d :: List.replicate (39 - M.length) 0) :
    (input.val[M.length]!).bv = d := by
  rw [← getElem!_bv, hin, getElem!_append_if]
  simp

theorem shake_pad_byte_eq : mid.sha3.SHAKE_PAD_BYTE = 31#u8 := by
  unfold mid.sha3.SHAKE_PAD_BYTE; rfl

/-- `states[j]` of a Keccak-f of four states is the Keccak-f of `a[j]`. -/
theorem sbl_states (a r : Std.Array (Std.Array U64 25#usize) 4#usize) (N : Nat)
    (h : (states r).take N = ((states a).take N).map (keccak 24)) (j : Nat) (hj : j < N)
    (hj4 : j < 4) : sbl (r.val[j]!).val = keccakF (sbl (a.val[j]!).val) := by
  apply keccakF_sbl
  have := congrArg (·[j]?) h
  simp only [List.getElem?_take, List.getElem?_map, ite_eq_left hj, states,
    List.getElem?_eq_getElem (show j < r.val.length by simp; omega),
    List.getElem?_eq_getElem (show j < a.val.length by simp; omega), Option.map_some,
    Option.some.injEq] at this
  rw [getElem!_pos r.val j (by simp; omega), getElem!_pos a.val j (by simp; omega), this]

/-! ### `SqueezingSponge4xShake128` -/

/-- ML-KEM's SHAKE128 inputs: messages `M j` of 34 bytes, padded. -/
def Shake128Inputs (inputs : Std.Array (Std.Array U8 40#usize) 4#usize) (M : Nat → List Byte) : Prop :=
  ∀ j < 4, (M j).length = 34 ∧
    bv (inputs.val[j]!).val = M j ++ shakePad :: List.replicate 5 0

/-- The state of SHAKE128 on `M` once absorbed. -/
abbrev shake128Absorbed (M : List Byte) : List Byte := absorb 168 zeros (keccakPad 168 shakePad M)

theorem shake128x4_new_loop_spec (M : Nat → List Byte)
    (inputs : Std.Array (Std.Array U8 40#usize) 4#usize) (hin : Shake128Inputs inputs M)
    (iter : core.ops.range.Range Usize) (a : Std.Array (Std.Array U64 25#usize) 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (ha : ∀ j < iter.start.val, keccakF (sbl (a.val[j]!).val) = shake128Absorbed (M j)) :
    mid.sha3.SqueezingSponge4xShake128.new_loop iter inputs a ⦃ r =>
      ∀ j < 4, keccakF (sbl (r.val[j]!).val) = shake128Absorbed (M j) ⦄ := by
  unfold mid.sha3.SqueezingSponge4xShake128.new_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      ∀ j < x.1.start.val, keccakF (sbl (x.2.val[j]!).val) = shake128Absorbed (M j))
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold mid.sha3.SqueezingSponge4xShake128.new_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      obtain ⟨hl, hj⟩ := hin it.start.val (by omega)
      step as ⟨x, hx⟩
      have hx' : bv x.val = M it.start.val ++ shakePad ::
          List.replicate (39 - (M it.start.val).length) 0 := by
        rw [hx, ← getElem!_pos inputs.val it.start.val (by simp; omega), hj, hl]
      step as ⟨i, hi⟩
      have hpad : i = mid.sha3.SHAKE_PAD_BYTE := by
        have hb := pad_byte_at x shakePad _ hx'
        rw [hl] at hb
        rw [hi, shake_pad_byte_eq, U8.eq_equiv_bv_eq, ← getElem!_pos x.val 34 (by simp)]
        exact hb
      step with massert_spec _ hpad
      step with padded_block_spec 168#usize (by decide) x shakePad (M it.start.val) (by omega) hx'
        as ⟨y, hy⟩
      step as ⟨a2, ha2⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro j hj'
      rw [ha2, array_set_getElem! _ _ _ _ (by simp; omega)]
      split
      · subst_vars; exact hy
      · exact hst j (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have hN' : it.start.val = 4 := by omega
      simpa [hN'] using hst
  · exact ⟨hs, he, ha⟩

/-- Four SHAKE128 sponges that have absorbed `M j` and squeezed `k` blocks:
state `j` yields block `k`. -/
def Shake128x4 (x : mid.sha3.SqueezingSponge4xShake128) (M : Nat → List Byte) (k : Nat) : Prop :=
  ∀ j < 4, sbl (x.states.val[j]!).val = keccakF^[k] (shake128Absorbed (M j))

/-- `SqueezingSponge4xShake128::new` absorbs four SHAKE128 inputs. -/
theorem shake128x4_new_spec (h : RunsSha3) (M : Nat → List Byte)
    (inputs : Std.Array (Std.Array U8 40#usize) 4#usize) (hin : Shake128Inputs inputs M) :
    mid.sha3.SqueezingSponge4xShake128.new inputs ⦃ x => Shake128x4 x M 0 ⦄ := by
  unfold mid.sha3.SqueezingSponge4xShake128.new
  step with shake128x4_new_loop_spec M inputs hin { start := 0#usize, «end» := 4#usize }
    (Std.Array.repeat 4#usize (Std.Array.repeat 25#usize 0#u64)) (by simp) (by simp)
    (fun j hj => absurd hj (by simp)) as ⟨a, ha⟩
  step with keccak4_f1600_spec h a as ⟨r, hr⟩
  intro j hj
  rw [Function.iterate_zero_apply, ← ha j hj]
  exact sbl_states a r 4 (by rw [hr, List.map_take]) j hj hj

theorem shake128_r_bytes : mid.sha3.SHAKE_128_R_BYTES ⦃ r => r.val = 168 ⦄ := by
  unfold mid.sha3.SHAKE_128_R_BYTES; step*

theorem bv_setSlice! (L X : List U8) (i : Nat) : bv (L.setSlice! i X) = (bv L).setSlice! i (bv X) := by
  simp [List.setSlice!, bv, List.map_take, List.map_drop]

/-- Fewer bytes than a block squeezed are the state's first. -/
theorem squeeze_block (R n : Nat) (T : List Byte) (hn : n ≤ R) (hT : n ≤ T.length) :
    squeeze R n T = T.take n := by
  apply ext_getElem! (by simp [squeeze]; omega)
  intro k hk
  replace hk : k < n := by first | omega | simpa [squeeze] using hk
  rw [getElem!_pos _ k (by rw [length_squeeze]; omega), getElem!_pos _ k (by simp; omega)]
  simp only [squeeze, List.getElem_map, List.getElem_range, List.getElem_take]
  rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Function.iterate_zero_apply,
    getElem!_pos T k (by omega)]

/-- Each output's first `n` bytes are SHAKE128's on `M j`. -/
def Shake128Out (output : Std.Array (Std.Array U8 504#usize) 4#usize) (M : Nat → List Byte)
    (n : Nat → Nat) : Prop :=
  ∀ j < 4, (bv (output.val[j]!).val).take (n j) = squeeze 168 (n j) (shake128Absorbed (M j))

theorem shake128x4_squeeze_inner_spec (x : mid.sha3.SqueezingSponge4xShake128)
    (M : Nat → List Byte) (b : Usize) (hb : b.val < 3) (hx : Shake128x4 x M b.val)
    (iter : core.ops.range.Range Usize) (output : Std.Array (Std.Array U8 504#usize) 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (ho : Shake128Out output M fun j => 168 * b.val + if j < iter.start.val then 168 else 0) :
    mid.sha3.SqueezingSponge4xShake128.squeeze_loop0_loop0 iter x output b ⦃ r =>
      r.1 = x ∧ Shake128Out r.2 M fun _ => 168 * b.val + 168 ⦄ := by
  unfold mid.sha3.SqueezingSponge4xShake128.squeeze_loop0_loop0
  apply loop.spec_decr_nat (fun y => 4 - y.1.start.val)
    (fun y => y.1.start.val ≤ 4 ∧ y.1.end.val = 4 ∧
      Shake128Out y.2 M fun j => 168 * b.val + if j < y.1.start.val then 168 else 0)
  · rintro ⟨it, out⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold mid.sha3.SqueezingSponge4xShake128.squeeze_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      have hen' : it'.end.val = it.end.val := by rw [hen]
      step with shake128_r_bytes as ⟨i, hi⟩
      step as ⟨start, hstart⟩
      step as ⟨st, hst_⟩
      step as ⟨a1, back, ha1, hback⟩
      step as ⟨i1, hi1⟩
      step with Array.index_mut_SliceIndexRangeUsizeSlice.step a1 { start, «end» := i1 }
        (by simp only; scalar_tac) (by simp only; scalar_tac) as ⟨sl, back1, hsl, hsll, hback1⟩
      have hstart' : start.val = 168 * b.val := by rw [hstart, hi, Nat.mul_comm]
      have hsl168 : sl.length = 168 := by omega
      step with store_bytes_spec st sl (by omega) as ⟨s1, hs1l, hs1⟩
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro j hj
      rw [hback, array_set_getElem! _ _ _ _ (by simp; omega)]
      have hj' := hst j hj
      split
      · subst_vars
        rw [hst']
        simp only [show it.start.val < it.start.val + 1 by omega, ite_true,
          show ¬ it.start.val < it.start.val by omega, ite_false, Nat.add_zero] at hj' ⊢
        have hl : (bv s1.val).length = 168 := by
          simp only [bv, List.length_map]; rw [show s1.val.length = s1.length from rfl, hs1l]
          omega
        have hl' : (bv (out.val[it.start.val]'(by simp; omega)).val).length = 504 := by simp [bv]
        rw [hback1, bv_setSlice!, show (168 * b.val + 168) = start.val + (bv s1.val).length by omega,
          take_setSlice! _ _ _ (by rw [hl, hl']; omega), hstart',
          ← getElem!_pos out.val _ (by simp; omega), hj', hl, squeeze_append 168 b.val 168 (by omega),
          hs1, hsl168, ← hx it.start.val hj, squeeze_block 168 168 _ (le_refl _) (by simp),
          ← getElem!_pos x.states.val _ (by simp; omega)]
      · have e1 : (j < it'.start.val) = (j < it.start.val) := by
          apply propext; omega
        simp only [e1]
        exact hj'
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok, true_and]
      intro j hj
      have := hst j hj
      simp only [show j < it.start.val by omega, ite_true] at this
      exact this
  · exact ⟨hs, he, ho⟩

theorem shake128x4_squeeze_loop_spec (h : RunsSha3) (M : Nat → List Byte)
    (iter : core.ops.range.Range Usize) (x : mid.sha3.SqueezingSponge4xShake128)
    (output : Std.Array (Std.Array U8 504#usize) 4#usize)
    (hs : iter.start.val ≤ 3) (he : iter.end.val = 3) (hx : Shake128x4 x M (iter.start.val - 1))
    (ho : Shake128Out output M fun _ => 168 * iter.start.val) :
    mid.sha3.SqueezingSponge4xShake128.squeeze_loop0 iter x output ⦃ r =>
      Shake128x4 r.1 M 2 ∧ Shake128Out r.2 M fun _ => 504 ⦄ := by
  unfold mid.sha3.SqueezingSponge4xShake128.squeeze_loop0
  apply loop.spec_decr_nat (fun y => 3 - y.1.start.val)
    (fun y => y.1.start.val ≤ 3 ∧ y.1.end.val = 3 ∧ Shake128x4 y.2.1 M (y.1.start.val - 1) ∧
      Shake128Out y.2.2 M fun _ => 168 * y.1.start.val)
  · rintro ⟨it, st, out⟩ ⟨hs, he, hst, hout⟩
    simp only at hs he hst hout ⊢
    unfold mid.sha3.SqueezingSponge4xShake128.squeeze_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      have hen' : it'.end.val = it.end.val := by rw [hen]
      have ho0 : Shake128Out out M fun j =>
          168 * it.start.val + if j < (0#usize : Usize).val then 168 else 0 := by
        intro j hj; simpa using hout j hj
      have hfin : ∀ (st1 : mid.sha3.SqueezingSponge4xShake128)
          (out1 : Std.Array (Std.Array U8 504#usize) 4#usize), Shake128x4 st1 M it.start.val →
          (Shake128Out out1 M fun _ => 168 * it.start.val + 168) →
          (it'.start.val ≤ 3 ∧ it'.end.val = 3 ∧ Shake128x4 st1 M (it'.start.val - 1) ∧
            (Shake128Out out1 M fun _ => 168 * it'.start.val)) ∧ 3 - it'.start.val < 3 - it.start.val := by
        intro st1 out1 h1 h2
        refine ⟨⟨by omega, by omega, by rw [hst']; simpa using h1, ?_⟩, by omega⟩
        rw [hst', Nat.mul_succ]; exact h2
      by_cases hb0 : it.start > 0#usize
      · simp only [hb0, ↓reduceIte]
        step with keccak4_f1600_spec h st.states as ⟨r, hr⟩
        have hx1 : Shake128x4 { states := r } M it.start.val := by
          intro j hj
          simp only
          rw [sbl_states st.states r 4 (by rw [hr, List.map_take]) j hj hj, hst j hj,
            ← Function.iterate_succ_apply' keccakF, show (it.start.val - 1).succ = it.start.val by
              scalar_tac]
        step with shake128x4_squeeze_inner_spec _ M it.start (by omega) hx1 { start := 0#usize, «end» := 4#usize } out
          (by simp) (by simp)
          ho0 as ⟨st2, out2, hst2, hout2⟩
        subst hst2
        obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := hfin _ _ hx1 hout2
        exact ⟨a1, a2, a3, a4, a5⟩
      · simp only [hb0, ↓reduceIte]
        have h0 : it.start.val = 0 := by scalar_tac
        have hx1 : Shake128x4 st M it.start.val := by
          intro j hj; rw [hst j hj, h0]
        step with shake128x4_squeeze_inner_spec _ M it.start (by omega) hx1 { start := 0#usize, «end» := 4#usize } out
          (by simp) (by simp)
          ho0 as ⟨st2, out2, hst2, hout2⟩
        subst hst2
        obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := hfin _ _ hx1 hout2
        exact ⟨a1, a2, a3, a4, a5⟩
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      have h3 : it.start.val = 3 := by omega
      rw [h3] at hst hout
      exact ⟨hst, hout⟩
  · exact ⟨hs, he, hx, ho⟩

deriving instance Inhabited for mid.sha3.SqueezingSponge

theorem foldlM_ok_append {α β γ : Type} (g : β → γ) (L : List β) (acc : List γ) (f : α) :
    L.foldlM (m := Result) (fun p x => ok (p.1 ++ [g x], p.2)) (acc, f) = ok (acc ++ L.map g, f) := by
  induction L generalizing acc with
  | nil => simp; rfl
  | cons x L ih => simp [ih]

/-- Mapping `SqueezingSponge::new` over states wraps each. -/
theorem map_squeezing_new (R N : Usize) (a : Std.Array (Std.Array U64 25#usize) N) :
    core.array.Array.map (P.Insts.CoreOpsFunctionFnMutTupleArrayU6425SqueezingSponge R) a
      (mid.sha3.SqueezingSponge.new R) ⦃ r =>
        r.val = a.val.map fun s => ({ s } : mid.sha3.SqueezingSponge R) ⦄ := by
  unfold core.array.Array.map
  simp [P.Insts.CoreOpsFunctionFnMutTupleArrayU6425SqueezingSponge.call_mut,
    mid.sha3.SqueezingSponge.new]
  rw [foldlM_ok_append (fun x => ({ s := x } : mid.sha3.SqueezingSponge R)), bind_ok]
  simp [WP.spec_ok]

/-- `SqueezingSponge4xShake128::squeeze` writes the first 504 bytes of each
input's SHAKE128, and returns the sponges having squeezed those three blocks. -/
theorem shake128x4_squeeze_spec (h : RunsSha3) (x : mid.sha3.SqueezingSponge4xShake128)
    (M : Nat → List Byte) (hx : Shake128x4 x M 0)
    (output : Std.Array (Std.Array U8 504#usize) 4#usize) :
    mid.sha3.SqueezingSponge4xShake128.squeeze x output ⦃ r =>
      ∀ j < 4, bv (r.2.val[j]!).val = shake128 (M j) 504 ∧ Squeezing (r.1.val[j]!) shakePad (M j) 3 ⦄ := by
  unfold mid.sha3.SqueezingSponge4xShake128.squeeze
  step with shake128x4_squeeze_loop_spec h M { start := 0#usize, «end» := 3#usize } x output
    (by simp) (by simp) (by simpa using hx) (by intro j hj; simp [squeeze]) as ⟨st, out, hst, hout⟩
  step with map_squeezing_new _ _ st.states as ⟨a, ha⟩
  intro j hj
  refine ⟨?_, ?_⟩
  · have := hout j hj
    rw [List.take_of_length_le (by simp [bv])] at this
    rw [this]; rfl
  · unfold Squeezing
    rw [ha, getElem!_pos _ j (by simp; omega), List.getElem_map, ← getElem!_pos st.states.val j
      (by simp; omega), hst j hj, ← Function.iterate_succ_apply' keccakF]
    rfl

/-! ### `shake256_batch` -/

/-- ML-KEM's SHAKE256 inputs: messages `M j` of 33 bytes, padded. -/
def Shake256Inputs {P : Usize} (inputs : Std.Array (Std.Array U8 40#usize) P) (M : Nat → List Byte) :
    Prop :=
  ∀ j < P.val, (M j).length = 33 ∧ bv (inputs.val[j]!).val = M j ++ shakePad :: List.replicate 6 0

/-- The state of SHAKE256 on `M` once absorbed. -/
abbrev shake256Absorbed (M : List Byte) : List Byte := absorb 136 zeros (keccakPad 136 shakePad M)

theorem shake256_fill_spec {P : Usize} (inputs : Std.Array (Std.Array U8 40#usize) P)
    (M : Nat → List Byte) (hin : Shake256Inputs inputs M) (done : Usize) (n : Nat)
    (hn : n ≤ 4) (hdn : done.val + n ≤ P.val)
    (iter : core.ops.range.Range Usize) (a : Std.Array (Std.Array U64 25#usize) 4#usize)
    (hs : iter.start.val ≤ n) (he : iter.end.val = n)
    (ha : ∀ j < iter.start.val, keccakF (sbl (a.val[j]!).val) = shake256Absorbed (M (done.val + j))) :
    mid.sha3.shake256_batch_loop0_loop0 iter inputs a done ⦃ r =>
      ∀ j < n, keccakF (sbl (r.val[j]!).val) = shake256Absorbed (M (done.val + j)) ⦄ := by
  unfold mid.sha3.shake256_batch_loop0_loop0
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => x.1.start.val ≤ n ∧ x.1.end.val = n ∧
      ∀ j < x.1.start.val, keccakF (sbl (x.2.val[j]!).val) = shake256Absorbed (M (done.val + j)))
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold mid.sha3.shake256_batch_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      have hen' : it'.end.val = it.end.val := by rw [hen]
      obtain ⟨hl, hj⟩ := hin (done.val + it.start.val) (by omega)
      step as ⟨k, hk⟩
      step as ⟨x, hx⟩
      have hx' : bv x.val = M (done.val + it.start.val) ++ shakePad ::
          List.replicate (39 - (M (done.val + it.start.val)).length) 0 := by
        rw [hx, ← getElem!_pos inputs.val k.val (by simp; omega), hk, hj, hl]
      step as ⟨i, hi⟩
      have hpad : i = mid.sha3.SHAKE_PAD_BYTE := by
        have hb := pad_byte_at x shakePad _ hx'
        rw [hl] at hb
        rw [hi, shake_pad_byte_eq, U8.eq_equiv_bv_eq, ← getElem!_pos x.val 33 (by simp)]
        exact hb
      step with massert_spec _ hpad
      step as ⟨x2, hx2⟩
      have hx2' : bv x2.val = M (done.val + it.start.val) ++ shakePad ::
          List.replicate (39 - (M (done.val + it.start.val)).length) 0 := by
        rw [hx2, ← hx, hx']
      step with padded_block_spec 136#usize (by decide) x2 shakePad _ (by omega) hx2' as ⟨y, hy⟩
      step as ⟨a2, ha2⟩
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro j hj'
      rw [ha2, array_set_getElem! _ _ _ _ (by simp; omega)]
      split
      · subst_vars; exact hy
      · exact hst j (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have hN' : it.start.val = n := by omega
      simpa [hN'] using hst
  · exact ⟨hs, he, ha⟩

theorem shake256_store_spec {P : Usize} (states : Std.Array (Std.Array U64 25#usize) 4#usize)
    (A : Nat → List Byte) (done : Usize) (n : Nat) (hn : n ≤ 4) (hdn : done.val + n ≤ P.val)
    (hst : ∀ j < n, sbl (states.val[j]!).val = A (done.val + j))
    (iter : core.ops.range.Range Usize) (out : Std.Array (Std.Array U8 128#usize) P)
    (hs : iter.start.val ≤ n) (he : iter.end.val = n)
    (ho : ∀ i < done.val + iter.start.val, bv (out.val[i]!).val = (A i).take 128) :
    mid.sha3.shake256_batch_loop0_loop1 iter out states done ⦃ r =>
      ∀ i < done.val + n, bv (r.val[i]!).val = (A i).take 128 ⦄ := by
  unfold mid.sha3.shake256_batch_loop0_loop1
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => x.1.start.val ≤ n ∧ x.1.end.val = n ∧
      ∀ i < done.val + x.1.start.val, bv (x.2.val[i]!).val = (A i).take 128)
  · rintro ⟨it, o1⟩ ⟨hs, he, hst1⟩
    simp only at hs he hst1 ⊢
    unfold mid.sha3.shake256_batch_loop0_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      have hen' : it'.end.val = it.end.val := by rw [hen]
      step as ⟨x, hx⟩
      step as ⟨k, hk⟩
      step as ⟨a1, back, ha1, hback⟩
      step as ⟨sl, back1, hsl, hback1⟩
      have hsll : sl.length = 128 := by
        rw [show sl.length = sl.val.length from rfl, hsl, ha1]; simp
      step with store_bytes_spec x sl (by omega) as ⟨s1, hs1l, hs1⟩
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro i hi
      rw [hback, array_set_getElem! _ _ _ _ (by simp; omega)]
      split
      · subst_vars
        rw [Array.from_slice_val _ _ (by
            rw [show s1.val.length = s1.length from rfl, hs1l, hsll]; rfl), hs1, hsll,
          ← getElem!_pos states.val _ (by simp; omega), hst _ (by omega), hk]
      · exact hst1 i (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have hN' : it.start.val = n := by omega
      simpa [hN'] using hst1
  · exact ⟨hs, he, ho⟩

theorem shake256_batch_loop_spec (h : RunsSha3) {P : Usize}
    (inputs : Std.Array (Std.Array U8 40#usize) P) (M : Nat → List Byte) (hin : Shake256Inputs inputs M)
    (outputs : Std.Array (Std.Array U8 128#usize) P) (states : Std.Array (Std.Array U64 25#usize) 4#usize)
    (done : Usize) (hd : done.val ≤ P.val)
    (ho : ∀ i < done.val, bv (outputs.val[i]!).val = (shake256Absorbed (M i)).take 128) :
    mid.sha3.shake256_batch_loop0 inputs outputs states done ⦃ r =>
      ∀ i < P.val, bv (r.val[i]!).val = (shake256Absorbed (M i)).take 128 ⦄ := by
  unfold mid.sha3.shake256_batch_loop0
  apply loop.spec_decr_nat (fun x => P.val - x.2.2.val)
    (fun x => x.2.2.val ≤ P.val ∧
      ∀ i < x.2.2.val, bv (x.1.val[i]!).val = (shake256Absorbed (M i)).take 128)
  · rintro ⟨o1, st, d⟩ ⟨hd, ho⟩
    simp only at hd ho ⊢
    unfold mid.sha3.shake256_batch_loop0.body
    split
    · rename_i hdP
      have hdP' : d.val < P.val := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨n, hn⟩
      have hn' : n.val = min (P.val - d.val) 4 := by
        rw [hn, core.cmp.impls.OrdUsize.min_val, hi]; rfl
      step with shake256_fill_spec inputs M hin d n.val (by omega) (by omega)
        { start := 0#usize, «end» := n } st (by simp) rfl (fun j hj => absurd hj (by simp))
        as ⟨s1, hs1⟩
      apply WP.spec_bind (Pₘ := fun r => ∀ j < n.val, sbl (r.val[j]!).val = shake256Absorbed (M (d.val + j)))
      · have hn4 : n.val = 4 ∨ n.val = 3 ∨ n.val = 2 ∨ n.val = 1 := by omega
        rcases hn4 with e | e | e | e <;> simp only [e]
        · step with keccak4_f1600_spec h s1 as ⟨r, hr⟩
          rename_i j hj
          rw [sbl_states s1 r 4 (by rw [hr, List.map_take]) j (by omega) (by omega), hs1 j (by omega)]
        · step with keccak_nof4_f1600_spec h 3#usize (by decide) s1 as ⟨r, hr⟩
          rename_i j hj
          rw [sbl_states s1 r 3 hr j (by omega) (by omega), hs1 j (by omega)]
        · step with keccak_nof4_f1600_spec h 2#usize (by decide) s1 as ⟨r, hr⟩
          rename_i j hj
          rw [sbl_states s1 r 2 hr j (by omega) (by omega), hs1 j (by omega)]
        · step with keccak_nof4_f1600_spec h 1#usize (by decide) s1 as ⟨r, hr⟩
          rename_i j hj
          rw [sbl_states s1 r 1 hr j (by omega) (by omega), hs1 j (by omega)]
      · intro s2 hs2
        step with shake256_store_spec s2 (fun i => shake256Absorbed (M i)) d n.val (by omega)
          (by omega) hs2 { start := 0#usize, «end» := n } o1 (by simp) rfl (by simpa using ho)
          as ⟨o2, ho2⟩
        step as ⟨d2, hd2⟩
        refine ⟨by omega, ?_, by omega⟩
        intro i hi
        exact ho2 i (by omega)
    · rename_i hdp
      have : P.val ≤ d.val := by scalar_tac
      simp only [WP.spec_ok]
      intro i hi
      exact ho i (by omega)
  · exact ⟨hd, ho⟩

/-- `shake256_batch` writes the first 128 bytes of each input's SHAKE256. -/
theorem shake256_batch_spec (h : RunsSha3) {P : Usize}
    (inputs : Std.Array (Std.Array U8 40#usize) P) (M : Nat → List Byte) (hin : Shake256Inputs inputs M)
    (outputs : Std.Array (Std.Array U8 128#usize) P) :
    mid.sha3.shake256_batch inputs outputs ⦃ r =>
      ∀ i < P.val, bv (r.val[i]!).val = shake256 (M i) 128 ⦄ := by
  unfold mid.sha3.shake256_batch
  apply WP.spec_mono (shake256_batch_loop_spec h inputs M hin outputs _ 0#usize (Nat.zero_le _)
    (fun i hi => absurd hi (Nat.not_lt_zero _)))
  intro r hr i hi
  rw [hr i hi, shake256, sponge, squeeze_block 136 128 _ (by omega)
    (by rw [length_absorb 136 zeros _ (List.length_replicate ..)]; omega)]

end rind.x86_64
