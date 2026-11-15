import Rind.AesKw
import Rind.X86_64.AesCipher
import Rind.X86_64.CtEqual
open Aeneas Aeneas.Std Result rind.vale rind.simd

namespace rind.x86_64

/-- A word's 8 bytes as `to_ne_bytes` writes them, little-endian on rind's targets. -/
abbrev le8 (a : U64) : List (BitVec 8) := a.bv.toLEBytes

theorem le8_from (arr : Std.Array U8 8#usize) : le8 (core.num.U64.from_le_bytes arr) = bvs arr.val := by
  exact (toLEBytes_cast (by simp) _).trans (toLEBytes_fromLEBytes (List.map U8.bv arr.val))

theorem bvs_to_le (a : U64) : bvs (core.num.U64.to_le_bytes a).val = le8 a := by
  simp [core.num.U64.to_le_bytes, bvs, List.map_map, Function.comp_def]

theorem le8_xor (a b : U64) : le8 (a ^^^ b) = xorBytes (le8 a) (le8 b) := by
  exact toLEBytes_xor a.bv b.bv

theorem le8_to_be (t : U64) : le8 (core.num.U64.from_le_bytes (core.num.U64.to_be_bytes t)) = be64 t.val := by
  rw [le8_from]
  simp [core.num.U64.to_be_bytes, bvs, List.map_map, Function.comp_def, toBEBytes_64]

@[step]
theorem block_spec (a : U64) (ri : Std.Array U8 8#usize) :
    mid.aes_kw.block a ri ⦃ blk => bvs blk.val = le8 a ++ bvs ri.val ⦄ := by
  unfold mid.aes_kw.block
  simp only [core.num.U64.to_ne_bytes]
  step*
  set L := (core.num.U64.to_le_bytes a).val
  have hL : L.length = 8 := by simp [L]
  have e1 := rind.spec.setSlice!_append [] (List.replicate 8 0#u8) (List.replicate 8 0#u8) L (by simp [hL])
  have e2 := rind.spec.setSlice!_append L (List.replicate 8 0#u8) [] ri.val (by simp)
  simp only [List.length_nil, List.nil_append, List.append_nil, hL] at e1 e2
  have e0 : (Std.Array.repeat 16#usize 0#u8).val = List.replicate 8 0#u8 ++ List.replicate 8 0#u8 := by
    simp
  rw [s3_post2, s5_post, s4_post, s2_post, s_post2, e0, s1_post, Std.Array.val_to_slice, e1, Std.Array.val_to_slice, e2]
  simp [bvs, L, bvs_to_le a]

/-- An AES-NI decryption key holding `KeyExpansionEIC`'s round keys for the key
bytes `key`. -/
def AesDecIs (alg : Algorithm) (key : List (BitVec 8)) (k : low.x86_64.aes.AesDecKey) : Prop :=
  ∃ hk, k = .Hw hk ∧ HwDecKeyIs alg (seqNat8ToSeqNat32LE key) hk

theorem enc_bytes {alg : Algorithm} {key : List (BitVec 8)} {k : mid.aes.Aes} (hk : AesIs alg key k)
    (b : Std.Array U8 16#usize) :
    low.x86_64.aes.AesKey.encrypt_block k b ⦃ out => bvs out.val = aesBlock alg key (bvs b.val) ⦄ := by
  rw [aes_encrypt alg key k hk b, WP.spec_ok, store_bytes]; rfl

theorem dec_bytes {alg : Algorithm} {key : List (BitVec 8)} {k : low.x86_64.aes.AesDecKey}
    (hk : AesDecIs alg key k) (b : Std.Array U8 16#usize) :
    low.x86_64.aes.AesDecKey.decrypt_block k b ⦃ out => bvs out.val = aesBlockDecrypt alg key (bvs b.val) ⦄ := by
  obtain ⟨hwk, rfl, hwk_is⟩ := hk
  rw [hw_decrypt_block_spec hwk alg _ hwk_is b, WP.spec_ok, store_bytes]; rfl

/-- `mid::aes::expand_key` passes `AesKey::new` its key unchanged. -/
theorem expand_key_eq (key : Slice U8) (hk : key.length ≤ 32) :
    mid.aes.expand_key key = low.x86_64.aes.AesKey.new key := by
  have h1 : (Slice.len key).val ≤ (Std.Array.repeat 32#usize 0#u8).to_slice.length := by simpa using hk
  simp only [mid.aes.expand_key, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut, h1, ite_true, bind_ok,
    core.slice.Slice.copy_from_slice, low.ct.secret_slice]
  simp
  split
  · simp only [bind_ok]
  · rename_i hne
    exact absurd (by apply UScalar.eq_of_val_eq; simpa [List.slice] using hk) hne

theorem aes_key_new_spec (h : RunsAesHw) (alg : Algorithm) (key : Slice U8) (hk : key.length = 4 * nk alg) :
    low.x86_64.aes.AesKey.new key ⦃ k => AesIs alg (bvs key.val) k ⦄ := by
  rw [← expand_key_eq key (by cases alg <;> simp [nk] at hk ⊢ <;> omega)]
  have hl : (bvs key.val).length = 4 * nk alg := by simp [bvs, hk]
  cases alg
  · exact WP.spec_mono (expand_key128_spec h key (by simpa [nk] using hk))
      fun k ⟨k128, hk1, hk2⟩ => ⟨hl, _, hk1, rfl, hk2⟩
  · exact WP.spec_mono (expand_key192_spec h key (by simpa [nk] using hk))
      fun k ⟨k192, hk1, hk2⟩ => ⟨hl, _, hk1, rfl, hk2⟩
  · exact WP.spec_mono (expand_key256_spec h key (by simpa [nk] using hk))
      fun k ⟨k256, hk1, hk2⟩ => ⟨hl, _, hk1, rfl, hk2⟩

/-- The KEK holds the key bytes `kek`, which `alg` sizes. -/
def KekIs (alg : Algorithm) (kek : List (BitVec 8)) (self : mid.aes_kw.AesKek) : Prop :=
  self.key_len.val = 4 * nk alg ∧ bvs (self.key.val.take self.key_len.val) = kek

theorem kek_key_spec {alg : Algorithm} {kek : List (BitVec 8)} {self : mid.aes_kw.AesKek}
    (hk : KekIs alg kek self) :
    mid.aes_kw.AesKek.impl.key self ⦃ s => s.length = 4 * nk alg ∧ bvs s.val = kek ⦄ := by
  obtain ⟨hl, hb⟩ := hk
  have hnk : 4 * nk alg ≤ 32 := by cases alg <;> simp [nk]
  unfold mid.aes_kw.AesKek.impl.key
  step*
  refine ⟨by omega, ?_⟩
  rw [s_post, ← hb, Std.Array.val_to_slice]
  simp [List.slice]

theorem kek_new_spec (h : RunsAesHw) (alg : Algorithm) (algorithm : cipher.Algorithm)
    (hlen : algorithm.key_len.val = 4 * nk alg) (key : Slice U8) :
    mid.aes_kw.AesKek.new algorithm key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok k ∧ KekIs alg (bvs key.val) k
      else r = .Err .WrongLength ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  unfold mid.aes_kw.AesKek.new
  rw [he, bind_ok]
  by_cases hk : key.length = 4 * nk alg
  · have hne : ¬ (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac
    simp only [hne, ite_eq_left hk, Bool.false_eq_true, ite_false]
    have hnk : 4 * nk alg ≤ 32 := by cases alg <;> simp [nk]
    step*
    simp only [low.ct.secret_slice, bind_ok, WP.spec_ok]
    refine ⟨_, rfl, by simp; omega, ?_⟩
    have ht := rind.spec.take_setSlice! (Std.Array.repeat 32#usize 0#u8).val key.val 0
      (by simp only [Slice.length] at hk; simp; omega)
    simp only [Nat.zero_add, List.take_zero, List.nil_append] at ht
    simp only [s_post2, s1_post, Slice.len_val, ht]
  · have hne : (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hk; rw [← hlen, ← he]; simp
    simp only [hne, ite_true, ite_eq_right hk, WP.spec_ok]

/-- The blocks of `r`, as bytes. -/
abbrev chunks (r : Slice (Std.Array U8 8#usize)) : List (List (BitVec 8)) := r.val.map fun x => bvs x.val

theorem wrap_pass_loop_spec {alg : Algorithm} {key : List (BitVec 8)} {aes : mid.aes.Aes} (hk : AesIs alg key aes)
    (n j : Nat) (iter : core.ops.range.Range Usize) (a t : U64) (r : Slice (Std.Array U8 8#usize))
    (hn : r.length = n) (he : iter.end.val = n) (hs : iter.start.val ≤ n)
    (ht : t.val = j * n + iter.start.val) (hb : j * n + n < 2 ^ 64) :
    mid.aes_kw.wrap_pass_loop iter aes a t r ⦃ res =>
      res.2.length = n ∧ (le8 res.1, chunks res.2) =
        (List.range' (j * n + iter.start.val) (n - iter.start.val)).foldl (wStep alg key n) (le8 a, chunks r) ⦄ := by
  unfold mid.aes_kw.wrap_pass_loop
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => x.1.start.val ≤ n ∧ x.1.end.val = n ∧ x.2.2.2.length = n ∧ x.2.2.1.val = j * n + x.1.start.val ∧
      (List.range' (j * n + x.1.start.val) (n - x.1.start.val)).foldl (wStep alg key n) (le8 x.2.1, chunks x.2.2.2) =
      (List.range' (j * n + iter.start.val) (n - iter.start.val)).foldl (wStep alg key n) (le8 a, chunks r))
  · rintro ⟨it, a, t, r⟩ ⟨hs, he, hn, ht, hf⟩
    simp only at hs he hn ht hf ⊢
    unfold mid.aes_kw.wrap_pass_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      simp only [core.num.U64.from_ne_bytes, core.num.U64.to_be]
      step*
      step with enc_bytes hk a2 as ⟨out, hout⟩
      have h8 : (8#usize : Usize).val ≤ out.to_slice.length := by simp
      simp only [lift, bind_ok, core.slice.Slice.first_chunk, core.slice.Slice.last_chunk, h8,
        core.option.Option.unwrap, Result.ofOption]
      simp only [↓reduceDIte, bind_ok]
      step*
      have hi : it.start.val < n := by omega
      have hl : s2.length = n := by simp [s2_post, hn]
      refine ⟨by omega, by rw [hen]; exact he, hl, by omega, ?_, by omega⟩
      rw [← hf]
      obtain ⟨m, hm⟩ : ∃ m, n - it.start.val = m + 1 := ⟨n - it.start.val - 1, by omega⟩
      rw [hm, List.range'_succ, List.foldl_cons, show n - it'.start.val = m by omega,
        show j * n + it.start.val + 1 = j * n + it'.start.val by omega]
      congr 1
      have hmod : (j * n + it.start.val) % n = it.start.val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
      have hri : (chunks r)[it.start.val]! = bvs a1.val := by
        rw [a1_post]; simp [chunks, getElem!_pos, hn, hi]
      simp only [wStep, hmod, hri, ← a2_post, ← hout]
      rw [le8_xor, le8_to_be, le8_from, t1_post, ht]
      congr 1
      · simp [bvs, List.map_take]
      · simp [s2_post, chunks, List.map_set, bvs, List.map_drop]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = n := by omega
      refine ⟨hn, ?_⟩
      rw [← hf, this, Nat.sub_self, List.range'_zero, List.foldl_nil]
  · exact ⟨hs, he, hn, ht, rfl⟩

-- Private, since `AesGcmAny` proves the same under this name and `Axioms` imports both.
private theorem usize_lt (x : Usize) : x.val < 2 ^ 64 := by
  have := x.hBounds
  rcases System.Platform.numBits_eq with h | h <;> simp only [UScalarTy.numBits, h] at this <;> omega

theorem cast_u64 (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; exact Nat.mod_eq_of_lt (usize_lt x)

theorem wrap_pass_spec {alg : Algorithm} {key : List (BitVec 8)} {aes : mid.aes.Aes} (hk : AesIs alg key aes)
    (j : Nat) (a t : U64) (r : Slice (Std.Array U8 8#usize))
    (ht : t.val = j * r.length) (hb : j * r.length + r.length < 2 ^ 64) :
    mid.aes_kw.wrap_pass aes a t r ⦃ res =>
      res.2.length = r.length ∧ (le8 res.1, chunks res.2) =
        (List.range' (j * r.length) r.length).foldl (wStep alg key r.length) (le8 a, chunks r) ⦄ := by
  unfold mid.aes_kw.wrap_pass
  apply WP.spec_mono (wrap_pass_loop_spec hk r.length j _ a t r rfl (by simp) (by simp) (by simpa using ht) hb)
  intro res hres
  simpa using hres

theorem wrap_blocks_loop_spec {alg : Algorithm} {key : List (BitVec 8)} {aes : mid.aes.Aes}
    (hk : AesIs alg key aes) (n : Nat) (iter : core.ops.range.Range U64) (r : Slice (Std.Array U8 8#usize))
    (nn a : U64) (hn : r.length = n) (hnn : nn.val = n) (he : iter.end.val = 6) (hs : iter.start.val ≤ 6)
    (hb : 6 * n < 2 ^ 64) :
    mid.aes_kw.wrap_blocks_loop iter aes r nn a ⦃ res =>
      res.1.length = n ∧ (le8 res.2, chunks res.1) =
        (List.range' (iter.start.val * n) ((6 - iter.start.val) * n)).foldl (wStep alg key n) (le8 a, chunks r) ⦄ := by
  unfold mid.aes_kw.wrap_blocks_loop
  apply loop.spec_decr_nat (fun x => 6 - x.1.start.val)
    (fun x => x.1.start.val ≤ 6 ∧ x.1.end.val = 6 ∧ x.2.1.length = n ∧
      (List.range' (x.1.start.val * n) ((6 - x.1.start.val) * n)).foldl (wStep alg key n) (le8 x.2.2, chunks x.2.1) =
      (List.range' (iter.start.val * n) ((6 - iter.start.val) * n)).foldl (wStep alg key n) (le8 a, chunks r))
  · rintro ⟨it, r, a⟩ ⟨hs, he, hn, hf⟩
    simp only at hs he hn hf ⊢
    unfold mid.aes_kw.wrap_blocks_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_U64_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      have h6 : (it.start.val + 1) * n ≤ 6 * n := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h6
      have hmul : it.start.val * nn.val ≤ U64.max := by
        have em : U64.max = 2 ^ 64 - 1 := by rw [U64.max_eq]; norm_num
        rw [hnn, em]; omega
      step as ⟨i, i_post⟩
      step with wrap_pass_spec hk it.start.val a i r (by rw [i_post, hnn, hn]) (by rw [hn]; omega)
        as ⟨ra, rr, hl, hres⟩
      try simp only [WP.spec_ok]
      refine ⟨by omega, by rw [hen]; exact he, by rw [hl, hn], ?_, by omega⟩
      rw [← hf]
      obtain ⟨m, hm⟩ : ∃ m, 6 - it.start.val = m + 1 := ⟨6 - it.start.val - 1, by omega⟩
      rw [hm, Nat.add_mul, Nat.one_mul, Nat.add_comm (m * n), ← List.range'_append_1, List.foldl_append]
      rw [hn] at hres
      rw [← hres, show 6 - it'.start.val = m by omega, hst, Nat.add_mul, Nat.one_mul]
    · step with core.iter.range.IteratorRange.next_U64_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = 6 := by omega
      refine ⟨hn, ?_⟩
      rw [← hf, this, Nat.sub_self, Nat.zero_mul, List.range'_zero, List.foldl_nil]
  · exact ⟨hs, he, hn, rfl⟩

/-- `wrap_blocks` is W's `6n` steps over the blocks. -/
theorem wrap_blocks_spec {alg : Algorithm} {key : List (BitVec 8)} {aes : mid.aes.Aes} (hk : AesIs alg key aes)
    (a : Std.Array U8 8#usize) (r : Slice (Std.Array U8 8#usize)) (hb : 6 * r.length < 2 ^ 64) :
    mid.aes_kw.wrap_blocks aes a r ⦃ res =>
      res.2.length = r.length ∧ (bvs res.1.val, chunks res.2) =
        (List.range (6 * r.length)).foldl (wStep alg key r.length) (bvs a.val, chunks r) ⦄ := by
  unfold mid.aes_kw.wrap_blocks
  simp only [core.num.U64.from_ne_bytes, core.num.U64.to_ne_bytes, bind_ok]
  step as ⟨nn, hnn⟩
  step with wrap_blocks_loop_spec hk r.length { start := 0#u64, «end» := 6#u64 } r nn _ rfl
    (by rw [hnn, cast_u64, Slice.len_val]) (by simp) (by simp) hb as ⟨rr, ra, hl, hres⟩
  try simp only [WP.spec_ok]
  refine ⟨hl, ?_⟩
  rw [bvs_to_le, hres, le8_from]
  simp [List.range_eq_range']

theorem unwrap_pass_loop_spec {alg : Algorithm} {key : List (BitVec 8)} {aes : low.x86_64.aes.AesDecKey}
    (hk : AesDecIs alg key aes) (n p : Nat) (iter : core.ops.range.Range Usize) (a t : U64)
    (r : Slice (Std.Array U8 8#usize)) (hn : r.length = n) (he : iter.end.val = n) (hs : iter.start.val ≤ n)
    (ht : t.val = p * n + n - iter.start.val) (hb : p * n + n < 2 ^ 64) :
    mid.aes_kw.unwrap_pass_loop iter aes a t r ⦃ res =>
      res.2.length = n ∧ (le8 res.1, chunks res.2) =
        (List.range' (p * n) (n - iter.start.val)).reverse.foldl (uStep alg key n) (le8 a, chunks r) ⦄ := by
  unfold mid.aes_kw.unwrap_pass_loop
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => x.1.start.val ≤ n ∧ x.1.end.val = n ∧ x.2.2.2.length = n ∧
      x.2.2.1.val = p * n + n - x.1.start.val ∧
      (List.range' (p * n) (n - x.1.start.val)).reverse.foldl (uStep alg key n) (le8 x.2.1, chunks x.2.2.2) =
      (List.range' (p * n) (n - iter.start.val)).reverse.foldl (uStep alg key n) (le8 a, chunks r))
  · rintro ⟨it, a, t, r⟩ ⟨hs, he, hn, ht, hf⟩
    simp only at hs he hn ht hf ⊢
    unfold mid.aes_kw.unwrap_pass_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      simp only [core.num.U64.from_ne_bytes, core.num.U64.to_be, bind_ok, lift]
      have hi : it.start.val < n := by omega
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨a1, ha1⟩
      step as ⟨b, hbk⟩
      have ht1' : (1#u64 : U64).val ≤ t.val := by simp; omega
      step as ⟨t1, ht1⟩
      step with dec_bytes hk b as ⟨b1, hb1⟩
      have h8 : (8#usize : Usize).val ≤ b1.to_slice.length := by simp
      simp only [lift, bind_ok, core.slice.Slice.first_chunk, core.slice.Slice.last_chunk, h8,
        core.option.Option.unwrap, Result.ofOption]
      simp only [↓reduceDIte, bind_ok]
      step*
      have hi2' : i2.val = n - 1 - it.start.val := by simp only [Slice.len_val] at hi1; omega
      have hl : s2.length = n := by simp [s2_post, hn]
      refine ⟨by omega, by rw [hen]; exact he, hl, by omega, ?_, by omega⟩
      rw [← hf]
      obtain ⟨m, hm⟩ : ∃ m, n - it.start.val = m + 1 := ⟨n - it.start.val - 1, by omega⟩
      rw [hm, List.range'_concat, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.foldl_cons, show n - it'.start.val = m by omega]
      congr 1
      have hkk : p * n + 1 * m = p * n + i2.val := by omega
      have hmod : (p * n + i2.val) % n = i2.val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hri : (chunks r)[i2.val]! = bvs a1.val := by
        have hi2n : i2.val < n := by omega
        rw [ha1]; simp [chunks, getElem!_pos, hn, hi2n]
      rw [le8_xor, le8_to_be] at hbk
      simp only [uStep, hkk, hmod, hri]
      rw [show p * n + i2.val + 1 = t.val by omega, ← hbk, ← hb1, le8_from]
      congr 1
      · simp [bvs, List.map_take]
      · simp [s2_post, chunks, List.map_set, bvs, List.map_drop]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = n := by omega
      refine ⟨hn, ?_⟩
      rw [← hf, this, Nat.sub_self, List.range'_zero, List.reverse_nil, List.foldl_nil]
  · exact ⟨hs, he, hn, ht, rfl⟩

theorem unwrap_pass_spec {alg : Algorithm} {key : List (BitVec 8)} {aes : low.x86_64.aes.AesDecKey}
    (hk : AesDecIs alg key aes) (p : Nat) (a t : U64) (r : Slice (Std.Array U8 8#usize))
    (ht : t.val = p * r.length + r.length) (hb : p * r.length + r.length < 2 ^ 64) :
    mid.aes_kw.unwrap_pass aes a t r ⦃ res =>
      res.2.length = r.length ∧ (le8 res.1, chunks res.2) =
        (List.range' (p * r.length) r.length).reverse.foldl (uStep alg key r.length) (le8 a, chunks r) ⦄ := by
  unfold mid.aes_kw.unwrap_pass
  apply WP.spec_mono (unwrap_pass_loop_spec hk r.length p _ a t r rfl (by simp) (by simp)
    (by simpa using ht) hb)
  intro res hres
  simpa using hres

theorem unwrap_blocks_loop_spec {alg : Algorithm} {key : List (BitVec 8)} {aes : low.x86_64.aes.AesDecKey}
    (hk : AesDecIs alg key aes) (n : Nat) (iter : core.ops.range.Range U64) (r : Slice (Std.Array U8 8#usize))
    (nn a : U64) (hn : r.length = n) (hnn : nn.val = n) (he : iter.end.val = 6) (hs : iter.start.val ≤ 6)
    (hb : 6 * n < 2 ^ 64) :
    mid.aes_kw.unwrap_blocks_loop iter aes r nn a ⦃ res =>
      res.1.length = n ∧ (le8 res.2, chunks res.1) =
        (List.range' 0 ((6 - iter.start.val) * n)).reverse.foldl (uStep alg key n) (le8 a, chunks r) ⦄ := by
  unfold mid.aes_kw.unwrap_blocks_loop
  apply loop.spec_decr_nat (fun x => 6 - x.1.start.val)
    (fun x => x.1.start.val ≤ 6 ∧ x.1.end.val = 6 ∧ x.2.1.length = n ∧
      (List.range' 0 ((6 - x.1.start.val) * n)).reverse.foldl (uStep alg key n) (le8 x.2.2, chunks x.2.1) =
      (List.range' 0 ((6 - iter.start.val) * n)).reverse.foldl (uStep alg key n) (le8 a, chunks r))
  · rintro ⟨it, r, a⟩ ⟨hs, he, hn, hf⟩
    simp only at hs he hn hf ⊢
    unfold mid.aes_kw.unwrap_blocks_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_U64_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      step as ⟨i, i_post⟩
      have hmul : i.val * nn.val ≤ U64.max := by
        have em : U64.max = 2 ^ 64 - 1 := by rw [U64.max_eq]; norm_num
        have : (6 - it.start.val) * n ≤ 6 * n := Nat.mul_le_mul_right _ (by omega)
        rw [hnn, em, i_post]; omega
      step as ⟨i1, i1_post⟩
      have h65 : (6 - it.start.val) * n = (5 - it.start.val) * n + n := by
        rw [show 6 - it.start.val = (5 - it.start.val) + 1 by omega, Nat.add_mul, Nat.one_mul]
      have h5 : (5 - it.start.val) * n ≤ 5 * n := Nat.mul_le_mul_right _ (by omega)
      step with unwrap_pass_spec hk (5 - it.start.val) a i1 r
        (by rw [i1_post, i_post, hnn, hn, ← h65]) (by rw [hn]; omega) as ⟨ra, rr, hl, hres⟩
      try simp only [WP.spec_ok]
      refine ⟨by omega, by rw [hen]; exact he, by rw [hl, hn], ?_, by omega⟩
      rw [← hf]
      obtain ⟨m, hm⟩ : ∃ m, 6 - it.start.val = m + 1 := ⟨6 - it.start.val - 1, by omega⟩
      rw [hm, Nat.add_mul, Nat.one_mul, ← List.range'_append_1, List.reverse_append, List.foldl_append,
        Nat.zero_add]
      rw [hn] at hres
      rw [show 5 - it.start.val = m by omega] at hres
      rw [← hres, show 6 - it'.start.val = m by omega]
    · step with core.iter.range.IteratorRange.next_U64_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = 6 := by omega
      refine ⟨hn, ?_⟩
      rw [← hf, this, Nat.sub_self, Nat.zero_mul, List.range'_zero, List.reverse_nil, List.foldl_nil]
  · exact ⟨hs, he, hn, rfl⟩

/-- `unwrap_blocks` is W⁻¹'s `6n` steps over the blocks, from the last. -/
theorem unwrap_blocks_spec {alg : Algorithm} {key : List (BitVec 8)} {aes : low.x86_64.aes.AesDecKey}
    (hk : AesDecIs alg key aes) (a : Std.Array U8 8#usize) (r : Slice (Std.Array U8 8#usize))
    (hb : 6 * r.length < 2 ^ 64) :
    mid.aes_kw.unwrap_blocks aes a r ⦃ res =>
      res.2.length = r.length ∧ (bvs res.1.val, chunks res.2) =
        (List.range (6 * r.length)).reverse.foldl (uStep alg key r.length) (bvs a.val, chunks r) ⦄ := by
  unfold mid.aes_kw.unwrap_blocks
  simp only [core.num.U64.from_ne_bytes, core.num.U64.to_ne_bytes, bind_ok]
  step as ⟨nn, hnn⟩
  step with unwrap_blocks_loop_spec hk r.length { start := 0#u64, «end» := 6#u64 } r nn _ rfl
    (by rw [hnn, cast_u64, Slice.len_val]) (by simp) (by simp) hb as ⟨rr, ra, hl, hres⟩
  try simp only [WP.spec_ok]
  refine ⟨hl, ?_⟩
  rw [bvs_to_le, hres, le8_from]
  simp [List.range_eq_range']

/-! ## The API -/

theorem bvs_IV : bvs mid.aes_kw.IV.val = icv1 := by
  simp [mid.aes_kw.IV, bvs, icv1]

theorem bvs_AIV : bvs mid.aes_kw.AIV.val = icv2 := by
  simp [mid.aes_kw.AIV, bvs, icv2, Std.Array.make]

theorem bvs_append (l l' : List U8) : bvs (l ++ l') = bvs l ++ bvs l' := List.map_append

theorem bvs_inj {l l' : List U8} : bvs l = bvs l' ↔ l = l' := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun x y hxy => by cases x; cases y; simp_all) h
  · rintro rfl; rfl

/-- `as_chunks_mut` of a whole number of 8-byte blocks views them as SP 800-38F's
semiblocks, and writes blocks of the same count back as their bytes in order. -/
theorem as_chunks_mut_8 (s : Slice U8) (h8 : s.length % 8 = 0) :
    core.slice.Slice.as_chunks_mut 8#usize s ⦃ res =>
      res.1.1.length = s.length / 8 ∧ chunks res.1.1 = semiblocks (bvs s.val) ∧
      ∀ c : Slice (Std.Array U8 8#usize), c.length = s.length / 8 →
        bvs (res.2 (c, res.1.2)).val = (chunks c).flatten ∧ (res.2 (c, res.1.2)).length = s.length ⦄ := by
  have hv : (8#usize : Usize).val = 8 := rfl
  simp only [core.slice.Slice.as_chunks_mut, core.slice.Slice.as_chunks, hv, OfNat.ofNat_ne_zero, ite_false,
    bind_ok, WP.spec_ok]
  refine ⟨by simp, ?_, ?_⟩
  · apply List.ext_getElem (by simp [chunks, semiblocks, bvs])
    intro i h1 h2
    simp [chunks, semiblocks, bvs, List.map_take, List.map_drop, Nat.mul_comm]
  · intro c hc
    have hrest : s.val.drop (s.length / 8 * 8) = [] := by
      simp only [List.drop_eq_nil_iff]; simp only [Slice.length] at h8 ⊢; omega
    have hflat : ∀ l : List (Std.Array U8 8#usize), (l.flatMap (·.val)).length = 8 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons x l ih => simp [List.flatMap_cons, ih]; ring
    have hlen : (c.val.flatMap (·.val)).length = s.length := by
      rw [hflat]; simp only [Slice.length] at hc h8 ⊢; omega
    have hbf : ∀ l : List (Std.Array U8 8#usize), bvs (l.flatMap (·.val)) = (l.map fun x => bvs x.val).flatten := by
      intro l; induction l with
      | nil => simp
      | cons x l ih => rw [List.flatMap_cons, List.map_cons, List.flatten_cons, ← ih]; simp [bvs]
    split
    · rename_i hle
      simp [hrest, hbf, chunks, Slice.length, hlen]
    · rename_i hle
      exfalso; apply hle; simp [hrest, hlen]

/-- `wrap` refuses what the Rust refuses, and otherwise writes KW-AE of the key. -/
theorem kek_wrap_spec (h : RunsAesHw) {alg : Algorithm} {kek : List (BitVec 8)} {self : mid.aes_kw.AesKek}
    (hk : KekIs alg kek self) (key wrapped : Slice U8) (hroom : key.length + 8 ≤ Usize.max) :
    mid.aes_kw.AesKek.wrap self key wrapped ⦃ res =>
      if 16 ≤ key.length ∧ key.length % 8 = 0 ∧ wrapped.length = key.length + 8 then
        res.1 = .Ok () ∧ bvs res.2.val = kwAE alg kek (bvs key.val)
      else res = (.Err .WrongLength, wrapped) ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.aes_kw.AesKek.wrap
  rw [he, bind_ok]
  by_cases h16 : key.length < 16
  · have hlt : Slice.len key < 16#usize := by scalar_tac
    have hn : ¬ (16 ≤ key.length ∧ key.length % 8 = 0 ∧ wrapped.length = key.length + 8) := by omega
    simp only [hlt, ite_true, hn, ite_false, WP.spec_ok]
  have hlt : ¬ Slice.len key < 16#usize := by scalar_tac
  simp only [hlt, ite_false]
  step as ⟨b, hb⟩
  cases b
  · have h8 : ¬ key.length % 8 = 0 := by simpa using hb
    have hn : ¬ (16 ≤ key.length ∧ key.length % 8 = 0 ∧ wrapped.length = key.length + 8) := by omega
    simp only [hn, Bool.false_eq_true, ite_false, WP.spec_ok]
  have h8 : key.length % 8 = 0 := by simpa using hb
  simp only [ite_true]
  step as ⟨i4, hi4⟩
  by_cases hw : wrapped.length = key.length + 8
  swap
  · have hne : (Slice.len wrapped != i4) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hw; rw [← Slice.len_val, he, hi4, Slice.len_val]
    have hn : ¬ (16 ≤ key.length ∧ key.length % 8 = 0 ∧ wrapped.length = key.length + 8) := by omega
    simp only [hne, hn, ite_true, ite_false, WP.spec_ok]
  have hne : ¬ (Slice.len wrapped != i4) = true := by
    simp only [bne_iff_ne, ne_eq, not_not]; apply UScalar.eq_of_val_eq; rw [hi4, Slice.len_val, Slice.len_val, hw]
  have hy : 16 ≤ key.length ∧ key.length % 8 = 0 ∧ wrapped.length = key.length + 8 := ⟨by omega, h8, hw⟩
  simp only [hne, Bool.false_eq_true, ite_false, hy, and_self, ite_true]
  step as ⟨ar, rr, sback, hal, hrl, harv, hrrv, hsback⟩
  step as ⟨r1, hr1'⟩
  subst r1
  simp only [low.ct.secret_slice, bind_ok]
  step with kek_key_spec hk as ⟨s, hsl, hsb⟩
  step with aes_key_new_spec h alg s hsl as ⟨ak, hak⟩
  rw [hsb] at hak
  simp only [core.mem.manually_drop.ManuallyDrop.new, core.mem.manually_drop.ManuallyDrop.Insts.CoreOpsDerefDeref.deref,
    bind_ok]
  step with as_chunks_mut_8 key h8 as ⟨ch, rest, cback, hcl, hch, hcback⟩
  step with wrap_blocks_spec hak mid.aes_kw.IV ch
    (by have := usize_lt key.len; rw [Slice.len_val] at this; rw [hcl]; omega)
    as ⟨wa, wr, hwl, hwb⟩
  have hc := hcback wr (by rw [hwl, hcl])
  simp only [lift, bind_ok]
  have hlen8 : ar.length = wa.to_slice.length := by simp [hal]
  step*
  have hs := hsback a2 (cback (wr, rest)) (by rw [a2_post]; simp) (by rw [hc.2]; omega)
  simp only [low.ct.public_slice, bind_ok, WP.spec_ok]
  refine ⟨trivial, ?_⟩
  have hn8 : (bvs key.val).length / 8 = ch.length := by rw [hcl]; simp [bvs, Slice.length]
  rw [hs.1, bvs_append, a2_post, Std.Array.val_to_slice, hc.1]
  rw [bvs_IV, hch, ← hn8] at hwb
  simp only [kwAE, kwW]
  rw [← hwb]

/-- `unwrap` refuses what the Rust refuses, returns `DecryptFailed` with the key
cleared exactly when KW-AD fails, and otherwise writes KW-AD's plaintext. -/
theorem kek_unwrap_spec (h : RunsAesHw) (hheld : low.entry.Entry.assert_held = ok ()) {alg : Algorithm}
    {kek : List (BitVec 8)} {self : mid.aes_kw.AesKek} (hk : KekIs alg kek self) (wrapped key : Slice U8) :
    mid.aes_kw.AesKek.unwrap self wrapped key ⦃ res =>
      if wrapped.length < 24 ∨ wrapped.length % 8 ≠ 0 then res = (.Err .DecryptFailed, key)
      else if key.length ≠ wrapped.length - 8 then res = (.Err .WrongLength, key)
      else match kwAD alg kek (bvs wrapped.val) with
        | some p => res.1 = .Ok () ∧ bvs res.2.val = p
        | none => res.1 = .Err .DecryptFailed ∧ res.2.val = List.replicate key.length 0#u8 ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.aes_kw.AesKek.unwrap
  rw [he, bind_ok]
  by_cases h24 : wrapped.length < 24
  · have hlt : Slice.len wrapped < 24#usize := by scalar_tac
    simp only [hlt, ite_true, h24, true_or, WP.spec_ok]
  have hlt : ¬ Slice.len wrapped < 24#usize := by scalar_tac
  simp only [hlt, ite_false, h24, false_or]
  step as ⟨b, hb⟩
  cases b
  · have h8 : ¬ wrapped.length % 8 = 0 := by simpa using hb
    simp [h8]
  have h8 : wrapped.length % 8 = 0 := by simpa using hb
  simp only [ite_true, h8, ne_eq, not_true_eq_false, ite_false]
  step as ⟨i4, hi4⟩
  by_cases hw : key.length = wrapped.length - 8
  swap
  · have hne : (Slice.len key != i4) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hw; rw [← Slice.len_val, he, hi4, Slice.len_val]
    simp only [hne, hw, ite_true, not_false_eq_true, WP.spec_ok]
  have hne : ¬ (Slice.len key != i4) = true := by
    simp only [bne_iff_ne, ne_eq, not_not]; apply UScalar.eq_of_val_eq
    rw [hi4, Slice.len_val, Slice.len_val, hw]
  simp only [hne, Bool.false_eq_true, ite_false, hw, not_true_eq_false]
  step as ⟨wa, wc, hwal, hwcl, hwav, hwcv⟩
  have hkc : key.length = wc.length := by omega
  step as ⟨key1, hkey1⟩
  subst key1
  step with kek_key_spec hk as ⟨s, hsl, hsb⟩
  step with dec_key_new_spec h alg s hsl as ⟨adk, hwk, hadk1, hadk2⟩
  have hdk : AesDecIs alg kek adk := ⟨hwk, hadk1, by rw [← hsb]; exact hadk2⟩
  simp only [core.mem.manually_drop.ManuallyDrop.new, core.mem.manually_drop.ManuallyDrop.Insts.CoreOpsDerefDeref.deref,
    bind_ok]
  step as ⟨r, hr⟩
  rcases r with arr | ⟨⟩
  swap
  · exact absurd hwal hr
  obtain ⟨harr, -⟩ := hr
  simp only [core.result.Result.unwrap, bind_ok]
  have hc8 : wc.length % 8 = 0 := by omega
  step with as_chunks_mut_8 wc hc8 as ⟨ch, rest, cback, hcl, hch, hcback⟩
  step with unwrap_blocks_spec hdk arr ch
    (by have := usize_lt wc.len; rw [Slice.len_val] at this; rw [hcl]; omega) as ⟨ua, ur, hul, hub⟩
  simp only [lift, bind_ok]
  step with ct_equal_spec hheld as ⟨b1, hb1⟩
  simp only [low.ct.into_public, bind_ok]
  have hc := hcback ur (by rw [hul, hcl])
  have hn8 : (bvs wc.val).length / 8 = ch.length := by rw [hcl]; simp [bvs, Slice.length]
  have hAD : kwAD alg kek (bvs wrapped.val) =
      if bvs ua.val = icv1 then some (chunks ur).flatten else none := by
    have ht : (bvs wrapped.val).take 8 = bvs arr.val := by rw [harr, hwav]; simp [bvs, List.map_take]
    have hd : (bvs wrapped.val).drop 8 = bvs wc.val := by rw [hwcv]; simp [bvs, List.map_drop]
    rw [hch, ← hn8] at hub
    simp only [kwAD, kwWInv, ht, hd, ← hub]
  rw [hAD]
  have hiv : (ua.to_slice.val = mid.aes_kw.IV.to_slice.val) ↔ bvs ua.val = icv1 := by
    rw [Std.Array.val_to_slice, Std.Array.val_to_slice, ← bvs_IV, bvs_inj]
  by_cases hok : bvs ua.val = icv1
  · have hb1t : b1 = true := by rw [hb1]; simpa using hiv.2 hok
    simp only [hb1t, ite_true, hok, low.ct.public_slice, bind_ok, WP.spec_ok]
    exact ⟨trivial, hc.1⟩
  · have hb1f : b1 = false := by rw [hb1]; simpa using fun h => hok (hiv.1 h)
    simp only [hb1f, Bool.false_eq_true, ite_false, hok]
    step*
    done

theorem next_multiple_of_8_spec (a : Usize) (h : a.val + 7 ≤ Usize.max) :
    core.num.Usize.next_multiple_of a 8#usize ⦃ r => r.val = (a.val + 7) / 8 * 8 ⦄ := by
  unfold core.num.Usize.next_multiple_of
  step as ⟨m, hm⟩
  split
  · rename_i h0
    have : m.val = 0 := by rw [h0]; rfl
    simp only [WP.spec_ok]; omega
  · rename_i h0
    have : m.val ≠ 0 := fun h' => h0 (UScalar.eq_of_val_eq (by rw [h']; rfl))
    step as ⟨d, hd⟩
    step as ⟨r, hr⟩
    omega

/-- `wrap_padded` refuses what the Rust refuses, keys empty or of `2^32` bytes or
more among them, and otherwise writes KWP-AE of the key. -/
theorem kek_wrap_padded_spec (h : RunsAesHw) {alg : Algorithm} {kek : List (BitVec 8)}
    {self : mid.aes_kw.AesKek} (hk : KekIs alg kek self) (key wrapped : Slice U8)
    (hroom : key.length + 15 ≤ Usize.max) :
    mid.aes_kw.AesKek.wrap_padded self key wrapped ⦃ res =>
      if 0 < key.length ∧ key.length < 2 ^ 32 ∧ wrapped.length = (key.length + 7) / 8 * 8 + 8 then
        res.1 = .Ok () ∧ bvs res.2.val = kwpAE alg kek (bvs key.val)
      else res = (.Err .WrongLength, wrapped) ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.aes_kw.AesKek.wrap_padded
  rw [he, bind_ok]
  have hu32 : U32.max = 2 ^ 32 - 1 := by rw [U32.max_eq]; norm_num
  step as ⟨r, hr1, hr2⟩
  by_cases hbig : 2 ^ 32 ≤ key.length
  · rw [hr2 (by rw [Slice.len_val]; omega)]
    have hn : ¬ (0 < key.length ∧ key.length < 2 ^ 32 ∧
      wrapped.length = (key.length + 7) / 8 * 8 + 8) := by omega
    simp only [hn, ite_false, WP.spec_ok]
  obtain ⟨len, rfl, hlen⟩ := hr1 (by rw [Slice.len_val]; omega)
  simp only
  step as ⟨b, hb⟩
  by_cases h0 : key.length = 0
  · have hbt : b = true := by rw [hb]; simpa using h0
    have hn : ¬ (0 < key.length ∧ key.length < 2 ^ 32 ∧
      wrapped.length = (key.length + 7) / 8 * 8 + 8) := by omega
    simp only [hbt, ite_true, hn, ite_false, WP.spec_ok]
  have hbf : b = false := by
    cases b
    · rfl
    · simp at hb; exact absurd (by simp [Slice.length, hb]) h0
  simp only [hbf, Bool.false_eq_true, ite_false]
  step with next_multiple_of_8_spec (Slice.len key) (by rw [Slice.len_val]; omega) as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  by_cases hw : wrapped.length = (key.length + 7) / 8 * 8 + 8
  swap
  · have hne : (Slice.len wrapped != i4) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hw
      rw [← Slice.len_val, he, hi4, hi3, Slice.len_val]
    have hn : ¬ (0 < key.length ∧ key.length < 2 ^ 32 ∧
      wrapped.length = (key.length + 7) / 8 * 8 + 8) := by omega
    simp only [hne, hn, ite_true, ite_false, WP.spec_ok]
  have hne : ¬ (Slice.len wrapped != i4) = true := by
    simp only [bne_iff_ne, ne_eq, not_not]; apply UScalar.eq_of_val_eq
    rw [hi4, hi3, Slice.len_val, Slice.len_val, hw]
  have hy : 0 < key.length ∧ key.length < 2 ^ 32 ∧ wrapped.length = (key.length + 7) / 8 * 8 + 8 :=
    ⟨by omega, by omega, hw⟩
  simp only [hne, Bool.false_eq_true, ite_false, hy, and_self, ite_true]
  have hkw : key.length + 8 ≤ wrapped.length := by omega
  have hclone : core.clone.CloneU8.clone 0#u8 ⦃ v' => v' = 0#u8 ⦄ := by
    simp [liftFun1]
  step*
  have haiv : bvs (index_mut_back1 s5).val = icv2 ++ be32 key.length := by
    have e0 : (Std.Array.repeat 8#usize 0#u8).val = List.replicate 4 0#u8 ++ List.replicate 4 0#u8 := by simp
    have hA : mid.aes_kw.AIV.val.length = 4 := by simp
    have e1 := rind.spec.setSlice!_append [] (List.replicate 4 0#u8) (List.replicate 4 0#u8)
      mid.aes_kw.AIV.val (by simp)
    have e2 := rind.spec.setSlice!_append mid.aes_kw.AIV.val (List.replicate 4 0#u8) [] a.val (by simp)
    simp only [List.length_nil, List.nil_append, List.append_nil, hA] at e1 e2
    rw [s3_post2, s_post2, e0, s5_post, s4_post, Std.Array.val_to_slice, s2_post, s1_post,
      Std.Array.val_to_slice, e1, e2, bvs_append, bvs_AIV, a_post]
    simp only [bvs, List.map_map, Function.comp_def, List.map_id']
    rw [toBEBytes_32]
    show _ ++ be32 len.val = _
    rw [hlen, Slice.len_val]
  have hpad : r_pad.length = (8 - key.length % 8) % 8 := by
    rw [r_key_post1, a1_post1, Slice.len_val]; omega
  obtain ⟨hr2v, hr2l⟩ := r_key_post4 r_key1 r_pad1 (by rw [r_key1_post]; simp)
    (by rw [r_pad1_post, r_key_post1])
  have hr2 : bvs (split_at_mut_back1 (r_key1, r_pad1)).val = kwpPad (bvs key.val) := by
    rw [hr2v, bvs_append, r_key1_post, r_pad1_post1, hpad]; simp [kwpPad, bvs]
  have hr2len : (split_at_mut_back1 (r_key1, r_pad1)).length = (key.length + 7) / 8 * 8 := by
    rw [hr2l, a1_post1]; omega
  set aiv2 := index_mut_back1 s5 with haiv2
  set r2 := split_at_mut_back1 (r_key1, r_pad1) with hr2def
  simp only [low.ct.secret_slice, bind_ok]
  step with kek_key_spec hk as ⟨s6, hsl, hsb⟩
  step with aes_key_new_spec h alg s6 hsl as ⟨ak, hak⟩
  rw [hsb] at hak
  simp only [core.mem.manually_drop.ManuallyDrop.new,
    core.mem.manually_drop.ManuallyDrop.Insts.CoreOpsDerefDeref.deref, bind_ok]
  have e8 : (8#usize : Usize).val = 8 := rfl
  have hpl : (bvs key.val).length = key.length := by simp [bvs, Slice.length]
  split
  · rename_i h8r
    have hk8 : key.length ≤ 8 := by
      have := congrArg UScalar.val h8r; rw [Slice.len_val, hr2len, e8] at this; omega
    have hw16 : wrapped.length = 16 := by omega
    have hr28 : r2.length = 8 := by rw [hr2len]; omega
    step*
    obtain ⟨s7, back2⟩ := x
    dsimp only at *
    have hs7 : s7.length = aiv2.to_slice.length := by simp [x_post1]
    obtain ⟨hw2v, hw2l⟩ := a1_post4 a1 r2 a1_post (by rw [hr28, hw16])
    try simp only [lift, bind_ok]
    step as ⟨s9, hs9⟩
    step as ⟨y, hyv, hyl, hyb⟩
    obtain ⟨s10, back3⟩ := y
    dsimp only at *
    have hs10 : s10.length = r2.length := by rw [hyl, hr28]
    step as ⟨s11, hs11⟩
    step with enc_bytes hak (back3 s11) as ⟨a2, ha2⟩
    try simp only [lift, bind_ok]
    have hs12l : (split_at_mut_back (a1, r2)).length = a2.to_slice.length := by simp [hw2l, hw16]
    step as ⟨s12, hs12⟩
    simp only [low.ct.public_slice, bind_ok, WP.spec_ok]
    refine ⟨trivial, ?_⟩
    have hA : aiv2.val.length = 8 := by simp
    have eb0 : (Std.Array.repeat 16#usize 0#u8).val = List.replicate 8 0#u8 ++ List.replicate 8 0#u8 := by
      simp
    have eb1 := rind.spec.setSlice!_append [] (List.replicate 8 0#u8) (List.replicate 8 0#u8) aiv2.val
      (by simp)
    have eb2 := rind.spec.setSlice!_append aiv2.val (List.replicate 8 0#u8) [] r2.val (by simp [hr28])
    simp only [List.length_nil, List.nil_append, List.append_nil, hA] at eb1 eb2
    have hblk : (back3 s11).val = aiv2.val ++ r2.val := by
      rw [hyb, x_post2, eb0, hs9, Std.Array.val_to_slice, eb1, hs11, eb2]
    rw [hs12, Std.Array.val_to_slice, ha2, hblk, bvs_append, haiv, hr2]
    simp only [kwpAE, hpl, hk8, ite_true]
  · rename_i h8r
    have hk8 : ¬ key.length ≤ 8 := by
      intro hk8; apply h8r; apply UScalar.eq_of_val_eq; rw [Slice.len_val, hr2len, e8]; omega
    have hr8 : r2.length % 8 = 0 := by rw [hr2len]; omega
    step with as_chunks_mut_8 r2 hr8 as ⟨x, hcl, hch, hcback⟩
    obtain ⟨⟨ch, rest⟩, cback⟩ := x
    dsimp only at *
    rw [← hr2def] at hcl hch hcback
    step with wrap_blocks_spec hak aiv2 ch
      (by rw [hcl, hr2len]; omega) as ⟨w, hwl, hwb⟩
    obtain ⟨wa, wr⟩ := w
    dsimp only at *
    rw [← haiv2] at hwb
    have hc := hcback wr (by rw [hwl, hcl])
    simp only [lift, bind_ok]
    have hlen8 : a1.length = wa.to_slice.length := by simp [a1_post]
    step as ⟨a3, ha3⟩
    have hs := a1_post4 a3 (cback (wr, rest)) (by rw [ha3]; simp) (by rw [hc.2, hr2len]; omega)
    simp only [low.ct.public_slice, bind_ok, WP.spec_ok]
    refine ⟨trivial, ?_⟩
    rw [hs.1, bvs_append, ha3, Std.Array.val_to_slice, hc.1]
    have hn8 : (kwpPad (bvs key.val)).length / 8 = ch.length := by
      rw [hcl, ← hr2]; simp [bvs, Slice.length]
    rw [haiv, hch, hr2, ← hn8] at hwb
    simp only [kwpAE, hpl, hk8, ite_false, kwW]
    rw [← hwb]

/-! ## `unwrap_padded` -/

theorem kw_from_be_bytes32 (a : Std.Array U8 4#usize) :
    (core.num.U32.from_be_bytes a).val = ofBe (bvs a.val) := by
  unfold core.num.U32.from_be_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact toNat_fromBEBytes _

/-- One step of `unwrap_padded`'s padding check. -/
theorem pad_step (bad x : BitVec 64) (k : BitVec 8) :
    (bad ||| (((x >>> 63) - 1#64) &&& k.setWidth 64)) = 0#64 ↔ (bad = 0#64 ∧ (x.msb = false → k = 0#8)) := by
  have hk : k.setWidth 64 = 0#64 ↔ k = 0#8 := by
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this; have := k.isLt; simp; omega
    · rintro rfl; rfl
  have hx := x.isLt
  rw [BitVec.or_eq_zero_iff, BitVec.msb_eq_decide]
  by_cases hm : 2 ^ 63 ≤ x.toNat
  · have hs : x >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      omega
    rw [hs, show (1#64 - 1#64) = 0#64 from by decide, BitVec.zero_and]
    constructor
    · rintro ⟨h, -⟩; exact ⟨h, fun h' => absurd h' (by simp; omega)⟩
    · rintro ⟨h, -⟩; exact ⟨h, rfl⟩
  · have hs : x >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      omega
    rw [hs, show (0#64 - 1#64) = BitVec.allOnes 64 from by decide, BitVec.allOnes_and, hk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 (decide_eq_false hm)⟩

/-- Every byte of `key` from `s` on at or past `c`, as the padding check's mask
computes it, is zero. -/
def PadZero (key : Slice U8) (c : U64) (s : Nat) : Prop :=
  ∀ j, s ≤ j → j < key.length → (BitVec.ofNat 64 j - c.bv).msb = false → (bvs key.val)[j]! = 0#8

theorem padZero_succ (key : Slice U8) (c : U64) (s : Nat) (hs : s < key.length) :
    PadZero key c s ↔ (((BitVec.ofNat 64 s - c.bv).msb = false → (bvs key.val)[s]! = 0#8) ∧
      PadZero key c (s + 1)) := by
  constructor
  · intro h; exact ⟨h s le_rfl hs, fun j hj => h j (by omega)⟩
  · rintro ⟨h0, h1⟩ j hj
    rcases Nat.eq_or_lt_of_le hj with rfl | hj
    · intro _; exact h0
    · exact h1 j hj

theorem unwrap_padded_loop_spec (key : Slice U8) (c : U64) (iter : core.ops.range.Range Usize) (bad : U64)
    (he : iter.end.val = key.length) (hs : iter.start.val ≤ key.length) :
    mid.aes_kw.AesKek.unwrap_padded_loop iter key c bad ⦃ r =>
      (r.bv = 0#64 ↔ bad.bv = 0#64 ∧ PadZero key c iter.start.val) ⦄ := by
  unfold mid.aes_kw.AesKek.unwrap_padded_loop
  apply loop.spec_decr_nat (fun x => key.length - x.1.start.val)
    (fun x => x.1.start.val ≤ key.length ∧ x.1.end.val = key.length ∧
      ((x.2.bv = 0#64 ∧ PadZero key c x.1.start.val) ↔ (bad.bv = 0#64 ∧ PadZero key c iter.start.val)))
  · rintro ⟨it, b⟩ ⟨hs, he, hf⟩
    simp only at hs he hf ⊢
    unfold mid.aes_kw.AesKek.unwrap_padded_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      simp only [core.hint.black_box]
      step*
      simp only [lift, bind_ok, WP.spec_ok]
      refine ⟨by omega, by rw [hen]; exact he, ?_, by omega⟩
      rw [← hf, padZero_succ key c it.start.val (by omega), hst]
      have hi1 : i1.bv = BitVec.ofNat 64 it.start.val := by
        have := usize_lt it.start
        apply BitVec.eq_of_toNat_eq; rw [UScalar.bv_toNat, i1_post, cast_u64]; simp; omega
      have hjl : it.start.val < key.val.length := by
        have : it.start.val < key.length := by omega
        simpa [Slice.length] using this
      have hk : (bvs key.val)[it.start.val]! = i4.bv := by
        rw [i4_post]; simp [bvs, getElem!_pos, hjl]
      simp only [UScalar.bv_or, UScalar.bv_and, past_post, core.num.U64.wrapping_sub_bv_eq, i3_post1, i2_post,
        hi1, core.convert.num.FromU64U8.from_bv_eq]
      rw [show U64.bv 1#u64 = 1#64 from rfl, pad_step, hk, and_assoc]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      have hz : PadZero key c it.start.val := fun j h1 h2 => absurd h2 (by omega)
      rw [← hf]
      simp [hz]
  · exact ⟨hs, he, Iff.rfl⟩

theorem u64_bv_zero (x : U64) : x.bv = 0#64 ↔ x.val = 0 := by
  constructor
  · intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.toNat_zero] at h'; exact h'
  · intro h; apply BitVec.eq_of_toNat_eq; exact h

theorem u64_eq_bv (x y : U64) : x = y ↔ x.bv = y.bv := by
  constructor
  · rintro rfl; rfl
  · intro h; cases x; cases y; simp_all

theorem or_flag_zero (x : U64) (b : Bool) :
    (x ||| core.convert.num.FromU64Bool.from (decide ¬b = true) = 0#u64) ↔ (x.bv = 0#64 ∧ b = true) := by
  rw [u64_eq_bv]
  cases b
  · change (x.bv ||| 1#64 = 0#64) ↔ _
    rw [BitVec.or_eq_zero_iff]
    simp
  · change (x.bv ||| 0#64 = 0#64) ↔ _
    simp only [BitVec.or_zero, and_true]

theorem msb_sub_iff (j : Nat) (c : U64) (hj : j < 2 ^ 63) (hc : c.val < 2 ^ 63) :
    (BitVec.ofNat 64 j - c.bv).msb = false ↔ c.val ≤ j := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : c.bv.toNat = c.val := rfl
  rw [this]
  omega

theorem drop_zero_iff (p : List (BitVec 8)) (m : Nat) :
    (∀ b ∈ p.drop m, b = 0#8) ↔ ∀ j, m ≤ j → j < p.length → p[j]! = 0#8 := by
  constructor
  · intro h j hm hj
    apply h
    rw [List.mem_iff_getElem]
    refine ⟨j - m, by simp; omega, ?_⟩
    simp [getElem!_pos, hj, show m + (j - m) = j by omega]
  · intro h b hb
    rw [List.mem_iff_getElem] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    simp only [List.length_drop] at hi
    have := h (m + i) (by omega) (by omega)
    simpa [getElem!_pos, show m + i < p.length by omega] using this

/-- What `unwrap_padded` decrypts, before its checks: KWP-AD's `A` and padded
plaintext. -/
def kwpDec (alg : Algorithm) (key c : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  if c.length / 8 - 1 = 1 then
    let s := aesBlockDecrypt alg key c
    (s.take 8, s.drop 8)
  else kwWInv alg key (c.take 8) (c.drop 8)

theorem kwpAD_eq (alg : Algorithm) (key c : List (BitVec 8)) :
    kwpAD alg key c = (fun ap : List (BitVec 8) × List (BitVec 8) =>
      if ap.1.take 4 = icv2 ∧ 8 * (c.length / 8 - 1 - 1) < ofBe (ap.1.drop 4) ∧
        ofBe (ap.1.drop 4) ≤ 8 * (c.length / 8 - 1) ∧ ∀ b ∈ ap.2.drop (ofBe (ap.1.drop 4)), b = 0
      then some (ap.2.take (ofBe (ap.1.drop 4))) else none) (kwpDec alg key c) := by
  unfold kwpAD kwpDec; rfl

/-- `unwrap_padded`'s result, once its lengths pass: KWP-AD's plaintext, or
`DecryptFailed` with the key cleared. -/
def padPost (alg : Algorithm) (kek c : List (BitVec 8)) (len : Nat)
    (res : core.result.Result (Slice U8) error.Error × (core.result.Result (Slice U8) error.Error → Slice U8)) :
    Prop :=
  match kwpAD alg kek c with
  | some p => ∃ s, res.1 = .Ok s ∧ bvs s.val = p
  | none => res.1 = .Err .DecryptFailed ∧ (res.2 res.1).val = List.replicate len 0#u8

/-- `unwrap_padded` refuses what the Rust refuses, returns `DecryptFailed` with
the key cleared exactly when KWP-AD fails, and otherwise returns KWP-AD's
plaintext. -/
theorem kek_unwrap_padded_spec (h : RunsAesHw) (hheld : low.entry.Entry.assert_held = ok ()) {alg : Algorithm}
    {kek : List (BitVec 8)} {self : mid.aes_kw.AesKek} (hk : KekIs alg kek self) (wrapped key : Slice U8) :
    mid.aes_kw.AesKek.unwrap_padded self wrapped key ⦃ res =>
      if wrapped.length < 16 ∨ wrapped.length % 8 ≠ 0 then res.1 = .Err .DecryptFailed ∧ res.2 res.1 = key
      else if key.length ≠ wrapped.length - 8 then res.1 = .Err .WrongLength ∧ res.2 res.1 = key
      else match kwpAD alg kek (bvs wrapped.val) with
        | some p => ∃ s, res.1 = .Ok s ∧ bvs s.val = p
        | none => res.1 = .Err .DecryptFailed ∧ (res.2 res.1).val = List.replicate key.length 0#u8 ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.aes_kw.AesKek.unwrap_padded
  rw [he, bind_ok]
  by_cases h16 : wrapped.length < 16
  · have hlt : Slice.len wrapped < 16#usize := by scalar_tac
    simp only [hlt, ite_true, h16, true_or, WP.spec_ok, and_self]
  have hlt : ¬ Slice.len wrapped < 16#usize := by scalar_tac
  simp only [hlt, ite_false, h16, false_or]
  step as ⟨b, hb⟩
  cases b
  · have h8 : ¬ wrapped.length % 8 = 0 := by simpa using hb
    simp [h8]
  have h8 : wrapped.length % 8 = 0 := by simpa using hb
  simp only [ite_true, h8, ne_eq, not_true_eq_false, ite_false]
  step as ⟨i4, hi4⟩
  by_cases hw : key.length = wrapped.length - 8
  swap
  · have hne : (Slice.len key != i4) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hw; rw [← Slice.len_val, he, hi4, Slice.len_val]
    simp only [hne, hw, ite_true, not_false_eq_true, WP.spec_ok, and_self]
  have hne : ¬ (Slice.len key != i4) = true := by
    simp only [bne_iff_ne, ne_eq, not_not]; apply UScalar.eq_of_val_eq
    rw [hi4, Slice.len_val, Slice.len_val, hw]
  simp only [hne, Bool.false_eq_true, ite_false, hw, not_true_eq_false]
  step with kek_key_spec hk as ⟨s, hsl, hsb⟩
  step with dec_key_new_spec h alg s hsl as ⟨adk, hwk, hadk1, hadk2⟩
  have hdk : AesDecIs alg kek adk := ⟨hwk, hadk1, by rw [← hsb]; exact hadk2⟩
  simp only [core.mem.manually_drop.ManuallyDrop.new,
    core.mem.manually_drop.ManuallyDrop.Insts.CoreOpsDerefDeref.deref, bind_ok]
  have hwl : (bvs wrapped.val).length = wrapped.length := by simp [bvs, Slice.length]
  change WP.spec _ (padPost alg kek (bvs wrapped.val) (wrapped.length - 8))
  apply WP.spec_bind (Pₘ := fun p => p.1.length = key.length ∧
    (bvs p.2.val, bvs p.1.val) = kwpDec alg kek (bvs wrapped.val))
  · split
    · rename_i h8k
      have hk8 : key.length = 8 := by
        have := congrArg UScalar.val h8k; rw [Slice.len_val] at this; simpa using this
      have hw16 : wrapped.length = 16 := by omega
      step as ⟨r, hr⟩
      rcases r with arr | ⟨⟩
      swap
      · exact absurd hw16 hr
      obtain ⟨harr, -⟩ := hr
      simp only [core.result.Result.unwrap, bind_ok]
      step with dec_bytes hdk arr as ⟨blk, hblk⟩
      step*
      subst key2 s2
      have h8' : (8#usize : Usize).val ≤ blk.to_slice.length := by simp
      simp only [core.slice.Slice.first_chunk, h8', ↓reduceDIte, core.option.Option.unwrap, Result.ofOption,
        bind_ok, WP.spec_ok]
      refine ⟨by rw [s1_post1]; simp [hk8], ?_⟩
      have h1 : (bvs wrapped.val).length / 8 - 1 = 1 := by rw [hwl, hw16]
      simp only [kwpDec, h1, ite_true]
      rw [← harr, ← hblk, s1_post]
      simp [bvs, List.map_take, List.map_drop]
    · rename_i h8k
      have hk8 : key.length ≠ 8 := by
        intro h'; apply h8k; apply UScalar.eq_of_val_eq; rw [Slice.len_val, h']; rfl
      step as ⟨wa, wc, hwal, hwcl, hwav, hwcv⟩
      step as ⟨key2, hkey2⟩
      subst key2
      step as ⟨r, hr⟩
      rcases r with arr | ⟨⟩
      swap
      · exact absurd hwal hr
      obtain ⟨harr, -⟩ := hr
      simp only [core.result.Result.unwrap, bind_ok]
      have hc8 : wc.length % 8 = 0 := by omega
      step with as_chunks_mut_8 wc hc8 as ⟨ch, rest, cback, hcl, hch, hcback⟩
      step with unwrap_blocks_spec hdk arr ch
        (by have := usize_lt wc.len; rw [Slice.len_val] at this; rw [hcl]; omega) as ⟨ua, ur, hul, hub⟩
      have hc := hcback ur (by rw [hul, hcl])
      refine ⟨by rw [hc.2]; omega, ?_⟩
      have ht : (bvs wrapped.val).take 8 = bvs arr.val := by rw [harr, hwav]; simp [bvs, List.map_take]
      have hd : (bvs wrapped.val).drop 8 = bvs wc.val := by rw [hwcv]; simp [bvs, List.map_drop]
      have hn8 : (bvs wc.val).length / 8 = ch.length := by rw [hcl]; simp [bvs, Slice.length]
      rw [hch, ← hn8] at hub
      simp only [kwpDec, hwl, show ¬(wrapped.length / 8 - 1 = 1) by omega, ite_false, kwWInv, ht, hd, ← hub, hc.1]
  · rintro ⟨key1, aiv⟩ ⟨hl1, hdec⟩
    simp only at hl1 hdec
    simp only [Std.uncurry]
    have h4 : (4#usize : Usize).val ≤ aiv.to_slice.length := by simp
    simp only [lift, bind_ok, core.slice.Slice.last_chunk, core.option.Option.unwrap,
      Result.ofOption, core.hint.black_box]
    rw [dite_eq_left_of_eq_true (eq_true h4)]
    simp only [bind_ok]
    set a := Std.Array.from (List.drop (aiv.to_slice.length - (4#usize : Usize).val) aiv.to_slice.val) _ with ha
    set claimed := core.convert.num.FromU64U32.from (core.num.U32.from_be_bytes a) with hclaimed
    step as ⟨bad, hbad, hbad'⟩
    step as ⟨i12, hi12⟩
    have hkl := Slice.len_val key1
    step with unwrap_padded_loop_spec key1 claimed { start := i12, «end» := Slice.len key1 } bad
      (by simp only [hkl]) (by simp only; omega) as ⟨bad1, hbad1⟩
    step as ⟨s2, hs2⟩
    step with ct_equal_spec hheld as ⟨b1, hb1⟩
    simp only [low.ct.into_public, bind_ok]
    -- the claimed length
    have hav : bvs a.val = (bvs aiv.val).drop 4 := by
      rw [ha]; simp [bvs, List.map_drop]
    have hm : claimed.val = ofBe ((bvs aiv.val).drop 4) := by
      rw [hclaimed, core.convert.num.FromU64U32.from_val_eq, kw_from_be_bytes32, hav]
    have hm32 : claimed.val < 2 ^ 32 := by
      rw [hclaimed, core.convert.num.FromU64U32.from_val_eq]; scalar_tac
    have hLlt := usize_lt key1.len
    rw [hkl] at hLlt
    have hL : key1.length = wrapped.length - 8 := by omega
    have hbadz : bad.bv = 0#64 ↔ (key1.length - 8 < claimed.val ∧ claimed.val ≤ key1.length) := by
      rw [u64_bv_zero, hbad, core.num.U64.wrapping_sub_val_eq, cast_u64, hkl, Nat.shiftRight_eq_div_pow]
      simp only [UScalar.size, UScalarTy.numBits]
      omega
    have hb1' : b1 = true ↔ (bvs aiv.val).take 4 = icv2 := by
      rw [hb1, decide_eq_true_iff, ← bvs_AIV, ← Std.Array.val_to_slice, ← bvs_inj, hs2]
      simp [bvs, List.map_take]
    have hpad : key1.length - 8 < claimed.val → claimed.val ≤ key1.length →
        (PadZero key1 claimed i12.val ↔ ∀ b ∈ (bvs key1.val).drop claimed.val, b = 0#8) := by
      intro h1 h2
      rw [drop_zero_iff, hi12, hkl]
      have hbl : (bvs key1.val).length = key1.length := by simp [bvs, Slice.length]
      constructor
      · intro hz j hmj hj
        rw [hbl] at hj
        exact hz j (by omega) hj ((msb_sub_iff j claimed (by omega) (by omega)).2 hmj)
      · intro hz j _ hj hmsb
        exact hz j ((msb_sub_iff j claimed (by omega) (by omega)).1 hmsb) (by rw [hbl]; exact hj)
    have hn : (bvs wrapped.val).length / 8 - 1 = key1.length / 8 := by rw [hwl]; omega
    have hcond : (bad1 ||| core.convert.num.FromU64Bool.from (decide ¬b1 = true) = 0#u64) ↔
        ((bvs aiv.val).take 4 = icv2 ∧ 8 * ((bvs wrapped.val).length / 8 - 1 - 1) < ofBe ((bvs aiv.val).drop 4) ∧
          ofBe ((bvs aiv.val).drop 4) ≤ 8 * ((bvs wrapped.val).length / 8 - 1) ∧
          ∀ b ∈ (bvs key1.val).drop (ofBe ((bvs aiv.val).drop 4)), b = 0) := by
      rw [or_flag_zero, hbad1, hb1', hn, ← hm]
      constructor
      · rintro ⟨⟨hz, hp⟩, hi⟩
        obtain ⟨h1, h2⟩ := hbadz.1 hz
        exact ⟨hi, by omega, by omega, (hpad h1 h2).1 hp⟩
      · rintro ⟨hi, h1, h2, hp⟩
        have h1' : key1.length - 8 < claimed.val := by omega
        have h2' : claimed.val ≤ key1.length := by omega
        exact ⟨⟨hbadz.2 ⟨h1', h2'⟩, (hpad h1' h2').2 hp⟩, hi⟩
    unfold padPost
    rw [kwpAD_eq, ← hdec]
    dsimp only
    by_cases hc : (bvs aiv.val).take 4 = icv2 ∧ 8 * ((bvs wrapped.val).length / 8 - 1 - 1) < ofBe ((bvs aiv.val).drop 4) ∧
          ofBe ((bvs aiv.val).drop 4) ≤ 8 * ((bvs wrapped.val).length / 8 - 1) ∧
          ∀ b ∈ (bvs key1.val).drop (ofBe ((bvs aiv.val).drop 4)), b = 0
    · rw [ite_eq_left (hcond.2 hc), ite_eq_left hc]
      simp only [low.ct.public_slice, bind_ok]
      have hmle : claimed.val ≤ key1.length := by rw [hn, ← hm] at hc; omega
      have hcast : (UScalar.cast .Usize claimed).val = claimed.val := by
        rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt
        have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by norm_num) (by cases System.Platform.numBits_eq <;> simp [*])
        omega
      step as ⟨s4, back, hs4⟩
      refine ⟨s4, rfl, ?_⟩
      rw [hs4, hcast, hm]
      simp [bvs, List.map_take]
    · rw [ite_eq_right (fun h => hc (hcond.1 h)), ite_eq_right hc]
      step as ⟨key2, hkey2, hkey2v⟩
      rw [hkey2v, hL]

end rind.x86_64
