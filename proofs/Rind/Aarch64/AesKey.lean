import Rind.Aarch64.Funs
import Rind.Aes
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# The crypto extension's AES key expansion and block cipher

`Rind.Aarch64.Neon` models the NEON intrinsics they call. The key expansions
compute FIPS 197's round keys as Vale's AES spec lays them out, and the block
ciphers Vale's `eval_cipher`, as `Rind.X86_64.AesKey` proves of AES-NI's:
`AESE` XORs the round key before its `SubBytes` and `ShiftRows`, where
`AESENC` XORs it after `MixColumns`, so the two run the same rounds grouped
differently. The same holds of AES-128's, AES-192's, and AES-256's, and of the
decryption schedule, which `AESD` and `AESIMC` run as FIPS 197's equivalent
inverse cipher, `Rind.AesInverse`, groups `AESDEC`'s rounds.
-/

namespace rind.aarch64

/-- A byte array's bytes. -/
abbrev bvs (l : List U8) : List (BitVec 8) := l.map (·.bv)

/-! ## Vectors as bytes -/

theorem load_eq (b : Std.Array Std.U8 16#usize) : low.aarch64.aes.load b = ok (loadBytes b.val) := by
  simp only [low.aarch64.aes.load, lift, core.num.U128.from_le_bytes, bind_ok,
    core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_p128, loadBytes, leBytesToQuad32]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem store_eq (v : BitVec 128) : low.aarch64.aes.store v = ok (storeBytes v) := by
  simp only [low.aarch64.aes.store, core.core_arch.arm_shared.neon.generated.vreinterpretq_p128_u8, bind_ok,
    core.num.U128.to_le_bytes, storeBytes, toLEBytes_eq]

theorem zero_eq : low.aarch64.aes.zero = ok 0 := by
  simp only [low.aarch64.aes.zero, core.core_arch.arm_shared.neon.generated.vdupq_n_u8]
  congr 1

/-- `EXT` of a zero vector and `t`: `t` shifted up by `16 - n` bytes. -/
theorem ext_zero (t : BitVec 128) (n : Nat) (hn : n < 16) :
    ((t ++ (0 : BitVec 128)) >>> (8 * n)).setWidth 128 = t <<< (8 * (16 - n)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft]
  by_cases h : 8 * n + i < 128
  · simp [h, show i < 8 * (16 - n) by omega]
  · simp [h, show ¬ i < 8 * (16 - n) by omega]
    congr 1; omega

theorem xor_prefix_eq (t : BitVec 128) : low.aarch64.aes.xor_prefix t = ok (xorPrefix t) := by
  have e12 : (12#i32).bv.toNat % 16 = 12 := by decide
  have e8 : (8#i32).bv.toNat % 16 = 8 := by decide
  simp only [low.aarch64.aes.xor_prefix, zero_eq, core.core_arch.arm_shared.neon.generated.vextq_u8,
    core.core_arch.arm_shared.neon.generated.veorq_u8, bind_ok, e12, e8, ext_zero _ 12 (by omega),
    ext_zero _ 8 (by omega), Nat.reduceMul, Nat.reduceSub, xorPrefix]

/-- `SubBytes` and `ShiftRows` of four equal words, as `AESE` with a zero key
runs them: `SubWord` of each. -/
theorem shiftRows_subBytes_dup (w : BitVec 32) :
    shiftRows (subBytes (ofLanes32 fun _ => w)) = ofLanes32 fun _ => subWord w := by
  rw [← subBytes_shiftRows, subBytes_shiftRows_dup]

/-- `sub_rot_word`'s value: `SubWord(RotWord(w3)) ^ rcon` in each word, where
`w3` is `t`'s last. -/
def subRotWord (t : BitVec 128) (rcon : Std.U32) : BitVec 128 :=
  ofLanes32 fun _ => subWord (rotWord (lane32 t 3)) ^^^ rcon.bv

theorem sub_rot_word_eq (t : BitVec 128) (rcon : Std.U32) :
    low.aarch64.aes.sub_rot_word t rcon = ok (subRotWord t rcon) := by
  simp only [low.aarch64.aes.sub_rot_word, load_eq, zero_eq, low.aarch64.aes.sub_rot_word.ROT_WORD_3,
    core.core_arch.aarch64.neon.generated.vqtbl1q_u8, core.core_arch.arm_shared.neon.generated.vaeseq_u8,
    core.core_arch.arm_shared.neon.generated.vdupq_n_u32,
    core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_u32,
    core.core_arch.arm_shared.neon.generated.veorq_u8, bind_ok, subRotWord]
  congr 1
  apply eq_of_byte_eq
  intro i hi
  interval_cases i <;>
    simp (config := { decide := true }) [loadBytes, Std.Array.make_val, byte_xor, byte_ofLanes32,
      byte_subBytes, byte_shiftRows, byte_ofBytes, byte_leBytesToQuad32, wbyte_xor, wbyte_subWord,
      wbyte_rotWord, wbyte_lane32]

theorem rcon_eq {r : Nat} (hr : r < 10) : aesRcon r = (low.aarch64.aes.RCON.val[r]!).bv := by
  interval_cases r <;> (unfold low.aarch64.aes.RCON; decide)

/-- AES-128's round key after round key `s`. -/
theorem aes128_next (kw : List (BitVec 32)) {s : Nat} (hs : s < 10) :
    xorPrefix (roundKey .AES_128 kw s) ^^^ subRotWord (roundKey .AES_128 kw s) low.aarch64.aes.RCON.val[s]! =
      roundKey .AES_128 kw (s + 1) := by
  rw [subRotWord, nextKey_eq, roundKey128_succ, rcon_eq hs]
  simp only [roundKey, (lane32_mkfour _ _ _ _).2.2.2]

/-- `aes128_expand`'s loop: from round key `iter.start`, held in `t` and
`out`, it writes the rest. -/
theorem aes128_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.Range Usize)
    (t : core.core_arch.arm_shared.neon.uint8x16_t) (out : Std.Array core.core_arch.arm_shared.neon.uint8x16_t 11#usize)
    (hs : iter.start.val ≤ 10) (he : iter.end.val = 10) (ht : t = roundKey .AES_128 kw iter.start.val)
    (ho : ∀ r ≤ iter.start.val, out.val[r]! = roundKey .AES_128 kw r) :
    low.aarch64.aes.aes128_expand_loop iter t out ⦃ rk => ∀ r < 11, rk.val[r]! = roundKey .AES_128 kw r ⦄ := by
  unfold low.aarch64.aes.aes128_expand_loop
  apply loop.spec_decr_nat (fun x => 10 - x.1.start.val)
    (fun x => x.1.start.val ≤ 10 ∧ x.1.end.val = 10 ∧ x.2.1 = roundKey .AES_128 kw x.1.start.val ∧
      ∀ r ≤ x.1.start.val, x.2.2.val[r]! = roundKey .AES_128 kw r)
  · rintro ⟨it, t, out⟩ ⟨hs, he, ht, ho⟩
    simp only at hs he ht ho ⊢
    unfold low.aarch64.aes.aes128_expand_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      simp only [xor_prefix_eq, sub_rot_word_eq, core.core_arch.arm_shared.neon.generated.veorq_u8, bind_ok]
      step*
      have hi1 : i1 = low.aarch64.aes.RCON.val[it.start.val]! := by
        rw [i1_post]; exact (getElem!_pos _ _ _).symm
      refine ⟨by omega, by rw [hen]; exact he, ?_, ?_, by omega⟩
      · rw [hst, ht, hi1]; exact aes128_next kw (by omega)
      · intro r hr
        rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), i2_post]
        split_ifs with h
        · rw [← h, ht, hi1]; exact aes128_next kw (by omega)
        · exact ho r (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      intro r hr
      exact ho r (by omega)
  · exact ⟨hs, he, ht, ho⟩

/-- The AES-128 key `key` expands to FIPS 197's round keys, each its 16 bytes in order. -/
@[step]
theorem aes128_expand_spec (key : Std.Array Std.U8 16#usize)
    (out : Std.Array core.core_arch.arm_shared.neon.uint8x16_t 11#usize) :
    low.aarch64.aes.aes128_expand key out ⦃ rk =>
      rk.val = keyToRoundKeys .AES_128 (seqNat8ToSeqNat32LE (key.val.map (·.bv))) ⦄ := by
  set kw := seqNat8ToSeqNat32LE (key.val.map (·.bv))
  have hl : (key.val.map (·.bv)).length = 16 := by simp
  have h0 : loadBytes key.val = roundKey .AES_128 kw 0 := by
    simp only [roundKey, keyWord_key .AES_128 kw (show 0 < 4 by decide),
      keyWord_key .AES_128 kw (show 1 < 4 by decide), keyWord_key .AES_128 kw (show 2 < 4 by decide),
      keyWord_key .AES_128 kw (show 3 < 4 by decide), Nat.mul_zero, Nat.zero_add]
    exact load_eq_mkfour _ hl
  unfold low.aarch64.aes.aes128_expand
  simp only [load_eq, bind_ok]
  apply WP.spec_mono (aes128_loop_spec kw _ _ _ (by simp) (by simp) (by rw [h0]; simp) ?_)
  · intro rk hrk
    rw [keyToRoundKeys_eq]
    exact eq_range_map _ _ (by simp [nr]) hrk
  · intro r hr
    simp only [show r = 0 by simpa using hr, Std.Array.repeat_val]
    simp [h0]

/-! ## AES-256 -/

/-- AES-256's even round key after round keys `2 * s` and `2 * s + 1`. -/
theorem aes256_next_even (kw : List (BitVec 32)) {s : Nat} (hs : s < 7) :
    xorPrefix (roundKey .AES_256 kw (2 * s)) ^^^
        subRotWord (roundKey .AES_256 kw (2 * s + 1)) low.aarch64.aes.RCON.val[s]! =
      roundKey .AES_256 kw (2 * s + 2) := by
  rw [subRotWord, nextKey_eq, roundKey256_even, rcon_eq (by omega)]

/-- `aes256_expand`'s loop: from round keys `2 * iter.start` and the next,
held in `a`, `b`, and `out`, it writes the rest. -/
theorem aes256_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.Range Usize)
    (a b : core.core_arch.arm_shared.neon.uint8x16_t) (out : Std.Array core.core_arch.arm_shared.neon.uint8x16_t 15#usize)
    (hs : iter.start.val ≤ 6) (he : iter.end.val = 7) (ha : a = roundKey .AES_256 kw (2 * iter.start.val))
    (hb : b = roundKey .AES_256 kw (2 * iter.start.val + 1))
    (ho : ∀ r ≤ 2 * iter.start.val + 1, out.val[r]! = roundKey .AES_256 kw r) :
    low.aarch64.aes.aes256_expand_loop iter a b out ⦃ rk => ∀ r < 15, rk.val[r]! = roundKey .AES_256 kw r ⦄ := by
  unfold low.aarch64.aes.aes256_expand_loop
  apply loop.spec_decr_nat (fun x => 7 - x.1.start.val)
    (fun x => x.1.start.val ≤ 6 ∧ x.1.end.val = 7 ∧ x.2.1 = roundKey .AES_256 kw (2 * x.1.start.val) ∧
      x.2.2.1 = roundKey .AES_256 kw (2 * x.1.start.val + 1) ∧
      ∀ r ≤ 2 * x.1.start.val + 1, x.2.2.2.val[r]! = roundKey .AES_256 kw r)
  · rintro ⟨it, a, b, out⟩ ⟨hs, he, ha, hb, ho⟩
    simp only at hs he ha hb ho ⊢
    unfold low.aarch64.aes.aes256_expand_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
    subst ho'
    have e3 : (3#i32).bv.toNat % 4 = 3 := by decide
    simp only [xor_prefix_eq, sub_rot_word_eq, core.core_arch.arm_shared.neon.generated.veorq_u8, bind_ok,
      zero_eq, core.core_arch.arm_shared.neon.generated.vreinterpretq_u32_u8,
      core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_u32,
      core.core_arch.arm_shared.neon.generated.vdupq_laneq_u32, e3,
      core.core_arch.arm_shared.neon.generated.vaeseq_u8,
      show ∀ x : BitVec 128, x ^^^ (0 : BitVec 128) = x from fun x => BitVec.xor_zero, shiftRows_subBytes_dup,
      nextKey_eq]
    step*
    all_goals
      have hi1 : i1 = low.aarch64.aes.RCON.val[it.start.val]! := by
        rw [i1_post]; exact (getElem!_pos _ _ _).symm
      have ha1 : xorPrefix a ^^^ subRotWord b i1 = roundKey .AES_256 kw (2 * it.start.val + 2) := by
        rw [ha, hb, hi1]; exact aes256_next_even kw (by omega)
    case h1 =>
      have hs6 : it.start.val = 6 := by rw [‹it.start = 6#usize›]; rfl
      intro r hr
      rw [index_mut_back_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), i3_post, i2_post]
      split_ifs with h
      · rw [← h, ha1]
      · exact ho r (by omega)
    have hs6 : it.start.val ≠ 6 := fun h => ‹¬it.start = 6#usize› (UScalar.eq_of_val_eq (by rw [h]; rfl))
    have hb1 : nextKey b (subWord (lane32 (xorPrefix a ^^^ subRotWord b i1) 3)) =
        roundKey .AES_256 kw (2 * it.start.val + 3) := by
      rw [ha1, hb, roundKey256_odd]
    refine ⟨by omega, by rw [hen]; exact he, ?_, ?_, ?_, by omega⟩
    · rw [hst, ha1, show 2 * (it.start.val + 1) = 2 * it.start.val + 2 by omega]
    · rw [hst, hb1, show 2 * (it.start.val + 1) + 1 = 2 * it.start.val + 3 by omega]
    · intro r hr
      rw [a2_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), index_mut_back_post,
        Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), i4_post, i3_post, i2_post]
      split_ifs with h h'
      · rw [← h, hb1]
      · rw [← h', ha1]
      · exact ho r (by omega)
  · exact ⟨hs, he, ha, hb, ho⟩

/-- The AES-256 key `key` expands to FIPS 197's round keys, each its 16 bytes in order. -/
@[step]
theorem aes256_expand_spec (key : Std.Array Std.U8 32#usize)
    (out : Std.Array core.core_arch.arm_shared.neon.uint8x16_t 15#usize) :
    low.aarch64.aes.aes256_expand key out ⦃ rk =>
      rk.val = keyToRoundKeys .AES_256 (seqNat8ToSeqNat32LE (key.val.map (·.bv))) ⦄ := by
  set l := key.val.map (·.bv)
  set kw := seqNat8ToSeqNat32LE l
  have hl : l.length = 32 := by simp [l]
  unfold low.aarch64.aes.aes256_expand
  step*
  have hsl : s.len = 16#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, hsl, ↓reduceDIte, core.result.Result.unwrap,
    bind_ok, load_eq]
  step*
  have hsl1 : s1.len = 16#usize := by scalar_tac
  simp only [hsl1, ↓reduceDIte, bind_ok, Std.Array.from_val]
  step*
  have hkl : key.val.length = 32 := by simp
  have h0 : loadBytes s.val = roundKey .AES_256 kw 0 := by
    simp only [roundKey, keyWord_key .AES_256 kw (show 0 < 8 by decide),
      keyWord_key .AES_256 kw (show 1 < 8 by decide), keyWord_key .AES_256 kw (show 2 < 8 by decide),
      keyWord_key .AES_256 kw (show 3 < 8 by decide), Nat.mul_zero, Nat.zero_add, loadBytes]
    refine load_words l _ 0 (by omega) ?_
    intro i hi
    have hk : i < key.val.length := by omega
    simp [l, s_post, List.slice, List.getElem!_eq_getElem?_getD, hi, List.getElem?_eq_getElem hk]
  have h1 : loadBytes s1.val = roundKey .AES_256 kw 1 := by
    simp only [roundKey, keyWord_key .AES_256 kw (show 4 < 8 by decide),
      keyWord_key .AES_256 kw (show 5 < 8 by decide), keyWord_key .AES_256 kw (show 6 < 8 by decide),
      keyWord_key .AES_256 kw (show 7 < 8 by decide), Nat.mul_one, loadBytes]
    refine load_words l _ 1 (by omega) ?_
    intro i hi
    simp [l, s1_post, List.getElem!_eq_getElem?_getD, List.getElem?_drop]
  apply WP.spec_mono (aes256_loop_spec kw _ _ _ _ (by simp) (by simp) (by rw [h0]; simp) (by rw [h1]; simp) ?_)
  · intro rk hrk
    rw [keyToRoundKeys_eq]
    exact eq_range_map _ _ (by simp [nr]) hrk
  · intro r hr
    rw [a3_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp), Std.Array.repeat_val]
    have hr' : r ≤ 1 := by simpa using hr
    split_ifs with h
    · rw [← show (1#usize : Usize).val = 1 from rfl] at h1; rw [← h, h1]
    · have : r = 0 := by simp at h; omega
      subst this; simp [h0]

/-! ## AES-192 -/

/-- `aes192_expand`'s `TBL` indices: RotWord of word 1 in each word. -/
def rotWord1 : BitVec 128 := loadBytes low.aarch64.aes.aes192_expand.ROT_WORD_1.val

/-- A step's first four words, whose first takes `RotWord`, `SubWord`, and the
round constant of `b`'s word 1. -/
theorem rot_step1 (a b : BitVec 128) (rcon : Std.U32) :
    xorPrefix a ^^^ (shiftRows (subBytes (ofBytes fun i =>
      if (byte rotWord1 i).toNat < 16 then byte b (byte rotWord1 i).toNat else 0)) ^^^
        ofLanes32 fun _ => rcon.bv) = nextKey a (subWord (rotWord (lane32 b 1)) ^^^ rcon.bv) := by
  apply eq_of_byte_eq
  intro i hi
  interval_cases i <;>
    simp (config := { decide := true }) [rotWord1, loadBytes, low.aarch64.aes.aes192_expand.ROT_WORD_1,
      Std.Array.make_val, xorPrefix, byte_xor, byte_shl, byte_ofLanes32, byte_subBytes, byte_shiftRows,
      byte_ofBytes, byte_leBytesToQuad32, nextKey, byte_mkfour, wbyte_xor, wbyte_subWord, wbyte_rotWord,
      wbyte_lane32, BitVec.xor_assoc]

/-- `aes192_expand`'s loop: from step `iter.start`, with the step before's
words in `a` and `b`'s low half, and the round keys they complete in `out`, it
writes the rest. -/
theorem aes192_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.Range Usize)
    (a b m : core.core_arch.arm_shared.neon.uint8x16_t)
    (out : Std.Array core.core_arch.arm_shared.neon.uint8x16_t 13#usize)
    (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 8) (he : iter.end.val = 9) (hm : m = rotWord1)
    (ha : a = key192 kw (iter.start.val - 1))
    (hb0 : lane32 b 0 = keyWord .AES_192 kw (6 * (iter.start.val - 1) + 4))
    (hb1 : lane32 b 1 = keyWord .AES_192 kw (6 * (iter.start.val - 1) + 5))
    (ho : ∀ r, 4 * r + 4 ≤ 6 * iter.start.val → out.val[r]! = roundKey .AES_192 kw r) :
    low.aarch64.aes.aes192_expand_loop iter a b m out ⦃ rk => ∀ r < 13, rk.val[r]! = roundKey .AES_192 kw r ⦄ := by
  unfold low.aarch64.aes.aes192_expand_loop
  apply loop.spec_decr_nat (fun x => 9 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 8 ∧ x.1.end.val = 9 ∧
      x.2.1 = key192 kw (x.1.start.val - 1) ∧
      lane32 x.2.2.1 0 = keyWord .AES_192 kw (6 * (x.1.start.val - 1) + 4) ∧
      lane32 x.2.2.1 1 = keyWord .AES_192 kw (6 * (x.1.start.val - 1) + 5) ∧
      ∀ r, 4 * r + 4 ≤ 6 * x.1.start.val → x.2.2.2.val[r]! = roundKey .AES_192 kw r)
  · rintro ⟨it, a, b, out⟩ ⟨hs1, hs, he, ha, hb0, hb1, ho⟩
    simp only at hs1 hs he ha hb0 hb1 ho ⊢
    unfold low.aarch64.aes.aes192_expand_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
    subst ho' hm
    have e3 : (3#i32).bv.toNat % 4 = 3 := by decide
    have e8 : (8#i32).bv.toNat % 16 = 8 := by decide
    have e12 : (12#i32).bv.toNat % 16 = 12 := by decide
    simp only [xor_prefix_eq, core.core_arch.arm_shared.neon.generated.veorq_u8, bind_ok, zero_eq,
      core.core_arch.aarch64.neon.generated.vqtbl1q_u8, core.core_arch.arm_shared.neon.generated.vaeseq_u8,
      core.core_arch.arm_shared.neon.generated.vdupq_n_u32,
      core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_u32,
      core.core_arch.arm_shared.neon.generated.vreinterpretq_u32_u8,
      core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_u64,
      core.core_arch.arm_shared.neon.generated.vreinterpretq_u64_u8,
      core.core_arch.aarch64.neon.generated.vzip1q_u64, core.core_arch.arm_shared.neon.generated.vextq_u8,
      core.core_arch.arm_shared.neon.generated.vdupq_laneq_u32, e3, e8, e12, ext_zero _ 12 (by omega),
      Nat.reduceMul, Nat.reduceSub, show ∀ x : BitVec 128, x ^^^ (0 : BitVec 128) = x from fun x => BitVec.xor_zero,
      rot_step1, zip_lo, ext_hi]
    step*
    have hi1 : i1 = low.aarch64.aes.RCON.val[it.start.val - 1]! := by
      rw [i1_post, ← i_post]; exact (getElem!_pos _ _ _).symm
    have hA : nextKey a (subWord (rotWord (lane32 b 1)) ^^^ i1.bv) = key192 kw it.start.val := by
      rw [hi1, ← rcon_eq (by omega), ha, hb1, ← key192_succ, Nat.sub_add_cancel hs1]
    simp only [hA]
    by_cases hp : it.start.val % 2 = 1
    · obtain ⟨k, hk⟩ : ∃ k, it.start.val = 2 * k + 1 := ⟨it.start.val / 2, by omega⟩
      have h2 : i2 = 1#usize := UScalar.eq_of_val_eq (by rw [i2_post, hp]; rfl)
      have h8 : it.start ≠ 8#usize := fun h => by
        have := congrArg UScalar.val h; simp at this; omega
      have hj : it.start.val - 1 = 2 * k := by omega
      rw [hj] at hb0 hb1
      simp only [h2, h8, ite_true, ite_false]
      step*
      have hb := key192_b kw (2 * k) b hb0 hb1
      have hx1 : x.val = 3 * k + 1 := by omega
      have hx2 : i5.val = 3 * k + 2 := by omega
      rw [hk] at a2_post out1_post
      rw [hst, hk]
      refine ⟨by omega, by omega, by rw [hen]; exact he, by simp, ?_, ?_, ?_, by omega⟩
      · rw [show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]; exact hb.1
      · rw [show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]; exact hb.2
      · intro r hr
        rw [a2_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), out1_post, Std.Array.set_val_eq,
          getElem!_set _ _ _ (by simp; omega)]
        split_ifs with h h'
        · rw [← h, hx2, roundKey192_odd2, hb.1, hb.2]
        · rw [← h', hx1, roundKey192_odd1, hb0, hb1]
        · exact ho r (by omega)
    · obtain ⟨k, hk⟩ : ∃ k, it.start.val = 2 * k + 2 := ⟨it.start.val / 2 - 1, by omega⟩
      have h2 : i2 ≠ 1#usize := fun h => by
        have := congrArg UScalar.val h; simp at this; omega
      simp only [h2, ite_false]
      step*
      all_goals
        have hx : x.val = 3 * k + 3 := by omega
        rw [hk] at out1_post
      case h1 =>
        have hk3 : k = 3 := by
          have := congrArg UScalar.val ‹it.start = 8#usize›; simp at this; omega
        intro r hr
        rw [out1_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
        split_ifs with h
        · rw [← h, hx, roundKey192_even]
        · exact ho r (by omega)
      have h8 : it.start.val ≠ 8 := fun h => ‹¬it.start = 8#usize› (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have hj : it.start.val - 1 = 2 * k + 1 := by omega
      rw [hj] at hb0 hb1
      have hb := key192_b kw (2 * k + 1) b hb0 hb1
      rw [hst, hk]
      refine ⟨by omega, by omega, by rw [hen]; exact he, by simp, ?_, ?_, ?_, by omega⟩
      · rw [show 2 * k + 2 + 1 - 1 = 2 * k + 1 + 1 by omega]; exact hb.1
      · rw [show 2 * k + 2 + 1 - 1 = 2 * k + 1 + 1 by omega]; exact hb.2
      · intro r hr
        rw [out1_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
        split_ifs with h
        · rw [← h, hx, roundKey192_even]
        · exact ho r (by omega)
  · exact ⟨hs1, hs, he, ha, hb0, hb1, ho⟩

/-- A `u64` read little-endian, widened to a vector: its bytes, the first lowest. -/
theorem load64_eq (a : Std.Array Std.U8 8#usize) :
    (core.convert.num.FromU128U64.from (core.num.U64.from_le_bytes a)).bv = loadBytes a.val := by
  simp only [loadBytes, leBytesToQuad32, core.convert.num.FromU128U64.from_bv_eq, core.num.U64.from_le_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

/-- The AES-192 key `key` expands to FIPS 197's round keys, each its 16 bytes in order. -/
@[step]
theorem aes192_expand_spec (key : Std.Array Std.U8 24#usize) :
    low.aarch64.aes.aes192_expand key ⦃ rk =>
      rk.val = keyToRoundKeys .AES_192 (seqNat8ToSeqNat32LE (key.val.map (·.bv))) ⦄ := by
  set l := key.val.map (·.bv)
  set kw := seqNat8ToSeqNat32LE l
  have hl : l.length = 24 := by simp [l]
  unfold low.aarch64.aes.aes192_expand
  step*
  have hsl : s.len = 16#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, hsl, ↓reduceDIte, core.result.Result.unwrap,
    bind_ok, load_eq]
  step*
  rcases r1 with a2 | ⟨⟩
  swap
  · exfalso; apply r1_post; simp [s1_post1]
  obtain ⟨ha2, -⟩ := r1_post
  simp only [bind_ok, lift, core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_p128,
    Std.Array.from_val, load64_eq]
  have hkl : key.val.length = 24 := by simp
  have h0 : loadBytes s.val = key192 kw 0 := by
    simp only [key192, keyWord_key .AES_192 kw (show 0 < 6 by decide),
      keyWord_key .AES_192 kw (show 1 < 6 by decide), keyWord_key .AES_192 kw (show 2 < 6 by decide),
      keyWord_key .AES_192 kw (show 3 < 6 by decide), Nat.mul_zero, Nat.zero_add, loadBytes]
    refine load_words l _ 0 (by omega) ?_
    intro i hi
    have hk : i < key.val.length := by omega
    simp [l, s_post, List.slice, List.getElem!_eq_getElem?_getD, hi, List.getElem?_eq_getElem hk]
  have hb : ∀ j < 2, lane32 (loadBytes a2.val) j = keyWord .AES_192 kw (4 + j) := by
    intro j hj
    rw [keyWord_key .AES_192 kw (show 4 + j < nk .AES_192 by simp [nk]; omega)]
    apply eq_of_wbyte_eq; intro t ht
    rw [wbyte_lane32 _ _ ht, loadBytes, byte_leBytesToQuad32 _ (by omega),
      wbyte_seqNat8ToSeqNat32LE l (by omega) ht, ha2, s1_post]
    simp [l, List.getElem!_eq_getElem?_getD, List.getElem?_drop]
    rw [show 16 + (4 * j + t) = 4 * (4 + j) + t by omega]
  apply WP.spec_mono (aes192_loop_spec kw _ _ _ _ _ (by simp) (by simp) (by simp) rfl (by rw [h0]; simp)
    (by simpa using hb 0 (by omega)) (by simpa using hb 1 (by omega)) ?_)
  · intro rk hrk
    rw [keyToRoundKeys_eq]
    exact eq_range_map _ _ (by simp [nr]) hrk
  · intro r hr
    have : r = 0 := by simp at hr; omega
    subst this; simp [h0, roundKey192_zero]

/-! ## The block cipher -/

theorem aese_eq (s k : BitVec 128) :
    core.core_arch.arm_shared.neon.generated.vaeseq_u8 s k = ok (shiftRows (subBytes (s ^^^ k))) := rfl

theorem aesmc_eq (s : BitVec 128) : core.core_arch.arm_shared.neon.generated.vaesmcq_u8 s = ok (mixColumns s) :=
  rfl

/-- `AESE` then `AESMC`: a round with its key XORed first. -/
def aeseMc (s k : BitVec 128) : BitVec 128 := mixColumns (shiftRows (subBytes (s ^^^ k)))

/-- Rounds that XOR each key first, then the next key, are Vale's rounds from
the first key XORed: each state is Vale's with its next key not yet added. -/
theorem foldl_aeseMc (rk : List (BitVec 128)) (s : BitVec 128) {n : Nat} (h : n + 1 ≤ rk.length) :
    (rk.take n).foldl aeseMc s ^^^ rk[n]! = ((rk.drop 1).take n).foldl evalRound (s ^^^ rk[0]!) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.take_add_one, List.take_add_one, List.foldl_append, List.foldl_append, ← ih (by omega),
      List.getElem?_drop, List.getElem?_eq_getElem (show n < rk.length by omega),
      List.getElem?_eq_getElem (show 1 + n < rk.length by omega)]
    simp [aeseMc, evalRound, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show n + 1 < rk.length by omega),
      List.getElem?_eq_getElem (show n < rk.length by omega), Nat.add_comm 1 n]

theorem aes_block_loop_eq (s : Slice core.core_arch.arm_shared.neon.uint8x16_t) (n : Nat) :
    ∀ i block, s.val.length - i = n →
      low.aarch64.aes.aes_block_loop ⟨s, i⟩ block = ok ((s.val.drop i).foldl aeseMc block) := by
  induction n with
  | zero =>
    intro i block hn
    unfold low.aarch64.aes.aes_block_loop
    rw [loop_done (z := block)]
    · simp [List.drop_eq_nil_of_le (show s.val.length ≤ i by omega)]
    · simp only [low.aarch64.aes.aes_block_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_right (by simp [Slice.len]; omega)]
      simp
  | succ n ih =>
    intro i block hn
    have hi : i < s.val.length := by omega
    unfold low.aarch64.aes.aes_block_loop
    rw [loop_cont (y := (⟨s, i + 1⟩, aeseMc block s.val[i]))]
    · rw [List.drop_eq_getElem_cons hi, List.foldl_cons]
      exact ih (i + 1) _ (by omega)
    · simp only [low.aarch64.aes.aes_block_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_left (by simp [Slice.len]; omega)]
      simp [aese_eq, aesmc_eq, aeseMc]
      rfl

/-- `aes_block` encrypts with its `nr alg + 1` round keys as Vale's `eval_cipher` does. -/
theorem aes_block_eq {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1)
    (rk : Std.Array core.core_arch.arm_shared.neon.uint8x16_t N) (b : Std.Array Std.U8 16#usize) :
    low.aarch64.aes.aes_block rk b = ok (storeBytes (evalCipher alg (loadBytes b.val) rk.val)) := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  have hl : rk.val.length = nr alg + 1 := by rw [rk.property, hN]
  have hsub : ∀ c : Usize, c.val ≤ N.val → ∃ i : Usize, N - c = ok i ∧ i.val = N.val - c.val := by
    intro c hc
    refine ⟨⟨BitVec.ofNat _ (N.val - c.val)⟩, ?_, ?_⟩
    · show UScalar.sub _ _ = _
      rw [UScalar.sub, ite_eq_right (by omega)]
    · have h1 : N.val - c.val < 2 ^ UScalarTy.Usize.numBits := by have := N.hBounds; omega
      show (BitVec.ofNat _ (N.val - c.val)).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  obtain ⟨i, hi, hiv⟩ := hsub 2#usize (by simp; omega)
  obtain ⟨i1, hi1, hi1v⟩ := hsub 1#usize (by simp; omega)
  simp only [show (2#usize).val = 2 from rfl, show (1#usize).val = 1 from rfl] at hiv hi1v
  unfold low.aarch64.aes.aes_block
  simp [load_eq, Std.Array.index_usize, hl, hi, hiv, hi1, hi1v, aese_eq,
    core.core_arch.arm_shared.neon.generated.veorq_u8,
    core.array.Array.index, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    core.ops.index.IndexSlice, core.slice.index.SliceIndexRangeToUsizeSlice.index, hN,
    aes_block_loop_eq _ _ 0 _ rfl, store_eq, show nr alg ≤ nr alg + 1 + 1 by omega]
  have hn : nr alg - 1 + 1 ≤ rk.val.length := by omega
  congr 2
  all_goals first
    | rw [evalRounds_foldl _ _ hn, ← foldl_aeseMc _ _ hn, getElem!_pos rk.val (nr alg - 1) (by omega)]
    | rw [getElem!_pos rk.val (nr alg) (by omega)]

/-- `aes128_block` encrypts with the round keys `rk` as Vale's `eval_cipher` does. -/
theorem aes128_block_spec (rk : Std.Array core.core_arch.arm_shared.neon.uint8x16_t 11#usize)
    (b : Std.Array Std.U8 16#usize) :
    low.aarch64.aes.aes128_block rk b = ok (storeBytes (evalCipher .AES_128 (loadBytes b.val) rk.val)) := by
  obtain ⟨l, hl, rfl⟩ : ∃ l h, rk = Std.Array.make _ l h := ⟨rk.val, rk.property, Std.Array.ext _ _ (by simp [Std.Array.make_val])⟩
  unfold low.aarch64.aes.aes128_block low.aarch64.aes._aes128_block
  match l, hl with
  | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10], _ =>
    simp [Std.Array.make_val, load_eq, store_eq, Std.Array.index_usize, aese_eq, aesmc_eq,
      core.core_arch.arm_shared.neon.generated.veorq_u8, evalCipher, evalRounds, evalRound, nr]

/-- `aes256_block` encrypts with the round keys `rk` as Vale's `eval_cipher` does. -/
theorem aes256_block_spec (rk : Std.Array core.core_arch.arm_shared.neon.uint8x16_t 15#usize)
    (b : Std.Array Std.U8 16#usize) :
    low.aarch64.aes.aes256_block rk b = ok (storeBytes (evalCipher .AES_256 (loadBytes b.val) rk.val)) := by
  obtain ⟨l, hl, rfl⟩ : ∃ l h, rk = Std.Array.make _ l h := ⟨rk.val, rk.property, Std.Array.ext _ _ (by simp [Std.Array.make_val])⟩
  unfold low.aarch64.aes.aes256_block low.aarch64.aes._aes256_block
  match l, hl with
  | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14], _ =>
    simp [Std.Array.make_val, load_eq, store_eq, Std.Array.index_usize, aese_eq, aesmc_eq,
      core.core_arch.arm_shared.neon.generated.veorq_u8, evalCipher, evalRounds, evalRound, nr]

/-! ## The equivalent inverse cipher -/

/-- `AESIMC` then `AESD`: an `EqInvCipher` round regrouped, its key XORed
before `InvShiftRows` and `InvSubBytes` rather than after. -/
def aesdImc (s k : BitVec 128) : BitVec 128 := invSubBytes (invShiftRows (invMixColumns s ^^^ k))

/-- Each `AESIMC` and `AESD` keeps the state `InvShiftRows` and `InvSubBytes`
ahead of `EqInvCipher`'s. -/
theorem foldl_aesdImc (l : List (BitVec 128)) (t : BitVec 128) :
    l.foldl aesdImc (invSubBytes (invShiftRows t)) = invSubBytes (invShiftRows (l.foldl eqInvRound t)) := by
  induction l generalizing t with
  | nil => rfl
  | cons k l ih =>
    have e : aesdImc (invSubBytes (invShiftRows t)) k = invSubBytes (invShiftRows (eqInvRound t k)) := by
      simp only [aesdImc, eqInvRound, invSubBytes_invShiftRows]
    rw [List.foldl_cons, List.foldl_cons, e, ih]

theorem hw_decrypt_block_loop_eq (s : Slice core.core_arch.arm_shared.neon.uint8x16_t) (n : Nat) :
    ∀ i block, s.val.length - i = n →
      low.aarch64.aes.hw_decrypt_block_loop ⟨s, i⟩ block = ok ((s.val.drop i).foldl aesdImc block) := by
  induction n with
  | zero =>
    intro i block hn
    unfold low.aarch64.aes.hw_decrypt_block_loop
    rw [loop_done (z := block)]
    · simp [List.drop_eq_nil_of_le (show s.val.length ≤ i by omega)]
    · simp only [low.aarch64.aes.hw_decrypt_block_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_right (by simp [Slice.len]; omega)]
      simp
  | succ n ih =>
    intro i block hn
    have hi : i < s.val.length := by omega
    unfold low.aarch64.aes.hw_decrypt_block_loop
    rw [loop_cont (y := (⟨s, i + 1⟩, aesdImc block s.val[i]))]
    · rw [List.drop_eq_getElem_cons hi, List.foldl_cons]
      exact ih (i + 1) _ (by omega)
    · simp only [low.aarch64.aes.hw_decrypt_block_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_left (by simp [Slice.len]; omega)]
      simp [core.core_arch.arm_shared.neon.generated.vaesimcq_u8,
        core.core_arch.arm_shared.neon.generated.vaesdq_u8, aesdImc]
      rfl

/-- `hw_decrypt_block` runs FIPS 197's equivalent inverse cipher under its
round keys reversed, the order `KeyExpansionEIC` expands them in. -/
theorem hw_decrypt_block_eq {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1)
    (rk : Std.Array core.core_arch.arm_shared.neon.uint8x16_t N) (b : Std.Array Std.U8 16#usize) :
    low.aarch64.aes.hw_decrypt_block rk b = ok (storeBytes (eqInvCipher alg (loadBytes b.val) rk.val.reverse)) := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  have hl : rk.val.length = nr alg + 1 := by rw [rk.property, hN]
  obtain ⟨i, hsub, hiv⟩ : ∃ i : Usize, N - 1#usize = ok i ∧ i.val = nr alg := by
    refine ⟨⟨BitVec.ofNat _ (N.val - 1)⟩, ?_, ?_⟩
    · show UScalar.sub _ _ = _
      rw [UScalar.sub, ite_eq_right (by simp; omega)]
      rfl
    · have h1 : N.val - 1 < 2 ^ UScalarTy.Usize.numBits := by have := N.hBounds; omega
      show (BitVec.ofNat _ (N.val - 1)).toNat = nr alg
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]; omega
  unfold low.aarch64.aes.hw_decrypt_block
  simp [load_eq, core.core_arch.arm_shared.neon.generated.veorq_u8,
    core.core_arch.arm_shared.neon.generated.vaesdq_u8, Std.Array.index_usize, hl, hsub, hiv,
    core.array.Array.index, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    core.ops.index.IndexSlice, core.slice.index.SliceIndexRangeUsizeSlice.index]
  rw [ite_eq_left hnr, bind_ok, hw_decrypt_block_loop_eq _ _ 0 _ rfl, bind_ok, store_eq]
  congr 1
  have hrl : rk.val.reverse.length = nr alg + 1 := by simp [hl]
  simp only [eqInvCipher, eqInvRounds_foldl _ _ _ (show nr alg - 1 + 1 ≤ rk.val.reverse.length by omega),
    show nr alg - 1 + 1 = nr alg by omega, ← reverse_slice rk.val.reverse hrl, List.reverse_reverse,
    Slice.from_val, List.drop_zero, List.slice, invSubBytes_invShiftRows]
  have e0 : rk.val.reverse[0]! = rk.val[nr alg]! := by
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_reverse (show 0 < rk.val.length by omega), hl]
    rfl
  have en : rk.val.reverse[nr alg]! = rk.val[0]! := by
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_reverse (show nr alg < rk.val.length by omega), hl]
    rw [show nr alg + 1 - 1 - nr alg = 0 by omega]
  rw [e0, en]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < rk.val.length by omega),
    List.getElem?_eq_getElem (show nr alg < rk.val.length by omega), Option.getD_some]
  rw [← invSubBytes_invShiftRows (loadBytes _ ^^^ _), foldl_aesdImc, invSubBytes_invShiftRows]

theorem invert_round_keys_loop_spec {N : Usize} (n : Nat) (i : Usize) (hi : i.val = n)
    (iter : core.ops.range.Range Usize) (rk out : Std.Array core.core_arch.arm_shared.neon.uint8x16_t N)
    (hN : N.val = n + 1) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ n) (he : iter.end = i)
    (ho : ∀ r < iter.start.val, out.val[r]! = invKey rk.val n r) :
    low.aarch64.aes.invert_round_keys_loop i iter rk out ⦃ out' => ∀ r < n, out'.val[r]! = invKey rk.val n r ⦄ := by
  unfold low.aarch64.aes.invert_round_keys_loop
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ n ∧ x.1.end = i ∧
      ∀ r < x.1.start.val, x.2.val[r]! = invKey rk.val n r)
  · rintro ⟨it, out⟩ ⟨hs1, hs, he, ho⟩
    simp only at hs1 hs he ho ⊢
    unfold low.aarch64.aes.invert_round_keys_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      simp only [core.core_arch.arm_shared.neon.generated.vaesimcq_u8, bind_ok]
      have hlt' : it.start.val < n := by rw [← hi, ← he]; exact hlt
      step*
      refine ⟨by omega, by omega, by rw [hen]; exact he, ?_, by omega⟩
      intro r hr
      rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
      split_ifs with h
      · rw [← h, invKey, ite_eq_right (by omega), ite_eq_right (by omega), uxt_post,
          getElem!_pos rk.val _ (by rw [rk.property]; omega)]
        simp only [i2_post, hi]
      · exact ho r (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      have hge : n ≤ it.start.val := by rw [← hi, ← he]; omega
      intro r hr
      exact ho r (by omega)
  · exact ⟨hs1, hs, he, ho⟩

/-- `invert_round_keys` expands `KeyExpansionEIC`'s round keys from the
cipher's, in reverse. -/
theorem invert_round_keys_spec {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1)
    (rk : Std.Array core.core_arch.arm_shared.neon.uint8x16_t N) :
    low.aarch64.aes.invert_round_keys rk ⦃ out => out.val.reverse = eqInvRoundKeys alg rk.val ⦄ := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  unfold low.aarch64.aes.invert_round_keys
  simp only [zero_eq, bind_ok]
  step*
  apply WP.spec_bind (invert_round_keys_loop_spec (nr alg) i (by omega) _ rk a hN (by simp) (by simp; omega) rfl ?_)
  · intro out1 h1
    step*
    apply invKeys_reverse alg rk.val _ (by simp [hN])
    intro r hr
    rw [out_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
    split_ifs with h
    · rw [invKey, ite_eq_right (by omega), ite_eq_left (by omega), uxt2_post, getElem!_pos]
    · exact h1 r (by omega)
  · intro r hr
    have : r = 0 := by simpa using hr
    subst this
    rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), ite_eq_left (by rfl), invKey,
      ite_eq_left rfl, uxt1_post, getElem!_pos rk.val _ (by rw [rk.property]; omega)]
    simp only [i_post, hN]
    rfl

/-! ## `AesKey`: its CPU check, key expansion, and block cipher -/

/-- rind runs its key expansion and block cipher on the crypto extension's AES
instructions on this CPU: its entry guard passes, and its CPU-feature check
finds the crypto extension. Neither reads an input. -/
def RunsAesHw : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧
  (∃ hw, low.aarch64.cpu.HaveCryptoExt.check = ok (some hw))

theorem expand_key128_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 16) :
    mid.aes.expand_key key ⦃ k => ∃ k128, k = .Hw (.Aes128 k128) ∧
      k128.round_keys.val = keyToRoundKeys .AES_128 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩⟩ := h
  unfold mid.aes.expand_key low.aarch64.aes.AesKey.new low.aarch64.aes.AesKey128.new
  step*
  have hl : copy_key1.len.val = 16 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 16#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, zero_eq]
  apply WP.spec_bind (aes128_expand_spec _ _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

theorem expand_key256_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 32) :
    mid.aes.expand_key key ⦃ k => ∃ k256, k = .Hw (.Aes256 k256) ∧
      k256.round_keys.val = keyToRoundKeys .AES_256 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩⟩ := h
  unfold mid.aes.expand_key low.aarch64.aes.AesKey.new low.aarch64.aes.AesKey256.new
  step*
  have hl : copy_key1.len.val = 32 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 32#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, zero_eq]
  apply WP.spec_bind (aes256_expand_spec _ _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

theorem expand_key192_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 24) :
    mid.aes.expand_key key ⦃ k => ∃ k192, k = .Hw (.Aes192 k192) ∧
      k192.round_keys.val = keyToRoundKeys .AES_192 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩⟩ := h
  unfold mid.aes.expand_key low.aarch64.aes.AesKey.new low.aarch64.aes.AesKey192.new
  step*
  have hl : copy_key1.len.val = 24 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 24#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap]
  apply WP.spec_bind (aes192_expand_spec _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

/-- The crypto extension's key holds Vale's round keys of the AES key `kw` for `alg`. -/
def HwKeyIs (alg : Algorithm) (kw : List (BitVec 32)) : low.aarch64.aes.HwKey → Prop
  | .Aes128 k => alg = .AES_128 ∧ k.round_keys.val = keyToRoundKeys .AES_128 kw
  | .Aes192 k => alg = .AES_192 ∧ k.round_keys.val = keyToRoundKeys .AES_192 kw
  | .Aes256 k => alg = .AES_256 ∧ k.round_keys.val = keyToRoundKeys .AES_256 kw

theorem hw_encrypt_block (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (h : HwKeyIs alg kw hk) (b : Std.Array U8 16#usize) :
    low.aarch64.aes.AesKey.encrypt_block (.Hw hk) b =
      ok (storeBytes (aesEncrypt alg kw (loadBytes b.val))) := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes.AesKey.encrypt_block,
      low.aarch64.aes.AesKey128.encrypt_block, aes128_block_spec, hrk, aesEncrypt]
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes.AesKey.encrypt_block, low.aarch64.aes.AesKey192.encrypt_block,
      aes_block_eq (N := 13#usize) .AES_192 rfl, hrk, aesEncrypt]
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes.AesKey.encrypt_block,
      low.aarch64.aes.AesKey256.encrypt_block, aes256_block_spec, hrk, aesEncrypt]

/-- The crypto extension's decryption key holds `KeyExpansionEIC`'s round keys
for the AES key `kw` and `alg`, in reverse. -/
def HwDecKeyIs (alg : Algorithm) (kw : List (BitVec 32)) : low.aarch64.aes.HwDecKey → Prop
  | .Aes128 k => alg = .AES_128 ∧ k.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg kw)
  | .Aes192 k => alg = .AES_192 ∧ k.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg kw)
  | .Aes256 k => alg = .AES_256 ∧ k.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg kw)

/-- `AesDecKey::new` expands `KeyExpansionEIC`'s round keys for the key bytes,
which `alg` sizes. -/
theorem dec_key_new_spec (h : RunsAesHw) (alg : Algorithm) (key : Slice U8) (hk : key.length = 4 * nk alg) :
    low.aarch64.aes.AesDecKey.new key ⦃ k => ∃ hk, k = .Hw hk ∧
      HwDecKeyIs alg (seqNat8ToSeqNat32LE (bvs key.val)) hk ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩⟩ := h
  have hl : key.len.val = 4 * nk alg := by simpa using hk
  unfold low.aarch64.aes.AesDecKey.new
  cases alg
  · have hl' : key.len = 16#usize := by simp [nk] at hl; scalar_tac
    simp only [hhw, bind_ok, hl', show ((16#usize : Usize) : Nat) = 16 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte, core.result.Result.unwrap,
      low.aarch64.aes.AesKey128.new, low.aarch64.aes.AesKey128.decryption_round_keys, zero_eq]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_128 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hout, x_post, Std.Array.from_val]
  · have hl' : key.len = 24#usize := by simp [nk] at hl; scalar_tac
    simp only [hhw, bind_ok, hl', show ((24#usize : Usize) : Nat) = 24 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte, core.result.Result.unwrap,
      low.aarch64.aes.AesKey192.new, low.aarch64.aes.AesKey192.decryption_round_keys]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_192 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hout, x_post, Std.Array.from_val]
  · have hl' : key.len = 32#usize := by simp [nk] at hl; scalar_tac
    simp only [hhw, bind_ok, hl', show ((32#usize : Usize) : Nat) = 32 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte, core.result.Result.unwrap,
      low.aarch64.aes.AesKey256.new, low.aarch64.aes.AesKey256.decryption_round_keys, zero_eq]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_256 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hout, x_post, Std.Array.from_val]

/-- `AesDecKey::decrypt_block` replaces the block with FIPS 197's decryption of it. -/
theorem hw_decrypt_block_spec (hk : low.aarch64.aes.HwDecKey) (alg : Algorithm) (kw : List (BitVec 32))
    (h : HwDecKeyIs alg kw hk) (b : Std.Array U8 16#usize) :
    low.aarch64.aes.AesDecKey.decrypt_block (.Hw hk) b = ok (storeBytes (aesDecrypt alg kw (loadBytes b.val))) := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes.AesDecKey.decrypt_block, hw_decrypt_block_eq (N := 11#usize) .AES_128 rfl, hrk,
      aesDecrypt]
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes.AesDecKey.decrypt_block, hw_decrypt_block_eq (N := 13#usize) .AES_192 rfl, hrk,
      aesDecrypt]
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes.AesDecKey.decrypt_block, hw_decrypt_block_eq (N := 15#usize) .AES_256 rfl, hrk,
      aesDecrypt]

end rind.aarch64
