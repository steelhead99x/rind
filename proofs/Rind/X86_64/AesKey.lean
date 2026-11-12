import Rind.X86_64.Ghash
import Rind.X86_64.ValeAesGcm
import Rind.Aes
open Aeneas Aeneas.Std Result rind.vale rind.simd

namespace rind.x86_64

/-! ## Vectors as bytes and `u128`s -/

theorem load_eq (b : Std.Array Std.U8 16#usize) : low.x86_64.aes.load b = ok (loadBytes b.val) := by
  simp only [low.x86_64.aes.load, lift, core.num.U128.from_le_bytes, bind_ok, u128_to_m128i_eq, loadBytes,
    leBytesToQuad32]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem store_eq (v : BitVec 128) : low.x86_64.aes.store v = ok (storeBytes v) := by
  have h64 : (64#i32).val ≥ 0 := by decide
  have t64 : (64#i32).toNat = 64 := by decide
  simp only [low.x86_64.aes.store, core.core_arch.x86_64.sse2._mm_cvtsi128_si64,
    core.core_arch.x86.sse2._mm_unpackhi_epi64, lift, IScalar.hcast, core.convert.num.FromU128U64.from,
    HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, h64, ite_true, t64, UScalar.shiftLeft, bind_ok,
    UScalarTy.numBits, show 64 < 128 by decide]
  have e : ((((lane64 (lane64 v 1 ++ lane64 v 1) 0).signExtend 64).setWidth 128).shiftLeft 64 |||
      ((lane64 v 0).signExtend 64).setWidth 128 : BitVec 128) = v := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lane64, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft]
    by_cases h : i < 64
    · simp [h, hi]
    · simp [h, hi, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega, show i - 64 < 128 by omega]
  have hbv : ∀ x : BitVec 64, U64.bv (UScalar.mk x) = x := fun _ => rfl
  have hor : ∀ x y : BitVec 128, (@UScalar.mk .U128 x ||| @UScalar.mk .U128 y) = @UScalar.mk .U128 (x ||| y) :=
    fun _ _ => rfl
  simp only [hbv, hor, e]
  simp only [core.num.U128.to_le_bytes, storeBytes, toLEBytes_eq]

theorem xor_prefix_eq (t : BitVec 128) : low.x86_64.aes.xor_prefix t = ok (xorPrefix t) := by
  have e4 : (4#i32).bv.toNat % 256 = 4 := by decide
  have e8 : (8#i32).bv.toNat % 256 = 8 := by decide
  simp only [low.x86_64.aes.xor_prefix, core.core_arch.x86.sse2._mm_slli_si128,
    core.core_arch.x86.sse2._mm_xor_si128, bind_ok, e4, e8, show ¬ (4 > 15) by omega,
    show ¬ (8 > 15) by omega, ite_false, xorPrefix]

/-- `sub_rot_word`'s value. -/
def subRotWord (t : BitVec 128) (rcon : Std.I32) : BitVec 128 :=
  subBytes (shiftRows (ofBytes fun i =>
    if (byte (leBytesToQuad32 [(13#i8).bv, (14#i8).bv, (15#i8).bv, (12#i8).bv, (13#i8).bv, (14#i8).bv,
      (15#i8).bv, (12#i8).bv, (13#i8).bv, (14#i8).bv, (15#i8).bv, (12#i8).bv, (13#i8).bv, (14#i8).bv,
      (15#i8).bv, (12#i8).bv]) i).msb then 0
    else byte t ((byte (leBytesToQuad32 [(13#i8).bv, (14#i8).bv, (15#i8).bv, (12#i8).bv, (13#i8).bv,
      (14#i8).bv, (15#i8).bv, (12#i8).bv, (13#i8).bv, (14#i8).bv, (15#i8).bv, (12#i8).bv, (13#i8).bv,
      (14#i8).bv, (15#i8).bv, (12#i8).bv]) i).toNat % 16))) ^^^ ofLanes32 fun _ => rcon.bv

theorem sub_rot_word_eq (t : BitVec 128) (rcon : Std.I32) :
    low.x86_64.aes.sub_rot_word t rcon = ok (subRotWord t rcon) := by
  simp only [low.x86_64.aes.sub_rot_word, core.core_arch.x86.sse2._mm_setr_epi8,
    core.core_arch.x86.ssse3._mm_shuffle_epi8, core.core_arch.x86.sse2._mm_set1_epi32,
    core.core_arch.x86.aes._mm_aesenclast_si128, bind_ok, subRotWord]

/-- A round key whose first word takes `RotWord`, `SubWord`, and the round constant. -/
theorem rot_step (t u : BitVec 128) (rcon : Std.I32) :
    xorPrefix t ^^^ subRotWord u rcon = nextKey t (subWord (rotWord (lane32 u 3)) ^^^ rcon.bv) := by
  apply eq_of_byte_eq
  intro i hi
  interval_cases i <;>
    simp (config := { decide := true }) [xorPrefix, subRotWord, byte_xor, byte_shl, byte_ofLanes32,
      byte_subBytes, byte_shiftRows, byte_ofBytes, byte_leBytesToQuad32, nextKey, byte_mkfour, wbyte_xor,
      wbyte_subWord, wbyte_rotWord, wbyte_lane32, BitVec.xor_assoc]

theorem rcon_eq {r : Nat} (hr : r < 10) : aesRcon r = (low.x86_64.aes.RCON.val[r]!).bv := by
  interval_cases r <;> (unfold low.x86_64.aes.RCON; decide)

/-- AES-128's round key after round key `s`. -/
theorem aes128_next (kw : List (BitVec 32)) {s : Nat} (hs : s < 10) :
    xorPrefix (roundKey .AES_128 kw s) ^^^ subRotWord (roundKey .AES_128 kw s) low.x86_64.aes.RCON.val[s]! =
      roundKey .AES_128 kw (s + 1) := by
  rw [rot_step, roundKey128_succ, rcon_eq hs]
  simp only [roundKey, (lane32_mkfour _ _ _ _).2.2.2]

/-- `aes128_expand`'s loop: from round key `iter.start`, held in `t` and
`out`, it writes the rest. -/
theorem aes128_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.Range Usize)
    (t : core.core_arch.x86.__m128i) (out : Std.Array core.core_arch.x86.__m128i 11#usize)
    (hs : iter.start.val ≤ 10) (he : iter.end.val = 10) (ht : t = roundKey .AES_128 kw iter.start.val)
    (ho : ∀ r ≤ iter.start.val, out.val[r]! = roundKey .AES_128 kw r) :
    low.x86_64.aes.aes128_expand_loop iter t out ⦃ rk => ∀ r < 11, rk.val[r]! = roundKey .AES_128 kw r ⦄ := by
  unfold low.x86_64.aes.aes128_expand_loop
  apply loop.spec_decr_nat (fun x => 10 - x.1.start.val)
    (fun x => x.1.start.val ≤ 10 ∧ x.1.end.val = 10 ∧ x.2.1 = roundKey .AES_128 kw x.1.start.val ∧
      ∀ r ≤ x.1.start.val, x.2.2.val[r]! = roundKey .AES_128 kw r)
  · rintro ⟨it, t, out⟩ ⟨hs, he, ht, ho⟩
    simp only at hs he ht ho ⊢
    unfold low.x86_64.aes.aes128_expand_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      simp only [xor_prefix_eq, sub_rot_word_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok]
      step*
      have hi1 : i1 = low.x86_64.aes.RCON.val[it.start.val]! := by
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
    (out : Std.Array core.core_arch.x86.__m128i 11#usize) :
    low.x86_64.aes.aes128_expand key out ⦃ rk =>
      rk.val = keyToRoundKeys .AES_128 (seqNat8ToSeqNat32LE (key.val.map (·.bv))) ⦄ := by
  set kw := seqNat8ToSeqNat32LE (key.val.map (·.bv))
  have hl : (key.val.map (·.bv)).length = 16 := by simp
  have h0 : loadBytes key.val = roundKey .AES_128 kw 0 := by
    simp only [roundKey, keyWord_key .AES_128 kw (show 0 < 4 by decide),
      keyWord_key .AES_128 kw (show 1 < 4 by decide), keyWord_key .AES_128 kw (show 2 < 4 by decide),
      keyWord_key .AES_128 kw (show 3 < 4 by decide), Nat.mul_zero, Nat.zero_add]
    exact load_eq_mkfour _ hl
  unfold low.x86_64.aes.aes128_expand
  simp only [load_eq, bind_ok]
  apply WP.spec_mono (aes128_loop_spec kw _ _ _ (by simp) (by simp) (by rw [h0]; simp) ?_)
  · intro rk hrk
    rw [keyToRoundKeys_eq]
    exact eq_range_map _ _ (by simp [nr]) hrk
  · intro r hr
    simp only [show r = 0 by simpa using hr, Std.Array.repeat_val]
    simp [h0]

/-! ## AES-256 -/

theorem sub_step' (a b : BitVec 128) :
    xorPrefix b ^^^ subBytes (shiftRows (ofLanes32 fun i => lane32 a (255 / 4 ^ i % 4))) =
      nextKey b (subWord (lane32 a 3)) := by
  apply eq_of_byte_eq
  intro i hi
  interval_cases i <;>
    simp (config := { decide := true }) [xorPrefix, byte_xor, byte_shl, byte_ofLanes32, byte_subBytes,
      byte_shiftRows, nextKey, byte_mkfour, wbyte_xor, wbyte_subWord, wbyte_lane32, BitVec.xor_assoc]

/-- AES-256's even round key after round keys `2 * s` and `2 * s + 1`. -/
theorem aes256_next_even (kw : List (BitVec 32)) {s : Nat} (hs : s < 7) :
    xorPrefix (roundKey .AES_256 kw (2 * s)) ^^^
        subRotWord (roundKey .AES_256 kw (2 * s + 1)) low.x86_64.aes.RCON.val[s]! =
      roundKey .AES_256 kw (2 * s + 2) := by
  rw [rot_step, roundKey256_even, rcon_eq (by omega)]

/-- `aes256_expand`'s loop: from round keys `2 * iter.start` and the next,
held in `a`, `b`, and `out`, it writes the rest. -/
theorem aes256_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.Range Usize)
    (a b : core.core_arch.x86.__m128i) (out : Std.Array core.core_arch.x86.__m128i 15#usize)
    (hs : iter.start.val ≤ 6) (he : iter.end.val = 7) (ha : a = roundKey .AES_256 kw (2 * iter.start.val))
    (hb : b = roundKey .AES_256 kw (2 * iter.start.val + 1))
    (ho : ∀ r ≤ 2 * iter.start.val + 1, out.val[r]! = roundKey .AES_256 kw r) :
    low.x86_64.aes.aes256_expand_loop iter a b out ⦃ rk => ∀ r < 15, rk.val[r]! = roundKey .AES_256 kw r ⦄ := by
  unfold low.x86_64.aes.aes256_expand_loop
  apply loop.spec_decr_nat (fun x => 7 - x.1.start.val)
    (fun x => x.1.start.val ≤ 6 ∧ x.1.end.val = 7 ∧ x.2.1 = roundKey .AES_256 kw (2 * x.1.start.val) ∧
      x.2.2.1 = roundKey .AES_256 kw (2 * x.1.start.val + 1) ∧
      ∀ r ≤ 2 * x.1.start.val + 1, x.2.2.2.val[r]! = roundKey .AES_256 kw r)
  · rintro ⟨it, a, b, out⟩ ⟨hs, he, ha, hb, ho⟩
    simp only at hs he ha hb ho ⊢
    unfold low.x86_64.aes.aes256_expand_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
    subst ho'
    have e255 : (255#i32).bv.toNat = 255 := by decide
    simp only [xor_prefix_eq, sub_rot_word_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok,
      low.x86_64.aes.zero, core.core_arch.x86.sse2._mm_shuffle_epi32,
      core.core_arch.x86.sse2._mm_setzero_si128, core.core_arch.x86.aes._mm_aesenclast_si128, e255,
      show ∀ x : BitVec 128, x ^^^ (0 : BitVec 128) = x from fun x => BitVec.xor_zero, sub_step']
    step*
    all_goals
      have hi1 : i1 = low.x86_64.aes.RCON.val[it.start.val]! := by
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
    (out : Std.Array core.core_arch.x86.__m128i 15#usize) :
    low.x86_64.aes.aes256_expand key out ⦃ rk =>
      rk.val = keyToRoundKeys .AES_256 (seqNat8ToSeqNat32LE (key.val.map (·.bv))) ⦄ := by
  set l := key.val.map (·.bv)
  set kw := seqNat8ToSeqNat32LE l
  have hl : l.length = 32 := by simp [l]
  unfold low.x86_64.aes.aes256_expand
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

/-- `aes192_expand`'s `PSHUFB` mask: RotWord of word 1 in each word. -/
def rotWord1 : BitVec 128 :=
  leBytesToQuad32 [(5#i8).bv, (6#i8).bv, (7#i8).bv, (4#i8).bv, (5#i8).bv, (6#i8).bv, (7#i8).bv, (4#i8).bv,
    (5#i8).bv, (6#i8).bv, (7#i8).bv, (4#i8).bv, (5#i8).bv, (6#i8).bv, (7#i8).bv, (4#i8).bv]

/-- A step's first four words, whose first takes `RotWord`, `SubWord`, and the
round constant of `b`'s word 1. -/
theorem rot_step1 (a b : BitVec 128) (rcon : Std.I32) :
    xorPrefix a ^^^ (subBytes (shiftRows (ofBytes fun i =>
      if (byte rotWord1 i).msb then 0 else byte b ((byte rotWord1 i).toNat % 16))) ^^^
        ofLanes32 fun _ => rcon.bv) = nextKey a (subWord (rotWord (lane32 b 1)) ^^^ rcon.bv) := by
  apply eq_of_byte_eq
  intro i hi
  interval_cases i <;>
    simp (config := { decide := true }) [rotWord1, xorPrefix, byte_xor, byte_shl, byte_ofLanes32,
      byte_subBytes, byte_shiftRows, byte_ofBytes, byte_leBytesToQuad32, nextKey, byte_mkfour, wbyte_xor,
      wbyte_subWord, wbyte_rotWord, wbyte_lane32, BitVec.xor_assoc]

theorem dup_lane3 (a : BitVec 128) :
    ofLanes32 (fun i => lane32 a ((255#i32).bv.toNat / 4 ^ i % 4)) = ofLanes32 fun _ => lane32 a 3 := by
  simp [ofLanes32]

/-- `aes192_expand`'s loop: from step `iter.start`, with the step before's
words in `a` and `b`'s low half, and the round keys they complete in `out`, it
writes the rest. -/
theorem aes192_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.Range Usize)
    (a b m : core.core_arch.x86.__m128i) (out : Std.Array core.core_arch.x86.__m128i 13#usize)
    (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 8) (he : iter.end.val = 9) (hm : m = rotWord1)
    (ha : a = key192 kw (iter.start.val - 1))
    (hb0 : lane32 b 0 = keyWord .AES_192 kw (6 * (iter.start.val - 1) + 4))
    (hb1 : lane32 b 1 = keyWord .AES_192 kw (6 * (iter.start.val - 1) + 5))
    (ho : ∀ r, 4 * r + 4 ≤ 6 * iter.start.val → out.val[r]! = roundKey .AES_192 kw r) :
    low.x86_64.aes.aes192_expand_loop iter a b m out ⦃ rk => ∀ r < 13, rk.val[r]! = roundKey .AES_192 kw r ⦄ := by
  unfold low.x86_64.aes.aes192_expand_loop
  apply loop.spec_decr_nat (fun x => 9 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 8 ∧ x.1.end.val = 9 ∧
      x.2.1 = key192 kw (x.1.start.val - 1) ∧
      lane32 x.2.2.1 0 = keyWord .AES_192 kw (6 * (x.1.start.val - 1) + 4) ∧
      lane32 x.2.2.1 1 = keyWord .AES_192 kw (6 * (x.1.start.val - 1) + 5) ∧
      ∀ r, 4 * r + 4 ≤ 6 * x.1.start.val → x.2.2.2.val[r]! = roundKey .AES_192 kw r)
  · rintro ⟨it, a, b, out⟩ ⟨hs1, hs, he, ha, hb0, hb1, ho⟩
    simp only at hs1 hs he ha hb0 hb1 ho ⊢
    unfold low.x86_64.aes.aes192_expand_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
    subst ho' hm
    have e4 : (4#i32).bv.toNat % 256 = 4 := by decide
    have e8 : (8#i32).bv.toNat % 256 = 8 := by decide
    simp only [xor_prefix_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok,
      core.core_arch.x86.ssse3._mm_shuffle_epi8, core.core_arch.x86.sse2._mm_set1_epi32,
      core.core_arch.x86.aes._mm_aesenclast_si128, core.core_arch.x86.sse2._mm_shuffle_epi32,
      core.core_arch.x86.sse2._mm_slli_si128, core.core_arch.x86.sse2._mm_unpacklo_epi64,
      core.core_arch.x86.ssse3._mm_alignr_epi8, e4, e8, show ¬ (4 > 15) by omega, ite_false, rot_step1, Nat.reduceMul,
      dup_lane3, zip_lo, ext_hi]
    step*
    have hi1 : i1 = low.x86_64.aes.RCON.val[it.start.val - 1]! := by
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
    low.x86_64.aes.aes192_expand key ⦃ rk =>
      rk.val = keyToRoundKeys .AES_192 (seqNat8ToSeqNat32LE (key.val.map (·.bv))) ⦄ := by
  set l := key.val.map (·.bv)
  set kw := seqNat8ToSeqNat32LE l
  have hl : l.length = 24 := by simp [l]
  unfold low.x86_64.aes.aes192_expand
  step*
  have hsl : s.len = 16#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, hsl, ↓reduceDIte, core.result.Result.unwrap,
    bind_ok, load_eq]
  step*
  rcases r1 with a2 | ⟨⟩
  swap
  · exfalso; apply r1_post; simp [s1_post1]
  obtain ⟨ha2, -⟩ := r1_post
  simp only [bind_ok, lift, u128_to_m128i_eq, core.core_arch.x86.sse2._mm_setr_epi8, Std.Array.from_val,
    load64_eq]
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

theorem aesenc_eq (s k : BitVec 128) : core.core_arch.x86.aes._mm_aesenc_si128 s k = ok (evalRound s k) := by
  simp only [core.core_arch.x86.aes._mm_aesenc_si128, evalRound, subBytes_shiftRows]

theorem aesenclast_eq (s k : BitVec 128) :
    core.core_arch.x86.aes._mm_aesenclast_si128 s k = ok (shiftRows (subBytes s) ^^^ k) := by
  simp only [core.core_arch.x86.aes._mm_aesenclast_si128, subBytes_shiftRows]


theorem aes_block_loop_eq (s : Slice core.core_arch.x86.__m128i) (n : Nat) :
    ∀ i block, s.val.length - i = n →
      low.x86_64.aes.aes_block_loop ⟨s, i⟩ block = ok ((s.val.drop i).foldl evalRound block) := by
  induction n with
  | zero =>
    intro i block hn
    unfold low.x86_64.aes.aes_block_loop
    rw [loop_done (z := block)]
    · simp [List.drop_eq_nil_of_le (show s.val.length ≤ i by omega)]
    · simp only [low.x86_64.aes.aes_block_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_right (by simp [Slice.len]; omega)]
      simp
  | succ n ih =>
    intro i block hn
    have hi : i < s.val.length := by omega
    unfold low.x86_64.aes.aes_block_loop
    rw [loop_cont (y := (⟨s, i + 1⟩, evalRound block s.val[i]))]
    · rw [List.drop_eq_getElem_cons hi, List.foldl_cons]
      exact ih (i + 1) _ (by omega)
    · simp only [low.x86_64.aes.aes_block_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_left (by simp [Slice.len]; omega)]
      simp [aesenc_eq]
      rfl

/-- `aes_block` encrypts with its `nr alg + 1` round keys as Vale's `eval_cipher` does. -/
theorem aes_block_eq {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1)
    (rk : Std.Array core.core_arch.x86.__m128i N) (b : Std.Array Std.U8 16#usize) :
    low.x86_64.aes.aes_block rk b = ok (storeBytes (evalCipher alg (loadBytes b.val) rk.val)) := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  have hl : rk.val.length = nr alg + 1 := by rw [rk.property, hN]
  unfold low.x86_64.aes.aes_block
  obtain ⟨i, hsub, hiv⟩ : ∃ i : Usize, N - 1#usize = ok i ∧ i.val = nr alg := by
    refine ⟨⟨BitVec.ofNat _ (N.val - 1)⟩, ?_, ?_⟩
    · show UScalar.sub _ _ = _
      rw [UScalar.sub, ite_eq_right (by simp; omega)]
      rfl
    · have h1 : N.val - 1 < 2 ^ UScalarTy.Usize.numBits := by have := N.hBounds; omega
      show (BitVec.ofNat _ (N.val - 1)).toNat = nr alg
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]; omega
  simp [load_eq, core.core_arch.x86.sse2._mm_xor_si128, Std.Array.index_usize, hl, hsub, hiv,
    core.array.Array.index, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    core.ops.index.IndexSlice, core.slice.index.SliceIndexRangeUsizeSlice.index]
  rw [ite_eq_left hnr, bind_ok, aes_block_loop_eq _ _ 0 _ rfl, bind_ok, aesenclast_eq, bind_ok, store_eq]
  congr 1
  simp only [evalCipher, evalRounds_foldl _ _ (show nr alg - 1 + 1 ≤ rk.val.length by omega), Slice.from_val,
    List.drop_zero, getElem!_pos rk.val (nr alg) (by omega), getElem!_pos rk.val 0 (by omega), List.slice]

/-- `aes128_block` encrypts with the round keys `rk` as Vale's `eval_cipher` does. -/
theorem aes128_block_spec (rk : Std.Array core.core_arch.x86.__m128i 11#usize) (b : Std.Array Std.U8 16#usize) :
    low.x86_64.aes.aes128_block rk b = ok (storeBytes (evalCipher .AES_128 (loadBytes b.val) rk.val)) := by
  obtain ⟨l, hl, rfl⟩ : ∃ l h, rk = Std.Array.make _ l h := ⟨rk.val, rk.property, Std.Array.ext _ _ (by simp [Std.Array.make_val])⟩
  unfold low.x86_64.aes.aes128_block
  match l, hl with
  | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10], _ =>
    simp [Std.Array.make_val, load_eq, store_eq, Std.Array.index_usize, aesenc_eq, aesenclast_eq,
      core.core_arch.x86.sse2._mm_xor_si128, evalCipher, evalRounds, nr]

/-- `aes256_block` encrypts with the round keys `rk` as Vale's `eval_cipher` does. -/
theorem aes256_block_spec (rk : Std.Array core.core_arch.x86.__m128i 15#usize) (b : Std.Array Std.U8 16#usize) :
    low.x86_64.aes.aes256_block rk b = ok (storeBytes (evalCipher .AES_256 (loadBytes b.val) rk.val)) := by
  obtain ⟨l, hl, rfl⟩ : ∃ l h, rk = Std.Array.make _ l h := ⟨rk.val, rk.property, Std.Array.ext _ _ (by simp [Std.Array.make_val])⟩
  unfold low.x86_64.aes.aes256_block
  match l, hl with
  | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14], _ =>
    simp [Std.Array.make_val, load_eq, store_eq, Std.Array.index_usize, aesenc_eq, aesenclast_eq,
      core.core_arch.x86.sse2._mm_xor_si128, evalCipher, evalRounds, nr]

theorem load_zero : loadBytes (Std.Array.repeat 16#usize 0#u8).val = mkfour 0 0 0 0 := by
  simp only [loadBytes, Std.Array.repeat_val]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_leBytesToQuad32 _ hk]
  have : k / 8 < 16 := by omega
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_replicate]
  rw [ite_eq_left (by simpa using this)]
  simp [mkfour]

/-- A block read big-endian, as `u128::from_be_bytes` reads `storeBytes`'s bytes, is
Vale's `reverse_bytes_quad32` of it. -/
theorem from_be_bytes_store (q : BitVec 128) :
    (core.num.U128.from_be_bytes (storeBytes q)).bv = reverseBytesQuad32 q := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have e : (storeBytes q).val.map U8.bv = leQuad32ToBytes q := by
    simp [storeBytes, Std.Array.from_val, Function.comp_def]
  simp only [core.num.U128.from_be_bytes, reverseBytesQuad32, leBytesToQuad32, BitVec.fromBEBytes]
  rw [BitVec.getLsbD_setWidth, decide_eq_true hk, Bool.true_and, BitVec.getLsbD_cast, BitVec.getLsbD_cast, e]


/-! ## The equivalent inverse cipher -/

theorem aesdec_eq (s k : BitVec 128) :
    core.core_arch.x86.aes._mm_aesdec_si128 s k = ok (eqInvRound s k) := by
  simp only [core.core_arch.x86.aes._mm_aesdec_si128, eqInvRound, invSubBytes_invShiftRows]

theorem hw_decrypt_block_loop_eq (s : Slice core.core_arch.x86.__m128i) (n : Nat) :
    ∀ i block, s.val.length - i = n →
      low.x86_64.aes.hw_decrypt_block_loop ⟨s, i⟩ block = ok ((s.val.drop i).foldl eqInvRound block) := by
  induction n with
  | zero =>
    intro i block hn
    unfold low.x86_64.aes.hw_decrypt_block_loop
    rw [loop_done (z := block)]
    · simp [List.drop_eq_nil_of_le (show s.val.length ≤ i by omega)]
    · simp only [low.x86_64.aes.hw_decrypt_block_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_right (by simp [Slice.len]; omega)]
      simp
  | succ n ih =>
    intro i block hn
    have hi : i < s.val.length := by omega
    unfold low.x86_64.aes.hw_decrypt_block_loop
    rw [loop_cont (y := (⟨s, i + 1⟩, eqInvRound block s.val[i]))]
    · rw [List.drop_eq_getElem_cons hi, List.foldl_cons]
      exact ih (i + 1) _ (by omega)
    · simp only [low.x86_64.aes.hw_decrypt_block_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_left (by simp [Slice.len]; omega)]
      simp [aesdec_eq]
      rfl

/-- `hw_decrypt_block` runs FIPS 197's equivalent inverse cipher under its
round keys reversed, the order `KeyExpansionEIC` expands them in. -/
theorem hw_decrypt_block_eq {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1)
    (rk : Std.Array core.core_arch.x86.__m128i N) (b : Std.Array Std.U8 16#usize) :
    low.x86_64.aes.hw_decrypt_block rk b = ok (storeBytes (eqInvCipher alg (loadBytes b.val) rk.val.reverse)) := by
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
  unfold low.x86_64.aes.hw_decrypt_block
  simp [load_eq, core.core_arch.x86.sse2._mm_xor_si128, Std.Array.index_usize, hl, hsub, hiv,
    core.array.Array.index, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    core.ops.index.IndexSlice, core.slice.index.SliceIndexRangeUsizeSlice.index]
  rw [ite_eq_left hnr, bind_ok, hw_decrypt_block_loop_eq _ _ 0 _ rfl, bind_ok,
    core.core_arch.x86.aes._mm_aesdeclast_si128, bind_ok, store_eq]
  congr 1
  have hrl : rk.val.reverse.length = nr alg + 1 := by simp [hl]
  simp only [eqInvCipher, eqInvRounds_foldl _ _ _ (show nr alg - 1 + 1 ≤ rk.val.reverse.length by omega),
    show nr alg - 1 + 1 = nr alg by omega, ← reverse_slice rk.val.reverse hrl, List.reverse_reverse,
    Slice.from_val, List.drop_zero, List.slice, invSubBytes_invShiftRows]
  simp [hl]

theorem invert_round_keys_loop_spec {N : Usize} (n : Nat) (i : Usize) (hi : i.val = n)
    (iter : core.ops.range.Range Usize) (rk out : Std.Array core.core_arch.x86.__m128i N)
    (hN : N.val = n + 1) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ n) (he : iter.end = i)
    (ho : ∀ r < iter.start.val, out.val[r]! = invKey rk.val n r) :
    low.x86_64.aes.invert_round_keys_loop i iter rk out ⦃ out' => ∀ r < n, out'.val[r]! = invKey rk.val n r ⦄ := by
  unfold low.x86_64.aes.invert_round_keys_loop
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ n ∧ x.1.end = i ∧
      ∀ r < x.1.start.val, x.2.val[r]! = invKey rk.val n r)
  · rintro ⟨it, out⟩ ⟨hs1, hs, he, ho⟩
    simp only at hs1 hs he ho ⊢
    unfold low.x86_64.aes.invert_round_keys_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      simp only [core.core_arch.x86.aes._mm_aesimc_si128, bind_ok]
      have hlt' : it.start.val < n := by rw [← hi, ← he]; exact hlt
      step*
      refine ⟨by omega, by omega, by rw [hen]; exact he, ?_, by omega⟩
      intro r hr
      rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
      split_ifs with h
      · rw [← h, invKey, ite_eq_right (by omega), ite_eq_right (by omega), mi_post,
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
    (rk : Std.Array core.core_arch.x86.__m128i N) :
    low.x86_64.aes.invert_round_keys rk ⦃ out => out.val.reverse = eqInvRoundKeys alg rk.val ⦄ := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  unfold low.x86_64.aes.invert_round_keys
  simp only [low.x86_64.aes.zero, core.core_arch.x86.sse2._mm_setzero_si128, bind_ok]
  step*
  apply WP.spec_bind (invert_round_keys_loop_spec (nr alg) i (by omega) _ rk a hN (by simp) (by simp; omega) rfl ?_)
  · intro out1 h1
    step*
    apply invKeys_reverse alg rk.val _ (by simp [hN])
    intro r hr
    rw [out_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
    split_ifs with h
    · rw [invKey, ite_eq_right (by omega), ite_eq_left (by omega), mi2_post, getElem!_pos]
    · exact h1 r (by omega)
  · intro r hr
    have : r = 0 := by simpa using hr
    subst this
    rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), ite_eq_left (by rfl), invKey,
      ite_eq_left rfl, mi1_post, getElem!_pos rk.val _ (by rw [rk.property]; omega)]
    simp only [i_post, hN]
    rfl

/-! ## `AesKey`: its CPU check, key expansion, and block cipher -/

/-- rind runs its AES-NI key expansion and block cipher on this CPU: its entry
guard passes, and its CPU-feature checks find AES-NI, PCLMULQDQ, SSSE3, and
SSE4.1. None reads an input. -/
def RunsAesHw : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧
  (∃ hw, low.x86_64.cpu.HaveAesHardware.check = ok (some hw)) ∧
  (∃ s, low.x86_64.cpu.HaveSsse3.check = ok s)

theorem expand_key128_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 16) :
    mid.aes.expand_key key ⦃ k => ∃ k128, k = .Hw (.Aes128 k128) ∧
      k128.round_keys.val = keyToRoundKeys .AES_128 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  unfold mid.aes.expand_key low.x86_64.aes.AesKey.new low.x86_64.aes.AesKey128.new
  step*
  have hl : copy_key1.len.val = 16 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 16#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, hss, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, low.x86_64.aes.zero,
    core.core_arch.x86.sse2._mm_setzero_si128]
  apply WP.spec_bind (aes128_expand_spec _ _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

theorem expand_key256_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 32) :
    mid.aes.expand_key key ⦃ k => ∃ k256, k = .Hw (.Aes256 k256) ∧
      k256.round_keys.val = keyToRoundKeys .AES_256 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  unfold mid.aes.expand_key low.x86_64.aes.AesKey.new low.x86_64.aes.AesKey256.new
  step*
  have hl : copy_key1.len.val = 32 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 32#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, hss, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, low.x86_64.aes.zero,
    core.core_arch.x86.sse2._mm_setzero_si128]
  apply WP.spec_bind (aes256_expand_spec _ _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

theorem expand_key192_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 24) :
    mid.aes.expand_key key ⦃ k => ∃ k192, k = .Hw (.Aes192 k192) ∧
      k192.round_keys.val = keyToRoundKeys .AES_192 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  unfold mid.aes.expand_key low.x86_64.aes.AesKey.new low.x86_64.aes.AesKey192.new
  step*
  have hl : copy_key1.len.val = 24 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 24#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, hss, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, low.x86_64.aes.zero,
    core.core_arch.x86.sse2._mm_setzero_si128]
  apply WP.spec_bind (aes192_expand_spec _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

/-- The AES-NI key holds Vale's round keys of the AES key `kw` for `alg`. -/
def HwKeyIs (alg : Algorithm) (kw : List (BitVec 32)) : low.x86_64.aes.HwKey → Prop
  | .Aes128 k => alg = .AES_128 ∧ k.round_keys.val = keyToRoundKeys .AES_128 kw
  | .Aes192 k => alg = .AES_192 ∧ k.round_keys.val = keyToRoundKeys .AES_192 kw
  | .Aes256 k => alg = .AES_256 ∧ k.round_keys.val = keyToRoundKeys .AES_256 kw

theorem hw_encrypt_block (hk : low.x86_64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (h : HwKeyIs alg kw hk) (b : Std.Array U8 16#usize) :
    low.x86_64.aes.AesKey.encrypt_block (.Hw hk) b =
      ok (storeBytes (aesEncrypt alg kw (loadBytes b.val))) := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.x86_64.aes.AesKey.encrypt_block, low.x86_64.aes.HwKey.encrypt_block,
      low.x86_64.aes.AesKey128.encrypt_block, aes128_block_spec, hrk, aesEncrypt]
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.x86_64.aes.AesKey.encrypt_block, low.x86_64.aes.HwKey.encrypt_block,
      low.x86_64.aes.AesKey192.encrypt_block, aes_block_eq (N := 13#usize) .AES_192 rfl, hrk, aesEncrypt]
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.x86_64.aes.AesKey.encrypt_block, low.x86_64.aes.HwKey.encrypt_block,
      low.x86_64.aes.AesKey256.encrypt_block, aes256_block_spec, hrk, aesEncrypt]

/-- The AES-NI decryption key holds `KeyExpansionEIC`'s round keys for the AES
key `kw` and `alg`, in reverse. -/
def HwDecKeyIs (alg : Algorithm) (kw : List (BitVec 32)) : low.x86_64.aes.HwDecKey → Prop
  | .Aes128 k => alg = .AES_128 ∧ k.round_keys.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg kw)
  | .Aes192 k => alg = .AES_192 ∧ k.round_keys.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg kw)
  | .Aes256 k => alg = .AES_256 ∧ k.round_keys.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg kw)

/-- `AesDecKey::new` expands `KeyExpansionEIC`'s round keys for the key bytes,
which `alg` sizes. -/
theorem dec_key_new_spec (h : RunsAesHw) (alg : Algorithm) (key : Slice U8) (hk : key.length = 4 * nk alg) :
    low.x86_64.aes.AesDecKey.new key ⦃ k => ∃ hk, k = .Hw hk ∧
      HwDecKeyIs alg (seqNat8ToSeqNat32LE (bvs key.val)) hk ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  have hl : key.len.val = 4 * nk alg := by simpa using hk
  unfold low.x86_64.aes.AesDecKey.new
  cases alg
  · have hl' : key.len = 16#usize := by simp [nk] at hl; scalar_tac
    have hv : key.len.val = 16 := by simp [nk] at hl; exact hl
    simp only [hhw, hss, bind_ok, hl', show ((16#usize : Usize) : Nat) = 16 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte,
      core.result.Result.unwrap, low.x86_64.aes.AesKey128.new, low.x86_64.aes.AesKey128.inverse,
      low.x86_64.aes.zero, core.core_arch.x86.sse2._mm_setzero_si128]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_128 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hout, x_post, Std.Array.from_val]
  · have hl' : key.len = 24#usize := by simp [nk] at hl; scalar_tac
    have hv : key.len.val = 24 := by simp [nk] at hl; exact hl
    simp only [hhw, hss, bind_ok, hl', show ((24#usize : Usize) : Nat) = 24 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte,
      core.result.Result.unwrap, low.x86_64.aes.AesKey192.new, low.x86_64.aes.AesKey192.inverse,
      low.x86_64.aes.zero, core.core_arch.x86.sse2._mm_setzero_si128]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_192 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hout, x_post, Std.Array.from_val]
  · have hl' : key.len = 32#usize := by simp [nk] at hl; scalar_tac
    have hv : key.len.val = 32 := by simp [nk] at hl; exact hl
    simp only [hhw, hss, bind_ok, hl', show ((32#usize : Usize) : Nat) = 32 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte,
      core.result.Result.unwrap, low.x86_64.aes.AesKey256.new, low.x86_64.aes.AesKey256.inverse,
      low.x86_64.aes.zero, core.core_arch.x86.sse2._mm_setzero_si128]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_256 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hout, x_post, Std.Array.from_val]

/-- `AesDecKey::decrypt_block` replaces the block with FIPS 197's decryption of it. -/
theorem hw_decrypt_block_spec (hk : low.x86_64.aes.HwDecKey) (alg : Algorithm) (kw : List (BitVec 32))
    (h : HwDecKeyIs alg kw hk) (b : Std.Array U8 16#usize) :
    low.x86_64.aes.AesDecKey.decrypt_block (.Hw hk) b = ok (storeBytes (aesDecrypt alg kw (loadBytes b.val))) := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.x86_64.aes.AesDecKey.decrypt_block, hw_decrypt_block_eq (N := 11#usize) .AES_128 rfl, hrk,
      aesDecrypt]
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.x86_64.aes.AesDecKey.decrypt_block, hw_decrypt_block_eq (N := 13#usize) .AES_192 rfl, hrk,
      aesDecrypt]
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.x86_64.aes.AesDecKey.decrypt_block, hw_decrypt_block_eq (N := 15#usize) .AES_256 rfl, hrk,
      aesDecrypt]

end rind.x86_64
