import Rind.X86_64.AesGcmBy8
import Rind.X86_64.CtEqual
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# rind's SSE AES-GCM, `tagged`

`aes_gcm::tagged` on a PCLMULQDQ GHASH table, which `by8` hashes, is Vale's
`gcm_encrypt_LE` and `gcm_decrypt_LE` for a 96-bit nonce, without their bound
of 2^32 bytes: its counter block is `compute_iv_BE`'s, its length block
`gcm_hash`'s, and its tag GCTR on the hash under that counter block.
-/

local notation "P" => Polynomial (ZMod 2)

namespace rind.x86_64

/-! ## Vale's words and blocks -/

theorem word_bytes (w : BitVec 32) :
    (BitVec.fromLEBytes ((List.range 4).map fun i => w.extractLsb' (8 * i) 8)).setWidth 32 = w := by
  apply eq_of_wbyte_eq; intro i hi
  rw [wbyte, byte_word _ hi, getElem!_range_map _ hi, wbyte]

/-- Vale's key bytes read back to the key's words. -/
theorem seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE :
    ∀ (w : List (BitVec 32)), seqNat8ToSeqNat32LE (seqNat32ToSeqNat8LE w) = w
  | [] => rfl
  | w :: ws => by
    have e : (List.range 4).map (fun i => w.extractLsb' (8 * i) 8) =
        [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8] := rfl
    rw [seqNat32ToSeqNat8LE, List.flatMap_cons, ← seqNat32ToSeqNat8LE, e, List.cons_append, List.cons_append,
      List.cons_append, List.cons_append, List.nil_append, seqNat8ToSeqNat32LE_cons4, ← e, word_bytes,
      seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE ws]

/-! ## The length block -/

@[step]
theorem mul_h_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t) (x : BitVec 128) :
    low.x86_64.ghash.ClmulTable.mul_h t x ⦃ y => toPoly y = gf128MulRev (toPoly x) H ⦄ := by
  obtain ⟨y, hy, hp⟩ := mul_h_eq H hH t ht x
  rw [hy, WP.spec_ok]; exact hp

theorem lengths_eq (A M : Nat) (hM : M < 2 ^ 64) :
    (BitVec.ofNat 128 A <<< 64) ||| BitVec.ofNat 128 M =
      insertNat64 (insertNat64 (mkfour 0 0 0 0) A 1) M 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [insertNat64, Nat.one_ne_zero, ite_false, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  by_cases h : k < 64
  · simp [h]
  · have : M.testBit k = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [h, this, show k - 64 < 64 by omega, show k - 64 < 128 by omega, show 64 + (k - 64) = k by omega]

theorem add_lengths_spec (g : low.x86_64.ghash.Ghash) (t : low.x86_64.ghash.ClmulTable) (H : P) (hH : Small H)
    (ht : TableFor H t) (hg : ClmulOf g.table t) (a m : Usize) (hm : m.val < 2 ^ 61) :
    g.add_lengths a m ⦃ g' => g'.table = g.table ∧
      toPoly g'.current = gf128MulRev (toPoly g.current +
        toPoly (insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * a.val) 1) (8 * m.val) 0)) H ⦄ := by
  obtain ⟨tb, cur⟩ := g
  simp only at hg
  unfold low.x86_64.ghash.Ghash.add_lengths
  rcases hg with rfl | ⟨k, rfl⟩ | ⟨k1, k2, rfl⟩ <;>
  all_goals
    step*
    case hmax =>
      subst i_post
      simp only [UScalar.cast_val_eq, UScalarTy.numBits]
      have ha : a.val < 2 ^ 64 := by
        have := a.hBounds
        rcases System.Platform.numBits_eq with h | h <;>
          simp only [UScalarTy.numBits, h] at this <;> omega
      rw [Nat.mod_eq_of_lt (by omega : a.val < 2 ^ 128)]
      have e8 : (8#u128).val = 8 := rfl
      have em : U128.max = 2 ^ 128 - 1 := by rw [U128.max_eq]; norm_num
      rw [e8, em]; omega
    simp only [u128_to_m128i_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok]
    apply WP.spec_bind (mul_h_spec H hH t ht _)
    intro y hy
    rw [WP.spec_ok]
    refine ⟨rfl, ?_⟩
    have h1 : i1.bv = BitVec.ofNat 128 (8 * a.val) := by
      apply BitVec.eq_of_toNat_eq
      subst i_post
      simp only [UScalar.bv_toNat, BitVec.toNat_ofNat, i1_post, UScalar.cast_val_eq]
      scalar_tac
    have h4 : i4.bv = BitVec.ofNat 128 (8 * m.val) := by
      apply BitVec.eq_of_toNat_eq
      subst i3_post
      simp only [UScalar.bv_toNat, BitVec.toNat_ofNat, i4_post, UScalar.cast_val_eq]
      scalar_tac
    have hb : block.bv = insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * a.val) 1) (8 * m.val) 0 := by
      simp only [block_post1, i2_post1, h1, h4]
      exact lengths_eq _ _ (by omega)
    show toPoly y = _
    rw [hy, toPoly_xor, hb]

/-! ## The counter block and the tag -/

theorem leBytesToQuad32_leQuad32ToBytes (q : Quad32) : leBytesToQuad32 (leQuad32ToBytes q) = q := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_leBytesToQuad32 _ hk, leQuad32ToBytes_getElem! _ (by omega), getLsbD_byte _ _ (by omega)]
  congr 1; omega

/-- GCTR on one whole block XORs in the keystream of the counter block itself. -/
theorem gctr_block (icb q : Quad32) (alg : Algorithm) (kw : List (BitVec 32)) :
    gctrEncrypt icb (leQuad32ToBytes q) alg kw =
      leQuad32ToBytes (q ^^^ aesEncrypt alg kw (reverseBytesQuad32 icb)) := by
  have hl : (leQuad32ToBytes q).length = 16 := by simp [leQuad32ToBytes]
  have hs : leBytesToSeqQuad32 (leQuad32ToBytes q) = [q] := by
    rw [leBytesToSeqQuad32_eq, chunksOf_self _ (by omega) hl, List.map_singleton,
      leBytesToQuad32_leQuad32ToBytes]
  simp only [gctrEncrypt, hl, Nat.mod_self, ite_true, hs, gctrEncryptRecursive, gctrEncryptBlock, inc32_zero,
    leSeqQuad32ToBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem computeIvBE_96 (hLE : Quad32) (iv : List (BitVec 8)) (h : iv.length = 12) :
    computeIvBE hLE iv =
      (reverseBytesQuad32 (leBytesToQuad32 (iv ++ List.replicate 4 0))).extractLsb' 32 96 ++ (1 : BitVec 32) := by
  rw [computeIvBE, ite_eq_left (by omega), padTo128Bits, ite_eq_right (by omega), h]

theorem counter_bits (hLE : Quad32) (l : List (BitVec 8)) (hl : l.length = 12) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.fromLEBytes (l.drop 8))) ||| 1#64 <<< 56) ++
      BitVec.setWidth 64 (BitVec.fromLEBytes (l.take 8)) = reverseBytesQuad32 (computeIvBE hLE l) := by
  rw [computeIvBE_96 hLE l hl]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_reverseBytesQuad32 _ hk]
  by_cases h1 : k < 64
  · have hp : ¬ 8 * (15 - k / 8) + k % 8 < 32 := by omega
    simp only [BitVec.getLsbD_append, h1, hp, ite_true, ite_false, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
      getLsbD_fromLEBytes]
    rw [getLsbD_reverseBytesQuad32 _ (by omega), getLsbD_leBytesToQuad32 _ (by omega)]
    have e : 8 * (15 - (32 + (8 * (15 - k / 8) + k % 8 - 32)) / 8) + (32 + (8 * (15 - k / 8) + k % 8 - 32)) % 8
      = k := by omega
    rw [e, decide_eq_true (by omega : 8 * (15 - k / 8) + k % 8 - 32 < 96)]
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take, decide_true, Bool.true_and,
      List.getElem?_append_left (by omega : k / 8 < l.length), show k / 8 < 8 by omega, ite_true]
  · by_cases h2 : k < 96
    · have hp : ¬ 8 * (15 - k / 8) + k % 8 < 32 := by omega
      simp only [BitVec.getLsbD_append, h1, hp, ite_false, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, getLsbD_fromLEBytes]
      rw [getLsbD_reverseBytesQuad32 _ (by omega), getLsbD_leBytesToQuad32 _ (by omega)]
      have e : 8 * (15 - (32 + (8 * (15 - k / 8) + k % 8 - 32)) / 8) + (32 + (8 * (15 - k / 8) + k % 8 - 32)) % 8
        = k := by omega
      rw [e, decide_eq_true (by omega : 8 * (15 - k / 8) + k % 8 - 32 < 96), decide_eq_true (by omega : k - 64 < 64),
        decide_eq_true (by omega : k - 64 < 32)]
      have hb : (k - 64 < 56) = True := by simp only [eq_iff_iff, iff_true]; omega
      have i1 : (k - 64) / 8 = k / 8 - 8 := by omega
      have i2 : (k - 64) % 8 = k % 8 := by omega
      simp only [hb, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false, Bool.true_and, i1, i2, List.getElem!_eq_getElem?_getD,
        List.getElem?_drop, List.getElem?_append_left (by omega : k / 8 < l.length), show 8 + (k / 8 - 8) = k / 8 by omega]
    · have hp : 8 * (15 - k / 8) + k % 8 < 32 := by omega
      simp only [BitVec.getLsbD_append, h1, hp, ite_false, ite_true, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, decide_eq_false (by omega : ¬ k - 64 < 32), Bool.false_and,
        Bool.and_false, Bool.false_or, BitVec.getLsbD_one]
      interval_cases k <;> simp

theorem counter_block_eq (hLE : Quad32) (nonce : Std.Array U8 12#usize) :
    ∃ y0, low.x86_64.aes_gcm.counter_block nonce = ok y0 ∧
      loadBytes y0.val = reverseBytesQuad32 (computeIvBE hLE (nonce.val.map (·.bv))) := by
  simp only [low.x86_64.aes_gcm.counter_block, core.core_arch.x86.sse2._mm_set_epi64x, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [load_store]
  have := counter_bits hLE (nonce.val.map (·.bv)) (by simp)
  rw [← List.map_drop, ← List.map_take] at this
  exact this

/-! ## `tagged_from` -/

/-- A GHASH table `cipher` hands to `by8` with `t` at every length. -/
def By8Of (g : low.x86_64.ghash.GhashTable) (t : low.x86_64.ghash.ClmulTable) : Prop :=
  g = .Clmul t ∨ ∃ a, g = .Avx t a

theorem By8Of.clmulOf {g : low.x86_64.ghash.GhashTable} {t : low.x86_64.ghash.ClmulTable} (h : By8Of g t) :
    ClmulOf g t := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem cipher_by8 (ENC : Bool) (hk : low.x86_64.aes.HwKey) (g : low.x86_64.ghash.Ghash)
    (t : low.x86_64.ghash.ClmulTable) (hg : By8Of g.table t) (y0 : Std.Array U8 16#usize) (aad inout : Slice U8) :
    low.x86_64.aes_gcm.cipher ENC (.Hw hk) g y0 aad inout = low.x86_64.aes_gcm.by8 ENC hk t g y0 aad inout := by
  obtain ⟨tb, cur⟩ := g
  simp only at hg
  rcases hg with rfl | ⟨a, rfl⟩ <;> rfl

/-- GHASH from zero over the padded AAD and ciphertext, then the length
block, is `gcm_hash`'s, its bytes reversed. -/
theorem gcmHash_eq (hLE : Quad32) (a c : List U8) (x : BitVec 128)
    (hx : toPoly x = gf128MulRev (ghashPoly (polyLE hLE) 0 ((padBlocks a ++ padBlocks c).map toPoly) +
      toPoly (insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * a.length) 1) (8 * c.length) 0)) (polyLE hLE)) :
    reverseBytesQuad32 x = gcmHash hLE (bvs a) (bvs c) := by
  have hrev : ∀ q, polyLE (reverseBytesQuad32 q) = toPoly q := fun q => by
    rw [polyLE, reverseBytesQuad32_involutive]
  have h : polyLE (gcmHash hLE (bvs a) (bvs c)) = toPoly x := by
    rw [hx, gcmHash]
    rw [polyLE_ghashLE, List.map_append, List.map_append, padBlocks_vale, padBlocks_vale, List.map_singleton,
      hrev, List.length_map, List.length_map, ← List.append_assoc, ghashPoly_append, ← List.map_append,
      ghashPoly_cons, ghashPoly_nil]
  rw [polyLE] at h
  rw [← toPoly_inj h, reverseBytesQuad32_involutive]

theorem length_leSeqQuad32ToBytes : ∀ (qs : List Quad32), (leSeqQuad32ToBytes qs).length = 16 * qs.length
  | [] => rfl
  | q :: qs => by
    rw [leSeqQuad32ToBytes, List.flatMap_cons, List.length_append, ← leSeqQuad32ToBytes,
      length_leSeqQuad32ToBytes qs]
    simp [leQuad32ToBytes]; ring

theorem length_gctrEncrypt (icb : Quad32) (p : List (BitVec 8)) (alg : Algorithm) (kw : List (BitVec 32)) :
    (gctrEncrypt icb p alg kw).length = p.length := by
  unfold gctrEncrypt
  dsimp only
  split
  · rw [length_leSeqQuad32ToBytes, length_gctr, leBytesToSeqQuad32_eq, List.length_map, chunksOf_length]; omega
  · rw [List.length_append, length_leSeqQuad32ToBytes, length_gctr, leBytesToSeqQuad32_eq, List.length_map,
      chunksOf_length, List.length_take, List.length_take]
    simp only [leQuad32ToBytes, List.length_map, List.length_range]
    omega

/-- `tagged_from` with the counter block `j0`, on a table `by8` takes: GCTR
from the block after `j0`, and the tag GCTR from `j0` on `gcm_hash` of the AAD
and ciphertext. -/
theorem tagged_from_spec (ENC : Bool) (hk : low.x86_64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.x86_64.ghash.ClmulTable)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t) (table : low.x86_64.ghash.GhashTable)
    (hg : By8Of table t) (j0 : Quad32) (y0 : Std.Array U8 16#usize)
    (hy : loadBytes y0.val = reverseBytesQuad32 j0) (aad inout : Slice U8) (hin : inout.length < 2 ^ 61) :
    low.x86_64.aes_gcm.tagged_from ENC (.Hw hk) table y0 aad inout ⦃ r =>
      r.2.length = inout.length ∧
      bvs r.2.val = gctrEncrypt (inc32 j0 1) (bvs inout.val) alg kw ∧
      bvs r.1.val = gctrEncrypt j0 (leQuad32ToBytes (gcmHash (aesEncrypt alg kw (mkfour 0 0 0 0)) (bvs aad.val)
        (bvs (if ENC then r.2.val else inout.val)))) alg kw ⦄ := by
  set hLE := aesEncrypt alg kw (mkfour 0 0 0 0)
  obtain ⟨g, out, h8, hgt, hout, hgh⟩ := by8_spec ENC hk alg kw hkey (polyLE hLE) (small_toPoly _) t ht
    ⟨table, 0⟩ hg.clmulOf j0 y0 hy aad inout
  have hlen : out.length = inout.length := by
    have := congrArg List.length hout
    rw [List.length_map, length_gctrEncrypt, List.length_map] at this
    exact this
  have hc : (if ENC then out.val else inout.val).length = out.length := by
    cases ENC
    · exact hlen.symm
    · rfl
  unfold low.x86_64.aes_gcm.tagged_from
  simp only [low.x86_64.ghash.Ghash.new, low.x86_64.ghash.zero, core.core_arch.x86.sse2._mm_setzero_si128,
    bind_ok, cipher_by8 ENC hk ⟨table, 0⟩ t hg, h8, uncurry_apply_pair]
  apply WP.spec_bind (add_lengths_spec g t (polyLE hLE) (small_toPoly _) ht (by rw [hgt]; exact hg.clmulOf) _ _
    (by rw [Slice.len_val, hlen]; exact hin))
  rintro g' ⟨-, hg'⟩
  simp only [hw_encrypt_block hk alg kw hkey, bind_ok, low.x86_64.ghash.Ghash.tag, byte_reverse_eq,
    core.core_arch.x86.sse2._mm_xor_si128, load_store, WP.spec_ok]
  refine ⟨hlen, hout, ?_⟩
  rw [store_bytes, gctr_block, ← hy, gcmHash_eq hLE aad.val _ g'.current ?_]
  rw [hg', hgh, toPoly_zero, Slice.len_val, Slice.len_val, hc]

/-! ## `tagged`, `seal`, and `open` -/

/-- `tagged` sealing with a 96-bit nonce is Vale's `gcm_encrypt_LE`. -/
theorem tagged_seal_spec (hk : low.x86_64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.x86_64.ghash.ClmulTable)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t) (table : low.x86_64.ghash.GhashTable)
    (hg : By8Of table t) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (hin : inout.length < 2 ^ 61) :
    low.x86_64.aes_gcm.tagged true (.Hw hk) table nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧ (bvs r.2.val, bvs r.1.val) =
        gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) ⦄ := by
  obtain ⟨y0, hcb, hy⟩ := counter_block_eq (aesEncrypt alg kw (mkfour 0 0 0 0)) nonce
  unfold low.x86_64.aes_gcm.tagged
  rw [hcb, bind_ok]
  apply WP.spec_mono (tagged_from_spec true hk alg kw hkey t ht table hg _ y0 hy aad inout hin)
  rintro r ⟨hl, ho, htag⟩
  refine ⟨hl, ?_⟩
  simp only [ite_true] at htag
  simp only [gcmEncrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  rw [← ho, ← htag]

/-- `tagged` opening with a 96-bit nonce is Vale's `gcm_decrypt_LE`, its
tag the one the check compares. -/
theorem tagged_open_spec (hk : low.x86_64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.x86_64.ghash.ClmulTable)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t) (table : low.x86_64.ghash.GhashTable)
    (hg : By8Of table t) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (hin : inout.length < 2 ^ 61) :
    low.x86_64.aes_gcm.tagged false (.Hw hk) table nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧ ∀ tag : List (BitVec 8),
        gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) tag =
          (bvs r.2.val, bvs r.1.val == tag) ⦄ := by
  obtain ⟨y0, hcb, hy⟩ := counter_block_eq (aesEncrypt alg kw (mkfour 0 0 0 0)) nonce
  unfold low.x86_64.aes_gcm.tagged
  rw [hcb, bind_ok]
  apply WP.spec_mono (tagged_from_spec false hk alg kw hkey t ht table hg _ y0 hy aad inout hin)
  rintro r ⟨hl, ho, htag⟩
  refine ⟨hl, fun tag => ?_⟩
  simp only [Bool.false_eq_true, ite_false] at htag
  simp only [gcmDecrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  rw [← ho, ← htag]

theorem vale_clmul (enc : Bool) (hk : low.x86_64.aes.HwKey) (t : low.x86_64.ghash.ClmulTable) (aad inout : Slice U8) :
    low.x86_64.aes_gcm.vale enc (.Hw hk) (.Clmul t) aad inout ⦃ o => o = none ⦄ := by
  unfold low.x86_64.aes_gcm.vale
  cases hk <;> cases enc <;> step*

theorem bvs_beq (a b : List U8) : (bvs a == bvs b) = decide (a = b) := by
  have hinj : Function.Injective (fun x : U8 => x.bv) := by
    intro x y h; cases x; cases y; simp_all
  by_cases h : a = b
  · subst h; simp
  · have : bvs a ≠ bvs b := fun e => h (List.map_injective_iff.2 hinj e)
    simp [h, this]

/-! ## `AesGcm` on the by8 tier -/

/-- rind runs its own SSE AES-GCM on this CPU: its entry guards pass, and
its CPU-feature checks find AES-NI and PCLMULQDQ but no tier with AVX. None
reads an input. -/
def RunsClmulAesGcm : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧
  (∃ hw, low.x86_64.cpu.HaveAesHardware.check = ok (some hw)) ∧
  (∃ s, low.x86_64.cpu.HaveSsse3.check = ok s) ∧
  low.x86_64.cpu.HaveAvx512ForAesGcm.check = ok none ∧
  low.x86_64.cpu.HaveVaesAvx2ForAesGcm.check = ok none ∧
  low.x86_64.cpu.HaveAvxMovbeForAesGcm.check = ok none ∧
  low.entry.Entry.assert_held = ok ()

theorem RunsClmulAesGcm.aesNi (h : RunsClmulAesGcm) : RunsAesHw :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- An AES-GCM key on rind's SSE tier, for the AES key `kw` and `alg`: FIPS
197's round keys, and the GHASH key's powers. -/
def ReadyClmul (alg : Algorithm) (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) : Prop :=
  ∃ hk t, g.key = .Hw hk ∧ HwKeyIs alg kw hk ∧ g.gh = .Clmul t ∧
    TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t

/-- `AesGcm::new` on the SSE tier sets up FIPS 197's round keys and the
GHASH key's powers. -/
theorem aes_gcm_new_clmul_spec (h : RunsClmulAesGcm) (alg : Algorithm) (key : Slice U8)
    (hk : KeyLen alg key.length) :
    mid.aes_gcm.AesGcm.new key ⦃ g => ReadyClmul alg (seqNat8ToSeqNat32LE (bvs key.val)) g ⦄ := by
  have hni := h.aesNi
  obtain ⟨⟨e, he⟩, ⟨hw, hhw⟩, -, h512, hvaes, hmovbe, -⟩ := h
  set kw := seqNat8ToSeqNat32LE (bvs key.val)
  have hkey : mid.aes.expand_key key ⦃ k => ∃ hwk, k = .Hw hwk ∧ HwKeyIs alg kw hwk ⦄ := by
    rcases hk with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩
    · exact WP.spec_mono (expand_key128_spec hni key hl) fun k ⟨k128, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
    · exact WP.spec_mono (expand_key192_spec hni key hl) fun k ⟨k192, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
    · exact WP.spec_mono (expand_key256_spec hni key hl) fun k ⟨k256, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
  unfold mid.aes_gcm.AesGcm.new
  rw [he, bind_ok]
  apply WP.spec_bind hkey
  rintro _ ⟨hwk, rfl, hwk_is⟩
  obtain ⟨t, ht, htf⟩ := clmul_new_spec (core.num.U128.from_be_bytes
    (storeBytes (aesEncrypt alg kw (mkfour 0 0 0 0)))) hw
  simp only [encrypt_zero hwk alg kw hwk_is, bind_ok, lift, low.x86_64.ghash.GhashTable.new, hhw, h512,
    hvaes, hmovbe, ht, WP.spec_ok]
  refine ⟨hwk, t, rfl, hwk_is, rfl, ?_⟩
  rw [from_be_bytes_store] at htf
  exact htf

/-- `AesGcm::encrypt` on a by8 table where `seal` declines Vale's routine,
for AAD under 2^61 bytes and messages rind takes: the ciphertext in place and
the tag are AES-GCM's. -/
theorem aes_gcm_encrypt_by8 (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hk : low.x86_64.aes.HwKey) (t : low.x86_64.ghash.ClmulTable)
    (hkey : g.key = .Hw hk) (hhk : HwKeyIs alg kw hk) (hgt : By8Of g.gh t)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (hv : low.x86_64.aes_gcm.vale true g.key g.gh aad inout ⦃ o => o = none ⦄)
    (haad : aad.length < 2 ^ 61) (hin : inout.length ≤ 2 ^ 36 - 32) :
    mid.aes_gcm.AesGcm.encrypt g nonce aad inout tag ⦃ r =>
      r.1 = .Ok () ∧ r.2.1.length = inout.length ∧ (bvs r.2.1.val, bvs r.2.2.val) =
        gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) ⦄ := by
  obtain ⟨e, he⟩ := he
  obtain ⟨key, gh⟩ := g
  simp only at hkey hgt hv
  subst hkey
  unfold mid.aes_gcm.AesGcm.encrypt low.x86_64.aes_gcm.seal
  rw [he, bind_ok]
  step*
  subst x_post
  apply WP.spec_bind (tagged_seal_spec hk alg kw hhk t ht gh hgt nonce aad inout (by omega))
  rintro ⟨tg, out⟩ ⟨hl, h⟩
  step*

/-- `AesGcm::decrypt` on a by8 table where `open` declines Vale's routine,
for AAD under 2^61 bytes and messages rind takes: it succeeds exactly when the
tag is AES-GCM's, leaving the plaintext in place, and otherwise fails,
leaving zeros. -/
theorem aes_gcm_decrypt_by8 (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hheld : low.entry.Entry.assert_held = ok ()) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hk : low.x86_64.aes.HwKey) (t : low.x86_64.ghash.ClmulTable)
    (hkey : g.key = .Hw hk) (hhk : HwKeyIs alg kw hk) (hgt : By8Of g.gh t)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (hv : low.x86_64.aes_gcm.vale false g.key g.gh aad inout ⦃ o => o = none ⦄)
    (haad : aad.length < 2 ^ 61) (hin : inout.length ≤ 2 ^ 36 - 32) :
    mid.aes_gcm.AesGcm.decrypt g nonce aad inout tag ⦃ r =>
      let out := gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val)
        (bvs tag.val)
      if out.2 then r.1 = .Ok () ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8 ⦄ := by
  obtain ⟨e, he⟩ := he
  obtain ⟨key, gh⟩ := g
  simp only at hkey hgt hv
  subst hkey
  unfold mid.aes_gcm.AesGcm.decrypt low.x86_64.aes_gcm.open
  rw [he, bind_ok]
  step*
  subst x_post
  step with tagged_open_spec hk alg kw hhk t ht gh hgt nonce aad inout (by omega) as ⟨res, hl, h⟩
  obtain ⟨tg, out⟩ := res
  simp only at hl h
  rw [h (bvs tag.val)]
  dsimp only
  simp only [lift, bind_ok]
  step with ct_equal_spec hheld as ⟨b, hb⟩
  have hb' : (bvs tg.val == bvs tag.val) = b := by
    rw [hb, bvs_beq]; simp [Std.Array.to_slice, Slice.from_val]
  rw [hb']
  simp only [low.ct.into_public, bind_ok]
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    step*
  · simp only [ite_true]
    step*

/-- On Vale's tier, `seal` and `open` decline its routines for AAD or
messages of 2^32 bytes or more, and `seal` for messages under 129 bytes. -/
theorem vale_avx_none (enc : Bool) (alg : Algorithm) (kw : List (BitVec 32)) (hk : low.x86_64.aes.HwKey)
    (hhk : HwKeyIs alg kw hk) (t : low.x86_64.ghash.ClmulTable) (kernel : low.x86_64.aes_gcm_avx.AvxKernel)
    (aad inout : Slice U8)
    (hshort : ¬ (aad.length < 2 ^ 32 ∧ inout.length < 2 ^ 32 ∧ (enc = true → 129 ≤ inout.length))) :
    low.x86_64.aes_gcm.vale enc (.Hw hk) (.Avx t kernel) aad inout ⦃ o => o = none ⦄ := by
  have hal := Slice.len_val aad
  have hil := Slice.len_val inout
  unfold low.x86_64.aes_gcm.vale
  cases hk with
  | Aes192 k => cases enc <;> step*
  | Aes128 k | Aes256 k =>
    cases enc <;> step*
    all_goals
      exfalso; apply hshort
      refine ⟨?_, ?_, ?_⟩
      · by_contra hc
        rw [r_post1 (by rw [U32.max_eq]; omega)] at b_post
        simp_all
      · by_contra hc
        rw [r1_post1 (by rw [U32.max_eq]; omega)] at b1_post
        simp_all
      · intro _
        simp only [low.x86_64.aes_gcm.AVX_VALE_SEAL_FROM, ge_iff_le] at *
        scalar_tac

end rind.x86_64
