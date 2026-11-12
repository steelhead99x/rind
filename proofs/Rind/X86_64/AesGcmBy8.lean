import Rind.X86_64.GhashClmul
import Rind.X86_64.AesGcm
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# rind's SSE AES-GCM, `by8`

`Rind.X86_64.AesGcmModel`'s `by8` is Vale's `gctr_encrypt_LE` and
`ghash_LE`, without their bound of 2^32 bytes: its counter is the block's
64-bit halves swapped, which `PADDD` steps as `inc32` does, its rounds are
FIPS 197's, and its GHASH is `Rind.X86_64.GhashClmul`'s.
-/

local notation "P" => Polynomial (ZMod 2)

set_option maxRecDepth 20000

namespace rind.x86_64

/-! ## Bits of the vector operations -/

theorem getLsbD_ofLanes16 (f : Nat → BitVec 16) (k : Nat) :
    (ofLanes16 f).getLsbD k = (decide (k < 128) && (f (k / 16)).getLsbD (k % 16)) := by
  by_cases hk : k < 128
  · simp only [ofLanes16, BitVec.getLsbD_append]
    interval_cases k <;> simp
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

theorem getLsbD_ofLanes32 (f : Nat → BitVec 32) (k : Nat) :
    (ofLanes32 f).getLsbD k = (decide (k < 128) && (f (k / 32)).getLsbD (k % 32)) := by
  by_cases hk : k < 128
  · simp only [ofLanes32, BitVec.getLsbD_append]
    interval_cases k <;> simp
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

theorem getLsbD_lane16 (a : BitVec 128) (j m : Nat) :
    (lane16 a j).getLsbD m = (decide (m < 16) && a.getLsbD (16 * j + m)) := by
  simp [lane16, BitVec.getLsbD_extractLsb']

theorem getLsbD_lane32 (a : BitVec 128) (j m : Nat) :
    (lane32 a j).getLsbD m = (decide (m < 32) && a.getLsbD (32 * j + m)) := by
  simp [lane32, BitVec.getLsbD_extractLsb']

theorem getLsbD_ite {w : Nat} (c : Prop) [Decidable c] (a b : BitVec w) (i : Nat) :
    (if c then a else b).getLsbD i = if c then a.getLsbD i else b.getLsbD i := by
  split <;> rfl

/-- `byte_reverse` reverses the bytes. -/
theorem byte_reverse_eq (x : BitVec 128) :
    low.x86_64.ghash.byte_reverse x = ok (reverseBytesQuad32 x) := by
  have e1 : (27#i32).bv.toNat = 27 := by decide
  have e2 : (177#i32).bv.toNat = 177 := by decide
  have e3 : (8#i32).bv.toNat = 8 := by decide
  simp only [low.x86_64.ghash.byte_reverse, core.core_arch.x86.sse2._mm_shuffle_epi32,
    core.core_arch.x86.sse2._mm_shufflelo_epi16, core.core_arch.x86.sse2._mm_shufflehi_epi16,
    core.core_arch.x86.sse2._mm_slli_epi16, core.core_arch.x86.sse2._mm_srli_epi16,
    core.core_arch.x86.sse2._mm_or_si128, bind_ok, e1, e2, e3]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_reverseBytesQuad32 _ hk]
  simp only [BitVec.getLsbD_or, getLsbD_ofLanes16, getLsbD_ite,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_lane16, getLsbD_ofLanes32, getLsbD_lane32,
    show ¬ (8 % 256 > 15) by decide, ite_false]
  interval_cases k <;> simp

theorem getLsbD_swap (v : BitVec 128) (k : Nat) :
    (swap v).getLsbD k = (decide (k < 128) && v.getLsbD ((k + 64) % 128)) := by
  by_cases hk : k < 128
  · simp only [swap, lo, hi, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases h : k < 64
    · simp [h, hk, show (k + 64) % 128 = 64 + k by omega]
    · simp [h, hk, show (k + 64) % 128 = k - 64 by omega]; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

theorem swap_swap (v : BitVec 128) : swap (swap v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_swap, getLsbD_swap]
  simp [hk, show (k + 64) % 128 < 128 by omega, show ((k + 64) % 128 + 64) % 128 = k by omega]

/-- `PSHUFB` by `BYTESWAP_EPI64` reverses each 64-bit half's bytes. -/
theorem shuffle_byteswap_epi64 (v : BitVec 128) :
    core.core_arch.x86.ssse3._mm_shuffle_epi8 v 0x08090a0b_0c0d0e0f_00010203_04050607#128 =
      ok (reverseBytesQuad32 (swap v)) := by
  simp only [core.core_arch.x86.ssse3._mm_shuffle_epi8]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_ofBytes _ hk, getLsbD_reverseBytesQuad32 _ hk, getLsbD_swap]
  simp only [getLsbD_byte _ _ (Nat.mod_lt _ (by omega : 8 > 0)), getLsbD_ite]
  interval_cases k <;> simp +decide [byte]

theorem load_store (v : BitVec 128) : loadBytes (storeBytes v).val = v := by
  apply eq_of_byte_eq; intro i hi
  simp only [loadBytes, storeBytes, Std.Array.from_val, List.map_map]
  rw [byte_leBytesToQuad32 _ hi]
  have hm : ∀ l : List (BitVec 8), l.map (fun x => U8.bv ⟨x⟩) = l := fun l => by
    conv_rhs => rw [← List.map_id l]
    rfl
  rw [Function.comp_def, hm, leQuad32ToBytes_getElem! _ hi]

/-! ## The counter -/

theorem lane32_inc32_zero (q : Quad32) (n : Nat) : lane32 (inc32 q n) 0 = lane32 q 0 + BitVec.ofNat 32 n := by
  have hz : ∀ x : Quad32, lane32 x 0 = x.extractLsb' 0 32 := fun _ => rfl
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [hz, hz, inc32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hm]

theorem high_inc32 (q : Quad32) (n : Nat) : (inc32 q n).extractLsb' 32 96 = q.extractLsb' 32 96 := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp only [inc32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hm, decide_true, Bool.true_and,
    show ¬ 32 + m < 32 by omega, ite_false, show 32 + m - 32 = m by omega]

theorem inc32_eq (q : Quad32) (n : Nat) :
    inc32 q n = q.extractLsb' 32 96 ++ (lane32 q 0 + BitVec.ofNat 32 n) := rfl

theorem inc32_inc32 (q : Quad32) (i j : Nat) : inc32 (inc32 q i) j = inc32 q (i + j) := by
  rw [inc32_eq (inc32 q i), high_inc32, lane32_inc32_zero, inc32_eq q (i + j), BitVec.add_assoc,
    BitVec.ofNat_add]

theorem inc32_zero (q : Quad32) : inc32 q 0 = q := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [inc32, BitVec.add_zero, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : k < 32
  · simp [h]
  · simp [h, show k - 32 < 96 by omega, show 32 + (k - 32) = k by omega]

theorem lane32_swap (v : BitVec 128) {i : Nat} (hi : i < 4) : lane32 (swap v) i = lane32 v ((i + 2) % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_lane32, getLsbD_lane32, getLsbD_swap]
  simp only [hm, decide_true, Bool.true_and, show 32 * i + m < 128 by omega]
  congr 1; omega

theorem lane32_inc32 (q : Quad32) (n : Nat) {i : Nat} (hi : 1 ≤ i) (hi' : i < 4) :
    lane32 (inc32 q n) i = lane32 q i := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_lane32, getLsbD_lane32]
  simp only [inc32, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hm, decide_true, Bool.true_and,
    show ¬ 32 * i + m < 32 by omega, ite_false, show 32 * i + m - 32 < 96 by omega]
  congr 1; omega

theorem ofLanes32_ext (f g : Nat → BitVec 32) (h : ∀ i < 4, f i = g i) : ofLanes32 f = ofLanes32 g := by
  simp only [ofLanes32, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem ofLanes32_lane32 (x : BitVec 128) : ofLanes32 (lane32 x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_ofLanes32, getLsbD_lane32]
  simp only [hk, decide_true, Bool.true_and, Nat.mod_lt _ (by omega : 32 > 0)]
  congr 1; omega

/-- `PADDD` of `COUNTER_1` steps the swapped counter as `inc32`. -/
theorem add_counter (q : Quad32) :
    core.core_arch.x86.sse2._mm_add_epi32 (swap q) 0x1_00000000_00000000#128 = ok (swap (inc32 q 1)) := by
  simp only [core.core_arch.x86.sse2._mm_add_epi32]
  refine congrArg ok ?_
  conv_rhs => rw [← ofLanes32_lane32 (swap (inc32 q 1))]
  apply ofLanes32_ext
  intro i hi
  have c0 : lane32 0x1_00000000_00000000#128 0 = 0#32 := by decide
  have c1 : lane32 0x1_00000000_00000000#128 1 = 0#32 := by decide
  have c2 : lane32 0x1_00000000_00000000#128 2 = 1#32 := by decide
  have c3 : lane32 0x1_00000000_00000000#128 3 = 0#32 := by decide
  rw [lane32_swap _ hi, lane32_swap _ hi]
  interval_cases i
  · rw [c0, BitVec.add_zero]; exact (lane32_inc32 q 1 (by omega) (by omega)).symm
  · rw [c1, BitVec.add_zero]; exact (lane32_inc32 q 1 (by omega) (by omega)).symm
  · rw [c2, show (2 + 2) % 4 = 0 by rfl, lane32_inc32_zero]
  · rw [c3, BitVec.add_zero]; exact (lane32_inc32 q 1 (by omega) (by omega)).symm

theorem rev_swap_rev (q : Quad32) : reverseBytesQuad32 (swap (reverseBytesQuad32 q)) = swap q := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_reverseBytesQuad32 _ hk, getLsbD_swap, getLsbD_swap, getLsbD_reverseBytesQuad32 _ (by omega)]
  simp only [hk, decide_true, Bool.true_and, show 8 * (15 - k / 8) + k % 8 < 128 by omega]
  congr 1; omega

/-- The counter `by8` keeps for the block `q`: its 64-bit halves swapped. -/
theorem counter_new (j0 : Quad32) (y0 : Std.Array U8 16#usize) (hy : loadBytes y0.val = reverseBytesQuad32 j0) :
    low.x86_64.aes_gcm.Counter.new y0 = ok (swap (inc32 j0 1)) := by
  simp only [low.x86_64.aes_gcm.Counter.new, low.x86_64.aes_gcm.BYTESWAP_EPI64, low.x86_64.aes_gcm.COUNTER_1,
    bind_ok, hy, shuffle_byteswap_epi64, rev_swap_rev, add_counter]

theorem counter_next (q : Quad32) :
    low.x86_64.aes_gcm.Counter.next (swap q) = ok (reverseBytesQuad32 q, swap (inc32 q 1)) := by
  simp only [low.x86_64.aes_gcm.Counter.next, low.x86_64.aes_gcm.BYTESWAP_EPI64, low.x86_64.aes_gcm.COUNTER_1,
    bind_ok, shuffle_byteswap_epi64, swap_swap, add_counter]

/-! ## The rounds -/

/-- `HwKey::round_keys`' first key, middle keys, and last key encrypt as Vale's AES. -/
theorem encrypt_eq (hk : low.x86_64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (h : HwKeyIs alg kw hk) (c : BitVec 128) :
    low.x86_64.aes_gcm.encrypt c hk.round_keys.1 hk.round_keys.2.1 hk.round_keys.2.2 = ok (aesEncrypt alg kw c) := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl := k.round_keys.property
    rw [aesEncrypt, ← hrk]
    simp only [low.x86_64.aes.HwKey.round_keys]
    generalize k.round_keys.val = l at hl ⊢
    match l, hl with
    | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10], _ =>
      simp [low.x86_64.aes_gcm.encrypt, aesenc_eq, aesenclast_eq, List.foldlM,
        core.core_arch.x86.sse2._mm_xor_si128, evalCipher, evalRounds, nr]
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl := k.round_keys.property
    rw [aesEncrypt, ← hrk]
    simp only [low.x86_64.aes.HwKey.round_keys]
    generalize k.round_keys.val = l at hl ⊢
    match l, hl with
    | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12], _ =>
      simp [low.x86_64.aes_gcm.encrypt, aesenc_eq, aesenclast_eq, List.foldlM,
        core.core_arch.x86.sse2._mm_xor_si128, evalCipher, evalRounds, nr]
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl := k.round_keys.property
    rw [aesEncrypt, ← hrk]
    simp only [low.x86_64.aes.HwKey.round_keys]
    generalize k.round_keys.val = l at hl ⊢
    match l, hl with
    | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14], _ =>
      simp [low.x86_64.aes_gcm.encrypt, aesenc_eq, aesenclast_eq, List.foldlM,
        core.core_arch.x86.sse2._mm_xor_si128, evalCipher, evalRounds, nr]

/-! ## CTR -/

theorem length_gctr (icb : Quad32) (alg : Algorithm) (kw : List (BitVec 32)) :
    ∀ (ps : List Quad32) (i : Nat), (gctrEncryptRecursive icb alg kw ps i).length = ps.length
  | [], _ => rfl
  | _ :: ps, i => by rw [gctrEncryptRecursive, List.length_cons, length_gctr icb alg kw ps (i + 1),
      List.length_cons]

theorem gctr_append (icb : Quad32) (alg : Algorithm) (kw : List (BitVec 32)) :
    ∀ (ps ps' : List Quad32) (i : Nat), gctrEncryptRecursive icb alg kw (ps ++ ps') i =
      gctrEncryptRecursive icb alg kw ps i ++ gctrEncryptRecursive icb alg kw ps' (i + ps.length)
  | [], _, _ => rfl
  | p :: ps, ps', i => by
    rw [List.cons_append, gctrEncryptRecursive, gctrEncryptRecursive, gctr_append icb alg kw ps ps' (i + 1),
      List.cons_append, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

section ctr
variable {f l : BitVec 128} {rks : List (BitVec 128)} {alg : Algorithm} {kw : List (BitVec 32)}
  (henc : ∀ c, low.x86_64.aes_gcm.encrypt c f rks l = ok (aesEncrypt alg kw c))
include henc

theorem ctr_block_eq (icb p : Quad32) (i : Nat) :
    low.x86_64.aes_gcm.ctr_block (swap (inc32 icb i)) f rks l p =
      ok (gctrEncryptBlock icb p alg kw i, swap (inc32 icb (i + 1))) := by
  simp only [low.x86_64.aes_gcm.ctr_block, counter_next, bind_ok, uncurry_apply_pair, henc,
    core.core_arch.x86.sse2._mm_xor_si128, inc32_inc32, gctrEncryptBlock, BitVec.xor_comm]

theorem ctr_blocks_eq (icb : Quad32) : ∀ (ps : List Quad32) (i : Nat),
    low.x86_64.aes_gcm.ctr_blocks f rks l ps (swap (inc32 icb i)) =
      ok (gctrEncryptRecursive icb alg kw ps i, swap (inc32 icb (i + ps.length)))
  | [], i => by simp [low.x86_64.aes_gcm.ctr_blocks, gctrEncryptRecursive]
  | p :: ps, i => by
    simp only [low.x86_64.aes_gcm.ctr_blocks, ctr_block_eq henc, bind_ok, uncurry_apply_pair,
      ctr_blocks_eq icb ps (i + 1), gctrEncryptRecursive, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

end ctr

/-! ## The loop over 128-byte chunks -/

/-- The 16-byte blocks of 128-byte chunks, as vectors. -/
def blocksAll (chunks : List (List U8)) : List Quad32 :=
  chunks.flatMap fun c => (chunksOf 16 c).map loadBytes

theorem length_blocksAll : ∀ (chunks : List (List U8)), (∀ c ∈ chunks, c.length = 128) →
    (blocksAll chunks).length = 8 * chunks.length
  | [], _ => rfl
  | c :: cs, h => by
    rw [blocksAll, List.flatMap_cons, ← blocksAll, List.length_append, List.length_map, chunksOf_length,
      h c (by simp), length_blocksAll cs (fun c hc => h c (by simp [hc])), List.length_cons]
    omega

/-- `_mul8` of eight vectors' bytes reversed, the first XORed with `current`. -/
def hashChunk (t : low.x86_64.ghash.ClmulTable) (current : BitVec 128) (hs : List (BitVec 128)) :
    BitVec 128 :=
  reduceAll ((tailInputs current (hs.map reverseBytesQuad32)).zip (powersDesc t 8))

theorem mul8_hash (H : P) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t) (current : BitVec 128)
    (hs : List (BitVec 128)) (h8 : hs.length = 8) :
    low.x86_64.ghash._mul8 t (current ^^^ reverseBytesQuad32 hs[0]!) (reverseBytesQuad32 hs[1]!)
      (reverseBytesQuad32 hs[2]!) (reverseBytesQuad32 hs[3]!) (reverseBytesQuad32 hs[4]!)
      (reverseBytesQuad32 hs[5]!) (reverseBytesQuad32 hs[6]!) (reverseBytesQuad32 hs[7]!) =
      ok (hashChunk t current hs) := by
  rw [mul8_eq H t ht, hashChunk]
  conv_rhs => rw [eight hs h8]
  rfl

theorem chunksOf_self {α : Type} {k : Nat} (l : List α) (hk : 0 < k) (h : l.length = k) : chunksOf k l = [l] := by
  rw [chunksOf_cons hk (by omega), List.take_of_length_le (by omega), chunksOf_of_lt (by simp; omega)]

theorem hashChunks_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t) :
    ∀ (n : Nat) (hs : List (BitVec 128)) (current : BitVec 128), hs.length = 8 * n →
      toPoly ((chunksOf 8 hs).foldl (hashChunk t) current) =
        ghashPoly H (toPoly current) (hs.map (toPoly ∘ reverseBytesQuad32))
  | 0, hs, current, h => by
    have : hs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    simp [chunksOf, ghashPoly_nil]
  | n + 1, hs, current, h => by
    have h8 : 8 ≤ hs.length := by omega
    rw [chunksOf_cons (by omega) h8, List.foldl_cons,
      hashChunks_spec H hH t ht n (hs.drop 8) _ (by simp; omega)]
    conv_rhs => rw [← List.take_append_drop 8 hs]
    rw [List.map_append, ghashPoly_append]
    congr 1
    have hl : (hs.take 8).length = 8 := by simp; omega
    have hx := toPoly_reduceAll_powers H hH t ht (tailInputs current ((hs.take 8).map reverseBytesQuad32))
      (by rw [length_tailInputs, List.length_map, hl])
    rw [length_tailInputs, List.length_map, hl] at hx
    rw [hashChunk, hx, sumPow_tailInputs H current _ (fun h => by
      have := congrArg List.length h; rw [List.length_map, hl] at this; simp at this), List.map_map]

section loop
variable {f l : BitVec 128} {rks : List (BitVec 128)} {alg : Algorithm} {kw : List (BitVec 32)}
  (henc : ∀ c, low.x86_64.aes_gcm.encrypt c f rks l = ok (aesEncrypt alg kw c))
include henc

theorem by8_loop_eq (ENC : Bool) (H : P) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t) (icb : Quad32) :
    ∀ (chunks : List (List U8)), (∀ c ∈ chunks, c.length = 128) → ∀ (i : Nat) (current : BitVec 128),
      low.x86_64.aes_gcm.by8_loop ENC t f rks l chunks (swap (inc32 icb i)) current =
        ok (swap (inc32 icb (i + 8 * chunks.length)),
          (chunksOf 8 (if ENC then gctrEncryptRecursive icb alg kw (blocksAll chunks) i else blocksAll chunks)).foldl
            (hashChunk t) current,
          (gctrEncryptRecursive icb alg kw (blocksAll chunks) i).flatMap low.x86_64.aes_gcm.bytes)
  | [], _, i, current => by simp [low.x86_64.aes_gcm.by8_loop, blocksAll, gctrEncryptRecursive, chunksOf]
  | c :: cs, hc, i, current => by
    have hc0 : c.length = 128 := hc c (by simp)
    have hcs : ∀ c ∈ cs, c.length = 128 := fun c h => hc c (by simp [h])
    have hp : ((chunksOf 16 c).map loadBytes).length = 8 := by
      rw [List.length_map, chunksOf_length, hc0]
    have hs8 : (if ENC then gctrEncryptRecursive icb alg kw ((chunksOf 16 c).map loadBytes) i
        else (chunksOf 16 c).map loadBytes).length = 8 := by
      cases ENC <;> simp only [Bool.false_eq_true, ite_false, ite_true, length_gctr, hp]
    rw [low.x86_64.aes_gcm.by8_loop]
    simp only [ctr_blocks_eq henc, bind_ok, uncurry_apply_pair, hp, low.x86_64.aes_gcm.BYTESWAP,
      shuffle_byteswap, core.core_arch.x86.sse2._mm_xor_si128, mul8_hash H t ht current _ hs8,
      by8_loop_eq ENC H t ht icb cs hcs (i + 8)]
    have hb : blocksAll (c :: cs) = (chunksOf 16 c).map loadBytes ++ blocksAll cs := by
      rw [blocksAll, List.flatMap_cons, ← blocksAll]
    have hhash : (if ENC then gctrEncryptRecursive icb alg kw (blocksAll (c :: cs)) i else blocksAll (c :: cs)) =
        (if ENC then gctrEncryptRecursive icb alg kw ((chunksOf 16 c).map loadBytes) i
          else (chunksOf 16 c).map loadBytes) ++
        (if ENC then gctrEncryptRecursive icb alg kw (blocksAll cs) (i + 8) else blocksAll cs) := by
      rw [hb]; cases ENC <;> simp only [Bool.false_eq_true, ite_false, ite_true, gctr_append, hp]
    rw [hhash, chunksOf_append (by omega) 1 _ _ (by rw [hs8]), chunksOf_self _ (by omega) hs8,
      List.singleton_append, List.foldl_cons, hb, gctr_append, hp, List.flatMap_append, List.length_cons,
      show i + 8 + 8 * cs.length = i + 8 * (cs.length + 1) by ring]

end loop

/-! ## Bytes and blocks -/

/-- A GHASH table whose hashing is `ClmulTable::add` with `t`. -/
def ClmulOf (g : low.x86_64.ghash.GhashTable) (t : low.x86_64.ghash.ClmulTable) : Prop :=
  g = .Clmul t ∨ (∃ a, g = .Avx t a) ∨ ∃ a b, g = .VaesAvx2 t a b

theorem addBytes_clmul (g : low.x86_64.ghash.Ghash) (t : low.x86_64.ghash.ClmulTable) (hg : ClmulOf g.table t)
    (bytes : List U8) :
    low.x86_64.ghash.Ghash.addBytes g bytes =
      (do
        let current ← low.x86_64.ghash.ClmulTable.add t bytes g.current
        ok { g with current }) := by
  obtain ⟨tb, cur⟩ := g
  simp only at hg
  rcases hg with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;> rfl

theorem length_bytes (q : BitVec 128) : (low.x86_64.aes_gcm.bytes q).length = 16 := by
  simp [low.x86_64.aes_gcm.bytes, storeBytes, leQuad32ToBytes]

theorem bytes_bv (q : BitVec 128) : (low.x86_64.aes_gcm.bytes q).map (·.bv) = leQuad32ToBytes q := by
  simp only [low.x86_64.aes_gcm.bytes, storeBytes, Std.Array.from_val, List.map_map]
  conv_rhs => rw [← List.map_id (leQuad32ToBytes q)]
  rfl

theorem flatMap_bytes_bv (qs : List (BitVec 128)) :
    (qs.flatMap low.x86_64.aes_gcm.bytes).map (·.bv) = leSeqQuad32ToBytes qs := by
  rw [leSeqQuad32ToBytes, List.map_flatMap]
  simp only [bytes_bv]

theorem length_flatMap_bytes (qs : List (BitVec 128)) :
    (qs.flatMap low.x86_64.aes_gcm.bytes).length = 16 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => rw [List.flatMap_cons, List.length_append, length_bytes, ih, List.length_cons]; ring

theorem chunksOf_flatMap_bytes : ∀ (qs : List (BitVec 128)),
    chunksOf 16 (qs.flatMap low.x86_64.aes_gcm.bytes) = qs.map low.x86_64.aes_gcm.bytes
  | [] => rfl
  | q :: qs => by
    rw [List.flatMap_cons, chunksOf_append (by omega) 1 _ _ (by rw [length_bytes]),
      chunksOf_self _ (by omega) (length_bytes q), chunksOf_flatMap_bytes qs, List.map_cons, List.singleton_append]

theorem chunksRest_flatMap_bytes (qs : List (BitVec 128)) :
    chunksRest 16 (qs.flatMap low.x86_64.aes_gcm.bytes) = [] :=
  List.eq_nil_of_length_eq_zero (by rw [chunksRest_length, length_flatMap_bytes]; omega)

theorem padBlocks_append (a b : List U8) (ha : a.length % 16 = 0) :
    padBlocks (a ++ b) = padBlocks a ++ padBlocks b := by
  have hj : a.length = 16 * (a.length / 16) := by omega
  have hr : chunksRest 16 a = [] := List.eq_nil_of_length_eq_zero (by rw [chunksRest_length]; omega)
  rw [padBlocks, padBlocks, padBlocks, chunksOf_append (by omega) _ _ _ hj, chunksRest_append (by omega) _ _ _ hj,
    hr, ite_eq_left rfl, List.append_nil, List.map_append, List.append_assoc]

theorem padBlocks_flatMap_bytes (qs : List (BitVec 128)) :
    padBlocks (qs.flatMap low.x86_64.aes_gcm.bytes) = qs.map reverseBytesQuad32 := by
  rw [padBlocks, chunksOf_flatMap_bytes, chunksRest_flatMap_bytes, ite_eq_left rfl, List.append_nil, List.map_map]
  refine List.map_congr_left (fun q _ => ?_)
  simp only [Function.comp, blockBE, low.x86_64.aes_gcm.bytes, load_store]

theorem blocks_split (b : List U8) :
    (chunksOf 16 b).map loadBytes =
      blocksAll (chunksOf 128 b) ++ (chunksOf 16 (chunksRest 128 b)).map loadBytes := by
  rw [(chunks_128 b).1, List.map_append, List.map_flatMap, blocksAll]

theorem padBlocks_head (b : List U8) :
    (chunksOf 128 b).flatMap padBlocks = (blocksAll (chunksOf 128 b)).map reverseBytesQuad32 := by
  rw [blocksAll, List.map_flatMap]
  apply List.flatMap_congr
  intro c hc
  rw [padBlocks_128 c (chunksOf_length_mem hc), List.map_map]
  rfl

theorem leBytesToSeqQuad32_load (b : List U8) :
    leBytesToSeqQuad32 (b.map (·.bv)) = (chunksOf 16 b).map loadBytes := by
  rw [leBytesToSeqQuad32_eq, chunksOf_map, List.map_map]
  rfl

/-! ## GCTR on the whole input -/

theorem chunksOf_take16 (b : List U8) : chunksOf 16 (b.take (b.length - b.length % 16)) = chunksOf 16 b := by
  have hk : b.length - b.length % 16 = 16 * (b.length / 16) := by omega
  have hA : (b.take (b.length - b.length % 16)).length = 16 * (b.length / 16) := by simp; omega
  conv_rhs => rw [← List.take_append_drop (b.length - b.length % 16) b]
  rw [chunksOf_append (by omega) _ _ _ hA, chunksOf_of_lt (l := b.drop (b.length - b.length % 16)) (by simp; omega),
    List.append_nil]

/-- `by8`'s output, the whole blocks then the last partial one, is Vale's GCTR. -/
theorem by8_out (icb : Quad32) (alg : Algorithm) (kw : List (BitVec 32)) (b : List U8) :
    ((gctrEncryptRecursive icb alg kw (blocksAll (chunksOf 128 b)) 0).flatMap low.x86_64.aes_gcm.bytes ++
      ((gctrEncryptRecursive icb alg kw ((chunksOf 16 (chunksRest 128 b)).map loadBytes)
          (0 + 8 * (chunksOf 128 b).length)).flatMap low.x86_64.aes_gcm.bytes ++
        if (chunksRest 16 (chunksRest 128 b)).isEmpty = true then []
        else List.take (chunksRest 16 (chunksRest 128 b)).length (low.x86_64.aes_gcm.bytes
          (gctrEncryptBlock icb (low.x86_64.ghash.loadPadded (chunksRest 16 (chunksRest 128 b))) alg kw
            (0 + 8 * (chunksOf 128 b).length +
              ((chunksOf 16 (chunksRest 128 b)).map loadBytes).length))))).map (·.bv) =
      gctrEncrypt icb (b.map (·.bv)) alg kw := by
  have hch : ∀ c ∈ chunksOf 128 b, c.length = 128 := fun c h => chunksOf_length_mem h
  have hB := length_blocksAll _ hch
  have hall : (chunksOf 16 b).map loadBytes =
      blocksAll (chunksOf 128 b) ++ (chunksOf 16 (chunksRest 128 b)).map loadBytes := blocks_split b
  have hidx : 0 + 8 * (chunksOf 128 b).length + ((chunksOf 16 (chunksRest 128 b)).map loadBytes).length =
      b.length / 16 := by
    rw [← hB, Nat.zero_add, ← List.length_append, ← hall, List.length_map, chunksOf_length]
  rw [← (chunks_128 b).2, hidx, show 0 + 8 * (chunksOf 128 b).length = 0 + (blocksAll (chunksOf 128 b)).length by
    rw [hB], ← List.append_assoc, ← List.flatMap_append, ← gctr_append, ← hall]
  have hr := chunksRest_length 16 b
  simp only [gctrEncrypt, List.length_map]
  by_cases h0 : b.length % 16 = 0
  · have ht : chunksRest 16 b = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [ht, List.isEmpty_nil, ite_true, h0, List.append_nil, flatMap_bytes_bv, leBytesToSeqQuad32_load]
  · have ht : (chunksRest 16 b).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff]; intro h; rw [h] at hr; simp at hr; omega
    have hk : b.length - b.length % 16 = 16 * (b.length / 16) := by omega
    have hd : b.drop (16 * (b.length / 16)) = chunksRest 16 b := rfl
    have hpad : padTo128Bits ((chunksRest 16 b).map (·.bv)) =
        (chunksRest 16 b).map (·.bv) ++ List.replicate (16 - b.length % 16) 0 := by
      rw [padTo128Bits, List.length_map, hr, Nat.mod_mod, ite_eq_right h0]
    have hlp : low.x86_64.ghash.loadPadded (chunksRest 16 b) =
        leBytesToQuad32 ((chunksRest 16 b).map (·.bv) ++ List.replicate (16 - b.length % 16) 0) := by
      rw [low.x86_64.ghash.loadPadded, loadBytes, List.map_append, List.map_replicate, hr]
      rfl
    simp only [ht, Bool.false_eq_true, ite_false, h0, List.map_append, flatMap_bytes_bv,
      hk, ← List.map_take, ← List.map_drop, hd, leBytesToSeqQuad32_load, hpad, hlp, hr,
      show 16 * (b.length / 16) / 16 = b.length / 16 by omega]
    rw [List.map_take, bytes_bv, ← hk, chunksOf_take16]

/-! ## `by8` -/

/-- `by8`: Vale's GCTR from the counter after `j0`, and GHASH over the AAD's
and the ciphertext's padded blocks. -/
theorem by8_spec (ENC : Bool) (hk : low.x86_64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (ghash : low.x86_64.ghash.Ghash) (hg : ClmulOf ghash.table t) (j0 : Quad32) (y0 : Std.Array U8 16#usize)
    (hy : loadBytes y0.val = reverseBytesQuad32 j0) (aad inout : Slice U8) :
    ∃ g out, low.x86_64.aes_gcm.by8 ENC hk t ghash y0 aad inout = ok (g, out) ∧ g.table = ghash.table ∧
      out.val.map (·.bv) = gctrEncrypt (inc32 j0 1) (inout.val.map (·.bv)) alg kw ∧
      toPoly g.current = ghashPoly H (toPoly ghash.current)
        ((padBlocks aad.val ++ padBlocks (if ENC then out.val else inout.val)).map toPoly) := by
  choose F hF hFp using fun b x => clmul_add_spec H hH t ht b x
  have hadd : ∀ c b, low.x86_64.ghash.Ghash.addBytes { ghash with current := c } b =
      ok { ghash with current := F b c } := fun c b => by
    rw [addBytes_clmul { ghash with current := c } t hg, hF, bind_ok]
  have hadd0 : ∀ b, low.x86_64.ghash.Ghash.addBytes ghash b = ok { ghash with current := F b ghash.current } :=
    fun b => hadd ghash.current b
  obtain ⟨⟨f, rks, l⟩, hrk⟩ : ∃ r, hk.round_keys = r := ⟨_, rfl⟩
  have henc : ∀ c, low.x86_64.aes_gcm.encrypt c f rks l = ok (aesEncrypt alg kw c) := by
    intro c; have := encrypt_eq hk alg kw hkey c; rw [hrk] at this; exact this
  have hcn : low.x86_64.aes_gcm.Counter.new y0 = ok (swap (inc32 (inc32 j0 1) 0)) := by
    rw [inc32_zero]; exact counter_new j0 y0 hy
  have hch : ∀ c ∈ chunksOf 128 inout.val, c.length = 128 := fun c h => chunksOf_length_mem h
  have hlen_out : ∀ x : BitVec 128,
      ((gctrEncryptRecursive (inc32 j0 1) alg kw (blocksAll (chunksOf 128 inout.val)) 0).flatMap
          low.x86_64.aes_gcm.bytes ++
        ((gctrEncryptRecursive (inc32 j0 1) alg kw
            ((chunksOf 16 (chunksRest 128 inout.val)).map loadBytes)
            (0 + 8 * (chunksOf 128 inout.val).length)).flatMap low.x86_64.aes_gcm.bytes ++
          if (chunksRest 16 (chunksRest 128 inout.val)).isEmpty = true then []
          else List.take (chunksRest 16 (chunksRest 128 inout.val)).length (low.x86_64.aes_gcm.bytes x))).length =
        inout.val.length := by
    intro x
    have h1 := chunksRest_length 16 (chunksRest 128 inout.val)
    have h2 := chunksRest_length 128 inout.val
    have h3 := chunksOf_length 16 (chunksRest 128 inout.val)
    have h4 := chunksOf_length 128 inout.val
    have hl : (if (chunksRest 16 (chunksRest 128 inout.val)).isEmpty = true then []
        else List.take (chunksRest 16 (chunksRest 128 inout.val)).length (low.x86_64.aes_gcm.bytes x)).length =
        (chunksRest 16 (chunksRest 128 inout.val)).length := by
      split
      · rename_i he; simp only [List.isEmpty_iff] at he; rw [he]
      · rw [List.length_take, length_bytes]; omega
    rw [List.length_append, List.length_append, hl, length_flatMap_bytes, length_flatMap_bytes, length_gctr,
      length_gctr, length_blocksAll _ hch, List.length_map]
    omega
  unfold low.x86_64.aes_gcm.by8
  cases ENC <;>
  simp only [hadd0, hadd, bind_ok, uncurry_apply_pair, hrk, hcn, by8_loop_eq henc _ H t ht _ _ hch,
    ctr_blocks_eq henc, ctr_block_eq henc, ite_ok, Bool.false_eq_true, ite_false, ite_true] <;>
  rw [dite_eq_left (by rw [hlen_out]; exact inout.property)] <;>
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩
  · rw [Slice.from_val]; exact by8_out (inc32 j0 1) alg kw inout.val
  · dsimp only
    rw [hFp, hashChunks_spec H hH t ht _ _ _ (length_blocksAll _ hch), hFp, List.map_append, ghashPoly_append,
      padBlocks_split inout.val, List.map_append, ghashPoly_append, padBlocks_head, List.map_map]
  · rw [Slice.from_val]; exact by8_out (inc32 j0 1) alg kw inout.val
  · dsimp only
    rw [Slice.from_val, hFp, hashChunks_spec H hH t ht _ _ _ (by rw [length_gctr, length_blocksAll _ hch]), hFp,
      padBlocks_append ((gctrEncryptRecursive (inc32 j0 1) alg kw (blocksAll (chunksOf 128 inout.val)) 0).flatMap
        low.x86_64.aes_gcm.bytes) _ (by rw [length_flatMap_bytes]; omega),
      padBlocks_append ((gctrEncryptRecursive (inc32 j0 1) alg kw
        ((chunksOf 16 (chunksRest 128 inout.val)).map loadBytes)
        (0 + 8 * (chunksOf 128 inout.val).length)).flatMap low.x86_64.aes_gcm.bytes) _
        (by rw [length_flatMap_bytes]; omega)]
    simp only [padBlocks_flatMap_bytes, List.map_append, ghashPoly_append, List.map_map]

end rind.x86_64
