import Rind.Aarch64.AesCipher
import Rind.Aarch64.Sha3
import Rind.AesModes
import Rind.ValeBytes
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# AES-CTR and AES-CBC on the crypto extension

`low::aarch64::aes_ctr::apply` and `low::aarch64::aes_cbc`'s `encrypt` and
`decrypt` compute `Rind.AesModes`'s SP 800-38A modes on bytes, under a key
`Rind.Aarch64.AesKey` proves holds FIPS 197's round keys. CTR runs eight
blocks at a time through `generic::ctr::by8`, each a counter block built from
the nonce and the big-endian 32-bit counter; CBC encryption chains one block
at a time, with its first `AESE` the inline-assembly `aese_chained`, which
`Rind.Aarch64.FunsExternal` models by hand as the `AESE` it runs, and CBC
decryption runs eight independent blocks at a time, then the rest one at a
time. Each regroups the cipher's rounds as `AESE`, `AESMC`, `AESD`, and
`AESIMC` run them, which `evalCipher_fold` and `eqInvCipher_fold` show are
Vale's `eval_cipher` and FIPS 197's `EqInvCipher`.
-/

namespace rind.aarch64

/-! ## The cipher's rounds as the instructions group them -/

/-- The cipher's rounds as `AESE` and `AESMC` run them: Vale's `eval_cipher`. -/
theorem evalCipher_fold (alg : Algorithm) (rk : List (BitVec 128)) (hl : rk.length = nr alg + 1)
    (x : BitVec 128) :
    evalCipher alg x rk =
      shiftRows (subBytes ((rk.take (nr alg - 1)).foldl aeseMc x ^^^ rk[nr alg - 1]!)) ^^^ rk[nr alg]! := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  have hn : nr alg - 1 + 1 ≤ rk.length := by omega
  rw [foldl_aeseMc _ _ hn, evalCipher, evalRounds_foldl _ _ hn]

/-- `AESD` then `AESIMC`. -/
def aesdImc' (s k : BitVec 128) : BitVec 128 := invMixColumns (invSubBytes (invShiftRows (s ^^^ k)))

theorem foldl_aesdImc'_imc (l : List (BitVec 128)) (y : BitVec 128) :
    l.foldl aesdImc' (invMixColumns y) = invMixColumns (l.foldl aesdImc y) := by
  induction l generalizing y with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    rfl

/-- The inverse cipher's rounds as `AESD` and `AESIMC` run them, under its
round keys in the order `KeyExpansionEIC` expands them: FIPS 197's
`EqInvCipher` under them reversed. -/
theorem eqInvCipher_fold (alg : Algorithm) (rk : List (BitVec 128)) (hl : rk.length = nr alg + 1)
    (x : BitVec 128) :
    eqInvCipher alg x rk.reverse =
      invSubBytes (invShiftRows ((rk.take (nr alg - 1)).foldl aesdImc' x ^^^ rk[nr alg - 1]!)) ^^^
        rk[nr alg]! := by
  have hnr : 2 ≤ nr alg := by cases alg <;> decide
  have hrl : rk.reverse.length = nr alg + 1 := by simp [hl]
  -- `EqInvCipher`'s rounds, from the reversed keys' 1 to `nr - 1`.
  have hmid : ((rk.reverse.take (nr alg)).drop 1).reverse = (rk.drop 1).take (nr alg - 1) := by
    rw [← reverse_slice rk.reverse hrl, List.reverse_reverse]
  have e0 : rk.reverse[nr alg]! = rk[0]! := by
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_reverse (show nr alg < rk.length by omega), hl]
    rw [show nr alg + 1 - 1 - nr alg = 0 by omega]
  have en : rk.reverse[0]! = rk[nr alg]! := by
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_reverse (show 0 < rk.length by omega), hl]
    rfl
  -- The instructions' fold, from its first key's `AESD`.
  have htake : rk.take (nr alg - 1) = rk[0]! :: (rk.drop 1).take (nr alg - 2) := by
    cases rk with
    | nil => simp at hl
    | cons a t => rw [show nr alg - 1 = nr alg - 2 + 1 by omega]; simp
  have hL : (rk.drop 1).take (nr alg - 1) = (rk.drop 1).take (nr alg - 2) ++ [rk[nr alg - 1]!] := by
    rw [show nr alg - 1 = nr alg - 2 + 1 by omega, List.take_add_one, List.getElem?_drop,
      List.getElem?_eq_getElem (show 1 + (nr alg - 2) < rk.length by omega),
      getElem!_pos rk _ (show nr alg - 2 + 1 < rk.length by omega)]
    simp only [Option.toList_some, List.append_cancel_left_eq, List.cons.injEq, and_true]
    congr 1; omega
  have hnr1 : nr alg - 1 + 1 ≤ rk.reverse.length := by omega
  simp only [eqInvCipher]
  rw [eqInvRounds_foldl _ _ _ hnr1, show nr alg - 1 + 1 = nr alg by omega, hmid, e0, en, htake,
    List.foldl_cons, show aesdImc' x rk[0]! = invMixColumns (invSubBytes (invShiftRows (x ^^^ rk[0]!))) from rfl,
    foldl_aesdImc'_imc, ← invSubBytes_invShiftRows, ← foldl_aesdImc, hL, List.foldl_append]
  rfl

/-! ## Loops over a range -/

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-- A loop over the range `it` to `e`, its state `s` meeting `P` of the index
each step. -/
theorem range_loop {σ β : Type}
    (F : core.ops.range.Range Usize × σ → Result (ControlFlow (core.ops.range.Range Usize × σ) β))
    (e : Usize) (P : Nat → σ → Prop) (Q : β → Prop)
    (hstep : ∀ (it : core.ops.range.Range Usize) (s : σ), it.end = e → it.start.val < e.val →
      P it.start.val s →
      F (it, s) ⦃ r => ∃ it' s', r = .cont (it', s') ∧ it'.start.val = it.start.val + 1 ∧ it'.end = e ∧
        P (it.start.val + 1) s' ⦄)
    (hdone : ∀ (it : core.ops.range.Range Usize) (s : σ), it.end = e → it.start.val = e.val →
      P it.start.val s → F (it, s) ⦃ r => ∃ y, r = .done y ∧ Q y ⦄)
    (it : core.ops.range.Range Usize) (s : σ) (he : it.end = e) (hs : it.start.val ≤ e.val)
    (hP : P it.start.val s) :
    loop F (it, s) ⦃ Q ⦄ := by
  apply loop.spec_decr_nat (fun x => e.val - x.1.start.val)
    (fun x => x.1.end = e ∧ x.1.start.val ≤ e.val ∧ P x.1.start.val x.2)
  · rintro ⟨it0, s0⟩ ⟨he0, hs0, hP0⟩
    simp only at he0 hs0 hP0
    by_cases hlt : it0.start.val < e.val
    · apply WP.spec_mono (hstep it0 s0 he0 hlt hP0)
      rintro r ⟨it', s', rfl, h1, h2, h3⟩
      simp only
      refine ⟨⟨h2, by omega, by rw [h1]; exact h3⟩, by omega⟩
    · apply WP.spec_mono (hdone it0 s0 he0 (by omega) hP0)
      rintro r ⟨y, rfl, hy⟩
      exact hy
  · exact ⟨he, hs, hP⟩

theorem usize_sub_ok (N c : Usize) (hc : c.val ≤ N.val) :
    ∃ i : Usize, N - c = ok i ∧ i.val = N.val - c.val := by
  refine ⟨⟨BitVec.ofNat _ (N.val - c.val)⟩, ?_, ?_⟩
  · show UScalar.sub _ _ = _
    rw [UScalar.sub, ite_eq_right (by omega)]
  · have h1 : N.val - c.val < 2 ^ UScalarTy.Usize.numBits := by have := N.hBounds; omega
    show (BitVec.ofNat _ (N.val - c.val)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]

/-! ## Eight blocks at a time -/

abbrev V := core.core_arch.arm_shared.neon.uint8x16_t

theorem aes_round_8_spec (b : Std.Array V 8#usize) (k : BitVec 128) :
    low.aarch64.aes._aes_round_8 b k ⦃ r => ∀ i < 8, r.val[i]! = aeseMc b.val[i]! k ⦄ := by
  unfold low.aarch64.aes._aes_round_8 low.aarch64.aes._aes_round_8_loop
  apply range_loop _ 8#usize
    (fun j (b' : Std.Array V 8#usize) => ∀ i < 8, b'.val[i]! = if i < j then aeseMc b.val[i]! k else b.val[i]!)
  · intro it b' he hlt hP
    have hlt : it.start.val < 8 := by simpa using hlt
    unfold low.aarch64.aes._aes_round_8_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
    subst ho
    simp only [aese_eq, aesmc_eq, bind_ok]
    step*
    refine ⟨it', _, rfl, hst, by rw [hen, he], ?_⟩
    intro i hi
    rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
    by_cases h1 : it.start.val = i
    · subst h1
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true (by omega)), uxt_post,
        ← getElem!_pos, hP _ hlt, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), hP _ hi]
      by_cases h2 : i < it.start.val
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · intro it b' he hst hP
    unfold low.aarch64.aes._aes_round_8_loop.body
    step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
    subst ho
    simp only [WP.spec_ok]
    refine ⟨b', rfl, ?_⟩
    intro i hi
    rw [hP _ hi, ite_eq_left_of_eq_true _ _ (eq_true (by simp at hst; omega))]
  · rfl
  · simp
  · intro i hi; simp

theorem aes_8_blocks_spec {N : Usize} (hN : 2 ≤ N.val) (rk : Std.Array V N) (b : Std.Array V 8#usize) :
    low.aarch64.aes._aes_8_blocks rk b ⦃ r => ∀ i < 8, r.val[i]! =
      shiftRows (subBytes ((rk.val.take (N.val - 2)).foldl aeseMc b.val[i]! ^^^ rk.val[N.val - 2]!)) ^^^
        rk.val[N.val - 1]! ⦄ := by
  have hl : rk.val.length = N.val := by simp
  unfold low.aarch64.aes._aes_8_blocks
  obtain ⟨i, hi, hiv⟩ := usize_sub_ok N 2#usize (by simp; omega)
  have hiv : i.val = N.val - 2 := by simpa using hiv
  simp only [hi, bind_ok]
  apply WP.spec_bind (Pₘ := fun b1 : Std.Array V 8#usize =>
    ∀ j < 8, b1.val[j]! = (rk.val.take (N.val - 2)).foldl aeseMc b.val[j]!)
  · unfold low.aarch64.aes._aes_8_blocks_loop0
    apply range_loop _ i (fun r (b' : Std.Array V 8#usize) =>
      ∀ j < 8, b'.val[j]! = (rk.val.take r).foldl aeseMc b.val[j]!)
    · intro it b' he hlt hP
      unfold low.aarch64.aes._aes_8_blocks_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      step*
      step with aes_round_8_spec as ⟨b1, hb1⟩
      refine ⟨it', b1, rfl, hst, by rw [hen, he], ?_⟩
      intro j hj
      rw [hb1 j hj, hP j hj, uxt_post, List.take_add_one, List.foldl_append,
        List.getElem?_eq_getElem (show it.start.val < rk.val.length by rw [← he] at hlt; omega)]
      rfl
    · intro it b' he hst hP
      unfold low.aarch64.aes._aes_8_blocks_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨b', rfl, ?_⟩
      intro j hj
      rw [hP j hj, hst, hiv]
    · rfl
    · simp
    · intro j hj; simp
  · intro b1 hb1
    unfold low.aarch64.aes._aes_8_blocks_loop1
    apply range_loop _ 8#usize (fun r (b' : Std.Array V 8#usize) =>
      ∀ j < 8, b'.val[j]! = if j < r then
        shiftRows (subBytes (b1.val[j]! ^^^ rk.val[N.val - 2]!)) ^^^ rk.val[N.val - 1]! else b1.val[j]!)
    · intro it b' he hlt hP
      have hlt : it.start.val < 8 := by simpa using hlt
      unfold low.aarch64.aes._aes_8_blocks_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      obtain ⟨i1, hi1, hi1v⟩ := usize_sub_ok N 1#usize (by simp; omega)
      have hi1v : i1.val = N.val - 1 := by simpa using hi1v
      simp only [aese_eq, core.core_arch.arm_shared.neon.generated.veorq_u8, bind_ok, hi1]
      step*
      refine ⟨it', _, rfl, hst, by rw [hen, he], ?_⟩
      intro j hj
      rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
      by_cases h1 : it.start.val = j
      · subst h1
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true (by omega)), uxt_post,
          uxt1_post, uxt3_post, ← getElem!_pos, ← getElem!_pos, ← getElem!_pos, hP _ hlt,
          ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hiv, hi1v]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), hP _ hj]
        by_cases h2 : j < it.start.val
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    · intro it b' he hst hP
      unfold low.aarch64.aes._aes_8_blocks_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨b', rfl, ?_⟩
      intro j hj
      rw [hP j hj, ite_eq_left_of_eq_true _ _ (eq_true (by simp at hst; omega)), hb1 j hj]
    · rfl
    · simp
    · intro j hj; simp

theorem getElem_eq_getElem! {α : Type _} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i] = l[i]! := (getElem!_pos l i h).symm

/-- Eight blocks' AES-192 cipher. -/
theorem aes192_8_blocks_spec (rk : Std.Array V 13#usize) (b0 b1 b2 b3 b4 b5 b6 b7 : V) :
    low.aarch64.aes._aes192_8_blocks rk b0 b1 b2 b3 b4 b5 b6 b7 ⦃ r => r =
      (evalCipher .AES_192 b0 rk.val, evalCipher .AES_192 b1 rk.val, evalCipher .AES_192 b2 rk.val,
       evalCipher .AES_192 b3 rk.val, evalCipher .AES_192 b4 rk.val, evalCipher .AES_192 b5 rk.val,
       evalCipher .AES_192 b6 rk.val, evalCipher .AES_192 b7 rk.val) ⦄ := by
  have hl : rk.val.length = nr .AES_192 + 1 := by simp [nr]
  unfold low.aarch64.aes._aes192_8_blocks
  step with aes_8_blocks_spec (N := 13#usize) (by decide) as ⟨a, ha⟩
  step*
  subst_vars
  simp only [getElem_eq_getElem!]
  rw [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide)]
  simp only [evalCipher_fold .AES_192 _ hl, Std.Array.make_val]
  simp [nr]

set_option maxRecDepth 100000 in
/-- Eight blocks' AES-128 cipher. -/
theorem aes128_8_blocks_eq (rk : Std.Array V 11#usize) (b0 b1 b2 b3 b4 b5 b6 b7 : V) :
    low.aarch64.aes._aes128_8_blocks rk b0 b1 b2 b3 b4 b5 b6 b7 = ok
      (evalCipher .AES_128 b0 rk.val, evalCipher .AES_128 b1 rk.val, evalCipher .AES_128 b2 rk.val,
       evalCipher .AES_128 b3 rk.val, evalCipher .AES_128 b4 rk.val, evalCipher .AES_128 b5 rk.val,
       evalCipher .AES_128 b6 rk.val, evalCipher .AES_128 b7 rk.val) := by
  obtain ⟨l, hl, rfl⟩ : ∃ l h, rk = Std.Array.make _ l h :=
    ⟨rk.val, rk.property, Std.Array.ext _ _ (by simp [Std.Array.make_val])⟩
  unfold low.aarch64.aes._aes128_8_blocks
  match l, hl with
  | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10], _ =>
    simp [Std.Array.make_val, Std.Array.index_usize, aese_eq, aesmc_eq,
      core.core_arch.arm_shared.neon.generated.veorq_u8, evalCipher, evalRounds, evalRound, nr]

set_option maxRecDepth 100000 in
/-- Eight blocks' AES-256 cipher. -/
theorem aes256_8_blocks_eq (rk : Std.Array V 15#usize) (b0 b1 b2 b3 b4 b5 b6 b7 : V) :
    low.aarch64.aes._aes256_8_blocks rk b0 b1 b2 b3 b4 b5 b6 b7 = ok
      (evalCipher .AES_256 b0 rk.val, evalCipher .AES_256 b1 rk.val, evalCipher .AES_256 b2 rk.val,
       evalCipher .AES_256 b3 rk.val, evalCipher .AES_256 b4 rk.val, evalCipher .AES_256 b5 rk.val,
       evalCipher .AES_256 b6 rk.val, evalCipher .AES_256 b7 rk.val) := by
  obtain ⟨l, hl, rfl⟩ : ∃ l h, rk = Std.Array.make _ l h :=
    ⟨rk.val, rk.property, Std.Array.ext _ _ (by simp [Std.Array.make_val])⟩
  unfold low.aarch64.aes._aes256_8_blocks
  match l, hl with
  | [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14], _ =>
    simp [Std.Array.make_val, Std.Array.index_usize, aese_eq, aesmc_eq,
      core.core_arch.arm_shared.neon.generated.veorq_u8, evalCipher, evalRounds, evalRound, nr]

/-- `encrypt_8` encrypts eight blocks under the key. -/
theorem encrypt_8_spec (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (h : HwKeyIs alg kw hk) (b0 b1 b2 b3 b4 b5 b6 b7 : V) :
    low.aarch64.aes_ctr.encrypt_8 hk b0 b1 b2 b3 b4 b5 b6 b7 ⦃ r => r =
      (aesEncrypt alg kw b0, aesEncrypt alg kw b1, aesEncrypt alg kw b2, aesEncrypt alg kw b3,
       aesEncrypt alg kw b4, aesEncrypt alg kw b5, aesEncrypt alg kw b6, aesEncrypt alg kw b7) ⦄ := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes_ctr.encrypt_8, low.aarch64.aes.AesKey128.impl.round_keys, bind_ok,
      aes128_8_blocks_eq, WP.spec_ok, hrk, aesEncrypt]
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes_ctr.encrypt_8, low.aarch64.aes.AesKey192.impl.round_keys, bind_ok]
    apply WP.spec_mono (aes192_8_blocks_spec _ b0 b1 b2 b3 b4 b5 b6 b7)
    intro r hr
    simp only [hr, hrk, aesEncrypt]
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.aarch64.aes_ctr.encrypt_8, low.aarch64.aes.AesKey256.impl.round_keys, bind_ok,
      aes256_8_blocks_eq, WP.spec_ok, hrk, aesEncrypt]

/-! ## Blocks as bytes -/

theorem leBytesToQuad32_zipWith (a b : List (BitVec 8)) (ha : a.length = 16) (hb : b.length = 16) :
    leBytesToQuad32 (List.zipWith (· ^^^ ·) a b) = leBytesToQuad32 a ^^^ leBytesToQuad32 b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_xor, getLsbD_leBytesToQuad32 _ hk, getLsbD_leBytesToQuad32 _ hk,
    getLsbD_leBytesToQuad32 _ hk, List.getElem!_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem (show k / 8 < a.length by omega),
    List.getElem?_eq_getElem (show k / 8 < b.length by omega),
    getElem!_pos a _ (by omega), getElem!_pos b _ (by omega)]
  simp

theorem leBytesToQuad32_leQuad32ToBytes' (q : Quad32) : leBytesToQuad32 (leQuad32ToBytes q) = q := by
  apply eq_of_byte_eq; intro i hi
  rw [byte_leBytesToQuad32 _ hi, leQuad32ToBytes_getElem! _ hi]

theorem length_leQuad32ToBytes (q : Quad32) : (leQuad32ToBytes q).length = 16 := by
  simp [leQuad32ToBytes]

theorem bvs_length (a : Std.Array U8 16#usize) : (bvs a.val).length = 16 := by simp

/-- A block's bytes, which `cbcEncrypt` and `cbcDecrypt` read. -/
abbrev blockBytes (a : Std.Array U8 16#usize) : List (BitVec 8) := bvs a.val

theorem aesBlock_eq (alg : Algorithm) (key : List (BitVec 8)) (p c : List (BitVec 8)) (hp : p.length = 16)
    (hc : c.length = 16) :
    aesBlock alg key (List.zipWith (· ^^^ ·) p c) =
      leQuad32ToBytes (aesEncrypt alg (seqNat8ToSeqNat32LE key) (leBytesToQuad32 p ^^^ leBytesToQuad32 c)) := by
  rw [aesBlock, leBytesToQuad32_zipWith _ _ hp hc]

theorem cbcEncrypt_nil (alg : Algorithm) (key iv : List (BitVec 8)) : cbcEncrypt alg key iv [] = [] := by
  rw [cbcEncrypt]; simp

theorem cbcEncrypt_cons (alg : Algorithm) (key iv p rest : List (BitVec 8)) (hp : p.length = 16) :
    cbcEncrypt alg key iv (p ++ rest) =
      aesBlock alg key (List.zipWith (· ^^^ ·) p iv) ++
        cbcEncrypt alg key (aesBlock alg key (List.zipWith (· ^^^ ·) p iv)) rest := by
  rw [cbcEncrypt]
  simp [hp]

theorem cbcDecrypt_nil (alg : Algorithm) (key iv : List (BitVec 8)) : cbcDecrypt alg key iv [] = [] := by
  rw [cbcDecrypt]; simp

theorem cbcDecrypt_cons (alg : Algorithm) (key iv c rest : List (BitVec 8)) (hc : c.length = 16) :
    cbcDecrypt alg key iv (c ++ rest) =
      List.zipWith (· ^^^ ·) (aesBlockDecrypt alg key c) iv ++ cbcDecrypt alg key c rest := by
  rw [cbcDecrypt]
  simp [hc]

/-! ## CBC encryption -/

theorem encrypt_rounds_loop_eq (s : Slice V) (n : Nat) :
    ∀ i b, s.val.length - i = n →
      low.aarch64.aes_cbc.encrypt_rounds_loop ⟨s, i⟩ b = ok ((s.val.drop i).foldl aeseMc b) := by
  induction n with
  | zero =>
    intro i b hn
    unfold low.aarch64.aes_cbc.encrypt_rounds_loop
    rw [loop_done (z := b)]
    · simp [List.drop_eq_nil_of_le (show s.val.length ≤ i by omega)]
    · simp only [low.aarch64.aes_cbc.encrypt_rounds_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_right (by simp [Slice.len]; omega)]
      simp
  | succ n ih =>
    intro i b hn
    have hi : i < s.val.length := by omega
    unfold low.aarch64.aes_cbc.encrypt_rounds_loop
    rw [loop_cont (y := (⟨s, i + 1⟩, aeseMc b s.val[i]))]
    · rw [List.drop_eq_getElem_cons hi, List.foldl_cons]
      exact ih (i + 1) _ (by omega)
    · simp only [low.aarch64.aes_cbc.encrypt_rounds_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_left (by simp [Slice.len]; omega)]
      simp [aese_eq, aesmc_eq, aeseMc]
      rfl

theorem encrypt_rounds_spec {N : Usize} (hN : 3 ≤ N.val) (rk : Std.Array V N) (b : V) :
    low.aarch64.aes_cbc.encrypt_rounds rk b ⦃ r =>
      r = shiftRows (subBytes (((rk.val.drop 1).take (N.val - 3)).foldl aeseMc b ^^^ rk.val[N.val - 2]!)) ⦄ := by
  have hl : rk.val.length = N.val := by simp
  obtain ⟨i, hi, hiv⟩ := usize_sub_ok N 2#usize (by simp; omega)
  have hiv : i.val = N.val - 2 := by simpa using hiv
  unfold low.aarch64.aes_cbc.encrypt_rounds
  simp only [hi, bind_ok]
  step with core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec as ⟨s, hs, hsl⟩
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
  rw [encrypt_rounds_loop_eq s _ 0 _ rfl, bind_ok]
  step*
  rw [uxt_post, aese_eq, WP.spec_ok, hs, ← getElem!_pos, hiv, List.drop_zero]
  simp [List.slice]
  rw [show N.val - 2 - 1 = N.val - 3 by omega]

/-- `aese_chained`'s `AESE` and an `AESMC` of the plaintext block XORed with
the first round key and the chaining block. -/
theorem xor_chain (p c k l : BitVec 128) : (c ^^^ l) ^^^ (p ^^^ (k ^^^ l)) = (p ^^^ c) ^^^ k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor]
  cases p.getLsbD i <;> cases c.getLsbD i <;> cases k.getLsbD i <;> cases l.getLsbD i <;> rfl

/-- One block of `hw_encrypt`'s chain: `aese_chained` of the chaining block
and the plaintext block, each XORed with the last round key off the chain,
then the rounds of `encrypt_rounds`, are the cipher of the plaintext XORed
with the chaining block, less the last round key. -/
theorem enc_chain {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1) (rk : Std.Array V N)
    (p c : BitVec 128) :
    shiftRows (subBytes (((rk.val.drop 1).take (N.val - 3)).foldl aeseMc
      (mixColumns (shiftRows (subBytes ((c ^^^ rk.val[N.val - 1]!) ^^^
        (p ^^^ (rk.val[0]! ^^^ rk.val[N.val - 1]!)))))) ^^^ rk.val[N.val - 2]!)) =
      evalCipher alg (p ^^^ c) rk.val ^^^ rk.val[N.val - 1]! := by
  have hnr : 2 ≤ nr alg := by cases alg <;> decide
  have hl : rk.val.length = nr alg + 1 := by simp [hN]
  have htake : rk.val.take (nr alg - 1) = rk.val[0]! :: (rk.val.drop 1).take (N.val - 3) := by
    obtain ⟨l, hl'⟩ : ∃ l, l = rk.val := ⟨_, rfl⟩
    rw [← hl'] at hl ⊢
    cases l with
    | nil => simp at hl
    | cons a t => rw [show nr alg - 1 = (N.val - 3) + 1 by omega]; simp
  rw [xor_chain, evalCipher_fold alg _ hl, show N.val - 1 = nr alg by omega, BitVec.xor_assoc (shiftRows _),
    BitVec.xor_self, BitVec.xor_zero, htake, List.foldl_cons, show N.val - 2 = nr alg - 1 by omega]
  rfl

theorem getElem!_of_drop_eq {α : Type _} [Inhabited α] {l l' : List α} {j : Nat} (h : l.drop j = l'.drop j) :
    l[j]! = l'[j]! := by
  have := congrArg (fun x => x[0]!) h
  simpa [List.getElem!_eq_getElem?_getD, List.getElem?_drop] using this

theorem drop_set_succ {α : Type _} (l : List α) (j : Nat) (x : α) :
    (l.set j x).drop (j + 1) = l.drop (j + 1) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_drop, List.getElem_set]
  rw [ite_f (by omega)]

theorem take_set_succ {α : Type _} (l : List α) (j : Nat) (x : α) (hj : j < l.length) :
    (l.set j x).take (j + 1) = l.take j ++ [x] := by
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [List.getElem_take, List.getElem_set, List.getElem_append]
  by_cases hk : k < j
  · rw [dite_eq_left_of_eq_true (eq_true (by simp; omega)), ite_f (by omega)]
  · rw [dite_eq_right_of_eq_false (eq_false (by simp; omega)), ite_t (by simp at h1; omega)]
    simp

theorem bvs_storeBytes (q : BitVec 128) : blockBytes (storeBytes q) = leQuad32ToBytes q := store_bytes q

theorem hw_encrypt_spec {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1) (key : List (BitVec 8))
    (rk : Std.Array V N) (hrk : rk.val = keyToRoundKeys alg (seqNat8ToSeqNat32LE key))
    (iv : Std.Array U8 16#usize) (blocks : Slice (Std.Array U8 16#usize)) :
    low.aarch64.aes_cbc.hw_encrypt rk iv blocks ⦃ r =>
      r.val.flatMap blockBytes = cbcEncrypt alg key (blockBytes iv) (blocks.val.flatMap blockBytes) ⦄ := by
  have hnr : 2 ≤ nr alg := by cases alg <;> decide
  have hl : rk.val.length = N.val := by simp
  obtain ⟨i, hi, hiv⟩ := usize_sub_ok N 1#usize (by simp; omega)
  have hiv : i.val = N.val - 1 := by simpa using hiv
  unfold low.aarch64.aes_cbc.hw_encrypt
  simp only [hi, bind_ok, load_eq, core.core_arch.arm_shared.neon.generated.veorq_u8]
  step as ⟨last, hlast⟩
  step as ⟨k0, hk0⟩
  rw [← getElem!_pos, hiv] at hlast
  rw [← getElem!_pos] at hk0
  subst hlast hk0
  unfold low.aarch64.aes_cbc.hw_encrypt_loop
  apply range_loop _ (Slice.len blocks)
    (fun j (st : Slice (Std.Array U8 16#usize) × V) =>
      st.1.val.length = blocks.val.length ∧ st.1.val.drop j = blocks.val.drop j ∧
      ∃ cB : List (BitVec 8), cB.length = 16 ∧ st.2 = leBytesToQuad32 cB ^^^ rk.val[N.val - 1]! ∧
        cbcEncrypt alg key (blockBytes iv) (blocks.val.flatMap blockBytes) =
          (st.1.val.take j).flatMap blockBytes ++ cbcEncrypt alg key cB ((blocks.val.drop j).flatMap blockBytes))
  · rintro it ⟨bl, y⟩ he hlt ⟨hlen, hdrop, cB, hcB, hy, hW⟩
    simp only at hlen hdrop hy hW
    have hlt : it.start.val < blocks.val.length := by simpa [he] using hlt
    unfold low.aarch64.aes_cbc.hw_encrypt_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
    subst ho
    step as ⟨a, ha⟩
    rw [← getElem!_pos, getElem!_of_drop_eq hdrop] at ha
    subst ha
    simp only [load_eq, core.core_arch.arm_shared.neon.generated.veorq_u8,
      low.aarch64.aes_cbc.aese_chained, aese_eq, aesmc_eq, bind_ok, hy]
    step with encrypt_rounds_spec (N := N) (by omega) as ⟨y1, hy1⟩
    rw [enc_chain alg hN] at hy1
    simp only [store_eq, bind_ok, hy1, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    step as ⟨s', hs'⟩
    refine ⟨it', (s', _), rfl, hst, by rw [hen, he], ?_⟩
    have hp : blocks.val.drop it.start.val =
        blocks.val[it.start.val]! :: blocks.val.drop (it.start.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt, getElem!_pos]
    rw [hs', Slice.set_val_eq]
    refine ⟨by simp [hlen], by rw [drop_set_succ, ← List.drop_drop, hdrop, List.drop_drop],
      leQuad32ToBytes (evalCipher alg (loadBytes (blocks.val[it.start.val]!).val ^^^ leBytesToQuad32 cB) rk.val),
      length_leQuad32ToBytes _, ?_, ?_⟩
    · simp only [leBytesToQuad32_leQuad32ToBytes']
    · rw [hW, take_set_succ _ _ _ (by omega), hp, List.flatMap_cons, cbcEncrypt_cons _ _ _ _ _ (by simp),
        aesBlock_eq _ _ _ _ (by simp) hcB, List.flatMap_append, List.append_assoc]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, bvs_storeBytes, aesEncrypt, hrk]
      rfl
  · rintro it ⟨bl, y⟩ he hst ⟨hlen, hdrop, cB, hcB, hy, hW⟩
    simp only at hlen hdrop hy hW
    have hst : it.start.val = blocks.val.length := by simpa [he] using hst
    unfold low.aarch64.aes_cbc.hw_encrypt_loop.body
    step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
    subst ho
    simp only [WP.spec_ok]
    refine ⟨bl, rfl, ?_⟩
    rw [hW, hst, List.drop_length, List.flatMap_nil, cbcEncrypt_nil, List.append_nil,
      List.take_of_length_le (by omega)]
  · rfl
  · simp
  · refine ⟨rfl, rfl, blockBytes iv, by simp, by simp [loadBytes], by simp⟩

/-! ## The keys -/

/-- `k` holds FIPS 197's round keys, on the crypto extension's AES
instructions, for the AES key bytes `key`, which `alg` sizes. -/
def ModeKeyIs (alg : Algorithm) (key : List (BitVec 8)) (k : low.aarch64.aes.AesKey) : Prop :=
  key.length = 4 * nk alg ∧ ∃ hk, k = .Hw hk ∧ HwKeyIs alg (seqNat8ToSeqNat32LE key) hk

/-- `k` holds `KeyExpansionEIC`'s round keys, in reverse, on the crypto
extension's AES instructions, for the AES key bytes `key`, which `alg` sizes. -/
def ModeDecKeyIs (alg : Algorithm) (key : List (BitVec 8)) (k : low.aarch64.aes.AesDecKey) : Prop :=
  key.length = 4 * nk alg ∧ ∃ hk, k = .Hw hk ∧ HwDecKeyIs alg (seqNat8ToSeqNat32LE key) hk

/-- `mid::aes::expand_key` expands an AES key of the algorithm's length on the
crypto extension. -/
theorem expand_key_mode_spec (h : RunsAesHw) (alg : Algorithm) (key : Slice U8) (hk : key.length = 4 * nk alg) :
    mid.aes.expand_key key ⦃ k => ModeKeyIs alg (bvs key.val) k ⦄ := by
  have hl : (bvs key.val).length = 4 * nk alg := by simpa using hk
  cases alg
  · exact WP.spec_mono (expand_key128_spec h key (by simpa [nk] using hk))
      fun k ⟨k128, hk1, hk2⟩ => ⟨hl, _, hk1, rfl, hk2⟩
  · exact WP.spec_mono (expand_key192_spec h key (by simpa [nk] using hk))
      fun k ⟨k192, hk1, hk2⟩ => ⟨hl, _, hk1, rfl, hk2⟩
  · exact WP.spec_mono (expand_key256_spec h key (by simpa [nk] using hk))
      fun k ⟨k256, hk1, hk2⟩ => ⟨hl, _, hk1, rfl, hk2⟩

/-- `AesDecKey::new` expands an AES key of the algorithm's length on the
crypto extension. -/
theorem dec_key_new_mode_spec (h : RunsAesHw) (alg : Algorithm) (key : Slice U8)
    (hk : key.length = 4 * nk alg) :
    low.aarch64.aes.AesDecKey.new key ⦃ k => ModeDecKeyIs alg (bvs key.val) k ⦄ := by
  have hl : (bvs key.val).length = 4 * nk alg := by simpa using hk
  exact WP.spec_mono (dec_key_new_spec h alg key hk) fun k ⟨hwk, hk1, hk2⟩ => ⟨hl, hwk, hk1, hk2⟩

/-! ## CBC -/

/-- `low::aarch64::aes_cbc::encrypt` is SP 800-38A's CBC encryption of the
blocks, chained from `iv`. -/
theorem aes_cbc_encrypt_spec (alg : Algorithm) (key : List (BitVec 8)) (k : low.aarch64.aes.AesKey)
    (hk : ModeKeyIs alg key k) (iv : Std.Array U8 16#usize) (blocks : Slice (Std.Array U8 16#usize)) :
    low.aarch64.aes_cbc.encrypt k iv blocks ⦃ r =>
      r.val.flatMap (fun b => bvs b.val) =
        cbcEncrypt alg key (bvs iv.val) (blocks.val.flatMap fun b => bvs b.val) ⦄ := by
  obtain ⟨-, hwk, rfl, hwk_is⟩ := hk
  cases hwk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := hwk_is
    simp only [low.aarch64.aes_cbc.encrypt, low.aarch64.aes.AesKey128.impl.round_keys, bind_ok]
    exact hw_encrypt_spec .AES_128 (by simp [nr]) key _ hrk iv blocks
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := hwk_is
    simp only [low.aarch64.aes_cbc.encrypt, low.aarch64.aes.AesKey192.impl.round_keys, bind_ok]
    exact hw_encrypt_spec .AES_192 (by simp [nr]) key _ hrk iv blocks
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := hwk_is
    simp only [low.aarch64.aes_cbc.encrypt, low.aarch64.aes.AesKey256.impl.round_keys, bind_ok]
    exact hw_encrypt_spec .AES_256 (by simp [nr]) key _ hrk iv blocks

theorem decrypt_rounds_loop_eq (s : Slice V) (n : Nat) :
    ∀ i b, s.val.length - i = n →
      low.aarch64.aes_cbc.decrypt_rounds_loop ⟨s, i⟩ b = ok ((s.val.drop i).foldl aesdImc' b) := by
  induction n with
  | zero =>
    intro i b hn
    unfold low.aarch64.aes_cbc.decrypt_rounds_loop
    rw [loop_done (z := b)]
    · simp [List.drop_eq_nil_of_le (show s.val.length ≤ i by omega)]
    · simp only [low.aarch64.aes_cbc.decrypt_rounds_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_right (by simp [Slice.len]; omega)]
      simp
  | succ n ih =>
    intro i b hn
    have hi : i < s.val.length := by omega
    unfold low.aarch64.aes_cbc.decrypt_rounds_loop
    rw [loop_cont (y := (⟨s, i + 1⟩, aesdImc' b s.val[i]))]
    · rw [List.drop_eq_getElem_cons hi, List.foldl_cons]
      exact ih (i + 1) _ (by omega)
    · simp only [low.aarch64.aes_cbc.decrypt_rounds_loop.body, core.slice.iter.IteratorSliceIter.next]
      rw [dite_eq_left (by simp [Slice.len]; omega)]
      simp [core.core_arch.arm_shared.neon.generated.vaesimcq_u8,
        core.core_arch.arm_shared.neon.generated.vaesdq_u8, aesdImc']
      rfl

/-- The inverse cipher's rounds as `AESD` and `AESIMC` run them, all but the
last round key's XOR. -/
def decRounds {N : Usize} (rk : Std.Array V N) (x : BitVec 128) : BitVec 128 :=
  invSubBytes (invShiftRows ((rk.val.take (N.val - 2)).foldl aesdImc' x ^^^ rk.val[N.val - 2]!))

theorem decrypt_rounds_spec {N : Usize} (hN : 2 ≤ N.val) (rk : Std.Array V N) (b : V) :
    low.aarch64.aes_cbc.decrypt_rounds rk b ⦃ r => r = decRounds rk b ⦄ := by
  have hl : rk.val.length = N.val := by simp
  obtain ⟨i, hi, hiv⟩ := usize_sub_ok N 2#usize (by simp; omega)
  have hiv : i.val = N.val - 2 := by simpa using hiv
  unfold low.aarch64.aes_cbc.decrypt_rounds
  simp only [hi, bind_ok]
  step with core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec as ⟨s, hs, hsl⟩
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
  rw [decrypt_rounds_loop_eq s _ 0 _ rfl, bind_ok]
  step*
  simp only [core.core_arch.arm_shared.neon.generated.vaesdq_u8, WP.spec_ok]
  rw [uxt_post, hs, ← getElem!_pos, hiv, List.drop_zero, decRounds]
  simp [List.slice]

/-- `decRounds` and the last round key's XOR are FIPS 197's decryption under
the key whose `KeyExpansionEIC` round keys are `rk` reversed. -/
theorem decRounds_eq {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1) (kw : List (BitVec 32))
    (rk : Std.Array V N) (hrk : rk.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg kw)) (x : BitVec 128) :
    decRounds rk x ^^^ rk.val[N.val - 1]! = aesDecrypt alg kw x := by
  have hl : rk.val.length = nr alg + 1 := by simp [hN]
  rw [aesDecrypt, ← hrk, eqInvCipher_fold alg _ hl, decRounds, show N.val - 2 = nr alg - 1 by omega,
    show N.val - 1 = nr alg by omega]

theorem decrypt_round_8_spec (b : Std.Array V 8#usize) (k : BitVec 128) :
    low.aarch64.aes_cbc.decrypt_round_8 b k ⦃ r => ∀ i < 8, r.val[i]! = aesdImc' b.val[i]! k ⦄ := by
  unfold low.aarch64.aes_cbc.decrypt_round_8 low.aarch64.aes_cbc.decrypt_round_8_loop
  apply range_loop _ 8#usize
    (fun j (b' : Std.Array V 8#usize) => ∀ i < 8, b'.val[i]! = if i < j then aesdImc' b.val[i]! k else b.val[i]!)
  · intro it b' he hlt hP
    have hlt : it.start.val < 8 := by simpa using hlt
    unfold low.aarch64.aes_cbc.decrypt_round_8_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
    subst ho
    simp only [core.core_arch.arm_shared.neon.generated.vaesimcq_u8,
      core.core_arch.arm_shared.neon.generated.vaesdq_u8, bind_ok]
    step*
    refine ⟨it', _, rfl, hst, by rw [hen, he], ?_⟩
    intro i hi
    rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
    by_cases h1 : it.start.val = i
    · subst h1
      rw [ite_t rfl, ite_t (by omega), uxt_post, ← getElem!_pos, hP _ hlt, ite_f (by omega)]
      rfl
    · rw [ite_f h1, hP _ hi]
      by_cases h2 : i < it.start.val
      · rw [ite_t h2, ite_t (by omega)]
      · rw [ite_f h2, ite_f (by omega)]
  · intro it b' he hst hP
    unfold low.aarch64.aes_cbc.decrypt_round_8_loop.body
    step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
    subst ho
    simp only [WP.spec_ok]
    refine ⟨b', rfl, ?_⟩
    intro i hi
    rw [hP _ hi, ite_t (by simp at hst; omega)]
  · rfl
  · simp
  · intro i hi; simp

/-- `decrypt_8` decrypts eight blocks, each XORed with the one before it, the
first with `prev`, and returns the last ciphertext block. -/
theorem decrypt_8_spec {N : Usize} (hN : 3 ≤ N.val) (rk : Std.Array V N) (prev : V)
    (chunk : Std.Array (Std.Array U8 16#usize) 8#usize) :
    low.aarch64.aes_cbc.decrypt_8 rk prev chunk ⦃ next chunk' =>
      next = loadBytes (chunk.val[7]!).val ∧
      ∀ j < 8, chunk'.val[j]! = storeBytes (decRounds rk (loadBytes (chunk.val[j]!).val) ^^^
        (rk.val[N.val - 1]! ^^^ if j = 0 then prev else loadBytes (chunk.val[j - 1]!).val)) ⦄ := by
  have hl : rk.val.length = N.val := by simp
  obtain ⟨i, hi, hiv⟩ := usize_sub_ok N 1#usize (by simp; omega)
  have hiv : i.val = N.val - 1 := by simpa using hiv
  obtain ⟨i1, hi1, hi1v⟩ := usize_sub_ok N 2#usize (by simp; omega)
  have hi1v : i1.val = N.val - 2 := by simpa using hi1v
  unfold low.aarch64.aes_cbc.decrypt_8
  simp only [hi, hi1, bind_ok]
  step as ⟨last, hlast⟩
  rw [← getElem!_pos, hiv] at hlast
  subst hlast
  -- The eight ciphertext blocks.
  apply WP.spec_bind (Pₘ := fun b1 : Std.Array V 8#usize => ∀ j < 8, b1.val[j]! = loadBytes (chunk.val[j]!).val)
  · unfold low.aarch64.aes_cbc.decrypt_8_loop0
    apply range_loop _ 8#usize (fun r (b' : Std.Array V 8#usize) =>
      ∀ j < 8, b'.val[j]! = if j < r then loadBytes (chunk.val[j]!).val else prev)
    · intro it b' he hlt hP
      have hlt : it.start.val < 8 := by simpa using hlt
      unfold low.aarch64.aes_cbc.decrypt_8_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      simp only [load_eq, bind_ok]
      step*
      refine ⟨it', _, rfl, hst, by rw [hen, he], ?_⟩
      intro j hj
      rw [a1_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
      by_cases h1 : it.start.val = j
      · subst h1
        rw [ite_t rfl, ite_t (by omega), a_post, ← getElem!_pos]
      · rw [ite_f h1, hP _ hj]
        by_cases h2 : j < it.start.val
        · rw [ite_t h2, ite_t (by omega)]
        · rw [ite_f h2, ite_f (by omega)]
    · intro it b' he hst hP
      unfold low.aarch64.aes_cbc.decrypt_8_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨b', rfl, ?_⟩
      intro j hj
      rw [hP _ hj, ite_t (by simp at hst; omega)]
    · rfl
    · simp
    · intro j hj
      rw [Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
      simp [hj]
  intro b1 hb1
  step as ⟨next, hnext⟩
  rw [← getElem!_pos, hb1 7 (by decide)] at hnext
  subst hnext
  -- Their rounds but the last.
  apply WP.spec_bind (Pₘ := fun b2 : Std.Array V 8#usize =>
    ∀ j < 8, b2.val[j]! = (rk.val.take (N.val - 2)).foldl aesdImc' (loadBytes (chunk.val[j]!).val))
  · unfold low.aarch64.aes_cbc.decrypt_8_loop1
    apply range_loop _ i1 (fun r (b' : Std.Array V 8#usize) =>
      ∀ j < 8, b'.val[j]! = (rk.val.take r).foldl aesdImc' (loadBytes (chunk.val[j]!).val))
    · intro it b' he hlt hP
      unfold low.aarch64.aes_cbc.decrypt_8_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      step*
      step with decrypt_round_8_spec as ⟨b3, hb3⟩
      refine ⟨it', b3, rfl, hst, by rw [hen, he], ?_⟩
      intro j hj
      rw [hb3 j hj, hP j hj, uxt_post, List.take_add_one, List.foldl_append,
        List.getElem?_eq_getElem (show it.start.val < rk.val.length by rw [← he] at hlt; omega)]
      rfl
    · intro it b' he hst hP
      unfold low.aarch64.aes_cbc.decrypt_8_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨b', rfl, ?_⟩
      intro j hj
      rw [hP j hj, hst, hi1v]
    · rfl
    · simp
    · intro j hj; simp [hb1 j hj]
  intro b2 hb2
  -- The last round's `AESD` and the chaining XOR, backwards.
  apply WP.spec_bind (Pₘ := fun c' : Std.Array (Std.Array U8 16#usize) 8#usize =>
    ∀ j < 8, c'.val[j]! = storeBytes (decRounds rk (loadBytes (chunk.val[j]!).val) ^^^
      (rk.val[N.val - 1]! ^^^ if j = 0 then prev else loadBytes (chunk.val[j - 1]!).val)))
  swap
  · intro c' hc'
    simp only [WP.spec_ok]
    exact ⟨rfl, hc'⟩
  unfold low.aarch64.aes_cbc.decrypt_8_loop2
  apply range_loop _ 8#usize (fun r (c' : Std.Array (Std.Array U8 16#usize) 8#usize) =>
    ∀ j < 8, c'.val[j]! = if 8 - r ≤ j then storeBytes (decRounds rk (loadBytes (chunk.val[j]!).val) ^^^
        (rk.val[N.val - 1]! ^^^ if j = 0 then prev else loadBytes (chunk.val[j - 1]!).val))
      else chunk.val[j]!)
  · intro it c' he hlt hP
    have hlt : it.start.val < 8 := by simpa using hlt
    unfold low.aarch64.aes_cbc.decrypt_8_loop2.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
    subst ho
    step as ⟨j, hj⟩
    have hj : j.val = 7 - it.start.val := by simpa using hj
    apply WP.spec_bind (Pₘ := fun chain : V => chain = if j.val = 0 then prev else loadBytes (chunk.val[j.val - 1]!).val)
    · by_cases hz : j = 0#usize
      · have : j.val = 0 := by simp [hz]
        rw [ite_t hz, WP.spec_ok, ite_t this]
      · have : j.val ≠ 0 := fun h => hz (by scalar_tac)
        rw [ite_f hz, ite_f this]
        step as ⟨j1, hj1⟩
        step as ⟨a, ha⟩
        rw [← getElem!_pos, hP _ (by omega), ite_f (by omega), hj1] at ha
        subst ha
        rw [load_eq, WP.spec_ok]
    intro chain hchain
    step as ⟨u, hu⟩
    step as ⟨u1, hu1⟩
    rw [← getElem!_pos, hb2 _ (by omega)] at hu
    rw [← getElem!_pos, hi1v] at hu1
    subst hu hu1
    simp only [core.core_arch.arm_shared.neon.generated.vaesdq_u8,
      core.core_arch.arm_shared.neon.generated.veorq_u8, store_eq, bind_ok]
    step as ⟨c2, hc2⟩
    refine ⟨it', c2, rfl, hst, by rw [hen, he], ?_⟩
    intro k hk
    rw [hc2, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
    by_cases h1 : j.val = k
    · subst h1
      rw [ite_t rfl, ite_t (show 8 - (it.start.val + 1) ≤ j.val by omega), hchain, decRounds]
    · rw [ite_f h1, hP _ hk]
      by_cases h2 : 8 - it.start.val ≤ k
      · rw [ite_t h2, ite_t (show 8 - (it.start.val + 1) ≤ k by omega)]
      · rw [ite_f h2, ite_f (show ¬ 8 - (it.start.val + 1) ≤ k by omega)]
  · intro it c' he hst hP
    unfold low.aarch64.aes_cbc.decrypt_8_loop2.body
    step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
    subst ho
    simp only [WP.spec_ok]
    refine ⟨c', rfl, ?_⟩
    intro j hj
    rw [hP _ hj, ite_t (show 8 - it.start.val ≤ j by simp at hst; omega)]
  · rfl
  · simp
  · intro j hj
    have : ¬ 8 ≤ j := by omega
    simp [this]

theorem leQuad32ToBytes_leBytesToQuad32 (l : List (BitVec 8)) (hl : l.length = 16) :
    leQuad32ToBytes (leBytesToQuad32 l) = l := by
  apply List.ext_getElem (by rw [length_leQuad32ToBytes, hl])
  intro i h1 h2
  rw [length_leQuad32ToBytes] at h1
  rw [← getElem!_pos, ← getElem!_pos, leQuad32ToBytes_getElem! _ h1, byte_leBytesToQuad32 _ h1]

theorem zipWith_leQuad32ToBytes (q : BitVec 128) (c : List (BitVec 8)) (hc : c.length = 16) :
    List.zipWith (· ^^^ ·) (leQuad32ToBytes q) c = leQuad32ToBytes (q ^^^ leBytesToQuad32 c) := by
  rw [← leQuad32ToBytes_leBytesToQuad32 (List.zipWith _ _ _) (by simp [length_leQuad32ToBytes, hc]),
    leBytesToQuad32_zipWith _ _ (length_leQuad32ToBytes q) hc, leBytesToQuad32_leQuad32ToBytes']

theorem loadBytes_eq (a : Std.Array U8 16#usize) : loadBytes a.val = leBytesToQuad32 (blockBytes a) := rfl

/-- One block of CBC decryption: `decRounds`, then the XOR with the last
round key and the chaining block `cB`. -/
theorem dec_block {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1) (key : List (BitVec 8))
    (rk : Std.Array V N)
    (hrk : rk.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg (seqNat8ToSeqNat32LE key)))
    (a : Std.Array U8 16#usize) (cB rest : List (BitVec 8)) (hcB : cB.length = 16) :
    blockBytes (storeBytes (decRounds rk (loadBytes a.val) ^^^ (rk.val[N.val - 1]! ^^^ leBytesToQuad32 cB))) ++
      cbcDecrypt alg key (blockBytes a) rest = cbcDecrypt alg key cB (blockBytes a ++ rest) := by
  rw [cbcDecrypt_cons _ _ _ _ _ (bvs_length a), aesBlockDecrypt, zipWith_leQuad32ToBytes _ _ hcB,
    bvs_storeBytes, ← BitVec.xor_assoc, decRounds_eq alg hN _ rk hrk, loadBytes_eq]

/-- A run of blocks of CBC decryption, each chained from the one before it,
the first from `cB`. -/
theorem dec_chain {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1) (key : List (BitVec 8))
    (rk : Std.Array V N)
    (hrk : rk.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg (seqNat8ToSeqNat32LE key)))
    (R : List (BitVec 8)) :
    ∀ (xs ds : List (Std.Array U8 16#usize)) (cB : List (BitVec 8)), cB.length = 16 →
      ds.length = xs.length →
      (∀ j < xs.length, ds[j]! = storeBytes (decRounds rk (loadBytes (xs[j]!).val) ^^^
        (rk.val[N.val - 1]! ^^^ if j = 0 then leBytesToQuad32 cB else loadBytes (xs[j - 1]!).val))) →
      ds.flatMap blockBytes ++ cbcDecrypt alg key ((cB :: xs.map blockBytes).getLast (by simp)) R =
        cbcDecrypt alg key cB (xs.flatMap blockBytes ++ R)
  | [], ds, cB, _, hl, _ => by
    rw [List.length_nil, List.length_eq_zero_iff] at hl
    subst hl
    simp
  | a :: xs, [], cB, _, hl, _ => by simp at hl
  | a :: xs, d :: ds, cB, hcB, hl, hd => by
    have h0 : d = storeBytes (decRounds rk (loadBytes a.val) ^^^ (rk.val[N.val - 1]! ^^^ leBytesToQuad32 cB)) := by
      simpa using hd 0 (by simp)
    have ih := dec_chain alg hN key rk hrk R xs ds (blockBytes a) (bvs_length a) (by simpa using hl) (by
      intro j hj
      have := hd (j + 1) (by simp; omega)
      cases j with
      | zero => simpa [loadBytes_eq] using this
      | succ j => simpa using this)
    rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.append_assoc,
      ← dec_block alg hN key rk hrk a cB _ hcB, ← ih, h0]
    simp only [List.map_cons, List.getLast_cons_cons]

/-- Eight blocks of CBC decryption xs `decrypt_8_spec` gives them. -/
theorem dec_chunk {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1) (key : List (BitVec 8))
    (rk : Std.Array V N)
    (hrk : rk.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg (seqNat8ToSeqNat32LE key)))
    (ch ch' : Std.Array (Std.Array U8 16#usize) 8#usize) (cB : List (BitVec 8)) (hcB : cB.length = 16)
    (R : List (BitVec 8))
    (h : ∀ j < 8, ch'.val[j]! = storeBytes (decRounds rk (loadBytes (ch.val[j]!).val) ^^^
        (rk.val[N.val - 1]! ^^^ if j = 0 then leBytesToQuad32 cB else loadBytes (ch.val[j - 1]!).val))) :
    ch'.val.flatMap blockBytes ++ cbcDecrypt alg key (blockBytes ch.val[7]!) R =
      cbcDecrypt alg key cB (ch.val.flatMap blockBytes ++ R) := by
  rw [← dec_chain alg hN key rk hrk R ch.val ch'.val cB hcB (by simp) (by simpa using h)]
  have : (cB :: ch.val.map blockBytes).getLast (by simp) = blockBytes ch.val[7]! := by
    rw [List.getLast_eq_getElem, getElem!_pos ch.val 7 (by simp)]
    simp
  rw [this]

/-- The chunks `as_chunks_mut` splits off are the slice's start. -/
theorem flatMap_chunks {T : Type} [Inhabited T] {M : Usize} :
    ∀ (cs : List (Std.Array T M)) (s : List T),
      (∀ i < cs.length, (cs[i]!).val = (s.drop (i * M.val)).take M.val) →
      cs.flatMap (·.val) = s.take (cs.length * M.val)
  | [], s, _ => by simp
  | c :: cs, s, h => by
    have h0 : c.val = s.take M.val := by simpa using h 0 (by simp)
    have ih := flatMap_chunks cs (s.drop M.val) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [List.drop_drop, Nat.add_mul, Nat.add_comm] using this)
    rw [List.flatMap_cons, h0, ih, List.length_cons,
      show (cs.length + 1) * M.val = M.val + cs.length * M.val by rw [Nat.succ_mul, Nat.add_comm],
      List.take_add]

theorem length_flatMap_val {T : Type} {M : Usize} (cs : List (Std.Array T M)) :
    (cs.flatMap (·.val)).length = cs.length * M.val := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.flatMap_cons, List.length_append, ih, c.property, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem hw_decrypt_spec {N : Usize} (alg : Algorithm) (hN : N.val = nr alg + 1) (key : List (BitVec 8))
    (rk : Std.Array V N)
    (hrk : rk.val.reverse = eqInvRoundKeys alg (keyToRoundKeys alg (seqNat8ToSeqNat32LE key)))
    (iv : Std.Array U8 16#usize) (blocks : Slice (Std.Array U8 16#usize)) :
    low.aarch64.aes_cbc.hw_decrypt rk iv blocks ⦃ r =>
      r.val.flatMap blockBytes = cbcDecrypt alg key (blockBytes iv) (blocks.val.flatMap blockBytes) ⦄ := by
  have hnr : 2 ≤ nr alg := by cases alg <;> decide
  obtain ⟨i, hi, hiv⟩ := usize_sub_ok N 1#usize (by simp; omega)
  have hiv : i.val = N.val - 1 := by simpa using hiv
  unfold low.aarch64.aes_cbc.hw_decrypt
  simp only [hi, bind_ok, load_eq]
  step as ⟨last, hlast⟩
  rw [← getElem!_pos, hiv] at hlast
  subst hlast
  step with as_chunks_mut_spec 8#usize blocks (by simp) as ⟨chunks, tail, back, hcl, hci, htl, hback⟩
  have hcl' : chunks.val.length = blocks.val.length / 8 := by simpa using hcl
  have htl' : tail.val = blocks.val.drop (blocks.val.length / 8 * 8) := by simpa using htl
  have hjoin : blocks.val.flatMap blockBytes =
      chunks.val.flatMap (fun ch => ch.val.flatMap blockBytes) ++ tail.val.flatMap blockBytes := by
    have h1 := flatMap_chunks (M := 8#usize) chunks.val blocks.val (fun i hi => by simpa using hci i hi)
    have h1' : chunks.val.flatMap (·.val) = blocks.val.take (blocks.val.length / 8 * 8) := by
      simpa [hcl'] using h1
    rw [← List.flatMap_assoc, h1', htl', ← List.flatMap_append, List.take_append_drop]
  -- The eight-block chunks.
  apply WP.spec_bind (Pₘ := fun st : V × Slice (Std.Array (Std.Array U8 16#usize) 8#usize) =>
    st.2.val.length = chunks.val.length ∧ ∃ cB : List (BitVec 8), cB.length = 16 ∧ st.1 = leBytesToQuad32 cB ∧
      cbcDecrypt alg key (blockBytes iv) (blocks.val.flatMap blockBytes) =
        st.2.val.flatMap (fun ch => ch.val.flatMap blockBytes) ++
          cbcDecrypt alg key cB (tail.val.flatMap blockBytes))
  · unfold low.aarch64.aes_cbc.hw_decrypt_loop0
    apply range_loop _ (Slice.len chunks)
      (fun c (st : V × Slice (Std.Array (Std.Array U8 16#usize) 8#usize)) =>
        st.2.val.length = chunks.val.length ∧ st.2.val.drop c = chunks.val.drop c ∧
        ∃ cB : List (BitVec 8), cB.length = 16 ∧ st.1 = leBytesToQuad32 cB ∧
          cbcDecrypt alg key (blockBytes iv) (blocks.val.flatMap blockBytes) =
            (st.2.val.take c).flatMap (fun ch => ch.val.flatMap blockBytes) ++
              cbcDecrypt alg key cB ((chunks.val.drop c).flatMap (fun ch => ch.val.flatMap blockBytes) ++
                tail.val.flatMap blockBytes))
    · rintro it ⟨pv, cs⟩ he hlt ⟨hlen, hdrop, cB, hcB, hpv, hW⟩
      simp only at hlen hdrop hpv hW
      subst hpv
      have hlt : it.start.val < chunks.val.length := by simpa [he] using hlt
      unfold low.aarch64.aes_cbc.hw_decrypt_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      step as ⟨a, bk, ha, hbk⟩
      rw [← getElem!_pos, getElem!_of_drop_eq hdrop] at ha
      subst ha hbk
      step with decrypt_8_spec (N := N) (by omega) as ⟨next, ch', hnext, hch'⟩
      refine ⟨it', (next, cs.set it.start ch'), rfl, hst, by rw [hen, he], ?_⟩
      have hp : chunks.val.drop it.start.val =
          chunks.val[it.start.val]! :: chunks.val.drop (it.start.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt, getElem!_pos]
      simp only [Slice.set_val_eq]
      refine ⟨by simp [hlen], by rw [drop_set_succ, ← List.drop_drop, hdrop, List.drop_drop], _, bvs_length _,
        by rw [hnext, loadBytes_eq], ?_⟩
      rw [hW, take_set_succ _ _ _ (by omega), hp]
      simp only [List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.append_nil, List.append_assoc]
      rw [← dec_chunk alg hN key rk hrk _ ch' cB hcB _ hch']
    · rintro it ⟨pv, cs⟩ he hst ⟨hlen, hdrop, cB, hcB, hpv, hW⟩
      simp only at hlen hdrop hpv hW
      have hst : it.start.val = chunks.val.length := by simpa [he] using hst
      unfold low.aarch64.aes_cbc.hw_decrypt_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨(pv, cs), rfl, hlen, cB, hcB, hpv, ?_⟩
      rw [hW, hst, List.drop_length, List.flatMap_nil, List.nil_append, List.take_of_length_le (by omega)]
    · rfl
    · simp
    · refine ⟨rfl, rfl, blockBytes iv, by simp, loadBytes_eq iv, ?_⟩
      simp [hjoin]
  rintro ⟨prev1, chunks1⟩ ⟨hlen1, cB1, hcB1, hprev1, hW1⟩
  simp only at hlen1 hprev1 hW1 ⊢
  -- The blocks left over.
  apply WP.spec_bind (Pₘ := fun tl : Slice (Std.Array U8 16#usize) =>
    tl.val.length = tail.val.length ∧
      cbcDecrypt alg key cB1 (tail.val.flatMap blockBytes) = tl.val.flatMap blockBytes)
  · unfold low.aarch64.aes_cbc.hw_decrypt_loop1
    apply range_loop _ (Slice.len tail)
      (fun t (st : V × Slice (Std.Array U8 16#usize)) =>
        st.2.val.length = tail.val.length ∧ st.2.val.drop t = tail.val.drop t ∧
        ∃ cB : List (BitVec 8), cB.length = 16 ∧ st.1 = leBytesToQuad32 cB ∧
          cbcDecrypt alg key cB1 (tail.val.flatMap blockBytes) =
            (st.2.val.take t).flatMap blockBytes ++ cbcDecrypt alg key cB ((tail.val.drop t).flatMap blockBytes))
    · rintro it ⟨pv, tl⟩ he hlt ⟨hlen, hdrop, cB, hcB, hpv, hW⟩
      simp only at hlen hdrop hpv hW
      subst hpv
      have hlt : it.start.val < tail.val.length := by simpa [he] using hlt
      unfold low.aarch64.aes_cbc.hw_decrypt_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      step as ⟨a, ha⟩
      rw [← getElem!_pos, getElem!_of_drop_eq hdrop] at ha
      subst ha
      simp only [load_eq, bind_ok]
      step with decrypt_rounds_spec (N := N) (by omega) as ⟨b, hb⟩
      subst hb
      simp only [core.core_arch.arm_shared.neon.generated.veorq_u8, store_eq, bind_ok]
      step as ⟨s', hs'⟩
      refine ⟨it', (_, s'), rfl, hst, by rw [hen, he], ?_⟩
      have hp : tail.val.drop it.start.val = tail.val[it.start.val]! :: tail.val.drop (it.start.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt, getElem!_pos]
      rw [hs', Slice.set_val_eq]
      refine ⟨by simp [hlen], by rw [drop_set_succ, ← List.drop_drop, hdrop, List.drop_drop], _, bvs_length _,
        loadBytes_eq _, ?_⟩
      rw [hW, take_set_succ _ _ _ (by omega), hp]
      simp only [List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.append_nil, List.append_assoc]
      rw [← dec_block alg hN key rk hrk _ cB _ hcB]
    · rintro it ⟨pv, tl⟩ he hst ⟨hlen, hdrop, cB, hcB, hpv, hW⟩
      simp only at hlen hdrop hpv hW
      have hst : it.start.val = tail.val.length := by simpa [he] using hst
      unfold low.aarch64.aes_cbc.hw_decrypt_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨tl, rfl, hlen, ?_⟩
      rw [hW, hst, List.drop_length, List.flatMap_nil, cbcDecrypt_nil, List.append_nil,
        List.take_of_length_le (by omega)]
    · rfl
    · simp
    · refine ⟨rfl, rfl, cB1, hcB1, hprev1, by simp⟩
  rintro tail1 ⟨hlen2, hW2⟩
  have hbound : (chunks1.val.flatMap (·.val) ++ tail1.val).length ≤ Usize.max := by
    have h1 := Slice.length_ineq blocks
    have h2 := Nat.div_mul_le_self blocks.val.length 8
    rw [List.length_append, length_flatMap_val, hlen1, hlen2, hcl', htl', List.length_drop,
      show (8#usize).val = 8 by simp]
    omega
  rw [WP.spec_ok, hback _ _ hbound, List.flatMap_append, List.flatMap_assoc, hW1, hW2]

/-- `low::aarch64::aes_cbc::decrypt` is SP 800-38A's CBC decryption of the
blocks, chained from `iv`. -/
theorem aes_cbc_decrypt_spec (alg : Algorithm) (key : List (BitVec 8)) (k : low.aarch64.aes.AesDecKey)
    (hk : ModeDecKeyIs alg key k) (iv : Std.Array U8 16#usize) (blocks : Slice (Std.Array U8 16#usize)) :
    low.aarch64.aes_cbc.decrypt k iv blocks ⦃ r =>
      r.val.flatMap (fun b => bvs b.val) =
        cbcDecrypt alg key (bvs iv.val) (blocks.val.flatMap fun b => bvs b.val) ⦄ := by
  obtain ⟨-, hwk, rfl, hwk_is⟩ := hk
  cases hwk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := hwk_is
    simp only [low.aarch64.aes_cbc.decrypt]
    exact hw_decrypt_spec .AES_128 (by simp [nr]) key _ hrk iv blocks
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := hwk_is
    simp only [low.aarch64.aes_cbc.decrypt]
    exact hw_decrypt_spec .AES_192 (by simp [nr]) key _ hrk iv blocks
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := hwk_is
    simp only [low.aarch64.aes_cbc.decrypt]
    exact hw_decrypt_spec .AES_256 (by simp [nr]) key _ hrk iv blocks

/-! ## CTR -/

/-- `data` XORed with the keystream whose block `j` is `ks j`, from block `m`. -/
def ctrXor (ks : Nat → List (BitVec 8)) (m : Nat) (data : List (BitVec 8)) : List (BitVec 8) :=
  (List.range data.length).map fun i => data[i]! ^^^ (ks (m + i / 16))[i % 16]!

theorem length_ctrXor (ks : Nat → List (BitVec 8)) (m : Nat) (data : List (BitVec 8)) :
    (ctrXor ks m data).length = data.length := by
  simp [ctrXor]

theorem getElem!_ctrXor (ks : Nat → List (BitVec 8)) (m : Nat) (data : List (BitVec 8)) (i : Nat)
    (hi : i < data.length) :
    (ctrXor ks m data)[i]! = data[i]! ^^^ (ks (m + i / 16))[i % 16]! := by
  rw [ctrXor, getElem!_pos _ _ (by simpa using hi)]
  simp

theorem aesCtr_eq (alg : Algorithm) (key : List (BitVec 8)) (m : Nat) (t0 data : List (BitVec 8)) :
    aesCtr alg key m t0 data = ctrXor (fun j => aesBlock alg key (be128 (ctrBlock m (ofBe t0) j))) 0 data := by
  simp [aesCtr, ctrXor]

theorem bvs_getElem! (l : List U8) (i : Nat) (hi : i < l.length) : (bvs l)[i]! = (l[i]!).bv := by
  rw [getElem!_pos (bvs l) i (by simpa using hi), getElem!_pos l i hi, List.getElem_map]

theorem getElem!_append_left' {α : Type _} [Inhabited α] (a b : List α) (i : Nat) (h : i < a.length) :
    (a ++ b)[i]! = a[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

theorem getElem!_append_right' {α : Type _} [Inhabited α] (a b : List α) (i : Nat) (h : a.length ≤ i) :
    (a ++ b)[i]! = b[i - a.length]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right h]

/-- Byte `i` of chunks of `N` is byte `i % N` of chunk `i / N`. -/
theorem getElem!_flatMap_val {T : Type} [Inhabited T] {N : Usize} (hN : 0 < N.val) :
    ∀ (cs : List (Std.Array T N)) (i : Nat), i < cs.length * N.val →
      (cs.flatMap (·.val))[i]! = (cs[i / N.val]!).val[i % N.val]!
  | [], i, h => by simp at h
  | c :: cs, i, h => by
    rw [List.flatMap_cons]
    by_cases hi : i < N.val
    · rw [getElem!_append_left' _ _ _ (by rw [c.property]; exact hi), Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      simp
    · rw [getElem!_append_right' _ _ _ (by rw [c.property]; omega), c.property,
        Nat.div_eq_sub_div hN (by omega), Nat.mod_eq_sub_mod (by omega)]
      rw [getElem!_flatMap_val hN cs (i - N.val) (by simp [Nat.succ_mul] at h; omega)]
      simp

/-! ### Counter blocks -/

theorem ofBe_foldl (l : List (BitVec 8)) (a : Nat) :
    l.foldl (fun a b => 256 * a + b.toNat) a = a * 256 ^ l.length + ofBe l := by
  induction l generalizing a with
  | nil => simp [ofBe]
  | cons b l ih =>
    simp only [List.foldl_cons, ofBe, List.length_cons]
    rw [ih, ih (256 * 0 + b.toNat)]
    ring

theorem ofBe_append (a b : List (BitVec 8)) : ofBe (a ++ b) = ofBe a * 256 ^ b.length + ofBe b := by
  rw [ofBe, List.foldl_append, ofBe_foldl]
  rfl

theorem ofBe_single (b : BitVec 8) : ofBe [b] = b.toNat := by
  simp [ofBe]

theorem ofBe_lt (l : List (BitVec 8)) : ofBe l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [ofBe]
  | append_singleton l b ih =>
    rw [ofBe_append, ofBe_single, List.length_append, List.length_singleton, pow_add, pow_one]
    have hb : b.toNat < 256 := b.isLt
    have := Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt ih)
    rw [Nat.succ_mul] at this
    omega

/-- Byte `i` of a big-endian integer, with `n` bytes after it. -/
theorem ofBe_digit (l : List (BitVec 8)) (i : Nat) (hi : i < l.length) (n : Nat) (hn : l.length = i + 1 + n) :
    ofBe l / 256 ^ n % 256 = (l[i]).toNat := by
  have hl : l.take i ++ ([l[i]] ++ l.drop (i + 1)) = l := by
    rw [List.singleton_append, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hB : (l.drop (i + 1)).length = n := by simp; omega
  have hx : (l[i]).toNat < 256 := (l[i]).isLt
  have hlt := ofBe_lt (l.drop (i + 1))
  rw [hB] at hlt
  have he : ofBe l = ofBe (l.drop (i + 1)) + (ofBe (l.take i) * 256 + (l[i]).toNat) * 256 ^ n := by
    conv_lhs => rw [← hl]
    rw [ofBe_append, ofBe_append, ofBe_single]
    simp only [List.length_append, List.length_singleton, hB]
    ring
  rw [he, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add]
  omega

theorem be128_ofBe (l : List (BitVec 8)) (hl : l.length = 16) : be128 (ofBe l) = l := by
  apply List.ext_getElem (by simp [be128, hl])
  intro i h1 h2
  simp only [be128, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← ofBe_digit l i h2 (15 - i) (by omega)]

theorem length_be32 (c : Nat) : (be32 c).length = 4 := by
  simp [be32, be128]

theorem ofBe_be32 (c : Nat) (hc : c < 2 ^ 32) : ofBe (be32 c) = c := by
  have : be32 c = [BitVec.ofNat 8 (c / 256 ^ 3), BitVec.ofNat 8 (c / 256 ^ 2), BitVec.ofNat 8 (c / 256 ^ 1),
      BitVec.ofNat 8 (c / 256 ^ 0)] := by
    simp [be32, be128, List.range_succ]
  rw [this]
  simp [ofBe]
  omega

/-- CTR's counter block `j`, counting in the last four bytes, has the nonce
and the counter plus `j`, modulo `2^32`. -/
theorem ctr_block_eq (n : List (BitVec 8)) (hn : n.length = 12) (c j : Nat) (hc : c < 2 ^ 32) :
    be128 (ctrBlock 32 (ofBe (n ++ be32 c)) j) = n ++ be32 ((c + j) % 2 ^ 32) := by
  rw [← be128_ofBe (n ++ be32 ((c + j) % 2 ^ 32)) (by simp [hn, length_be32])]
  congr 1
  rw [ctrBlock, ofBe_append, ofBe_append, ofBe_be32 _ hc, ofBe_be32 _ (Nat.mod_lt _ (by positivity))]
  simp only [length_be32]
  generalize ofBe n = A
  norm_num
  omega

/-! ### The counter blocks on the vector unit -/

theorem swap_wbyte (x : BitVec 32) (b : Nat) (hb : b < 4) :
    wbyte (x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8) b =
      x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  obtain rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
  all_goals
    simp only [wbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp [hk]
    try (split_ifs <;> first | omega | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega))

theorem extract_eq_ofNat (x : BitVec 32) (k : Nat) :
    x.extractLsb' (8 * k) 8 = BitVec.ofNat 8 (x.toNat / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem be32_getElem! (v b : Nat) (hb : b < 4) : (be32 v)[b]! = BitVec.ofNat 8 (v / 256 ^ (3 - b)) := by
  obtain rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
  all_goals simp [be32, be128, List.range_succ]

/-- The counter block `_apply_8` builds: the nonce, then the counter's bytes
big-endian, which `swap_bytes` makes of its little-endian lane. -/
theorem ctr_vec (nonce : Std.Array U8 12#usize) (base : List U8) (hb : base.length = 16)
    (hbase : ∀ i < 12, base[i]! = nonce.val[i]!) (x : BitVec 32) :
    (ofLanes32 fun i => if i = 3 then
        x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8
      else lane32 (loadBytes base) i) = leBytesToQuad32 (bvs nonce.val ++ be32 x.toNat) := by
  apply eq_of_byte_eq
  intro i hi
  rw [byte_ofLanes32 _ hi, byte_leBytesToQuad32 _ hi]
  have hn : (bvs nonce.val).length = 12 := by simp
  by_cases h : i < 12
  · rw [ite_f (show i / 4 ≠ 3 by omega), wbyte_lane32 _ _ (by omega), show 4 * (i / 4) + i % 4 = i by omega,
      loadBytes, byte_leBytesToQuad32 _ hi, getElem!_append_left' _ _ _ (by omega),
      bvs_getElem! base i (by omega), bvs_getElem! nonce.val i (by simp; omega), hbase i h]
  · rw [ite_t (show i / 4 = 3 by omega), getElem!_append_right' _ _ _ (by omega), hn,
      swap_wbyte _ _ (by omega), extract_eq_ofNat, be32_getElem! _ _ (by omega),
      show 3 - i % 4 = 3 - (i - 12) by omega]

theorem getElem!_take_drop {α : Type _} [Inhabited α] (l : List α) (a n k : Nat) (hk : k < n) :
    ((l.drop a).take n)[k]! = l[a + k]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop, hk]

theorem storeBytes_getElem! (q : BitVec 128) (k : Nat) (hk : k < 16) : ((storeBytes q).val[k]!).bv = byte q k := by
  rw [← bvs_getElem! (storeBytes q).val k (by have := (storeBytes q).property; simp at this ⊢; omega),
    show bvs (storeBytes q).val = leQuad32ToBytes q from bvs_storeBytes q, leQuad32ToBytes_getElem! _ hk]

/-- One counter block of `_apply_8`'s closure: the nonce, then the counter
plus `j` big-endian. -/
theorem ctr_call_eq (nonce : Std.Array U8 12#usize) (base : Std.Array U8 16#usize)
    (hbase : ∀ i < 12, base.val[i]! = nonce.val[i]!) (counter j : U32) :
    low.aarch64.aes_ctr._apply_8.closure.Insts.CoreOpsFunctionFnTupleU32uint8x16_t.call
        (counter, loadBytes base.val) j =
      ok (leBytesToQuad32 (bvs nonce.val ++ be32 ((counter.val + j.val) % 2 ^ 32))) := by
  unfold low.aarch64.aes_ctr._apply_8.closure.Insts.CoreOpsFunctionFnTupleU32uint8x16_t.call
  simp only [lift, bind_ok, core.num.U32.swap_bytes, core.core_arch.arm_shared.neon.generated.vsetq_lane_u32,
    core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_u32]
  show ok (ofLanes32 fun i => if i = (3#i32).bv.toNat % 4 then
      (core.num.U32.wrapping_add counter j).bv.extractLsb' 0 8 ++ (core.num.U32.wrapping_add counter j).bv.extractLsb' 8 8 ++
        (core.num.U32.wrapping_add counter j).bv.extractLsb' 16 8 ++
        (core.num.U32.wrapping_add counter j).bv.extractLsb' 24 8
      else lane32 (loadBytes base.val) i) = _
  congr 1
  rw [show (3#i32).bv.toNat % 4 = 3 by decide, ctr_vec nonce base.val (by simp) hbase]
  congr 3

theorem apply_8_spec (alg : Algorithm) (key : List (BitVec 8)) (hk : low.aarch64.aes.HwKey)
    (h : HwKeyIs alg (seqNat8ToSeqNat32LE key) hk) (nonce : Std.Array U8 12#usize) (counter : U32)
    (inout : Std.Array U8 128#usize) :
    low.aarch64.aes_ctr._apply_8 hk nonce counter inout ⦃ out =>
      bvs out.val = ctrXor (fun j => aesBlock alg key (bvs nonce.val ++ be32 ((counter.val + j) % 2 ^ 32))) 0
        (bvs inout.val) ⦄ := by
  unfold low.aarch64.aes_ctr._apply_8
  step with Array.index_mut_SliceIndexRangeToUsizeSlice as ⟨s, bk, hs, hsl, hbk⟩
  simp only [lift, bind_ok]
  step with core.slice.Slice.copy_from_slice.step_spec as ⟨s2, hs2⟩
  have hbase : ∀ i < 12, (bk s2).val[i]! = nonce.val[i]! := by
    intro i hi
    rw [hbk, List.getElem!_setSlice!_middle _ _ _ _ (by simp [hs2, Array.to_slice]; omega), hs2]
    simp [Array.to_slice]
  simp only [load_eq, bind_ok, core.core_arch.arm_shared.neon.generated.vreinterpretq_u32_u8,
    ctr_call_eq nonce _ hbase]
  apply WP.spec_bind (encrypt_8_spec hk alg _ h _ _ _ _ _ _ _ _)
  rintro _ rfl
  simp only [Array.to_slice_mut]
  step with as_chunks_mut_spec 16#usize (Array.to_slice inout) (by simp) as ⟨blocks, s4, back4, hcl, hci, htl, hback4⟩
  have hin : (Array.to_slice inout).val = inout.val := by simp [Array.to_slice]
  have hlen : blocks.val.length = 8 := by simpa [hin] using hcl
  have hs4 : s4.val = [] := by simpa [hin] using htl
  have hci' : ∀ q < 8, (blocks.val[q]!).val = (inout.val.drop (q * 16)).take 16 := by
    intro q hq
    simpa [hin] using hci q (by omega)
  have hl0 : blocks.val.length = 8 := hlen
  simp only [core.core_arch.arm_shared.neon.generated.veorq_u8, store_eq, bind_ok]
  step with Slice.index_usize_spec blocks 0#usize (by simp [hl0]) as ⟨a0, ha0⟩
  rw [← getElem!_pos] at ha0
  step with Slice.update_spec blocks 0#usize _ (by simp [hl0]) as ⟨B1, hB1⟩
  have hl1 : B1.val.length = 8 := by rw [hB1, Slice.set_val_eq, List.length_set, hl0]
  step with Slice.index_usize_spec B1 1#usize (by simp [hl1]) as ⟨a1, ha1⟩
  rw [← getElem!_pos] at ha1
  step with Slice.update_spec B1 1#usize _ (by simp [hl1]) as ⟨B2, hB2⟩
  have hl2 : B2.val.length = 8 := by rw [hB2, Slice.set_val_eq, List.length_set, hl1]
  step with Slice.index_usize_spec B2 2#usize (by simp [hl2]) as ⟨a2, ha2⟩
  rw [← getElem!_pos] at ha2
  step with Slice.update_spec B2 2#usize _ (by simp [hl2]) as ⟨B3, hB3⟩
  have hl3 : B3.val.length = 8 := by rw [hB3, Slice.set_val_eq, List.length_set, hl2]
  step with Slice.index_usize_spec B3 3#usize (by simp [hl3]) as ⟨a3, ha3⟩
  rw [← getElem!_pos] at ha3
  step with Slice.update_spec B3 3#usize _ (by simp [hl3]) as ⟨B4, hB4⟩
  have hl4 : B4.val.length = 8 := by rw [hB4, Slice.set_val_eq, List.length_set, hl3]
  step with Slice.index_usize_spec B4 4#usize (by simp [hl4]) as ⟨a4, ha4⟩
  rw [← getElem!_pos] at ha4
  step with Slice.update_spec B4 4#usize _ (by simp [hl4]) as ⟨B5, hB5⟩
  have hl5 : B5.val.length = 8 := by rw [hB5, Slice.set_val_eq, List.length_set, hl4]
  step with Slice.index_usize_spec B5 5#usize (by simp [hl5]) as ⟨a5, ha5⟩
  rw [← getElem!_pos] at ha5
  step with Slice.update_spec B5 5#usize _ (by simp [hl5]) as ⟨B6, hB6⟩
  have hl6 : B6.val.length = 8 := by rw [hB6, Slice.set_val_eq, List.length_set, hl5]
  step with Slice.index_usize_spec B6 6#usize (by simp [hl6]) as ⟨a6, ha6⟩
  rw [← getElem!_pos] at ha6
  step with Slice.update_spec B6 6#usize _ (by simp [hl6]) as ⟨B7, hB7⟩
  have hl7 : B7.val.length = 8 := by rw [hB7, Slice.set_val_eq, List.length_set, hl6]
  step with Slice.index_usize_spec B7 7#usize (by simp [hl7]) as ⟨a7, ha7⟩
  rw [← getElem!_pos] at ha7
  step with Slice.update_spec B7 7#usize _ (by simp [hl7]) as ⟨B8, hB8⟩
  have hl8 : B8.val.length = 8 := by rw [hB8, Slice.set_val_eq, List.length_set, hl7]
  have hB : ∀ q < 8, B8.val[q]! = storeBytes (aesEncrypt alg (seqNat8ToSeqNat32LE key)
      (leBytesToQuad32 (bvs nonce.val ++ be32 ((counter.val + q) % 2 ^ 32))) ^^^ loadBytes (blocks.val[q]!).val) := by
    intro q hq
    interval_cases q <;>
      simp [hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1, ha7, ha6, ha5, ha4, ha3, ha2, ha1, ha0, Slice.set_val_eq, hlen]
  have h16 : (16#usize).val = 16 := by simp
  have hflat : (back4 (B8, s4)).val = B8.val.flatMap (·.val) := by
    rw [hback4 _ _ (by rw [List.length_append, length_flatMap_val, hl8, hs4]; simp; scalar_tac), hs4,
      List.append_nil]
  rw [Array.from_slice_val _ _ (by rw [hflat, length_flatMap_val, hl8]; rfl), hflat]
  apply ext_getElem! (by simp [length_ctrXor, hl8])
  intro i hi
  have hi : i < 128 := by simpa [length_flatMap_val, hl8] using hi
  rw [bvs_getElem! _ _ (by rw [length_flatMap_val, hl8]; simpa using hi),
    getElem!_flatMap_val (by simp) _ _ (by rw [hl8]; simpa using hi), h16,
    getElem!_ctrXor _ _ _ _ (by simp; omega), bvs_getElem! _ _ (by simp; omega),
    hB _ (by omega), storeBytes_getElem! _ _ (by omega), byte_xor, BitVec.xor_comm, Nat.zero_add,
    aesBlock, leQuad32ToBytes_getElem! _ (by omega), loadBytes, byte_leBytesToQuad32 _ (by omega),
    bvs_getElem! _ _ (by rw [(blocks.val[i / 16]!).property]; simp; omega), hci' _ (by omega),
    getElem!_take_drop _ _ _ _ (by omega), show i / 16 * 16 + i % 16 = i by omega]

/-- `by8` runs `ctr8` on each 128-byte chunk, then on the rest padded with
zeros, counting the counter up by eight blocks a chunk: CTR over the whole
input, whichever keystream `ctr8` XORs. -/
theorem by8_spec {T : Type} (inst : low.generic.ctr.Ctr8 T) (key : T) (nonce : Std.Array U8 12#usize)
    (counter : U32) (inout : Slice U8) (ks : Nat → List (BitVec 8))
    (hctr : ∀ (m : Nat) (ctr : U32) (chunk : Std.Array U8 128#usize), ctr.val = (counter.val + 8 * m) % 2 ^ 32 →
      inst.ctr8 key nonce ctr chunk ⦃ out => bvs out.val = ctrXor ks (8 * m) (bvs chunk.val) ⦄) :
    low.generic.ctr.by8 inst key nonce counter inout ⦃ r => bvs r.val = ctrXor ks 0 (bvs inout.val) ⦄ := by
  unfold low.generic.ctr.by8
  step with as_chunks_mut_spec 128#usize inout (by simp) as ⟨chunks, tail, back, hcl, hci, htl, hback⟩
  have hcl' : chunks.val.length = inout.val.length / 128 := by simpa using hcl
  have htl' : tail.val = inout.val.drop (inout.val.length / 128 * 128) := by simpa using htl
  have hci' : ∀ q < chunks.val.length, (chunks.val[q]!).val = (inout.val.drop (q * 128)).take 128 := by
    intro q hq
    simpa using hci q hq
  have htlen : tail.val.length = inout.val.length - chunks.val.length * 128 := by
    rw [htl', List.length_drop, hcl']
  have hdm := Nat.div_mul_le_self inout.val.length 128
  have hmd : inout.val.length - inout.val.length / 128 * 128 < 128 := by omega
  apply WP.spec_bind (Pₘ := fun st : Slice (Std.Array U8 128#usize) × U32 =>
    st.1.val.length = chunks.val.length ∧ st.2.val = (counter.val + 8 * chunks.val.length) % 2 ^ 32 ∧
    ∀ q < chunks.val.length, bvs (st.1.val[q]!).val = ctrXor ks (8 * q) (bvs (chunks.val[q]!).val))
  · unfold low.generic.ctr.by8_loop
    apply range_loop _ (Slice.len chunks) (fun c (st : Slice (Std.Array U8 128#usize) × U32) =>
      st.1.val.length = chunks.val.length ∧ st.1.val.drop c = chunks.val.drop c ∧
      st.2.val = (counter.val + 8 * c) % 2 ^ 32 ∧
      ∀ q < c, bvs (st.1.val[q]!).val = ctrXor ks (8 * q) (bvs (chunks.val[q]!).val))
    · rintro it ⟨cs, ctr⟩ he hlt ⟨hlen, hdrop, hc, hdone⟩
      simp only at hlen hdrop hc hdone
      have hlt : it.start.val < chunks.val.length := by simpa [he] using hlt
      unfold low.generic.ctr.by8_loop.body
      step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      step as ⟨a, bk, ha, hbk⟩
      rw [← getElem!_pos, getElem!_of_drop_eq hdrop] at ha
      subst ha hbk
      step with hctr it.start.val ctr _ hc as ⟨a1, ha1⟩
      rw [show lift (core.num.U32.wrapping_add ctr 8#u32) = ok (core.num.U32.wrapping_add ctr 8#u32) from rfl,
        bind_ok]
      simp only [WP.spec_ok]
      refine ⟨it', (cs.set it.start a1, core.num.U32.wrapping_add ctr 8#u32), rfl, hst, by rw [hen, he], ?_⟩
      simp only [Slice.set_val_eq]
      refine ⟨by simp [hlen], by rw [drop_set_succ, ← List.drop_drop, hdrop, List.drop_drop], ?_, ?_⟩
      · have h8 : (8#u32).val = 8 := rfl
        have hsz : UScalar.size UScalarTy.U32 = 2 ^ 32 := by simp [UScalar.size_def]
        rw [show core.num.U32.wrapping_add ctr 8#u32 = UScalar.wrapping_add ctr 8#u32 from rfl,
          UScalar.wrapping_add_val_eq, hc, h8, hsz]
        omega
      · intro q hq
        rw [getElem!_set _ _ _ (by omega)]
        by_cases hq' : it.start.val = q
        · subst hq'
          rw [ite_t rfl, ha1]
        · rw [ite_f hq', hdone q (by omega)]
    · rintro it ⟨cs, ctr⟩ he hst ⟨hlen, hdrop, hc, hdone⟩
      simp only at hlen hdrop hc hdone
      have hst : it.start.val = chunks.val.length := by simpa [he] using hst
      unfold low.generic.ctr.by8_loop.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨(cs, ctr), rfl, hlen, by rw [hc, hst], fun q hq => hdone q (by omega)⟩
    · rfl
    · simp
    · refine ⟨rfl, rfl, ?_, fun q hq => by simp at hq⟩
      have := counter.bv.isLt
      show counter.bv.toNat = (counter.bv.toNat + 8 * (0#usize).val) % 2 ^ 32
      simp only [show (0#usize).val = 0 by simp, Nat.mul_zero, Nat.add_zero]
      exact (Nat.mod_eq_of_lt this).symm
  rintro ⟨chunks1, ctr1⟩ ⟨hlen1, hc1, hdone1⟩
  simp only at hlen1 hc1 hdone1 ⊢
  -- The whole result, from the chunks and the rest.
  have hfin : ∀ tail1 : Slice U8, tail1.val.length = tail.val.length →
      (∀ t < tail.val.length, (tail1.val[t]!).bv =
        (tail.val[t]!).bv ^^^ (ks (8 * chunks.val.length + t / 16))[t % 16]!) →
      bvs (back (chunks1, tail1)).val = ctrXor ks 0 (bvs inout.val) := by
    intro tail1 htl1 hW
    rw [hback _ _ (by
      rw [List.length_append, length_flatMap_val, hlen1, htl1, htlen]
      have := Slice.length_ineq inout
      simp only [show (128#usize).val = 128 by simp]
      omega)]
    apply ext_getElem! (by
      simp only [length_ctrXor, bvs, List.length_map, List.length_append, length_flatMap_val, hlen1, htl1, htlen,
        show (128#usize).val = 128 by simp]
      omega)
    intro i hi
    have hi' : i < inout.val.length := by
      simp only [bvs, List.length_map, List.length_append, length_flatMap_val, hlen1, htl1, htlen,
        show (128#usize).val = 128 by simp] at hi
      omega
    rw [getElem!_ctrXor _ _ _ _ (by simpa using hi'), bvs_getElem! _ _ hi', Nat.zero_add,
      bvs_getElem! _ _ (by simpa using hi)]
    by_cases hq : i < chunks.val.length * 128
    · rw [getElem!_append_left' _ _ _ (by rw [length_flatMap_val, hlen1]; simpa using hq),
        getElem!_flatMap_val (by simp) _ _ (by rw [hlen1]; simpa using hq)]
      simp only [show (128#usize).val = 128 by simp]
      have hq1 : i / 128 < chunks.val.length := by omega
      rw [← bvs_getElem! (chunks1.val[i / 128]!).val (i % 128) (by
          rw [(chunks1.val[i / 128]!).property]; simp; omega),
        hdone1 _ hq1, getElem!_ctrXor _ _ _ _ (by
          rw [bvs, List.length_map, (chunks.val[i / 128]!).property]; simp; omega),
        bvs_getElem! _ _ (by rw [(chunks.val[i / 128]!).property]; simp; omega), hci' _ hq1,
        getElem!_take_drop _ _ _ _ (by omega), show i / 128 * 128 + i % 128 = i by omega,
        show 8 * (i / 128) + i % 128 / 16 = i / 16 by omega, show i % 128 % 16 = i % 16 by omega]
    · rw [getElem!_append_right' _ _ _ (by rw [length_flatMap_val, hlen1]; simp; omega), length_flatMap_val,
        hlen1]
      simp only [show (128#usize).val = 128 by simp]
      have ht : i - chunks.val.length * 128 < tail.val.length := by omega
      rw [hW _ ht, htl', getElem!_drop', ← hcl', show chunks.val.length * 128 + (i - chunks.val.length * 128) = i by omega,
        show 8 * chunks.val.length + (i - chunks.val.length * 128) / 16 = i / 16 by omega,
        show (i - chunks.val.length * 128) % 16 = i % 16 by omega]
  step as ⟨b, hb⟩
  split
  · rename_i hz
    simp only [WP.spec_ok]
    have hz : tail.val.length = 0 := by simpa [hb] using hz
    exact hfin tail rfl (fun t ht => by omega)
  · rename_i hz
    have hz : tail.val.length ≠ 0 := by simpa [hb] using hz
    have hle : (Slice.len tail).val ≤ 128 := by simp; omega
    step with Array.index_mut_SliceIndexRangeToUsizeSlice (Array.repeat 128#usize 0#u8) { «end» := Slice.len tail }
      (by scalar_tac) as ⟨s, bk, hs, hsl, hbk⟩
    step with core.slice.Slice.copy_from_slice.step_spec core.marker.CopyU8 s tail (by rw [hsl]; simp) as ⟨s1, hs1⟩
    step with hctr chunks.val.length ctr1 _ hc1 as ⟨buf2, hbuf2⟩
    step as ⟨s2, hs2, hs2l⟩
    step with core.slice.Slice.copy_from_slice.step_spec core.marker.CopyU8 tail s2 (by rw [hs2l]; simp)
      as ⟨tail1, htail1⟩
    rw [htail1]
    refine hfin s2 (by simpa using hs2l) (fun t ht => ?_)
    have h1 : (s2.val[t]!) = buf2.val[t]! := by
      rw [hs2]
      simp [Array.to_slice, List.getElem!_eq_getElem?_getD, ht]
    have h2 : (bk s1).val[t]! = tail.val[t]! := by
      rw [hbk, List.getElem!_setSlice!_middle _ _ _ _ (by simp [hs1]; omega), hs1]
      simp
    rw [h1, ← bvs_getElem! buf2.val t (by rw [buf2.property]; simp; omega), hbuf2,
      getElem!_ctrXor _ _ _ _ (by rw [bvs, List.length_map, (bk s1).property]; simp; omega),
      bvs_getElem! _ _ (by rw [(bk s1).property]; simp; omega), h2]

/-- `low::aarch64::aes_ctr::apply` is SP 800-38A's CTR mode with the nonce
and counter as the first counter block, counting in its last four bytes. -/
theorem aes_ctr_apply_spec (alg : Algorithm) (key : List (BitVec 8)) (k : low.aarch64.aes.AesKey)
    (hk : ModeKeyIs alg key k) (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8) :
    low.aarch64.aes_ctr.apply k nonce counter inout ⦃ r =>
      bvs r.val = aesCtr alg key 32 (bvs nonce.val ++ be32 counter.val) (bvs inout.val) ⦄ := by
  obtain ⟨-, hwk, rfl, hwk_is⟩ := hk
  have hc : counter.val < 2 ^ 32 := by scalar_tac
  have hn : (bvs nonce.val).length = 12 := by simp
  simp only [low.aarch64.aes_ctr.apply]
  apply WP.spec_mono (by8_spec _ hwk nonce counter inout
    (fun j => aesBlock alg key (be128 (ctrBlock 32 (ofBe (bvs nonce.val ++ be32 counter.val)) j))) ?_)
  · intro r hr
    rw [hr, aesCtr_eq]
  · intro m ctr chunk hctr
    apply WP.spec_mono (apply_8_spec alg key hwk hwk_is nonce ctr chunk)
    intro out hout
    have hj : ∀ j, (ctr.val + j) % 2 ^ 32 = (counter.val + (8 * m + j)) % 2 ^ 32 := by
      intro j
      rw [hctr]
      omega
    rw [hout]
    simp only [ctrXor, ctr_block_eq _ hn _ _ hc, Nat.zero_add, hj]

end rind.aarch64
