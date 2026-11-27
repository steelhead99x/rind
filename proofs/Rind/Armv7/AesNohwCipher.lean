import Rind.Armv7.AesNohwBatch
open Aeneas Aeneas.Std Result rind.vale

/-!
# The bitsliced AES's rounds

`Schedule::encrypt_batch` runs FIPS 197's cipher on both blocks of a batch,
given the round keys its schedule holds.
-/

namespace rind.armv7

open low.portable.aes_nohw

instance : Inhabited Batch := ⟨{ w := Std.Array.repeat 8#usize 0#u32 }⟩

/-- The round keys a schedule holds for block `i` of a batch. -/
def low.portable.aes_nohw.Schedule.roundKeys (s : Schedule) (i : Nat) : List Quad32 :=
  s.keys.val.map (·.block i)

theorem roundKeys_get (s : Schedule) (i r : Nat) (hr : r < 15) :
    (s.roundKeys i)[r]! = (s.keys.val[r]!).block i := by
  have hl : r < s.keys.val.length := by simpa using hr
  rw [getElem!_pos s.keys.val r hl, Schedule.roundKeys, getElem!_pos _ r (by simpa using hl)]
  simp

/-- FIPS 197's cipher without its key expansion: Vale's `eval_cipher`, for any
number of rounds. -/
def cipherRounds (rounds : Nat) (input : Quad32) (rk : List Quad32) : Quad32 :=
  shiftRows (subBytes (evalRounds (input ^^^ rk[0]!) rk (rounds - 1))) ^^^ rk[rounds]!

theorem evalCipher_eq (alg : Algorithm) (input : Quad32) (rk : List Quad32) :
    evalCipher alg input rk = cipherRounds (nr alg) input rk := rfl

/-- Rounds `iter.start` to `rounds - 1`, of a batch whose first `iter.start - 1` are done. -/
theorem encrypt_batch_loop_spec (s : Schedule) (init : Nat → Quad32)
    (iter : core.ops.range.Range Usize) (b : Batch)
    (hr : s.rounds.val ≤ 14) (h1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ s.rounds.val)
    (he : iter.end.val = s.rounds.val)
    (hb : ∀ i < 2, b.block i = evalRounds (init i) (s.roundKeys i) (iter.start.val - 1)) :
    Schedule.encrypt_batch_loop iter s.keys b ⦃ r =>
      ∀ i < 2, r.block i = evalRounds (init i) (s.roundKeys i) (s.rounds.val - 1) ⦄ := by
  unfold Schedule.encrypt_batch_loop
  apply loop.spec_decr_nat (fun x => s.rounds.val - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ s.rounds.val ∧ x.1.end.val = s.rounds.val ∧
      ∀ i < 2, x.2.block i = evalRounds (init i) (s.roundKeys i) (x.1.start.val - 1))
  · rintro ⟨it, st⟩ ⟨h1, hs, he, hst⟩
    simp only at h1 hs he hst ⊢
    unfold Schedule.encrypt_batch_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with sub_bytes_block st as ⟨b1, hb1⟩
      step with shift_rows_block b1 as ⟨b2, hb2⟩
      step with mix_columns_block b2 as ⟨b3, hb3⟩
      step with Array.index_usize_spec s.keys it.start (by simp; omega) as ⟨k, hk⟩
      step with add_round_key_block b3 k as ⟨b4, hb4⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, by omega, ?_, by omega⟩
      intro i hi
      have hn : it'.start.val - 1 = (it.start.val - 1) + 1 := by omega
      rw [hb4 i hi, hb3 i hi, hb2 i hi, hb1 i hi, hst i hi, hn, evalRounds, evalRound,
        show it.start.val - 1 + 1 = it.start.val by omega, roundKeys_get s i _ (by omega), hk,
        getElem!_pos s.keys.val it.start.val (by simp; omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have hN : it.start.val = s.rounds.val := by omega
      simpa [hN] using hst
  · exact ⟨h1, hs, he, hb⟩

/-- `encrypt_batch` is the cipher on both blocks, under the schedule's round keys. -/
theorem encrypt_batch_spec (s : Schedule) (b : Batch) (h1 : 1 ≤ s.rounds.val) (hr : s.rounds.val ≤ 14) :
    s.encrypt_batch b ⦃ r =>
      ∀ i < 2, r.block i = cipherRounds s.rounds.val (b.block i) (s.roundKeys i) ⦄ := by
  unfold Schedule.encrypt_batch
  step with Array.index_usize_spec s.keys 0#usize (by simp) as ⟨k0, hk0⟩
  step with add_round_key_block b k0 as ⟨b1, hb1⟩
  step with encrypt_batch_loop_spec s (fun i => b.block i ^^^ (s.roundKeys i)[0]!)
    { start := 1#usize, «end» := s.rounds } b1 hr (by show 1 ≤ (1#usize).val; decide) (by simpa using h1) rfl (by
      intro i hi
      simp only [show (1#usize).val - 1 = 0 from rfl, evalRounds]
      rw [hb1 i hi, roundKeys_get s i 0 (by omega), hk0, getElem!_pos s.keys.val 0 (by simp)]
      ) as ⟨b2, hb2⟩
  step with sub_bytes_block b2 as ⟨b3, hb3⟩
  step with shift_rows_block b3 as ⟨b4, hb4⟩
  step with Array.index_usize_spec s.keys s.rounds (by simp; omega) as ⟨kn, hkn⟩
  apply WP.spec_mono (add_round_key_block b4 kn)
  intro r hrr i hi
  rw [hrr i hi, hb4 i hi, hb3 i hi, hb2 i hi, cipherRounds, roundKeys_get s i s.rounds.val (by omega), hkn,
    getElem!_pos s.keys.val s.rounds.val (by simp; omega)]

end rind.armv7
