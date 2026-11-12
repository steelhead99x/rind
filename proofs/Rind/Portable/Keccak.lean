import Rind.Portable.Funs
import Rind.KeccakStates
open Aeneas Aeneas.Std Result rind.spec

/-!
# The portable backend's Keccak-f[1600]

`low/portable/keccak.rs` computes s2n-bignum's `keccak 24`, which
`Rind.Keccak` proves FIPS 202's KECCAK-f[1600]: `keccak_f1600_spec`, one
state; `keccak4_f1600_spec`, four; `keccak_nof4_f1600_spec`, the first `N` of
four, as `Rind/<Arch>/KeccakDispatch.lean` states them for the other
backends, given FIPS 202's round constants and nothing of the CPU.
-/

namespace rind.portable

/-- A constant index into a state reads its lane. -/
theorem index_lane (a : Std.Array U64 25#usize) (k : Usize) (hk : k.val < 25) :
    a.index_usize k = ok a.val[k.val]! := by
  have h := Array.index_usize_spec a k (by simpa using hk)
  rw [getElem!_pos a.val k.val (by simpa using hk)]
  revert h; cases a.index_usize k <;> simp_all

/-- A state's lane, as `keccakRound` reads it. -/
theorem lanes_get (a : Std.Array U64 25#usize) (k : Nat) (hk : k < 25) :
    (lanes a)[k]! = a.val[k]!.bv := by
  rw [getElem!_pos _ k (by simpa using hk), getElem!_pos _ k (by simpa using hk)]; simp

/-- `keccak_round`'s rotation of lane `A[0, 0]`, by zero. -/
theorem rotateLeft_zero (x : BitVec 64) : x.rotateLeft 0 = x := by
  ext i; simp [BitVec.getElem_rotateLeft]

/-- `u64::rotate_left` rotates the lane's bits. -/
theorem bv_rotate_left (x : U64) (k : U32) :
    (core.num.U64.rotate_left x k).bv = x.bv.rotateLeft k.val := rfl

/-- One round is s2n-bignum's `keccak_round`. -/
theorem round_spec (a : Std.Array U64 25#usize) (rc : U64) :
    low.portable.keccak.round a rc ⦃ r => lanes r = keccakRound rc.bv (lanes a) ⦄ := by
  unfold low.portable.keccak.round
  simp (disch := simp) only [index_lane a, lift, bind_ok, WP.spec_ok]
  simp (disch := simp) only [keccakRound, lanes_get a, lanes, Array.make_val, List.map_cons, List.map_nil,
    UScalar.bv_xor, UScalar.bv_and, UScalar.bv_not, bv_rotate_left, rotateLeft_zero]
  rfl

/-- Rounds `iter.start` to 23 of state `s`, whose first `iter.start` are done. -/
theorem rounds_spec (L : List (BitVec 64)) (rc : Std.Array U64 24#usize)
    (hrc : rc.val.map (·.bv) = keccakRoundConstants)
    (iter : core.ops.range.Range Usize) (s : Std.Array U64 25#usize)
    (hs : iter.start.val ≤ 24) (he : iter.end.val = 24) (hl : lanes s = keccak iter.start.val L) :
    low.portable.keccak.sha3_keccak_f1600_loop iter s rc ⦃ r => lanes r = keccak 24 L ⦄ := by
  unfold low.portable.keccak.sha3_keccak_f1600_loop
  apply loop.spec_decr_nat (fun x => 24 - x.1.start.val)
    (fun x => x.1.start.val ≤ 24 ∧ x.1.end.val = 24 ∧ lanes x.2 = keccak x.1.start.val L)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold low.portable.keccak.sha3_keccak_f1600_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with Array.index_usize_spec rc it.start (by simp; omega) as ⟨c, hc⟩
      step with round_spec st c as ⟨y, hy⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      have hcv : c.bv = keccakRoundConstants[it.start.val]! := by
        rw [← hrc, hc, getElem!_pos _ it.start.val (by simp; omega)]; simp
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hy, hst', hst, hcv, keccak]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have h24 : it.start.val = 24 := by omega
      simpa [h24] using hst
  · exact ⟨hs, he, hl⟩

/-- `keccak_f1600_spec`: one state, given FIPS 202's round constants. -/
theorem keccak_f1600_spec (a : Std.Array U64 25#usize) (rc : Std.Array U64 24#usize)
    (hrc : rc.val.map (·.bv) = keccakRoundConstants) :
    low.portable.keccak.sha3_keccak_f1600 a rc ⦃ r => lanes r = keccak 24 (lanes a) ⦄ :=
  rounds_spec _ rc hrc _ a (by simp) (by simp) rfl

/-- States `iter.start` to `N - 1` of four, whose first `iter.start` are permuted. -/
theorem states_loop_spec (S : List (List (BitVec 64))) (N : Nat) (hN : N ≤ 4)
    (rc : Std.Array U64 24#usize) (hrc : rc.val.map (·.bv) = keccakRoundConstants)
    (iter : core.ops.range.Range Usize) (a : Std.Array (Std.Array U64 25#usize) 4#usize)
    (hs : iter.start.val ≤ N) (he : iter.end.val = N)
    (ha : states a = (S.take iter.start.val).map (keccak 24) ++ S.drop iter.start.val) :
    low.portable.keccak.sha3_keccak_nof4_f1600_loop iter a rc ⦃ r =>
      states r = (S.take N).map (keccak 24) ++ S.drop N ⦄ := by
  unfold low.portable.keccak.sha3_keccak_nof4_f1600_loop
  apply loop.spec_decr_nat (fun x => N - x.1.start.val)
    (fun x => x.1.start.val ≤ N ∧ x.1.end.val = N ∧
      states x.2 = (S.take x.1.start.val).map (keccak 24) ++ S.drop x.1.start.val)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold low.portable.keccak.sha3_keccak_nof4_f1600_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with Array.index_mut_usize_spec st it.start (by simp; omega) as ⟨x, back, hx, hback⟩
      step with keccak_f1600_spec x rc hrc as ⟨y, hy⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hback, hst', states_set S st it.start (by omega) hst y (by
        rw [hy, hx, getElem!_pos st.val it.start.val (by simp; omega)])]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have hN' : it.start.val = N := by omega
      simpa [hN'] using hst
  · exact ⟨hs, he, ha⟩

/-- `keccak_nof4_f1600_spec`: the first `N` of four states. -/
theorem keccak_nof4_f1600_spec (N : Usize) (hN : N.val ≤ 4)
    (a : Std.Array (Std.Array U64 25#usize) 4#usize) (rc : Std.Array U64 24#usize)
    (hrc : rc.val.map (·.bv) = keccakRoundConstants) :
    low.portable.keccak.sha3_keccak_nof4_f1600 N a rc ⦃ r =>
      (states r).take N.val = ((states a).take N.val).map (keccak 24) ⦄ := by
  apply WP.spec_mono (states_loop_spec (states a) N.val hN rc hrc _ a (by simp) rfl (by simp))
  intro r hr
  rw [hr, take_loop _ _ (by simp; omega)]

/-- `keccak4_f1600_spec`: four states. -/
theorem keccak4_f1600_spec (a : Std.Array (Std.Array U64 25#usize) 4#usize)
    (rc : Std.Array U64 24#usize) (hrc : rc.val.map (·.bv) = keccakRoundConstants) :
    low.portable.keccak.sha3_keccak4_f1600 a rc ⦃ r =>
      states r = (states a).map (keccak 24) ⦄ := by
  unfold low.portable.keccak.sha3_keccak4_f1600
  apply WP.spec_mono (states_loop_spec (states a) 4 (by omega) rc hrc _ a (by simp) (by simp)
    (by simp))
  intro r hr
  rwa [take_map_drop_four _ _ (by simp)] at hr


end rind.portable
