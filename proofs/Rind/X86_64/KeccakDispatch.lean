import Rind.X86_64.S2nBignum
open Aeneas Aeneas.Std Result rind.spec

/-!
# Keccak-f[1600]'s dispatch on x86_64

What the routines rind's sponge calls compute, from s2n-bignum's contracts in
`Rind.X86_64.S2nBignum`: `keccak_f1600_spec`, one state; `keccak4_f1600_spec`,
four; `keccak_nof4_f1600_spec`, the first `N` of four. The sponge's proof,
which `admin/prove` writes for aarch64 from x86_64's, uses these names on both,
and `Rind.Aarch64.KeccakDispatch` proves aarch64's.
-/

namespace rind.x86_64

/-- rind's SHA-3 runs on this CPU: its entry guard, the debug build's check
that one is held, and its AVX2 check pass. None reads an input. -/
def RunsSha3 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
    ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t

theorem sha3_new_secret_spec (h : RunsSha3) : low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  simp [he]

theorem sha3_assert_held_spec (h : RunsSha3) : low.entry.Entry.assert_held ⦃ _ => True ⦄ := by
  obtain ⟨-, he, -⟩ := h
  simp [he]

/-- A state's lanes. -/
abbrev lanes (a : Std.Array U64 25#usize) : List (BitVec 64) := a.val.map (·.bv)

/-- Four states' lanes. -/
abbrev states (a : Std.Array (Std.Array U64 25#usize) 4#usize) : List (List (BitVec 64)) :=
  a.val.map lanes

theorem rc_bv : mid.sha3.RC.val.map (·.bv) = keccakRoundConstants := by
  simp [mid.sha3.RC, keccakRoundConstants]

/-- `keccak_f1600_spec`: one state. -/
theorem keccak_f1600_spec (_h : RunsSha3) (a : Std.Array U64 25#usize) :
    low.x86_64.sha3_keccak_f1600.sha3_keccak_f1600 a mid.sha3.RC ⦃ r =>
      lanes r = keccak 24 (lanes a) ⦄ :=
  sha3_keccak_f1600_spec a _ rc_bv

/-- Applying `f` at index `k` of a list whose first `k` have had it applies it
to the first `k + 1`. -/
theorem set_take_map {α : Type} [Inhabited α] (f : α → α) (S : List α) (k : Nat)
    (hk : k < S.length) :
    ((S.take k).map f ++ S.drop k).set k (f S[k]!) = (S.take (k + 1)).map f ++ S.drop (k + 1) := by
  have h1 : ((S.take k).map f).length = k := by simp; omega
  rw [List.drop_eq_getElem_cons hk, List.set_append_right _ _ (by omega), h1, Nat.sub_self,
    List.set_cons_zero, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.map_append, List.append_assoc, getElem!_pos S k hk]
  rfl

/-- Permuting state `k` of states whose first `k` are permuted permutes the first `k + 1`. -/
theorem states_set (S : List (List (BitVec 64))) (a : Std.Array (Std.Array U64 25#usize) 4#usize)
    (k : Usize) (hk : k.val < 4) (ha : states a = (S.take k.val).map (keccak 24) ++ S.drop k.val)
    (x : Std.Array U64 25#usize) (hx : lanes x = keccak 24 (lanes (a.val[k.val]!))) :
    states (a.set k x) = (S.take (k.val + 1)).map (keccak 24) ++ S.drop (k.val + 1) := by
  have hl : S.length = 4 := by
    have := congrArg List.length ha
    simp at this; omega
  have ha4 : a.val.length = 4 := by simp
  have hSk : lanes (a.val[k.val]!) = S[k.val]! := by
    have := congrArg (·[k.val]?) ha
    simp only [states, List.getElem?_map, List.getElem?_append_right (by simp : (List.map
      (keccak 24) (List.take k.val S)).length ≤ k.val), List.getElem?_drop, List.length_map,
      List.length_take, show min k.val S.length = k.val by omega, Nat.sub_self, Nat.add_zero,
      List.getElem?_eq_getElem (show k.val < a.val.length by omega),
      List.getElem?_eq_getElem (show k.val < S.length by omega), Option.map_some,
      Option.some.injEq] at this
    rw [getElem!_pos a.val k.val (by omega), getElem!_pos S k.val (by omega), this]
  simp only [states, Std.Array.set_val_eq, List.map_set]
  rw [show List.map lanes a.val = states a from rfl, ha, hx, hSk]
  exact set_take_map _ S k.val (by omega)

/-- The fallback permutes states `iter.start` to `N - 1` in turn. -/
theorem keccak_loop_spec (h : RunsSha3) (S : List (List (BitVec 64))) (N : Nat) (hN : N ≤ 4)
    (iter : core.ops.range.Range Usize) (a : Std.Array (Std.Array U64 25#usize) 4#usize)
    (hs : iter.start.val ≤ N) (he : iter.end.val = N)
    (ha : states a = (S.take iter.start.val).map (keccak 24) ++ S.drop iter.start.val) :
    low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop iter a mid.sha3.RC ⦃ r =>
      states r = (S.take N).map (keccak 24) ++ S.drop N ⦄ := by
  unfold low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop
  apply loop.spec_decr_nat (fun x => N - x.1.start.val)
    (fun x => x.1.start.val ≤ N ∧ x.1.end.val = N ∧
      states x.2 = (S.take x.1.start.val).map (keccak 24) ++ S.drop x.1.start.val)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with Array.index_mut_usize_spec st it.start (by simp; omega) as ⟨x, back, hx, hback⟩
      step with keccak_f1600_spec h x as ⟨y, hy⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hback, hst', states_set S st it.start (by omega) hst y (by
        rw [hy, hx, getElem!_pos st.val it.start.val (by simp; omega)])]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have hN' : it.start.val = N := by omega
      simpa [hN'] using hst
  · exact ⟨hs, he, ha⟩

theorem take_map_drop_four {α : Type} (f : α → α) (S : List α) (hS : S.length = 4) :
    (S.take 4).map f ++ S.drop 4 = S.map f := by
  rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil]

theorem RHO8_bv : low.x86_64.sha3_keccak4_f1600_shim.RHO8.val.map (·.bv) = keccakRho8 := by
  simp [low.x86_64.sha3_keccak4_f1600_shim.RHO8, keccakRho8]

theorem RHO56_bv : low.x86_64.sha3_keccak4_f1600_shim.RHO56.val.map (·.bv) = keccakRho56 := by
  simp [low.x86_64.sha3_keccak4_f1600_shim.RHO56, keccakRho56]

/-- `keccak4_f1600_spec`: four states. -/
theorem keccak4_f1600_spec (h : RunsSha3) (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600 a mid.sha3.RC ⦃ r =>
      states r = (states a).map (keccak 24) ⦄ := by
  have hl : (states a).length = 4 := by simp
  obtain ⟨-, -, t, ht⟩ := id h
  unfold low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600
  rw [ht, bind_ok]
  cases t with
  | none =>
    apply WP.spec_mono (keccak_loop_spec h (states a) 4 (by omega) _ a (by simp) (by simp) (by simp))
    intro r hr
    rwa [take_map_drop_four _ _ hl] at hr
  | some t =>
    exact sha3_keccak4_f1600_alt_spec a _ _ _ rc_bv RHO8_bv RHO56_bv

theorem nof4_loop0_eq : @low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop0 =
    @low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop := by
  funext iter a rc
  unfold low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop0
    low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop
    low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop0.body
    low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop.body
  rfl

theorem nof4_loop1_eq : @low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop1 =
    @low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop := by
  funext iter a rc
  unfold low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop1
    low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop
    low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop1.body
    low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600_loop.body
  rfl

theorem take_loop (S : List (List (BitVec 64))) (N : Nat) (hN : N ≤ S.length) :
    ((S.take N).map (keccak 24) ++ S.drop N).take N = (S.take N).map (keccak 24) := by
  rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp)]

/-- `keccak_nof4_f1600_spec`: the first `N` of four states. -/
theorem keccak_nof4_f1600_spec (h : RunsSha3) (N : Usize) (hN : 1 ≤ N.val ∧ N.val ≤ 4)
    (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600 N a mid.sha3.RC ⦃ r =>
      (states r).take N.val = ((states a).take N.val).map (keccak 24) ⦄ := by
  have hl : (states a).length = 4 := by simp
  obtain ⟨-, -, t, ht⟩ := id h
  unfold low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600
  rw [ht, bind_ok]
  cases t with
  | none =>
    rw [nof4_loop0_eq]
    apply WP.spec_mono (keccak_loop_spec h (states a) N.val hN.2 _ a (by simp) rfl (by simp))
    intro r hr
    rw [hr, take_loop _ _ (by omega)]
  | some t =>
    simp only
    split
    · apply WP.spec_mono (keccak4_f1600_spec h a)
      intro r hr
      rw [hr, List.map_take]
    · rw [nof4_loop1_eq]
      apply WP.spec_mono (keccak_loop_spec h (states a) N.val hN.2 _ a (by simp) rfl (by simp))
      intro r hr
      rw [hr, take_loop _ _ (by omega)]

end rind.x86_64
