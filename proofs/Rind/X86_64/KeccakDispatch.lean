import Rind.X86_64.S2nBignum
import Rind.KeccakStates
open Aeneas Aeneas.Std Result rind.spec

/-!
# Keccak-f[1600]'s dispatch on x86_64

What the routines rind's sponge calls compute, from s2n-bignum's contracts in
`Rind.X86_64.S2nBignum`: `keccak_f1600_spec`, one state; `keccak4_f1600_spec`,
four; `keccak_nof4_f1600_spec`, the first `N` of four; and
`keccak_nof8_f1600_spec`, the first `n` of eight. The sponge's proof,
which `admin/prove` writes for aarch64 from x86_64's, uses these names on both,
and `Rind.Aarch64.KeccakDispatch` proves aarch64's.
-/

namespace rind.x86_64

/-- rind's SHA-3 runs on this CPU: its entry guard, the debug build's check
that one is held, and its AVX2 and AVX-512 checks pass, none reading an
input; and rind's own eight-way AVX-512 Keccak-f, which no proof covers yet,
computes Keccak-f on each of its eight states. -/
def RunsSha3 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
    (∃ t, low.x86_64.cpu.HaveAvx2.check = ok t) ∧
    (∃ t, low.x86_64.cpu.HaveAvx512Vl.check = ok t) ∧
    ∀ a t, low.x86_64.sha3_keccak8_f1600.permute a mid.sha3.RC t ⦃ r =>
      states8 r = (states8 a).map (keccak 24) ⦄

theorem sha3_new_secret_spec (h : RunsSha3) : low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  simp [he]

theorem sha3_assert_held_spec (h : RunsSha3) : low.entry.Entry.assert_held ⦃ _ => True ⦄ := by
  obtain ⟨-, he, -⟩ := h
  simp [he]

theorem rc_bv : mid.sha3.RC.val.map (·.bv) = keccakRoundConstants := by
  simp [mid.sha3.RC, keccakRoundConstants]

/-- `keccak_f1600_spec`: one state. -/
theorem keccak_f1600_spec (_h : RunsSha3) (a : Std.Array U64 25#usize) :
    low.x86_64.sha3_keccak_f1600.sha3_keccak_f1600 a mid.sha3.RC ⦃ r =>
      lanes r = keccak 24 (lanes a) ⦄ :=
  sha3_keccak_f1600_spec a _ rc_bv

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

theorem RHO8_bv : low.x86_64.sha3_keccak4_f1600_shim.RHO8.val.map (·.bv) = keccakRho8 := by
  simp [low.x86_64.sha3_keccak4_f1600_shim.RHO8, keccakRho8]

theorem RHO56_bv : low.x86_64.sha3_keccak4_f1600_shim.RHO56.val.map (·.bv) = keccakRho56 := by
  simp [low.x86_64.sha3_keccak4_f1600_shim.RHO56, keccakRho56]

/-- `keccak4_f1600_spec`: four states. -/
theorem keccak4_f1600_spec (h : RunsSha3) (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.x86_64.sha3_keccak4_f1600_shim.sha3_keccak4_f1600 a mid.sha3.RC ⦃ r =>
      states r = (states a).map (keccak 24) ⦄ := by
  have hl : (states a).length = 4 := by simp
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := id h
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

/-- `keccak_nof4_f1600_spec`: the first `N` of four states. -/
theorem keccak_nof4_f1600_spec (h : RunsSha3) (N : Usize) (hN : 1 ≤ N.val ∧ N.val ≤ 4)
    (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.x86_64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600 N a mid.sha3.RC ⦃ r =>
      (states r).take N.val = ((states a).take N.val).map (keccak 24) ⦄ := by
  have hl : (states a).length = 4 := by simp
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := id h
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

/-- `generic::keccak8`'s `nof4`: the first `n` of four states, one to four. -/
theorem generic_nof4_spec (h : RunsSha3) (n : Usize) (hn : 1 ≤ n.val ∧ n.val ≤ 4)
    (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.generic.keccak8.nof4 a n mid.sha3.RC ⦃ r =>
      (states r).take n.val = ((states a).take n.val).map (keccak 24) ⦄ := by
  unfold low.generic.keccak8.nof4
  have hl : (states a).length = 4 := by simp
  obtain h1 | h2 | h3 | h4 : n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 := by omega
  · simp only [h1]
    exact keccak_nof4_f1600_spec h 1#usize (by decide) a
  · simp only [h2]
    exact keccak_nof4_f1600_spec h 2#usize (by decide) a
  · simp only [h3]
    exact keccak_nof4_f1600_spec h 3#usize (by decide) a
  · simp only [h4]
    apply WP.spec_mono (keccak4_f1600_spec h a)
    intro r hr
    have hr4 : (states r).length = 4 := by simp
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    exact hr

/-- `generic::keccak8`: the first `n` of eight states, four at a time. -/
theorem generic_nof8_spec (h : RunsSha3) (n : Usize) (hn : 1 ≤ n.val ∧ n.val ≤ 8)
    (a : Std.Array (Std.Array U64 25#usize) 8#usize) :
    low.generic.keccak8.sha3_keccak_nof8_f1600 a n mid.sha3.RC ⦃ r =>
      (states8 r).take n.val = ((states8 a).take n.val).map (keccak 24) ⦄ := by
  unfold low.generic.keccak8.sha3_keccak_nof8_f1600
  step with Std.Array.to_slice_mut_spec a as ⟨s, back, hs, hback⟩
  step with as_chunks_mut_four_spec s (by simp [Slice.length, hs]) as
    ⟨quads, rest, cback, hq, hrest, hcback⟩
  have hq2 : quads.val.length = 2 := by
    have := congrArg List.length hq; simpa using this
  have hqe : ∀ i (hi : i < 2), (quads.val[i]!).val = [a.val.take 4, a.val.drop 4][i]! := by
    intro i hi
    have := congrArg (·[i]!) hq
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show i < quads.val.length by omega), Option.map_some,
      Option.getD_some, hs] at this ⊢
    exact this
  have hq0 : (quads.val[0]!).val = a.val.take 4 := hqe 0 (by omega)
  have hq1 : (quads.val[1]!).val = a.val.drop 4 := hqe 1 (by omega)
  -- The view writes two groups back in order.
  have hflat : ∀ p : Slice (Std.Array (Std.Array U64 25#usize) 4#usize), p.val.length = 2 →
      (back (cback (p, rest))).val = (p.val[0]!).val ++ (p.val[1]!).val := by
    intro p hp
    obtain ⟨p0, p1, hp'⟩ := List.length_eq_two.1 hp
    have hc := hcback p hp
    rw [hp'] at hc
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
    rw [hback, Std.Array.from_slice_val _ _ (by rw [hc]; simp), hc, hp']
    rfl
  have ha8 : (states8 a).length = 8 := by simp
  split
  · rename_i hgt
    step with Slice.index_mut_usize_spec as ⟨x, imb, hx, himb⟩
    step with keccak4_f1600_spec h x as ⟨z, hz⟩
    step with Slice.index_mut_usize_spec (imb z) 1#usize (by rw [himb]; simp [Slice.length, hq2])
      as ⟨x2, imb2, hx2, himb2⟩
    step as ⟨m, hm⟩
    step with generic_nof4_spec h m (by scalar_tac) x2 as ⟨z2, hz2⟩
    have hx0 : x.val = a.val.take 4 := by rw [hx, ← getElem!_pos, hq0]
    have hx1 : x2.val = a.val.drop 4 := by
      rw [hx2, ← getElem!_pos, himb, Slice.set_val_eq, getElem!_set' _ _ _ _ (by omega)]
      simp only [show (0#usize : Usize).val = 0 from rfl, show ¬((0 : Nat) = 1) by omega,
        ite_false, hq1]
    have hp' : (imb2 z2).val.length = 2 := by rw [himb2, himb]; simp [hq2]
    have hr : (back (cback (imb2 z2, rest))).val = z.val ++ z2.val := by
      obtain ⟨q0, q1, hq'⟩ := List.length_eq_two.1 hq2
      rw [hflat _ hp', himb2, himb, Slice.set_val_eq, Slice.set_val_eq, hq']
      rfl
    have hzl : z.val.length = 4 := by simp
    apply take_eq_map_take _ _ _ _ (by simp; omega) (by simp; omega)
    intro i hi
    rw [states8_getElem! _ i (by omega), states8_getElem! a i (by omega), hr,
      getElem!_append_cond, hzl]
    by_cases hi4 : i < 4
    · rw [ite_eq_left hi4, ← states_getElem! z i hi4, hz, getElem!_pos _ i (by simp; omega),
        List.getElem_map, ← getElem!_pos, states_getElem! x i hi4, hx0,
        getElem!_take' _ _ _ hi4]
    · rw [ite_eq_right hi4, ← states_getElem! z2 _ (by omega),
        getElem!_of_take_map _ _ _ m.val _ hz2 (by omega) (by simp; omega) (by simp; omega),
        states_getElem! x2 _ (by omega), hx1, getElem!_drop', show 4 + (i - 4) = i by omega]
  · rename_i hle
    step with Slice.index_mut_usize_spec as ⟨x, imb, hx, himb⟩
    step with generic_nof4_spec h n (by scalar_tac) x as ⟨z, hz⟩
    have hx0 : x.val = a.val.take 4 := by rw [hx, ← getElem!_pos, hq0]
    have hp' : (imb z).val.length = 2 := by rw [himb]; simp [hq2]
    have hr : (back (cback (imb z, rest))).val = z.val ++ a.val.drop 4 := by
      rw [hflat _ hp', himb, Slice.set_val_eq, getElem!_set' _ _ _ _ (by omega),
        getElem!_set' _ _ _ _ (by omega)]
      simp only [show (0#usize : Usize).val = 0 from rfl, ite_true,
        show ¬((0 : Nat) = 1) by omega, ite_false, hq1]
    have hzl : z.val.length = 4 := by simp
    apply take_eq_map_take _ _ _ _ (by simp; omega) (by simp; omega)
    intro i hi
    have hi4 : i < 4 := by scalar_tac
    rw [states8_getElem! _ i (by omega), states8_getElem! a i (by omega), hr,
      getElem!_append_cond, hzl, ite_eq_left hi4, ← states_getElem! z i hi4,
      getElem!_of_take_map _ _ _ n.val _ hz (by omega) (by simp; omega) (by simp; omega),
      states_getElem! x i hi4, hx0, getElem!_take' _ _ _ hi4]

/-- `keccak_nof8_f1600_spec`: the first `n` of eight states, all eight at
once on AVX-512, as `RunsSha3` takes its kernel to compute. -/
theorem keccak_nof8_f1600_spec (h : RunsSha3) (n : Usize) (hn : 1 ≤ n.val ∧ n.val ≤ 8)
    (a : Std.Array (Std.Array U64 25#usize) 8#usize) :
    low.x86_64.sha3_keccak8_f1600.sha3_keccak_nof8_f1600 a n mid.sha3.RC ⦃ r =>
      (states8 r).take n.val = ((states8 a).take n.val).map (keccak 24) ⦄ := by
  obtain ⟨-, -, -, ⟨t, ht⟩, hp⟩ := id h
  unfold low.x86_64.sha3_keccak8_f1600.sha3_keccak_nof8_f1600
  rw [ht, bind_ok]
  cases t with
  | none => exact generic_nof8_spec h n hn a
  | some t =>
    simp only
    split
    · apply WP.spec_mono (hp a t)
      intro r hr
      rw [hr, List.map_take]
    · exact generic_nof8_spec h n hn a

end rind.x86_64
