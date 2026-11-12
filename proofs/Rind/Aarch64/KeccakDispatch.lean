import Rind.Aarch64.S2nBignum
open Aeneas Aeneas.Std Result rind.spec

/-!
# Keccak-f[1600]'s dispatch on aarch64

What the routines rind's sponge calls compute, from s2n-bignum's contracts in
`Rind.Aarch64.S2nBignum`: `keccak_f1600_spec`, one state; `keccak4_f1600_spec`,
four; `keccak_nof4_f1600_spec`, the first `N` of four. The sponge's proof,
which `admin/prove` writes from x86_64's, uses these names, which
`Rind.X86_64.KeccakDispatch` proves for x86_64.
-/

namespace rind.aarch64

/-- rind's SHA-3 runs on this CPU: its entry guard, the debug build's check
that one is held, and its SHA-3 extension check pass. None reads an input. -/
def RunsSha3 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
    ∃ t, low.aarch64.cpu.HaveSha3.check = ok t

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
theorem keccak_f1600_spec (h : RunsSha3) (a : Std.Array U64 25#usize) :
    low.aarch64.sha3_keccak_f1600_mux.sha3_keccak_f1600 a mid.sha3.RC ⦃ r =>
      lanes r = keccak 24 (lanes a) ⦄ := by
  obtain ⟨-, -, t, ht⟩ := h
  unfold low.aarch64.sha3_keccak_f1600_mux.sha3_keccak_f1600
  rw [ht, bind_ok]
  cases t
  · exact sha3_keccak_f1600_spec a _ rc_bv
  · exact sha3_keccak_f1600_alt_spec a _ rc_bv

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
theorem keccak_loop_spec (S : List (List (BitVec 64))) (N : Nat) (hN : N ≤ 4)
    (iter : core.ops.range.Range Usize) (a : Std.Array (Std.Array U64 25#usize) 4#usize)
    (hs : iter.start.val ≤ N) (he : iter.end.val = N)
    (ha : states a = (S.take iter.start.val).map (keccak 24) ++ S.drop iter.start.val) :
    low.aarch64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop iter a mid.sha3.RC ⦃ r =>
      states r = (S.take N).map (keccak 24) ++ S.drop N ⦄ := by
  unfold low.aarch64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop
  apply loop.spec_decr_nat (fun x => N - x.1.start.val)
    (fun x => x.1.start.val ≤ N ∧ x.1.end.val = N ∧
      states x.2 = (S.take x.1.start.val).map (keccak 24) ++ S.drop x.1.start.val)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold low.aarch64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with Array.index_mut_usize_spec st it.start (by simp; omega) as ⟨x, back, hx, hback⟩
      step with sha3_keccak_f1600_spec x _ rc_bv as ⟨y, hy⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hback, hst', states_set S st it.start (by omega) hst y (by
        rw [lanes, hy, hx, getElem!_pos st.val it.start.val (by simp; omega)])]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have hN' : it.start.val = N := by omega
      simpa [hN'] using hst
  · exact ⟨hs, he, ha⟩

theorem take_map_drop_four {α : Type} (f : α → α) (S : List α) (hS : S.length = 4) :
    (S.take 4).map f ++ S.drop 4 = S.map f := by
  rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil]

theorem take_loop (S : List (List (BitVec 64))) (N : Nat) (hN : N ≤ S.length) :
    ((S.take N).map (keccak 24) ++ S.drop N).take N = (S.take N).map (keccak 24) := by
  rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp)]

/-- `as_chunks_mut::<2>` of four states: two pairs, nothing left, and a view
that writes pairs back in order. -/
theorem as_chunks_mut_two_spec {T : Type} (s : Slice T) (hs : s.length = 4) :
    core.slice.Slice.as_chunks_mut 2#usize s ⦃ v back =>
      v.1.val.map (·.val) = [s.val.take 2, s.val.drop 2] ∧ v.2.val = [] ∧
      ∀ p : Slice (Std.Array T 2#usize), p.length = 2 →
        (back (p, v.2)).val = p.val.flatMap (·.val) ⦄ := by
  have hl : s.val.length = 4 := hs
  simp only [core.slice.Slice.as_chunks_mut, core.slice.Slice.as_chunks, Slice.length, hl,
    show (2#usize : Usize).val = 2 from rfl, show ¬(2 = 0) from by decide, ite_false]
  simp only [bind_ok, WP.spec_ok, List.ofFn_succ, List.ofFn_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp; omega
  · simp [List.drop_of_length_le (show s.val.length ≤ 2 * 2 by omega)]
  · intro p hp
    have hp' : p.val.length = 2 := hp
    have hd : List.drop (4 / 2 * 2) s.val = [] := List.drop_of_length_le (by omega)
    have hlen : (p.val.flatMap (·.val)).length = 4 := by
      simp [List.length_flatMap, hp']
    simp only []
    split
    · simp [hd]
    · rename_i h
      exfalso; apply h
      simp only [List.length_append, hlen]
      simp [hd]; scalar_tac

theorem getElem!_set' {α : Type} [Inhabited α] (l : List α) (j i : Nat) (v : α) (hi : i < l.length) :
    (l.set j v)[i]! = if j = i then v else l[i]! := by
  rw [getElem!_pos (l.set j v) i (by simp; omega), List.getElem_set, getElem!_pos l i hi]

/-- A list's first `n` are `f` of another's if each is. -/
theorem take_eq_map_take {α : Type} [Inhabited α] (f : α → α) (L M : List α) (n : Nat)
    (hL : n ≤ L.length) (hM : n ≤ M.length) (h : ∀ i, i < n → L[i]! = f M[i]!) :
    L.take n = (M.take n).map f := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_take] at h1
  simp only [List.getElem_take, List.getElem_map]
  have := h i (by omega)
  rwa [getElem!_pos L i (by omega), getElem!_pos M i (by omega)] at this

theorem states_getElem! (r : Std.Array (Std.Array U64 25#usize) 4#usize) (i : Nat) (hi : i < 4) :
    (states r)[i]! = lanes (r.val[i]!) := by
  rw [getElem!_pos _ i (by simp [hi]), getElem!_pos _ i (by simp [hi])]
  simp

theorem getElem!_append' {α : Type} [Inhabited α] (l1 l2 : List α) (i : Nat) :
    (l1 ++ l2)[i]! = if i < l1.length then l1[i]! else l2[i - l1.length]! := by
  simp only [List.getElem!_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega)]

theorem getElem!_take' {α : Type} [Inhabited α] (l : List α) (n i : Nat) (h : i < n) :
    (l.take n)[i]! = l[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take, h, ite_true]

theorem getElem!_drop' {α : Type} [Inhabited α] (l : List α) (n i : Nat) :
    (l.drop n)[i]! = l[n + i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

/-- Each of a pair permuted. -/
theorem pair_lanes {z x : Std.Array (Std.Array U64 25#usize) 2#usize}
    (h : z.val.map (·.val.map (·.bv)) = (x.val.map (·.val.map (·.bv))).map (keccak 24))
    (i : Nat) (hi : i < 2) : lanes (z.val[i]!) = keccak 24 (lanes (x.val[i]!)) := by
  have hz : z.val.length = 2 := by simp
  have hx : x.val.length = 2 := by simp
  have := congrArg (·[i]!) h
  simp only at this
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i (by simp; omega)] at this
  simp only [List.getElem_map] at this
  rw [getElem!_pos _ i (by omega), getElem!_pos _ i (by omega)]
  exact this

/-- `keccak_nof4_f1600_spec`: the first `N` of four states. -/
theorem keccak_nof4_f1600_spec (h : RunsSha3) (N : Usize) (hN : 1 ≤ N.val ∧ N.val ≤ 4)
    (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.aarch64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600 N a mid.sha3.RC ⦃ r =>
      (states r).take N.val = ((states a).take N.val).map (keccak 24) ⦄ := by
  have hl : (states a).length = 4 := by simp
  obtain ⟨-, -, t, ht⟩ := id h
  unfold low.aarch64.sha3_keccak_nof4_f1600.sha3_keccak_nof4_f1600
  rw [ht, bind_ok]
  cases t with
  | none =>
    apply WP.spec_mono (keccak_loop_spec (states a) N.val hN.2 _ a (by simp) rfl (by simp))
    intro r hr
    rw [hr, take_loop _ _ (by omega)]
  | some t =>
    simp only
    step with Std.Array.to_slice_mut_spec a as ⟨s, back, hs, hback⟩
    step with as_chunks_mut_two_spec s (by simp [Slice.length, hs]) as
      ⟨pairs, rest, cback, hpairs, hrest, hcback⟩
    have ha4 : a.val.length = 4 := by simp
    have hp2 : pairs.val.length = 2 := by
      have := congrArg List.length hpairs; simpa using this
    have hpe : ∀ i (hi : i < 2), (pairs.val[i]!).val = [a.val.take 2, a.val.drop 2][i]! := by
      intro i hi
      have := congrArg (·[i]!) hpairs
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show i < pairs.val.length by omega), Option.map_some,
        Option.getD_some, hs] at this ⊢
      exact this
    have hp0 : (pairs.val[0]!).val = a.val.take 2 := hpe 0 (by omega)
    have hp1 : (pairs.val[1]!).val = a.val.drop 2 := hpe 1 (by omega)
    -- The view writes two pairs back in order.
    have hflat : ∀ p : Slice (Std.Array (Std.Array U64 25#usize) 2#usize), p.val.length = 2 →
        (back (cback (p, rest))).val = (p.val[0]!).val ++ (p.val[1]!).val := by
      intro p hp
      obtain ⟨p0, p1, hp'⟩ := List.length_eq_two.1 hp
      have hc := hcback p hp
      rw [hp'] at hc
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
      rw [hback, Std.Array.from_slice_val _ _ (by rw [hc]; simp), hc, hp']
      rfl
    have hfull : (back (cback (pairs, rest))).val = a.val := by
      rw [hflat pairs hp2, hp0, hp1, List.take_append_drop]
    obtain hN1 | hN2 | hN3 | hN' : N.val = 1 ∨ N.val = 2 ∨ N.val = 3 ∨ N.val = 4 := by omega
    · simp only [hN1]
      step with Std.Array.index_mut_usize_spec as ⟨x, imb, hx, himb⟩
      step with sha3_keccak_f1600_alt_spec x _ rc_bv as ⟨y, hy⟩
      apply take_eq_map_take _ _ _ _ (by simp) (by simp)
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      rw [states_getElem! _ 0 (by omega), states_getElem! a 0 (by omega), himb, Std.Array.set_val_eq,
        getElem!_set' _ _ _ _ (by simp), show (0#usize : Usize).val = 0 from rfl, ite_eq_left rfl, lanes,
        hy, hx, ← getElem!_pos, hfull]
    · simp only [hN2]
      step with Slice.index_mut_usize_spec as ⟨x, imb, hx, himb⟩
      step with sha3_keccak2_f1600_spec x _ rc_bv as ⟨z, hz⟩
      have hp' : (imb z).val.length = 2 := by rw [himb]; simp [hp2]
      have hx0 : x.val = a.val.take 2 := by rw [hx, ← getElem!_pos, hp0]
      apply take_eq_map_take _ _ _ _ (by simp) (by simp)
      intro i hi
      rw [states_getElem! _ i (by omega), states_getElem! a i (by omega), hflat _ hp', himb,
        Slice.set_val_eq, getElem!_set' _ _ _ _ (by omega), getElem!_set' _ _ _ _ (by omega)]
      simp only [show (0#usize : Usize).val = 0 from rfl, ite_true, show ¬((0 : Nat) = 1) by omega,
        ite_false, getElem!_append']
      rw [ite_eq_left (by simp; omega), pair_lanes hz i (by omega), hx0, getElem!_take' _ _ _ (by omega)]
    · simp only [hN3]
      step with Slice.index_mut_usize_spec as ⟨x, imb, hx, himb⟩
      step with sha3_keccak2_f1600_spec x _ rc_bv as ⟨z, hz⟩
      have hp' : (imb z).val.length = 2 := by rw [himb]; simp [hp2]
      have hx0 : x.val = a.val.take 2 := by rw [hx, ← getElem!_pos, hp0]
      have hr1 : (back (cback (imb z, rest))).val = z.val ++ a.val.drop 2 := by
        rw [hflat _ hp', himb, Slice.set_val_eq, getElem!_set' _ _ _ _ (by omega),
          getElem!_set' _ _ _ _ (by omega)]
        simp only [show (0#usize : Usize).val = 0 from rfl, ite_true,
          show ¬((0 : Nat) = 1) by omega, ite_false, hp1]
      step with Std.Array.index_mut_usize_spec as ⟨y, imb2, hy, himb2⟩
      step with sha3_keccak_f1600_alt_spec y _ rc_bv as ⟨w, hw⟩
      apply take_eq_map_take _ _ _ _ (by simp) (by simp)
      intro i hi
      rw [states_getElem! _ i (by omega), states_getElem! a i (by omega), himb2,
        Std.Array.set_val_eq, getElem!_set' _ _ _ _ (by simp; omega)]
      simp only [show (2#usize : Usize).val = 2 from rfl]
      by_cases hi2 : i = 2
      · subst hi2
        rw [ite_eq_left rfl, lanes, hw, hy, ← getElem!_pos, hr1, getElem!_append', ite_eq_right (by simp),
          getElem!_drop']
        simp
      · rw [ite_eq_right (Ne.symm hi2), hr1, getElem!_append', ite_eq_left (by simp; omega),
          pair_lanes hz i (by omega), hx0, getElem!_take' _ _ _ (by omega)]
    · simp only [hN']
      step with Slice.index_mut_usize_spec as ⟨x, imb, hx, himb⟩
      step with sha3_keccak2_f1600_spec x _ rc_bv as ⟨z, hz⟩
      step with Slice.index_mut_usize_spec (imb z) 1#usize (by rw [himb]; simp [Slice.length, hp2])
        as ⟨x2, imb2, hx2, himb2⟩
      step with sha3_keccak2_f1600_spec x2 _ rc_bv as ⟨z2, hz2⟩
      have hx0 : x.val = a.val.take 2 := by rw [hx, ← getElem!_pos, hp0]
      have hx1 : x2.val = a.val.drop 2 := by
        rw [hx2, ← getElem!_pos, himb, Slice.set_val_eq, getElem!_set' _ _ _ _ (by omega)]
        simp only [show (0#usize : Usize).val = 0 from rfl, show ¬((0 : Nat) = 1) by omega,
          ite_false, hp1]
      have hp' : (imb2 z2).val.length = 2 := by rw [himb2, himb]; simp [hp2]
      have hr : (back (cback (imb2 z2, rest))).val = z.val ++ z2.val := by
        obtain ⟨q0, q1, hq⟩ := List.length_eq_two.1 hp2
        rw [hflat _ hp', himb2, himb, Slice.set_val_eq, Slice.set_val_eq, hq]
        rfl
      have hzl : z.val.length = 2 := by simp
      apply take_eq_map_take _ _ _ _ (by simp) (by simp)
      intro i hi
      rw [states_getElem! _ i (by omega), states_getElem! a i (by omega), hr, getElem!_append', hzl]
      by_cases hi2 : i < 2
      · rw [ite_eq_left hi2, pair_lanes hz i hi2, hx0, getElem!_take' _ _ _ hi2]
      · rw [ite_eq_right hi2, pair_lanes hz2 _ (by omega), hx1, getElem!_drop',
          show 2 + (i - 2) = i by omega]

/-- `keccak4_f1600_spec`: four states. -/
theorem keccak4_f1600_spec (h : RunsSha3) (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.aarch64.sha3_keccak4_f1600_mux.sha3_keccak4_f1600 a mid.sha3.RC ⦃ r =>
      states r = (states a).map (keccak 24) ⦄ := by
  unfold low.aarch64.sha3_keccak4_f1600_mux.sha3_keccak4_f1600
  apply WP.spec_mono (keccak_nof4_f1600_spec h 4#usize (by simp) a)
  intro r hr
  have hr4 : (states r).length = 4 := by simp
  have ha4 : (states a).length = 4 := by simp
  rwa [show (4#usize : Usize).val = 4 from rfl, List.take_of_length_le (by omega),
    List.take_of_length_le (by omega)] at hr

end rind.aarch64
