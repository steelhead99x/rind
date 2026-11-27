import Aeneas
import Rind.Core
import Rind.Keccak
open Aeneas Aeneas.Std

/-!
# Keccak-f[1600] states as lanes

The translations' Keccak-f states, as `Rind.Keccak`'s lists of lanes, and
what permuting the first of four states one at a time does to them, and
how eight split into two groups of four, which each backend's dispatch proof (`Rind/<Arch>/KeccakDispatch.lean`,
`Rind/Portable/Keccak.lean`) shares.
-/

namespace rind.spec

/-- A state's lanes. -/
abbrev lanes (a : Std.Array U64 25#usize) : List (BitVec 64) := a.val.map (·.bv)

/-- Four states' lanes. -/
abbrev states (a : Std.Array (Std.Array U64 25#usize) 4#usize) : List (List (BitVec 64)) :=
  a.val.map lanes

/-- Eight states' lanes. -/
abbrev states8 (a : Std.Array (Std.Array U64 25#usize) 8#usize) : List (List (BitVec 64)) :=
  a.val.map lanes

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

theorem take_map_drop_four {α : Type} (f : α → α) (S : List α) (hS : S.length = 4) :
    (S.take 4).map f ++ S.drop 4 = S.map f := by
  rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil]

theorem take_loop (S : List (List (BitVec 64))) (N : Nat) (hN : N ≤ S.length) :
    ((S.take N).map (keccak 24) ++ S.drop N).take N = (S.take N).map (keccak 24) := by
  rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp)]

/-- `as_chunks_mut::<4>` of eight states: two groups of four, nothing left,
and a view that writes the groups back in order. -/
theorem as_chunks_mut_four_spec {T : Type} (s : Slice T) (hs : s.length = 8) :
    core.slice.Slice.as_chunks_mut 4#usize s ⦃ v back =>
      v.1.val.map (·.val) = [s.val.take 4, s.val.drop 4] ∧ v.2.val = [] ∧
      ∀ p : Slice (Std.Array T 4#usize), p.length = 2 →
        (back (p, v.2)).val = p.val.flatMap (·.val) ⦄ := by
  have hl : s.val.length = 8 := hs
  simp only [core.slice.Slice.as_chunks_mut, core.slice.Slice.as_chunks, Slice.length, hl,
    show (4#usize : Usize).val = 4 from rfl, show ¬(4 = 0) from by decide, ite_false]
  simp only [bind_ok, WP.spec_ok, List.ofFn_succ, List.ofFn_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp; omega
  · simp [List.drop_of_length_le (show s.val.length ≤ 2 * 4 by omega)]
  · intro p hp
    have hp' : p.val.length = 2 := hp
    have hd : List.drop (8 / 4 * 4) s.val = [] := List.drop_of_length_le (by omega)
    have hlen : (p.val.flatMap (·.val)).length = 8 := by
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

theorem getElem!_append_cond {α : Type} [Inhabited α] (l1 l2 : List α) (i : Nat) :
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

theorem states8_getElem! (r : Std.Array (Std.Array U64 25#usize) 8#usize) (i : Nat) (hi : i < 8) :
    (states8 r)[i]! = lanes (r.val[i]!) := by
  rw [getElem!_pos _ i (by simp [hi]), getElem!_pos _ i (by simp [hi])]
  simp

/-- Each of a list's first `n` is `f` of another's if its first `n` are. -/
theorem getElem!_of_take_map {α : Type} [Inhabited α] (f : α → α) (L M : List α) (n i : Nat)
    (h : L.take n = (M.take n).map f) (hi : i < n) (hL : i < L.length) (hM : i < M.length) :
    L[i]! = f M[i]! := by
  have := congrArg (·[i]?) h
  simp only [List.getElem?_take, hi, ite_true, List.getElem?_map, List.getElem?_eq_getElem hL,
    List.getElem?_eq_getElem hM, Option.map_some, Option.some.injEq] at this
  rw [getElem!_pos L i hL, getElem!_pos M i hM, this]

end rind.spec
