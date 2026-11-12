import Aeneas
import Rind.Keccak
open Aeneas Aeneas.Std

/-!
# Keccak-f[1600] states as lanes

The translations' Keccak-f states, as `Rind.Keccak`'s lists of lanes, and
what permuting the first of four states one at a time does to them, which
each backend's dispatch proof (`Rind/<Arch>/KeccakDispatch.lean`,
`Rind/Portable/Keccak.lean`) shares.
-/

namespace rind.spec

/-- A state's lanes. -/
abbrev lanes (a : Std.Array U64 25#usize) : List (BitVec 64) := a.val.map (·.bv)

/-- Four states' lanes. -/
abbrev states (a : Std.Array (Std.Array U64 25#usize) 4#usize) : List (List (BitVec 64)) :=
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

end rind.spec
