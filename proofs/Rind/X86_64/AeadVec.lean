import Rind.X86_64.AeadDispatch
open Aeneas Aeneas.Std Result

/-!
# `Vec<u8>` as an AEAD buffer

The `AsMut<[u8]>` and `Extend<&u8>` impls through which the AEAD API's
`seal_in_place_append_tag` takes a `Vec<u8>`, and what they do: the view is
the whole vector, and `extend` appends a slice.
-/

namespace rind.x86_64

/-- `Vec<u8>`'s `AsMut<[u8]>`. -/
abbrev VecAsMut : core.convert.AsMut (alloc.vec.Vec U8) (Slice U8) :=
  alloc.vec.Vec.Insts.CoreConvertAsMutSlice U8 alloc.alloc.Global

/-- `Vec<u8>`'s `Extend<&u8>`. -/
abbrev VecExtend : core.iter.traits.collect.Extend (alloc.vec.Vec U8) U8 :=
  alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT alloc.alloc.Global core.marker.CopyU8

theorem vec_as_mut (v : alloc.vec.Vec U8) :
    alloc.vec.Vec.Insts.CoreConvertAsMutSlice.as_mut alloc.alloc.Global v = ok (alloc.vec.Vec.deref_mut v) :=
  rfl

private theorem slice_next_lt {T : Type} (s : Slice T) (i : Nat) (h : i < s.length) :
    core.slice.iter.IteratorSliceIter.next ⟨s, i⟩ = ok (some s.val[i], ⟨s, i + 1⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  rw [dite_eq_left (by simpa [Slice.len, Slice.length] using h)]
  rfl

private theorem slice_next_ge {T : Type} (s : Slice T) (i : Nat) (h : ¬ i < s.length) :
    core.slice.iter.IteratorSliceIter.next ⟨s, i⟩ = ok (none, ⟨s, i⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  rw [dite_eq_right (by simpa [Slice.len, Slice.length] using h)]

/-- A slice's iterator from `i` yields the elements from `i`. -/
theorem iterToList_slice {T : Type} (s : Slice T) (i : Nat) (acc : List T) :
    alloc.vec.FromIteratorVec.iterToList (core.iter.traits.iterator.IteratorSliceIter T) ⟨s, i⟩ acc =
      ok (acc.reverse ++ s.val.drop i) := by
  rw [alloc.vec.FromIteratorVec.iterToList]
  by_cases h : i < s.length
  · simp only [core.iter.traits.iterator.IteratorSliceIter, slice_next_lt s i h, bind_ok]
    show alloc.vec.FromIteratorVec.iterToList (core.iter.traits.iterator.IteratorSliceIter T)
      ⟨s, i + 1⟩ (s.val[i] :: acc) = _
    rw [iterToList_slice s (i + 1)]
    have hi : i < s.val.length := h
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hi]
  · simp only [core.iter.traits.iterator.IteratorSliceIter, slice_next_ge s i h, bind_ok]
    show ok acc.reverse = _
    simp [List.drop_eq_nil_of_le (show s.val.length ≤ i by simp [Slice.length] at h; omega)]
termination_by s.length - i
decreasing_by omega

private theorem clone_u8 (l : List U8) :
    List.clone (liftFun1 core.clone.impls.CloneU8.clone) l = ok ⟨l, rfl⟩ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.clone, List.mapM_with_length] at ih ⊢
    rw [ih]
    simp only [liftFun1, core.clone.impls.CloneU8.clone, bind_tc_ok]
    rfl

/-- `Vec<u8>`'s `extend` of a slice is its `extend_from_slice`. -/
theorem vec_extend (v : alloc.vec.Vec U8) (s : Slice U8) :
    VecExtend.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) v s =
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s := by
  simp only [alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend, alloc.vec.Vec.extend_from_slice,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok, iterToList_slice,
    List.reverse_nil, List.nil_append, List.drop_zero, clone_u8]
  by_cases h : v.length + s.val.length ≤ Usize.max
  · rw [dite_eq_left h, dite_eq_left (by simpa [Slice.length] using h), bind_tc_ok]
  · rw [dite_eq_right h, dite_eq_right (by simpa [Slice.length] using h)]

end rind.x86_64
