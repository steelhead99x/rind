import Rind.X86_64.Funs
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.spec

/-!
# X25519's conversions between bytes and limbs, `mid::util`

What the X25519 proof reads and writes keys through: 32 little-endian bytes
as four 64-bit limbs, and back. `admin/prove` writes the aarch64 and armv7
copies of this file by renaming the target.
-/

namespace rind.x86_64

/-! ## Byte and limb conversions, `mid::util` -/

theorem le_to_u64x4_loop_spec
    (z : core.iter.adapters.zip.Zip (core.ops.range.Range Std.Usize) (core.slice.iter.ChunksExact Std.U8))
    (r : Std.Array Std.U64 4#usize) (F : List Nat)
    (hs : z.fst.start.val ≤ 4) (he : z.fst.end.val = 4)
    (hc : z.snd.chunks.length = 4 - z.fst.start.val)
    (h8 : ∀ c ∈ z.snd.chunks, c.length = 8)
    (hF : (r.val.take z.fst.start.val).map (·.val) ++ z.snd.chunks.map (leNat ·.val) = F) :
    mid.util.little_endian_to_u64x4_loop z r ⦃ r' => r'.val.map (·.val) = F ⦄ := by
  unfold mid.util.little_endian_to_u64x4_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.fst.start.val)
    (fun x => x.1.fst.start.val ≤ 4 ∧ x.1.fst.end.val = 4 ∧
      x.1.snd.chunks.length = 4 - x.1.fst.start.val ∧ (∀ c ∈ x.1.snd.chunks, c.length = 8) ∧
      (x.2.val.take x.1.fst.start.val).map (·.val) ++ x.1.snd.chunks.map (leNat ·.val) = F)
  · rintro ⟨⟨rg, ce⟩, r⟩ ⟨hs, he, hc, h8, hF⟩
    simp only at hs he hc h8 hF ⊢
    unfold mid.util.little_endian_to_u64x4_loop.body
    unfold core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    step*
    obtain ⟨o, rg'⟩ := x
    simp only at x_post x_post1
    split_ifs at x_post with hlt
    · obtain ⟨rfl, hst⟩ := x_post
      rcases hch : ce.chunks with _ | ⟨c, rest⟩
      · simp [hch] at hc; omega
      simp only [core.slice.iter.IteratorChunksExact.next, hch]
      have hc8 : c.length = 8 := h8 c (by simp [hch])
      step*
      · rcases r1 with a | _
        · exact ⟨a, rfl⟩
        · exact absurd hc8 r1_post
      · subst r1_post
        obtain ⟨hac, -⟩ := r1_post
        have hi : i.val = leNat c.val := by rw [val_of_fromLEBytes _ i i_post, hac]
        have hlen : (r.val).length = 4 := r.property
        refine ⟨by omega, by simp [x_post1, he], by simp [hch] at hc; omega,
          fun c' hc' => h8 c' (by simp [hch, hc']), ?_, by omega⟩
        rw [hst, a1_post, Std.Array.set_val_eq, List.take_add_one, List.getElem?_set_self (by omega),
          List.take_set_of_le (by omega)]
        rw [hch] at hF
        simp only [List.map_append, List.map_cons, Option.toList_some, List.map_nil, hi] at hF ⊢
        simpa using hF
    · obtain ⟨rfl, hst⟩ := x_post
      have hst4 : rg.start.val = 4 := by omega
      have hnil : ce.chunks = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hlen : (r.val).length = 4 := r.property
      rw [hnil, hst4, List.take_of_length_le (by omega)] at hF
      simpa [WP.spec_ok] using hF
  · exact ⟨hs, he, hc, h8, hF⟩

@[step]
theorem le_to_u64x4_spec (b : Std.Array U8 32#usize) :
    mid.util.little_endian_to_u64x4 b ⦃ w => wordsNat w.val = leNat b.val ⦄ := by
  unfold mid.util.little_endian_to_u64x4
  simp only [core.slice.Slice.chunks_exact, show (8#usize).val > 0 by decide, ↓reduceDIte]
  step*
  simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter, ok.injEq] at iter_post
  subst s_post iter_post
  have hflat := toChunksExact_flatten 8 (by decide) b.val
  have hlen8 := toChunksExact_length 8 (by decide) b.val
  have hrem := toChunksExact_remainder 8 (by decide) b.val
  set C := (List.toChunksExact 8 (by decide) b.val).1
  have hb : b.val.length = 32 := b.property
  have hfl := length_flatten_of_length C 8 hlen8
  have hC : C.length = 4 := by
    have := congrArg List.length hflat
    simp only [List.length_append, hfl, hb] at this
    omega
  have hR : (List.toChunksExact 8 (by decide) b.val).2 = [] := by
    have := congrArg List.length hflat
    simp only [List.length_append, hfl, hb, hC] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  rw [hR, List.append_nil] at hflat
  apply WP.spec_mono (le_to_u64x4_loop_spec iter _ (C.map leNat) ?_ ?_ ?_ ?_ ?_)
  · intro w hw
    rw [wordsNat, hw, ← leNat_flatten C hlen8, hflat]
  · simp [iter_post1]
  · simp [iter_post1]
  · simpa [iter_post1, other'_post, C] using hC
  · simp only [other'_post, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    rintro _ ⟨c, hc, rfl⟩
    simpa [C] using hlen8 c (by simpa [C] using hc)
  · simp [iter_post1, other'_post, C]

/-- The bytes `u64::to_le_bytes` writes. -/
def leBytes (w : U64) : List U8 := w.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8)

theorem u64x4_to_le_loop_spec
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Std.U64))
    (r : Std.Array U8 32#usize) (V : List U64) (hVl : V.length = 4)
    (hV : it.iter.slice.val = V) (hi : it.iter.i = it.count.val) (hk : it.count.val ≤ 4)
    (hr : r.val.take (8 * it.count.val) = (V.take it.count.val).flatMap leBytes) :
    mid.util.u64x4_to_little_endian_loop it r ⦃ r' => r'.val = V.flatMap leBytes ⦄ := by
  unfold mid.util.u64x4_to_little_endian_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.count.val)
    (fun x => x.1.iter.slice.val = V ∧ x.1.iter.i = x.1.count.val ∧ x.1.count.val ≤ 4 ∧
      x.2.val.take (8 * x.1.count.val) = (V.take x.1.count.val).flatMap leBytes)
  · rintro ⟨it, r⟩ ⟨hV, hi, hk, hr⟩
    simp only at hV hi hk hr ⊢
    unfold mid.util.u64x4_to_little_endian_loop.body
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next]
    have hsl : it.iter.slice.len.val = 4 := by simp [Slice.len, hV, hVl]
    split
    · rename_i hlt
      have hk4 : it.count.val < 4 := by omega
      step*
      · rw [s_post1, s1_post]
        simp [i3_post, i2_post, i1_post, Slice.length]
        omega
      · have ha8 : (a.val).length = 8 := a.property
        have hw : it.iter.slice[it.iter.i] = V[it.count.val] := by
          subst hV
          show it.iter.slice.val[it.iter.i]'(by simp [Slice.len] at hlt; omega) = _
          simp only [hi]
        refine ⟨hV, by omega, by omega, ?_, by omega⟩
        rw [s_post2, s2_post, s1_post]
        have hr32 : (r.val).length = 32 := r.property
        have := take_setSlice! r.val a.val (i1.val) (by rw [ha8, i1_post]; omega)
        simp only [Array.val_to_slice, ha8] at this ⊢
        rw [show 8 * x.val = i1.val + 8 by rw [x_post, i1_post]; ring, this, i1_post,
          show it.count.val * 8 = 8 * it.count.val by ring, hr, x_post, List.take_add_one,
          List.flatMap_append, List.getElem?_eq_getElem (by omega)]
        simp [a_post, hw, leBytes]
    · rename_i hlt
      have hk4 : it.count.val = 4 := by omega
      have hr32 : (r.val).length = 32 := r.property
      rw [hk4, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hr
      simpa [WP.spec_ok] using hr
  · exact ⟨hV, hi, hk, hr⟩

@[step]
theorem u64x4_to_le_spec (v : Std.Array U64 4#usize) :
    mid.util.u64x4_to_little_endian v ⦃ b => leNat b.val = wordsNat v.val ⦄ := by
  unfold mid.util.u64x4_to_little_endian
  simp only [core.slice.Slice.iter]
  step*
  have hv : (v.val).length = 4 := v.property
  apply WP.spec_mono (u64x4_to_le_loop_spec iter _ v.val hv ?_ ?_ ?_ ?_)
  · intro b hb
    have h8 : ∀ c ∈ v.val.map leBytes, c.length = 8 := by
      simp [leBytes]
    rw [hb, List.flatMap_def, leNat_flatten _ h8, wordsNat, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w _
    exact leNat_toLEBytes w
  all_goals simp [iter_post, iter_post1, s_post, Array.val_to_slice]

@[step]
theorem le_slice_to_u64x4_spec (s : Slice U8) :
    mid.util.little_endian_slice_to_u64x4 s ⦃ o =>
      if s.length = 32 then ∃ w, o = some w ∧ wordsNat w.val = leNat s.val else o = none ⦄ := by
  unfold mid.util.little_endian_slice_to_u64x4
  step*
  rcases r with a | _
  · obtain ⟨ha, hl⟩ := r_post
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    step*
  · simp [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, r_post]

end rind.x86_64
