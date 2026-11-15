import Rind.Portable.Hacl
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-1 and SHA-256's block functions on the portable backend

SHA-256's block function is HACL*'s, whose contract `Rind.Portable.Hacl`
restates, so the SHA-256 theorems take `Sha256Blocks`, only that the entry
checks pass. No proof covers SHA-1's, `low::generic::sha1`, so the SHA-1
theorems take `Sha1Blocks`, its contract, as on x86_64 and aarch64.
`Rind.X86_64.ShaBlocks` states the same names for x86_64.
-/

namespace rind.portable

/-- What the SHA-1 theorems assume of the code below rind's padding on the
portable backend: the block function computes FIPS 180-4's, and the entry
checks pass. None reads an input. -/
structure Sha1Blocks : Prop where
  entry : ∃ e, low.entry.Entry.new_secret = ok e
  held : low.entry.Entry.assert_held = ok ()
  sha1 : Compresses sha1.compress low.generic.sha1.sha1_compress_blocks

/-- What the SHA-256 theorems assume on the portable backend: the entry
checks pass. Neither reads an input. -/
structure Sha256Blocks : Prop where
  entry : ∃ e, low.entry.Entry.new_secret = ok e
  held : low.entry.Entry.assert_held = ok ()

/-- SHA-256's block function as `Sha256State` calls it. -/
theorem sha256_block_spec (hb : Sha256Blocks) : Compresses sha256.compress mid.sha2.Sha256State.compress := by
  intro h b hl
  unfold mid.sha2.Sha256State.compress
  rw [hb.held]
  simpa using sha256_compress_blocks_spec h b hl

/-- SHA-1's block function as `Sha1State` calls it. -/
theorem sha1_block_spec (hb : Sha1Blocks) :
    Compresses sha1.compress mid.sha1.Sha1State.compress := by
  intro h b hl
  unfold mid.sha1.Sha1State.compress
  rw [hb.held]
  simpa using hb.sha1 h b hl

/-- What `pad` writes after `rest` is a whole number of blocks with it. -/
theorem padded_mod (rest : Slice U8) (length : Std.Array U8 8#usize) :
    (rest.val ++ [128#u8] ++ List.replicate (padZeros (64#usize).val (8#usize).val rest.length) 0#u8 ++
      length.val).length % 64 = 0 := by
  have hl : length.val.length = 8 := length.property
  have := pad_mod (N := 64) (L := 8) rest.val.length (by decide)
  rw [show rest.length = rest.val.length from rfl]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate, hl]
  have h64 : (64#usize).val = 64 := by simp
  have h8 : (8#usize).val = 8 := by simp
  rw [h64, h8]
  omega

/-- SHA-1's padded last blocks. -/
theorem sha1_compress_padded_spec (hb : Sha1Blocks) (P : List U8) (state : Std.Array U32 5#usize)
    (message : Slice U8) (length : Std.Array U8 8#usize)
    (hR : Absorbed sha1.compress sha1.H0 P state) :
    low.portable.sha.sha1_compress_padded state message length ⦃ h' =>
      Absorbed sha1.compress sha1.H0
        (P ++ message.val ++ [128#u8] ++ List.replicate (padZeros 64 8 message.length) 0#u8 ++
          length.val) h' ⦄ := by
  unfold low.portable.sha.sha1_compress_padded
  step with split_tail_spec (N := 64#usize) (L := 8#usize) message (by decide) (by scalar_tac)
    (by decide) as ⟨bl, re, hs1, hs2, hs3, hs4⟩
  step with hb.sha1 state bl hs1 as ⟨st1, h1⟩
  step with pad_spec (N := 64#usize) (L := 8#usize) re length (by decide) (by scalar_tac)
    (by decide) hs3 as ⟨s, _, hs⟩
  apply WP.spec_mono (hb.sha1 st1 s (by rw [Slice.length, hs]; exact padded_mod re length))
  intro h' hh
  have h2 := absorbed_append (absorbed_append hR hs1 h1)
    (b := s.val) (by rw [hs]; exact padded_mod re length) hh
  rw [hs, hs4] at h2
  rw [← hs2]
  simpa [List.append_assoc] using h2

/-- SHA-256's digest of what `state` has absorbed followed by `message`. -/
theorem sha256_finish_spec (_hb : Sha256Blocks) (P : List U8) (state : Std.Array U32 8#usize)
    (message : Slice U8) (length : Std.Array U8 8#usize)
    (hR : Absorbed sha256.compress sha256.H0 P state) :
    low.portable.sha.sha256_finish state message length ⦃ r =>
      bv r.val = sha256Finished P message.val length.val ⦄ := by
  unfold low.portable.sha.sha256_finish
  step with split_tail_spec (N := 64#usize) (L := 8#usize) message (by decide) (by scalar_tac)
    (by decide) as ⟨bl, re, hs1, hs2, hs3, hs4⟩
  step with sha256_compress_blocks_spec state bl hs1 as ⟨st1, h1⟩
  step with pad_spec (N := 64#usize) (L := 8#usize) re length (by decide) (by scalar_tac)
    (by decide) hs3 as ⟨s, _, hs⟩
  step with sha256_compress_blocks_spec st1 s (by rw [Slice.length, hs]; exact padded_mod re length)
    as ⟨st2, h2⟩
  apply WP.spec_mono (sha256_digest_spec st2)
  intro r hr
  have hA := absorbed_append (absorbed_append hR hs1 h1)
    (b := s.val) (by rw [hs]; exact padded_mod re length) h2
  have hP : P ++ bl.val ++ s.val = P ++ message.val ++ [128#u8] ++
      List.replicate (padZeros 64 8 message.length) 0#u8 ++ length.val := by
    rw [hs, ← hs2, ← hs4]
    simp [List.append_assoc]
  rw [hP] at hA
  rw [hr, hA.1]
  rfl

end rind.portable
