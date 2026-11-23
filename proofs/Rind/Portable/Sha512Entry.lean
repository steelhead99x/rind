import Rind.Portable.Blockwise
import Rind.Sha2Lemmas
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-512's block function as the SHA-512 proof calls it

`Rind.Portable.Sha512`, which `admin/prove` writes from x86_64's, takes
`RunsSha512` and the block function's contract from here, as x86_64's takes
them from `Rind.X86_64.AwsLc`. This file is apart from
`Rind.Portable.ShaBlocks` so that SHA-1's and SHA-256's proofs, which import
that, do not see these entry-guard lemmas.
-/

namespace rind.portable

/-- rind's SHA-512 has no CPU dispatch here, so this assumes that its entry
guard and the debug build's check that one is held pass, and the contract of
its block function, `low::generic::sha512`, aws-lc's C in Rust, which no
proof covers yet: FIPS 180-4's over every whole block. None reads an input. -/
def RunsSha512 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
    ∀ (state : Std.Array U64 8#usize) (blocks : Slice U8), blocks.length % 128 = 0 →
      low.generic.sha512.sha512_compress_blocks state blocks ⦃ r =>
        r.val = compress state.val blocks.val ⦄

@[step]
theorem sha512_new_secret_spec (h : RunsSha512) : low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  simp [he]

@[step]
theorem assert_held_spec (h : RunsSha512) : low.entry.Entry.assert_held ⦃ _ => True ⦄ := by
  obtain ⟨-, he, -⟩ := h
  simp [he]

/-- The entry guard is held, as `ct_equal` checks, which every target's
`RunsSha512` states. -/
theorem RunsSha512.held (h : RunsSha512) : low.entry.Entry.assert_held = ok () := h.2.1

/-- SHA-512's block function as the backend exports it, which calls
`low::generic::sha512`'s, over a whole number of blocks. -/
@[step]
theorem sha512_compress_blocks_spec (h : RunsSha512) (state : Std.Array U64 8#usize)
    (blocks : Slice U8) (hm : blocks.length % 128 = 0) :
    low.portable.sha.sha512_compress_blocks state blocks ⦃ r =>
      r.val = compress state.val blocks.val ⦄ := by
  unfold low.portable.sha.sha512_compress_blocks
  exact h.2.2 state blocks hm

end rind.portable
