import Rind.Aarch64.Funs
import Rind.Aarch64.VgSha512
import Rind.Sha2Lemmas
open Aeneas Aeneas.Std Result rind.spec

/-!
# rind's SHA-512 block functions on aarch64

aws-lc-verification's NSym proof that aws-lc's `sha512_block_data_order_nohw`
computes `sha512_block_data_order_array_spec`, at the revision rind's README
cites (79730247), restated as an axiom about the opaque Rust wrapper
`compress_nohw` around rind's copy of that routine. rind copies it from aws-lc
5ed12cce, whose `sha512-armv8.pl` is the proven c21d40da's.

aws-lc-verification's SAW proof of the C assumes that spec on aarch64 and its
NSym proof discharges it, with the caveats its README lists: NSym's spec of
the block loop, `processBlocks_rec`, recurses from the last block where
cryptol-specs' `processBlocks` loops from the first (ArmSpecGap), which
`compress` restates as the first; and its block function,
`processBlock_Common_rec`, is `processBlock_Common` by `SHA512rec.icry`'s
`:prove processBlock_Common_equiv`. The spec's preconditions hold for every
call `compress_nohw`'s safety contract allows: `state` and `blocks` are
distinct allocations, and `blocks` is a whole number of blocks, at least one
and, as a slice, fewer than 2^57.

The restatement, and that rind's naked function is aws-lc's object code with
the wrapper passing the pointers and block count the spec names, are trusted.

On the SHA-512 instructions rind runs pyca/verified-garbage's routine
instead, whose contract `Rind.Aarch64.VgSha512` restates.
-/

namespace rind.aarch64

/-- `sha512_block_data_order_array_spec`, which aws-lc-verification assumes of
`sha512_block_data_order_nohw` in its SAW proof,
https://github.com/awslabs/aws-lc-verification/blob/797302470c1703cbb1a3a6fa98daffef0bfd3d80/SAW/proof/SHA512/SHA512-common.saw#L61
with the spec at
https://github.com/awslabs/aws-lc-verification/blob/797302470c1703cbb1a3a6fa98daffef0bfd3d80/SAW/proof/SHA512/SHA512-common-specs.saw#L101 ,
and its NSym proof discharges, whose postcondition is at
https://github.com/awslabs/aws-lc-verification/blob/797302470c1703cbb1a3a6fa98daffef0bfd3d80/NSym/proof/proofs/SHA512/sha512_block_data_order_unbounded.ml#L191 :
for `num` blocks, at least one, the state becomes cryptol-specs'
`processBlocks state data 0 num`, which `compress` restates. -/
@[step]
axiom compress_nohw_spec (state : Std.Array U64 8#usize) (blocks : Slice U8)
    (hm : blocks.length % 128 = 0) (hn : blocks.length ≠ 0) :
    low.aarch64.sha512.compress_nohw state blocks ⦃ r => r.val = compress state.val blocks.val ⦄

/-- rind's SHA-512 dispatch checks the CPU for the SHA-512 instructions without
failing, and its entry guard and the debug build's check that one is held
pass. None reads an input. -/
def RunsSha512 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
    ∃ c, low.aarch64.cpu.HaveSha3.check = ok c

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

/-- The dispatch runs either routine on a whole number of blocks, and returns
the state for none. -/
@[step]
theorem sha512_compress_blocks_spec (h : RunsSha512) (state : Std.Array U64 8#usize)
    (blocks : Slice U8) (hm : blocks.length % 128 = 0) :
    low.aarch64.sha512.sha512_compress_blocks state blocks ⦃ r =>
      r.val = compress state.val blocks.val ⦄ := by
  obtain ⟨-, -, c, hc⟩ := h
  unfold low.aarch64.sha512.sha512_compress_blocks
  step*
  · simp_all [compress_short]
  · rw [hc]
    cases c with
    | none =>
      step with compress_nohw_spec
      simp_all
    | some c =>
      step with compress_hw_spec
      simp_all

end rind.aarch64
