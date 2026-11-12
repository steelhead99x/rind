import Rind.Aarch64.Funs
import Rind.S2nSha512
open Aeneas Aeneas.Std Result rind.spec

/-!
# aws-lc's SHA-512 contract on aarch64

aws-lc-verification's NSym proof that aws-lc's `sha512_block_data_order_nohw`
computes `sha512_block_data_order_array_spec`, at the revision rind's README
cites (79730247), restated as an axiom about the opaque Rust wrapper
`compress_nohw` around rind's copy of that routine. rind copies it from aws-lc
91c93a8e, whose `sha512-armv8.pl` is the proven c21d40da's.

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

For the routine for the SHA-512 instructions, `sha512_block_data_order_hw`,
NSym's proof asserts the digest in registers at the end of its block loop,
before the instruction that stores it to `state`, so rind proves the routine
itself: its HOL Light proof `SHA512_HW_SUBROUTINE_CORRECT`, in
`proofs/hol-light/aarch64/sha512_block_data_order_hw.ml` at rind's commit, that
rind's naked function, as rind's build emits it, computes s2n-bignum's
`sha512_hash_blocks`, from awslabs/s2n-bignum#420 at 7ef7ba7c, restated as an
axiom about the Rust wrapper `compress_hw` around it. `admin/prove` checks the
HOL Light proof against the object code rind's release build emits, its
instructions, relocations, and the `K512` table they read. The theorem's
hypotheses hold for every call `compress_hw`'s safety contract allows: `state`
and `blocks` are distinct allocations, neither overlapping the code, the
table, or the 16 bytes below the stack pointer the routine saves its frame to;
`blocks` is a whole number of blocks, at least one and, as a slice, fewer than
2^64; the linker places the table within the reach of the `adrp` that
addresses it; and the ABI keeps the stack pointer 16-byte aligned. The
restatement, and that the wrapper passes the pointers and block count the
theorem names, are trusted. `S2nSha512` proves s2n-bignum's spec `compress`.
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

/-- `SHA512_HW_SUBROUTINE_CORRECT`: for `n` blocks, at least one, whose `i`th
block's `j`th word, read big-endian, is the `j`th word of `m i`, the state's
eight words, read little-endian, become `sha512_hash_blocks m state n`. -/
@[step]
axiom sha512_block_data_order_hw_spec (c : low.aarch64.cpu.HaveSha3)
    (state : Std.Array U64 8#usize) (blocks : Slice U8)
    (hm : blocks.length % 128 = 0) (hn : blocks.length ≠ 0) :
    low.aarch64.sha512.compress_hw c state blocks ⦃ r =>
      r.val.map (·.bv) = s2n.sha512.hashBlocks
        (fun i => (blockWords ((blocks.val.drop (128 * i)).take 128)).map (·.bv))
        (state.val.map (·.bv)) (blocks.length / 128) ⦄

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
      step with sha512_block_data_order_hw_spec as ⟨r, hr⟩
      apply s2n.sha512.map_bv_injective
      rw [hr, ← s2n.sha512.hashBlocks_eq state.val (by simp) blocks.val hm]

end rind.aarch64
