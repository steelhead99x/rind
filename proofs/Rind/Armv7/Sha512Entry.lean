import Rind.Armv7.Blockwise
import Rind.S2nSha512
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-512's block function on armv7

`low::arm::sha_armv4::sha512_compress_blocks` runs aws-lc's `sha512-armv4`
assembly: the NEON routine where the CPU has NEON, the integer one otherwise.
`SHA512_BLOCK_DATA_ORDER_NEON_SUBROUTINE_CORRECT`, in
`proofs/hol-light/armv7/sha512_armv4.ml` at rind's commit, proves that the
NEON routine, as rind's build emits it, computes s2n-bignum's FIPS 180-4
spec, `sha512_hash_blocks`, on s2n-bignum's AArch32 model, which `admin/prove
cosim` checks against qemu-arm. `sha512_block_data_order_neon_spec` restates
that theorem about the opaque Rust wrapper `compress_neon`, over
`Rind.S2nSha512`'s transliteration of the spec, and
`sha512_compress_blocks_spec` composes it with the dispatch. The integer
routine has no proof, so `RunsSha512` takes a CPU with NEON.

`Rind.Armv7.Sha512Context`, which `admin/prove` writes from x86_64's, takes
`RunsSha512` and the block function's contract from here, as x86_64's takes
them from `Rind.X86_64.AwsLc`.

Trusted: the restatement, and that each call meets the theorem's premises,
which every call `compress_neon`'s safety contract allows does. `state` and
`blocks` do not overlap, since one is borrowed mutably while the other is
borrowed, and neither overlaps the code or the 64 bytes below the stack
pointer where the routine saves d8-d15; no Rust object, and not those 64
bytes, which lie in the stack, wraps the address space; `state` is 8-byte
aligned, as `[u64; 8]` is on armv7, the stack pointer 4-byte aligned, as the
AAPCS keeps it, and the code, which starts at `K512`, 32-byte aligned by its
`.align 5`; the return address is one `bx` takes back to the caller, as the
`bl` or `blx` of an A32 or T32 caller leaves it; `blocks` is a whole number
of blocks, at least one, and a slice on armv7 spans fewer than 2^31 bytes,
so `128 * n < 2 ^ 32`. The routine's constant time is not proven.
-/

namespace rind.armv7

/-- `SHA512_BLOCK_DATA_ORDER_NEON_SUBROUTINE_CORRECT`: for `n` blocks, at
least one, whose `i`th block's `j`th word, read big-endian, is the `j`th word
of `m i`, the state's eight words, read little-endian, become
`sha512_hash_blocks m state n`. -/
@[step]
axiom sha512_block_data_order_neon_spec (t : low.arm.cpu.HaveNeon)
    (state : Std.Array U64 8#usize) (blocks : Slice U8)
    (hm : blocks.length % 128 = 0) (hn : blocks.length ≠ 0) :
    low.arm.sha_armv4.compress_neon t state blocks ⦃ r =>
      r.val.map (·.bv) = s2n.sha512.hashBlocks
        (fun i => (blockWords ((blocks.val.drop (128 * i)).take 128)).map (·.bv))
        (state.val.map (·.bv)) (blocks.length / 128) ⦄

/-- What armv7's SHA-512 theorems assume: its entry guard and the debug
build's check that one is held pass, and the CPU has NEON, so SHA-512 runs
the routine with a proof. None reads an input. -/
def RunsSha512 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
    ∃ t, low.arm.cpu.HaveNeon.check = ok (some t)

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

/-- The dispatch runs the NEON routine on a whole number of blocks, and
returns the state for none. -/
@[step]
theorem sha512_compress_blocks_spec (h : RunsSha512) (state : Std.Array U64 8#usize)
    (blocks : Slice U8) (hm : blocks.length % 128 = 0) :
    low.arm.sha_armv4.sha512_compress_blocks state blocks ⦃ r =>
      r.val = compress state.val blocks.val ⦄ := by
  obtain ⟨-, -, t, ht⟩ := h
  unfold low.arm.sha_armv4.sha512_compress_blocks
  step*
  · simp_all [compress_short]
  · rw [ht]
    step with sha512_block_data_order_neon_spec as ⟨r, hr⟩
    apply s2n.sha512.map_bv_injective
    rw [hr, ← s2n.sha512.hashBlocks_eq state.val (by simp) blocks.val hm]

end rind.armv7
