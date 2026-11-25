import Rind.Aarch64.Blockwise
import Rind.Aarch64.Sha256HwAsm
import Rind.S2nSha256
import Rind.Sha2Lemmas
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-256's block function with the crypto extension on aarch64

rind's Lean theorem
`rind.aarch64.sha256hw.sha256_block_data_order_hw_correct`, in
`Rind/Aarch64/Sha256HwAsm.lean`, which the same build checks, that rind's
naked function `sha256_block_data_order_hw`, as rind's Linux build emits it, run in
rind's extension of pyca/verified-garbage's AArch64 model, computes
s2n-bignum's `sha256_hash_blocks`, restated as an axiom about the Rust
wrapper `compress_hw` around it. `admin/prove lean` checks that the program
the theorem is about is the object code rind's Linux release build emits,
its instructions, relocations, and the `K256` table they read; Apple's build
assembles its own copy of the routine, `sha256_block_data_order_hw.apple.s`,
which no check compares. `admin/prove vg` cosimulates each distinct
instruction and branch condition against the CPU, or qemu where the CPU lacks
the extension, but for the `adrp` and `add` the linker fills and the final
`ret`, as it does VG's.

The theorem's precondition holds for every call `compress_hw`'s safety
contract allows: the routine may read `blocks` and the table and read and
write `state` and the 16 bytes below the stack pointer it saves its frame to, which
overlap none of the others; `blocks` is a whole number of blocks, at least
one and, as a slice, fewer than 2^64; and the ABI keeps the stack pointer
16-byte aligned. The restatement, and that the wrapper passes the pointers
and block count the theorem names, are trusted.

`S2nSha256` proves s2n-bignum's spec FIPS 180-4's, as `Rind.HashSpec` states
it, so the dispatch meets `Compresses` wherever the CPU has the extension.
-/

namespace rind.aarch64

/-- `sha256_block_data_order_hw_correct`: for `n` blocks, at least one, the
state's eight words, read little-endian, become `sha256_hash_blocks` of the
blocks, each's words read big-endian, from them. -/
@[step]
axiom sha256_block_data_order_hw_spec (c : low.aarch64.cpu.HaveCryptoExt)
    (state : Std.Array U32 8#usize) (blocks : Slice U8)
    (hm : blocks.length % 64 = 0) (hn : blocks.length ≠ 0) :
    low.aarch64.sha256.compress_hw c state blocks ⦃ r =>
      words r.val = s2n.hashBlocks (fun i => rind.spec.words (((bv blocks.val).drop (64 * i)).take 64))
        (words state.val) (blocks.length / 64) ⦄

/-- The dispatch, on a CPU with the crypto extension, compresses every whole
block, and returns the state for none. -/
theorem sha256_compress_blocks_hw_spec (hc : ∃ c, low.aarch64.cpu.HaveCryptoExt.check = ok (some c)) :
    Compresses sha256.compress low.aarch64.sha256.sha256_compress_blocks := by
  intro h s hl
  obtain ⟨c, hc⟩ := hc
  unfold low.aarch64.sha256.sha256_compress_blocks
  step*
  · have hs : s.val = [] := by
      rw [← List.length_eq_zero_iff]; simp_all
    rw [hs, show bv ([] : List U8) = [] from rfl, blocks]
    simp
  · rw [hc]
    step with sha256_block_data_order_hw_spec as ⟨r, hr⟩
    rw [hr]
    simpa [bv] using s2n.hashBlocks_eq (words h.val) (by simp [words]) (bv s.val)

end rind.aarch64
