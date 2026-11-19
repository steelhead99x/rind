import Rind.X86_64.Funs
import Rind.S2nSha512
open Aeneas Aeneas.Std Result rind.spec

/-!
# aws-lc's SHA-512 contract on x86_64

aws-lc-verification's SAW proof that aws-lc's `sha512_block_data_order_avx`
meets `sha512_block_data_order_array_spec`, at the revision rind's README
cites (79730247), restated as an axiom about the opaque Rust wrapper
`compress_avx` around rind's copy of that routine. rind copies it from aws-lc
5ed12cce, whose `sha512-x86_64.pl` is the proven c21d40da's.

The spec's preconditions hold for every call `compress_avx`'s safety contract
allows: `state` and `blocks` are distinct allocations, `blocks` is a whole
number of blocks, at least one, and the token proves AVX. Its precondition on
`OPENSSL_ia32cap_P` names a global that rind's copy of the routine does not
read. rind runs that routine only on Intel's CPUs with AVX but without AVX2.

The restatement, and that rind's naked function is aws-lc's object code with
the wrapper passing the pointers and block count the spec names, are trusted.

For OpenSSL's AVX2 routine, `sha512_block_data_order_avx2`, which rind runs on
CPUs with AVX2, BMI1, BMI2, POPCNT, and SSSE3, rind proves the
routine itself: its HOL Light proof `SHA512_AVX2_SUBROUTINE_CORRECT`, in
`proofs/hol-light/x86_64/sha512_block_data_order_avx2.ml` at rind's commit,
that rind's naked function, as rind's build emits it, computes s2n-bignum's
`sha512_hash_blocks`, from awslabs/s2n-bignum#420 at 7ef7ba7c, restated as an
axiom about the Rust wrapper `compress_avx2` around it. `admin/prove` checks
the HOL Light proof against the object code rind's release build emits, its
instructions, relocations, and the `K512` table they read, on s2n-bignum's
x86 model with the instructions rind adds to it, which `admin/prove cosim`
checks against the CPU. The theorem's hypotheses hold for every call
`compress_avx2`'s safety contract allows: `state` and `blocks` are distinct
allocations, neither overlapping the code, the table, or the 3448 bytes from
the 3440 below the stack pointer, where the routine keeps its frame, through
the return address; `blocks` is a whole number of blocks, at least one, and
it and the 128 bytes after it end below 2^64, as x86_64's user addresses do;
the stack pointer is at least 4096, as page zero is never mapped; the linker
places the table, which `K512`'s type aligns to 64 bytes, within the reach of
the `lea` that addresses it. The restatement, and that the wrapper passes the
pointers and block count the theorem names, are trusted. aws-lc's scalar
routine has no proof.
-/

namespace rind.x86_64

/-- `sha512_block_data_order_array_spec`, which SAW's
`llvm_verify_fixpoint_x86` proves of `sha512_block_data_order_avx`,
https://github.com/awslabs/aws-lc-verification/blob/797302470c1703cbb1a3a6fa98daffef0bfd3d80/SAW/proof/SHA512/SHA512-common.saw#L61
with the spec at
https://github.com/awslabs/aws-lc-verification/blob/797302470c1703cbb1a3a6fa98daffef0bfd3d80/SAW/proof/SHA512/SHA512-common-specs.saw#L101 :
for `num` blocks, `len = num * 128` bytes and not zero, the state becomes
cryptol-specs' `processBlocks state data 0 num`, which `compress` restates. -/
@[step]
axiom compress_avx_spec (t : low.x86_64.cpu.HaveAvx) (state : Std.Array U64 8#usize)
    (blocks : Slice U8) (hm : blocks.length % 128 = 0) (hn : blocks.length ≠ 0) :
    low.x86_64.sha512.compress_avx t state blocks ⦃ r => r.val = compress state.val blocks.val ⦄

/-- `SHA512_AVX2_SUBROUTINE_CORRECT`: for `n` blocks, at least one, whose `i`th
block's `j`th word, read big-endian, is the `j`th word of `m i`, the state's
eight words, read little-endian, become `sha512_hash_blocks m state n`. -/
@[step]
axiom sha512_block_data_order_avx2_spec (t : low.x86_64.cpu.HaveAvx2)
    (state : Std.Array U64 8#usize) (blocks : Slice U8)
    (hm : blocks.length % 128 = 0) (hn : blocks.length ≠ 0) :
    low.x86_64.sha512.compress_avx2 t state blocks ⦃ r =>
      r.val.map (·.bv) = s2n.sha512.hashBlocks
        (fun i => (blockWords ((blocks.val.drop (128 * i)).take 128)).map (·.bv))
        (state.val.map (·.bv)) (blocks.length / 128) ⦄

/-- rind's SHA-512 runs one of the two routines with a proof on this CPU:
aws-lc's AVX routine, on Intel's CPUs with AVX and SSSE3 but not AVX2, or
OpenSSL's AVX2 routine, on CPUs with AVX2, BMI1, BMI2, POPCNT, and SSSE3; and
its entry guard and the debug build's check that one is held pass. None reads
an input. -/
def RunsSha512 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
    ((∃ t, low.x86_64.sha512.path = ok (low.x86_64.sha512.Path.Avx t)) ∨
      ∃ t, low.x86_64.sha512.path = ok (low.x86_64.sha512.Path.Avx2 t))

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
    low.x86_64.sha512.sha512_compress_blocks state blocks ⦃ r =>
      r.val = compress state.val blocks.val ⦄ := by
  obtain ⟨-, -, ht⟩ := h
  unfold low.x86_64.sha512.sha512_compress_blocks
  step*
  · simp_all [compress_short]
  · rcases ht with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [ht]
      step with compress_avx_spec
      simp_all
    · rw [ht]
      step with sha512_block_data_order_avx2_spec as ⟨r, hr⟩
      apply s2n.sha512.map_bv_injective
      rw [hr, ← s2n.sha512.hashBlocks_eq state.val (by simp) blocks.val hm]

end rind.x86_64
