import Rind.Portable.Blockwise
import Rind.Sha2Lemmas
open Aeneas Aeneas.Std Result rind.spec

/-!
# HACL*'s SHA-2 contracts on the portable backend

The portable backend compresses SHA-256 and SHA-512 blocks with HACL*'s
`Hacl_Hash_SHA2`, as libcrux-sha2 0.0.9 ships the Rust that KaRaMeL prints
from it, in pieces under 2^31 bytes, since HACL* takes a 32-bit length.
Charon cannot translate the two functions: `krml::unroll_for!` unrolls their
rounds into one body whose blocks nest deeper than Charon's recursion bound.
So each is an axiom here, restating HACL*'s F* theorem about it under the
composition rule, about the opaque function the translation calls. See
UPSTREAM.md, "Charon panics on HACL*'s unrolled SHA-2".

The theorem is `Hacl.SHA2.Scalar32`'s `sha256_update_nblocks` and
`sha512_update_nblocks`, of type `update_nblocks_vec_t'`
(`code/sha2-mb/Hacl.Impl.SHA2.Generic.fst`, lines 296 to 309): the state
becomes `Hacl.Spec.SHA2.Vec.update_nblocks len b st`, which
`Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l` proves is
`Hacl.Spec.SHA2.update_nblocks`, FIPS 180-4's block function over each of the
`len / block_length` whole blocks of `b`, as `Hacl.Spec.SHA2.EquivScalar`
proves `Spec.SHA2`'s. Its preconditions are that the state is live and
disjoint from `b`, which Rust's borrows give, and that `b` holds `len` bytes,
which rind passes as `piece.len() as u32` of a piece under 2^31 bytes.
libcrux records no HACL* revision, so this cites HACL*'s main branch as of
2026-11-03, as `benchmarks/verified.toml` cites it for libcrux.

The restatement, that KaRaMeL prints that code as libcrux ships it, and that
HACL*'s `Spec.SHA2` is FIPS 180-4 as `Rind.HashSpec` and `Rind.Sha2`
transliterate it, are trusted.
-/

namespace rind.portable

/-- HACL*'s `sha256_update_nblocks`: the state after SHA-256's block function
over each whole block of `b`, which holds `len` bytes. -/
axiom sha256_update_nblocks_spec (len : U32) (b : Slice U8) (st : Slice U32)
    (hb : b.length = len.val) (hs : st.length = 8) :
    libcrux_sha2.hacl.sha256_update_nblocks len b st ⦃ st' =>
      st'.length = 8 ∧ words st'.val = (blocks 64 (bv b.val)).foldl sha256.compress (words st.val) ⦄

/-- HACL*'s `sha512_update_nblocks`: the state after SHA-512's block function
over each whole block of `b`, which holds `len` bytes. -/
axiom sha512_update_nblocks_spec (len : U32) (b : Slice U8) (st : Slice U64)
    (hb : b.length = len.val) (hs : st.length = 8) :
    libcrux_sha2.hacl.sha512_update_nblocks len b st ⦃ st' =>
      st'.length = 8 ∧ st'.val = compress st.val b.val ⦄

/-! ## The pieces, `low::portable::sha` -/

/-- `PIECE`, 2^31. -/
theorem piece_spec : low.portable.sha.PIECE ⦃ p => p.val = 2 ^ 31 ⦄ := by
  unfold low.portable.sha.PIECE
  have h31 : (31#i32).val < System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  step*
  rw [p_post, Nat.shiftLeft_eq, one_mul]
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- `sha256_compress_blocks`'s loop: each piece's blocks, in turn. -/
theorem sha256_loop_spec (c : core.slice.iter.Chunks U8) (state : Std.Array U32 8#usize)
    (hsz : c.size.val = 2 ^ 31) (hm : c.rest.length % 64 = 0) :
    low.portable.sha.sha256_compress_blocks_loop c state ⦃ r =>
      words r.val = (blocks 64 (bv c.rest.val)).foldl sha256.compress (words state.val) ⦄ := by
  unfold low.portable.sha.sha256_compress_blocks_loop
  apply loop.spec_decr_nat (fun x => x.1.rest.length)
    (fun x => x.1.size.val = 2 ^ 31 ∧ x.1.rest.length % 64 = 0 ∧
      (blocks 64 (bv x.1.rest.val)).foldl sha256.compress (words x.2.val) = (blocks 64 (bv c.rest.val)).foldl sha256.compress (words state.val))
  · rintro ⟨c', st⟩ ⟨hsz', hm', hT⟩
    simp only at hsz' hm' hT ⊢
    unfold low.portable.sha.sha256_compress_blocks_loop.body
      core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    split
    · rename_i h0
      have hnil : c'.rest.val = [] := List.eq_nil_of_length_eq_zero h0
      simp only [bind_ok]
      rw [← hT, hnil]
      simp [bv, blocks_nil]
    · rename_i h0
      have hp : (c'.rest.val.take c'.size.val).length ≤ 2 ^ 31 := by
        simp only [List.length_take, hsz']; omega
      have hpm : (c'.rest.val.take c'.size.val).length % 64 = 0 := by
        simp only [List.length_take, hsz', Slice.length] at hm' ⊢; omega
      simp only [bind_ok, lift, Array.to_slice_mut, Array.to_slice]
      apply WP.spec_bind (sha256_update_nblocks_spec _ _ _ ?_ ?_)
      · rintro s1 ⟨hl1, hw1⟩
        simp only [WP.spec_ok, Slice.from_val] at hw1 ⊢
        have hv : (Array.from_slice st s1).val = s1.val := Array.from_slice_val _ _ (by simpa using hl1)
        refine ⟨⟨hsz', ?_, ?_⟩, ?_⟩
        · simp only [Slice.length, Slice.from_val, List.length_drop] at hm' ⊢; omega
        · rw [← hT, hv, hw1, ← List.foldl_append]
          conv_rhs => rw [← List.take_append_drop c'.size.val c'.rest.val]
          simp only [bv, List.map_append]
          rw [blocks_append (by decide) _ _ (by simpa using hpm)]
        · simp only [Slice.length, Slice.from_val, List.length_drop]
          have : 0 < c'.rest.val.length := by simpa [Slice.length] using Nat.pos_of_ne_zero h0
          omega
      · simp only [Slice.len, Slice.length, UScalar.cast_val_eq, Slice.from_val]
        rw [Nat.mod_eq_of_lt (by scalar_tac)]
        rfl
      · show (Slice.from _ _).val.length = 8
        rw [Slice.from_val]
        exact st.property
  · exact ⟨hsz, hm, rfl⟩

/-- `sha512_compress_blocks`'s loop: each piece's blocks, in turn. -/
theorem sha512_loop_spec (c : core.slice.iter.Chunks U8) (state : Std.Array U64 8#usize)
    (hsz : c.size.val = 2 ^ 31) (hm : c.rest.length % 128 = 0) :
    low.portable.sha.sha512_compress_blocks_loop c state ⦃ r =>
      r.val = compress state.val c.rest.val ⦄ := by
  unfold low.portable.sha.sha512_compress_blocks_loop
  apply loop.spec_decr_nat (fun x => x.1.rest.length)
    (fun x => x.1.size.val = 2 ^ 31 ∧ x.1.rest.length % 128 = 0 ∧
      compress x.2.val x.1.rest.val = compress state.val c.rest.val)
  · rintro ⟨c', st⟩ ⟨hsz', hm', hT⟩
    simp only at hsz' hm' hT ⊢
    unfold low.portable.sha.sha512_compress_blocks_loop.body
      core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    split
    · rename_i h0
      have hnil : c'.rest.val = [] := List.eq_nil_of_length_eq_zero h0
      simp only [bind_ok]
      rw [← hT, hnil]
      simp [compress_nil]
    · rename_i h0
      have hp : (c'.rest.val.take c'.size.val).length ≤ 2 ^ 31 := by
        simp only [List.length_take, hsz']; omega
      have hpm : (c'.rest.val.take c'.size.val).length % 128 = 0 := by
        simp only [List.length_take, hsz', Slice.length] at hm' ⊢; omega
      simp only [bind_ok, lift, Array.to_slice_mut, Array.to_slice]
      apply WP.spec_bind (sha512_update_nblocks_spec _ _ _ ?_ ?_)
      · rintro s1 ⟨hl1, hw1⟩
        simp only [WP.spec_ok, Slice.from_val] at hw1 ⊢
        have hv : (Array.from_slice st s1).val = s1.val := Array.from_slice_val _ _ (by simpa using hl1)
        refine ⟨⟨hsz', ?_, ?_⟩, ?_⟩
        · simp only [Slice.length, Slice.from_val, List.length_drop] at hm' ⊢; omega
        · rw [← hT]
          conv_rhs => rw [← List.take_append_drop c'.size.val c'.rest.val]
          rw [compress_append _ _ _ (by simpa [Slice.length] using hpm), hv, hw1]
        · simp only [Slice.length, Slice.from_val, List.length_drop]
          have : 0 < c'.rest.val.length := by simpa [Slice.length] using Nat.pos_of_ne_zero h0
          omega
      · simp only [Slice.len, Slice.length, UScalar.cast_val_eq, Slice.from_val]
        rw [Nat.mod_eq_of_lt (by scalar_tac)]
        rfl
      · show (Slice.from _ _).val.length = 8
        rw [Slice.from_val]
        exact st.property
  · exact ⟨hsz, hm, rfl⟩

/-- SHA-256's block function, HACL*'s in pieces under 2^31 bytes. -/
theorem sha256_compress_blocks_spec :
    Compresses sha256.compress low.portable.sha.sha256_compress_blocks := by
  intro state blocks hm
  unfold low.portable.sha.sha256_compress_blocks
  simp only [core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_ok, Slice.len_val,
    show (64#usize).val = 64 by simp, show blocks.length % 64 = 0 from hm, beq_self_eq_true,
    massert_True]
  step with piece_spec as ⟨p, hp⟩
  simp only [core.slice.Slice.chunks, hp, show (2 : Nat) ^ 31 ≠ 0 by decide, ite_false, bind_ok]
  exact sha256_loop_spec ⟨blocks, p⟩ state hp hm

/-- SHA-512's block function, HACL*'s in pieces under 2^31 bytes, over a whole
number of blocks. -/
theorem sha512_blocks_spec (state : Std.Array U64 8#usize)
    (blocks : Slice U8) (hm : blocks.length % 128 = 0) :
    low.portable.sha.sha512_compress_blocks state blocks ⦃ r =>
      r.val = compress state.val blocks.val ⦄ := by
  unfold low.portable.sha.sha512_compress_blocks
  simp only [core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_ok, Slice.len_val,
    show (128#usize).val = 128 by simp, hm, beq_self_eq_true, massert_True]
  step with piece_spec as ⟨p, hp⟩
  simp only [core.slice.Slice.chunks, hp, show (2 : Nat) ^ 31 ≠ 0 by decide, ite_false, bind_ok]
  exact sha512_loop_spec ⟨blocks, p⟩ state hp hm

end rind.portable
