import Rind.X86_64.AwsLc
import Rind.X86_64.Blockwise
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-512's context, proven to the block routine's contract

A context's state holds the chaining value after the whole blocks it has
compressed and its buffer the rest (`Hashed`), and finishing pads that rest
and compresses it as FIPS 180-4 does, through `Rind.X86_64.Blockwise`'s
padding and buffering, which SHA-1 and SHA-256 share. `Rind.X86_64.Sha512`
builds the digest API's SHA-512 family on this. `admin/prove` writes the
aarch64, portable, and armv7 proofs from this file by renaming the target;
armv7 translates SHA-512's context, which Ed25519 hashes with, but not yet
the digest API.
-/

namespace rind.x86_64

/-! ## Finishing, `mid::sha2::Sha512State::finish_with` -/

theorem finish_with_loop_spec
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Std.U64))
    (r : Std.Array U8 64#usize) (V : List U64) (hVl : V.length = 8)
    (hV : it.iter.slice.val = V) (hi : it.iter.i = it.count.val) (hk : it.count.val ≤ 8)
    (hr : r.val.take (8 * it.count.val) = (V.take it.count.val).flatMap spec.beBytes) :
    mid.sha2.Sha512State.finish_with_loop it r ⦃ r' => r'.val = V.flatMap spec.beBytes ⦄ := by
  unfold mid.sha2.Sha512State.finish_with_loop
  apply loop.spec_decr_nat (fun x => 8 - x.1.count.val)
    (fun x => x.1.iter.slice.val = V ∧ x.1.iter.i = x.1.count.val ∧ x.1.count.val ≤ 8 ∧
      x.2.val.take (8 * x.1.count.val) = (V.take x.1.count.val).flatMap spec.beBytes)
  · rintro ⟨it, r⟩ ⟨hV, hi, hk, hr⟩
    simp only at hV hi hk hr ⊢
    unfold mid.sha2.Sha512State.finish_with_loop.body
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next]
    have hsl : it.iter.slice.len.val = 8 := by simp [Slice.len, hV, hVl]
    split
    · rename_i hlt
      have hk8 : it.count.val < 8 := by omega
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
        have hr64 : (r.val).length = 64 := r.property
        have := take_setSlice! r.val a.val (i1.val) (by rw [ha8, i1_post]; omega)
        simp only [Array.val_to_slice, ha8] at this ⊢
        rw [show 8 * x.val = i1.val + 8 by rw [x_post, i1_post]; ring, this, i1_post,
          show it.count.val * 8 = 8 * it.count.val by ring, hr, x_post, List.take_add_one,
          List.flatMap_append, List.getElem?_eq_getElem (by omega)]
        simp [a_post, hw, spec.beBytes]
    · rename_i hlt
      have hk8 : it.count.val = 8 := by omega
      have hr64 : (r.val).length = 64 := r.property
      rw [hk8, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hr
      simpa [WP.spec_ok] using hr
  · exact ⟨hV, hi, hk, hr⟩

@[step]
theorem from_u128_u64_spec (x : U64) :
    lift (core.convert.num.FromU128U64.from x) ⦃ y => y.val = x.val ⦄ := by
  simp [lift, core.convert.num.FromU128U64.from_val_eq]

@[step]
theorem compress_spec (h : RunsSha512) (state : Std.Array U64 8#usize) (blocks : Slice U8)
    (hm : blocks.length % 128 = 0) :
    mid.sha2.Sha512State.compress state blocks ⦃ r => r.val = compress state.val blocks.val ⦄ := by
  unfold mid.sha2.Sha512State.compress
  step*

/-- `finish_with` hashes the message after the state's blocks, padded. -/
@[step]
theorem finish_with_spec (h : RunsSha512) (self : mid.sha2.Sha512State) (message : Slice U8) :
    mid.sha2.Sha512State.finish_with self message ⦃ r =>
      r.val = (compress self.h.val (padAfter (128 * self.nblocks.val) message.val)).flatMap spec.beBytes ⦄ := by
  unfold mid.sha2.Sha512State.finish_with
  have hB : (UScalar.cast .U128 mid.sha2.Sha512State.finish_with.BLOCK_SZ).val = 128 := by
    simp [mid.sha2.Sha512State.finish_with.BLOCK_SZ, mid.sha2.Sha512Context.BLOCK_SZ, UScalar.cast_val_eq]
  have hL : (UScalar.cast .U128 message.len).val = message.length := by
    have := slice_length_lt message
    simp [UScalar.cast_val_eq, Slice.length] at this ⊢; omega
  have hn : self.nblocks.val < 2 ^ 64 := self.nblocks.hBounds
  have hm : message.length < 2 ^ 64 := slice_length_lt message
  step*
  have hbits : bits.val = 8 * (128 * self.nblocks.val + message.length) := by
    rw [bits_post, i5_post, i2_post, i_post, i1_post, hB, i4_post, hL]; ring
  have hh : (if b = true then ok self.h else mid.sha2.Sha512State.compress self.h blocks) ⦃ h' =>
      h'.val = compress self.h.val blocks.val ⦄ := by
    split
    · have : blocks.val = [] := List.eq_nil_of_length_eq_zero (by simp_all [Slice.length])
      simp [this]
    · step*
  step with hh as ⟨h', hh'⟩
  step as ⟨a1, a1_post⟩
  step with pad_spec (N := 128#usize) (L := 16#usize) rest a1 (by simp) (by scalar_tac) (by simp)
    (by simpa using blocks_post2) as ⟨s, _, s_post⟩
  step*
  · have h16 : (a1.val).length = 16 := by simp
    have := pad_mod (N := 128) (L := 16) rest.length (by decide)
    simp only [Slice.length, s_post, List.length_append, List.length_singleton, List.length_replicate,
      h16] at this ⊢
    omega
  · simp only [core.slice.Slice.iter]
    step*
    have hl : (h1.val).length = 8 := h1.property
    apply WP.spec_mono (finish_with_loop_spec iter _ h1.val hl ?_ ?_ ?_ ?_)
    · intro r hr
      rw [hr, h1_post, hh', ← compress_append _ _ _ blocks_post]
      congr 2
      have hbv : bits.bv = BitVec.ofNat 128 (8 * (128 * self.nblocks.val + message.length)) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, ← hbits]
        exact (Nat.mod_eq_of_lt bits.bv.isLt).symm
      have hz : padZeros 128 16 rest.length = (239 - message.length % 128) % 128 := by
        rw [blocks_post3]; unfold padZeros; omega
      rw [s_post, a1_post, hbv, hz, padAfter]
      simp only [Slice.length]
      rw [← blocks_post1]
      simp
    all_goals simp [iter_post, iter_post1, s1_post, Array.val_to_slice]

/-! ## Updating, `mid::sha2::Sha512Context::update` -/

@[step]
theorem saturating_add_spec (x y : U64) (h : x.val + y.val < 2 ^ 64) :
    lift (core.num.U64.saturating_add x y) ⦃ z => z.val = x.val + y.val ⦄ := by
  simp only [lift, WP.spec_ok, core.num.U64.saturating_add, UScalar.saturating_add]
  show (BitVec.ofNat _ _).toNat = _
  rw [BitVec.toNat_ofNat, min_eq_right (by simp [U64.max_eq]; omega)]
  simp; omega

/-- `update_blocks` compresses whole blocks and counts them. -/
@[step]
theorem update_blocks_spec (h : RunsSha512) (st : mid.sha2.Sha512State) (blocks : Slice U8)
    (hm : blocks.length % 128 = 0) (hn : st.nblocks.val + blocks.length / 128 < 2 ^ 64) :
    mid.sha2.Sha512State.Insts.RindLowGenericBlockwiseUpdateBlocks.update_blocks st blocks ⦃ st' =>
      st'.h.val = compress st.h.val blocks.val ∧
        st'.nblocks.val = st.nblocks.val + blocks.length / 128 ⦄ := by
  unfold mid.sha2.Sha512State.Insts.RindLowGenericBlockwiseUpdateBlocks.update_blocks
  have hB : mid.sha2.Sha512Context.BLOCK_SZ.val = 128 := by simp [mid.sha2.Sha512Context.BLOCK_SZ]
  step*
  rename_i hb
  have h0 : blocks.length = 0 := by simpa [hb] using b1_post
  simp [compress_short _ _ (by omega : blocks.length < 128), h0]

/-- A SHA-512 state, from initial value `iv`, that has compressed `P`, whole
blocks. -/
def Sha512Absorbed (iv : List U64) (P : List U8) (st : mid.sha2.Sha512State) : Prop :=
  st.h.val = compress iv P ∧ 128 * st.nblocks.val = P.length

theorem sha512_update_blocks_spec (h : RunsSha512) (iv : List U64) (P : List U8)
    (st : mid.sha2.Sha512State) (blocks : Slice U8) (hs : Sha512Absorbed iv P st)
    (hm : blocks.length % 128 = 0) (hb : P.length + blocks.length < 2 ^ 64) :
    mid.sha2.Sha512State.Insts.RindLowGenericBlockwiseUpdateBlocks.update_blocks st blocks ⦃ st' =>
      Sha512Absorbed iv (P ++ blocks.val) st' ⦄ := by
  obtain ⟨hh, hn⟩ := hs
  apply WP.spec_mono (update_blocks_spec h st blocks hm (by omega))
  rintro st' ⟨hh', hn'⟩
  refine ⟨by rw [hh', hh, compress_append iv P blocks.val (by omega)], ?_⟩
  rw [hn', List.length_append]
  simp only [Slice.length] at *
  omega

/-- A SHA-512 context, from initial value `iv`, that has hashed `m`: its state
has compressed whole blocks of it, and its buffer holds the rest. -/
def Hashed (iv : List U64) (c : mid.sha2.Sha512Context) (m : List U8) : Prop :=
  Buffered (Sha512Absorbed iv) m c.blockwise c.state

/-- `update` adds `bytes` to what the context has hashed. -/
theorem context_update_spec (h : RunsSha512) (iv : List U64) (c : mid.sha2.Sha512Context)
    (m : List U8) (bytes : Slice U8) (hc : Hashed iv c m) (hl : m.length + bytes.length < 2 ^ 64) :
    mid.sha2.Sha512Context.update c bytes ⦃ c' => Hashed iv c' (m ++ bytes.val) ⦄ := by
  unfold mid.sha2.Sha512Context.update
  step with update_spec (N := 128#usize) mid.sha2.Sha512State.Insts.RindLowGenericBlockwiseUpdateBlocks
    (Sha512Absorbed iv) (2 ^ 64 - 1)
    (fun p s b hs hm hb => sha512_update_blocks_spec h iv p s b hs hm (by omega))
    m c.blockwise bytes c.state hc (by decide) (by omega) as ⟨bw, s', h'⟩
  exact h'

/-! ## Starting and finishing contexts -/

theorem sha512_initial_spec :
    mid.sha2.Sha512State.new ⦃ st => st.h.val = sha512Iv ∧ st.nblocks.val = 0 ⦄ := by
  simp [mid.sha2.Sha512State.new, mid.sha2.Sha512State.with_h, sha512Iv]

/-- A context resumed from an initial value has hashed nothing. -/
theorem resume_spec (iv : List U64) (st : mid.sha2.Sha512State) (hh : st.h.val = iv)
    (hn : st.nblocks.val = 0) :
    mid.sha2.Sha512Context.resume st ⦃ c => Hashed iv c [] ⦄ := by
  simp [mid.sha2.Sha512Context.resume, low.generic.blockwise.Blockwise.new, Hashed, Buffered,
    Sha512Absorbed, hh, hn]

/-- `finish` is the hash of what the context has hashed. -/
theorem context_finish_spec (h : RunsSha512) (iv : List U64) (c : mid.sha2.Sha512Context)
    (m : List U8) (hc : Hashed iv c m) :
    mid.sha2.Sha512Context.finish c ⦃ r => r.val = sha512Words iv m ⦄ := by
  obtain ⟨hu, q, ⟨hh, hn⟩, hqm⟩ := hc
  unfold mid.sha2.Sha512Context.finish
  step with buffered_spec c.blockwise hu as ⟨s, hs⟩
  apply WP.spec_mono (finish_with_spec h c.state s)
  intro r hr
  have hq : q.length % 128 = 0 := by omega
  rw [hr, hh, hn, ← compress_append _ _ _ hq, sha512Words, ← hqm, ← hs, pad_append _ _ hq]

end rind.x86_64
