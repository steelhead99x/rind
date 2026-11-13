import Rind.X86_64.ShaBlocks
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-1 and SHA-256, from their `Hash` impls to the block functions

The hash of a message is FIPS 180-4's, given `Sha1Blocks` or `Sha256Blocks`:
the contracts of the block functions below rind's padding, which no proof
covers yet on x86_64.
`admin/prove` writes the aarch64 proof from this file by renaming the target.
-/

namespace rind.x86_64

/-! ## The digest's encoding -/

theorem sha1_out_loop_spec
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Std.U32))
    (r : Std.Array U8 20#usize) (V : List U32) (hVl : V.length = 5)
    (hV : it.iter.slice.val = V) (hi : it.iter.i = it.count.val) (hk : it.count.val ≤ 5)
    (hr : r.val.take (4 * it.count.val) = (V.take it.count.val).flatMap beBytes32) :
    mid.sha1.Sha1State.finish_with_loop it r ⦃ r' => r'.val = V.flatMap beBytes32 ⦄ := by
  unfold mid.sha1.Sha1State.finish_with_loop
  apply loop.spec_decr_nat (fun x => 5 - x.1.count.val)
    (fun x => x.1.iter.slice.val = V ∧ x.1.iter.i = x.1.count.val ∧ x.1.count.val ≤ 5 ∧
      x.2.val.take (4 * x.1.count.val) = (V.take x.1.count.val).flatMap beBytes32)
  · rintro ⟨it, r⟩ ⟨hV, hi, hk, hr⟩
    simp only at hV hi hk hr ⊢
    unfold mid.sha1.Sha1State.finish_with_loop.body
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next]
    have hsl : it.iter.slice.len.val = 5 := by simp [Slice.len, hV, hVl]
    split
    · rename_i hlt
      have hk4 : it.count.val < 5 := by omega
      step*
      · rw [s_post1, s1_post]
        simp [i3_post, i2_post, i1_post, Slice.length]
        omega
      · have ha8 : (a.val).length = 4 := a.property
        have hw : it.iter.slice[it.iter.i] = V[it.count.val] := by
          subst hV
          show it.iter.slice.val[it.iter.i]'(by simp [Slice.len] at hlt; omega) = _
          simp only [hi]
        refine ⟨hV, by omega, by omega, ?_, by omega⟩
        rw [s_post2, s2_post, s1_post]
        have hr32 : (r.val).length = 20 := r.property
        have := take_setSlice! r.val a.val (i1.val) (by rw [ha8, i1_post]; omega)
        simp only [Array.val_to_slice, ha8] at this ⊢
        rw [show 4 * x.val = i1.val + 4 by rw [x_post, i1_post]; ring, this, i1_post,
          show it.count.val * 4 = 4 * it.count.val by ring, hr, x_post, List.take_add_one,
          List.flatMap_append, List.getElem?_eq_getElem (by omega)]
        simp [a_post, hw, beBytes32]
    · rename_i hlt
      have hk4 : it.count.val = 5 := by omega
      have hr32 : (r.val).length = 20 := r.property
      rw [hk4, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hr
      simpa [WP.spec_ok] using hr
  · exact ⟨hV, hi, hk, hr⟩

/-- Rust's padding of `m` after the whole blocks `P`, closed by `bits` as
`u64::to_be_bytes` writes it, is FIPS 180-4's of `P ++ m`. -/
theorem pad_bv (P m : List U8) (bits : U64) (hP : P.length % 64 = 0)
    (hb : bits.val = 8 * (P.length + m.length)) :
    bv (P ++ m ++ [128#u8] ++ List.replicate (padZeros 64 8 m.length) 0#u8 ++
      bits.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)) = pad (bv (P ++ m)) := by
  have hz : padZeros 64 8 m.length = (64 - ((bv (P ++ m)).length + 9) % 64) % 64 := by
    have := padZeros_sub (N := 64) (L := 8) (n := P.length + m.length) (start := P.length) hP
      (by omega)
    rw [show P.length + m.length - P.length = m.length by omega] at this
    rw [this]
    simp [padZeros, bv]
  have hbits : bits.bv = BitVec.ofNat 64 (8 * (bv (P ++ m)).length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, bv, List.length_map, List.length_append]
    rw [← hb, Nat.mod_eq_of_lt (by scalar_tac)]
    rfl
  rw [pad, hz, hbits]
  simp [bv, List.map_map, Function.comp_def]

/-! ## `mid::sha2::Sha256State` -/

/-- A SHA-256 state that has absorbed `P`, a whole number of blocks. -/
def Sha256Absorbed (P : List U8) (s : mid.sha2.Sha256State) : Prop :=
  Absorbed sha256.compress sha256.H0 P s.h ∧ s.nblocks.val * 64 = P.length

/-- The padding's length field for what `s` has absorbed, `P`, followed by
`more` bytes. -/
theorem sha256_length_spec (P : List U8) (s : mid.sha2.Sha256State) (more : Usize)
    (hn : s.nblocks.val * 64 = P.length) (hlen : 8 * (P.length + more.val) ≤ U64.max) :
    mid.sha2.Sha256State.length s more ⦃ l => ∃ bits : U64,
      bits.val = 8 * (P.length + more.val) ∧
      l.val = bits.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8) ⦄ := by
  unfold mid.sha2.Sha256State.length
  step*
  have hi : i.val = 64 := by
    rw [i_post]
    simp [mid.sha2.Sha256State.length.BLOCK_SZ, mid.sha2.Sha256Context.BLOCK_SZ]
  rcases o with _ | z
  · simp only at o_post; rw [hi] at o_post; omega
  simp only at o_post
  have hz : z.val = P.length := by rw [o_post.2.1, hi, hn]
  simp only [core.option.Option.and_then,
    mid.sha2.Sha256State.length.closure.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64.call_once]
  step*
  have hx : x.val = more.val := by rw [x_post]; simp
  have ha := U64.checked_add_bv_spec z x
  rcases hz2 : z.checked_add x with _ | z2
  · rw [hz2] at ha; simp only at ha; omega
  rw [hz2] at ha
  simp only at ha
  simp only [mid.sha2.Sha256State.length.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64.call_once,
    bind_ok]
  have hm := U64.checked_mul_bv_spec z2 8#u64
  have h8 : (8#u64).val = 8 := by simp
  rcases hz3 : z2.checked_mul 8#u64 with _ | bits
  · rw [hz3] at hm; simp only at hm; rw [h8] at hm; omega
  rw [hz3] at hm
  simp only at hm
  simp only [core.option.Option.expect, Result.ofOption, bind_ok]
  step*
  have hbytes := core.num.U64.to_be_bytes.step_spec bits
  simp only [lift, WP.spec_ok] at hbytes
  exact ⟨bits, by rw [hm.2.1, h8, ha.2.1]; omega, hbytes⟩

theorem sha256_finish_with_spec (hb : Sha256Blocks) (P : List U8) (s : mid.sha2.Sha256State)
    (message : Slice U8) (hs : Sha256Absorbed P s)
    (hlen : 8 * (P.length + message.length) ≤ U64.max) :
    mid.sha2.Sha256State.finish_with s message ⦃ r =>
      bv r.val = sha256.hash (bv (P ++ message.val)) ⦄ := by
  obtain ⟨⟨hh, hP⟩, hn⟩ := hs
  have hml : message.len.val = message.length := by simp [Slice.len, Slice.length]
  unfold mid.sha2.Sha256State.finish_with
  step with sha256_length_spec P s message.len hn (by rw [hml]; omega) as ⟨l, bits, hbits, hl⟩
  simp only [hb.held, bind_ok]
  apply WP.spec_mono (sha256_finish_spec hb P s.h message l ⟨hh, hP⟩)
  intro r hr
  rw [hr, sha256Finished, hl, pad_bv P message.val bits hP (by rw [hbits, hml])]
  rfl

/-- On this backend the long-path flag is false: only 32-bit portable SHA-256
sets it. -/
theorem sha256_finish_uses_long_spec (message : Slice U8) :
    mid.sha2.Sha256State.finish_uses_long message ⦃ _ => True ⦄ := by
  unfold mid.sha2.Sha256State.finish_uses_long
  step*

/-- On this backend `finish_with_long` is `finish_with`. -/
theorem sha256_finish_with_long_spec (hb : Sha256Blocks) (P : List U8) (s : mid.sha2.Sha256State)
    (message : Slice U8) (hs : Sha256Absorbed P s)
    (hlen : 8 * (P.length + message.length) ≤ U64.max) :
    mid.sha2.Sha256State.finish_with_long s message ⦃ r =>
      bv r.val = sha256.hash (bv (P ++ message.val)) ⦄ := by
  unfold mid.sha2.Sha256State.finish_with_long
  exact sha256_finish_with_spec hb P s message hs hlen

theorem saturating_add_val (x y : U64) (h : x.val + y.val ≤ U64.max) :
    (core.num.U64.saturating_add x y).val = x.val + y.val := by
  simp only [core.num.U64.saturating_add, UScalar.saturating_add]
  rw [Nat.min_eq_right (by simpa [U64.max] using h)]
  show (BitVec.ofNat 64 _).toNat = _
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by scalar_tac)

theorem sha256_update_blocks_spec (hb : Sha256Blocks) (P : List U8) (s : mid.sha2.Sha256State)
    (blk : Slice U8) (hs : Sha256Absorbed P s) (hl : blk.length % 64 = 0)
    (hbound : P.length + blk.length ≤ U64.max) :
    mid.sha2.Sha256State.Insts.RindLowGenericBlockwiseUpdateBlocks.update_blocks s blk ⦃ s' => Sha256Absorbed (P ++ blk.val) s' ⦄ := by
  obtain ⟨hh, hn⟩ := hs
  have hbl : blk.len.val = blk.length := by simp [Slice.len, Slice.length]
  have h64 : mid.sha2.Sha256Context.BLOCK_SZ.val = 64 := by simp [mid.sha2.Sha256Context.BLOCK_SZ]
  obtain ⟨e, he⟩ := hb.entry
  unfold mid.sha2.Sha256State.Insts.RindLowGenericBlockwiseUpdateBlocks.update_blocks
  step*
  case h2 =>
    rw [he, bind_ok]
    step with sha256_block_spec hb s.h blk hl as ⟨a, ha⟩
    step*
    have hi3 : i3.val = blk.length / 64 := by
      rw [i3_post]; simp only [UScalar.cast_val_eq, i2_post, hbl, h64]
      apply Nat.mod_eq_of_lt; scalar_tac
    simp only [lift, bind_ok, WP.spec_ok]
    refine ⟨absorbed_append hh hl ha, ?_⟩
    simp only
    rw [saturating_add_val _ _ (by rw [hi3]; omega), hi3, List.length_append]
    simp only [Slice.length] at *
    omega
  all_goals
    rename_i h0
    have : blk.val = [] := List.eq_nil_of_length_eq_zero (by simpa [b1_post] using h0)
    simp only [this, List.append_nil]
    exact ⟨hh, hn⟩

theorem sha256_new_spec : mid.sha2.Sha256State.new ⦃ s => Sha256Absorbed [] s ⦄ := by
  unfold mid.sha2.Sha256State.new
  simp only [WP.spec_ok]
  refine ⟨⟨?_, by simp⟩, by simp⟩
  rw [bv, List.map_nil, blocks_nil, List.foldl_nil]
  simp [words, Std.Array.make, sha256.H0]

/-! ## `mid::sha2::Sha256Context` -/

/-- A SHA-256 context that has been given `p`. -/
def Sha256Ctx (p : List U8) (c : mid.sha2.Sha256Context) : Prop :=
  Buffered Sha256Absorbed p c.blockwise c.state

/-- How long a SHA-256 input may be: its length in bits fits the padding. -/
def maxInput : Nat := U64.max / 8

theorem blockwise_new_spec (N : Usize) :
    low.generic.blockwise.Blockwise.new N ⦃ bw => bw.used.val = 0 ⦄ := by
  unfold low.generic.blockwise.Blockwise.new
  simp

theorem sha256_resume_spec (P : List U8) (s : mid.sha2.Sha256State) (hs : Sha256Absorbed P s) :
    mid.sha2.Sha256Context.resume s ⦃ c => Sha256Ctx P c ⦄ := by
  unfold mid.sha2.Sha256Context.resume
  step with blockwise_new_spec as ⟨bw, hbw⟩
  exact ⟨by simp [hbw], P, hs, by simp [hbw]⟩

theorem sha256_ctx_update_spec (hb : Sha256Blocks) (p : List U8) (c : mid.sha2.Sha256Context)
    (bytes : Slice U8) (hc : Sha256Ctx p c) (hlen : p.length + bytes.length ≤ maxInput) :
    mid.sha2.Sha256Context.update c bytes ⦃ c' => Sha256Ctx (p ++ bytes.val) c' ⦄ := by
  unfold mid.sha2.Sha256Context.update
  step with update_spec (N := 64#usize)
    mid.sha2.Sha256State.Insts.RindLowGenericBlockwiseUpdateBlocks Sha256Absorbed maxInput
    (fun p s b hs hl hb' => sha256_update_blocks_spec hb p s b hs hl
      (by unfold maxInput at hb'; omega))
    p c.blockwise bytes c.state hc (by decide) hlen as ⟨bw, s', h⟩
  exact h

theorem sha256_ctx_finish_spec (hb : Sha256Blocks) (p : List U8) (c : mid.sha2.Sha256Context)
    (hc : Sha256Ctx p c) (hlen : p.length ≤ maxInput) :
    mid.sha2.Sha256Context.finish c ⦃ r => bv r.val = sha256.hash (bv p) ⦄ := by
  obtain ⟨hu, q, hq, hqp⟩ := hc
  unfold mid.sha2.Sha256Context.finish
  step with buffered_spec c.blockwise hu as ⟨m, hm⟩
  have hpl : q.length + m.length = p.length := by
    rw [← hqp]; simp only [Slice.length, hm, List.length_append]
  have := sha256_finish_with_spec hb q c.state m hq (by unfold maxInput at hlen; omega)
  rw [hm, hqp] at this
  exact this

/-! ## The digest model -/

/-- An algorithm's output length. -/
def outLen : high.digest.Algorithm → Nat
  | .MD5 => 16
  | .SHA1 => 20
  | .SHA256 => 32
  | .SHA384 => 48
  | .SHA512 => 64
  | .SHA512_256 => 32
  | .SHA3_256 => 32
  | .SHA3_384 => 48
  | .SHA3_512 => 64

theorem output_len_eq (a : high.digest.Algorithm) :
    ∃ n, a.output_len = ok n ∧ n.val = outLen a ∧ n.val ≤ 64 := by
  cases a <;> refine ⟨_, rfl, ?_, ?_⟩ <;> simp [outLen]

/-- The bytes a digest holds, as `as_ref` reads them. -/
def digestBytes (d : high.digest.Digest) : List Byte :=
  bv (d.value.val.take (outLen d.algorithm))

theorem digest_new_spec (a : high.digest.Algorithm) (v : Slice U8) (hv : v.length = outLen a) :
    high.digest.Digest.new a v ⦃ d => d.algorithm = a ∧ digestBytes d = bv v.val ⦄ := by
  obtain ⟨n, hn, hnv, hn64⟩ := output_len_eq a
  unfold high.digest.Digest.new high.digest.Digest.zeroed high.digest.Digest.as_mut
  simp only [hn, bind_ok]
  step*
  rcases x with ⟨sl, back⟩
  simp only at x_post x_post1 x_post2 ⊢
  step*
  simp only [digestBytes]
  rw [x_post2, s1_post, setSlice!_eq _ _ _ (by simp only [Slice.length] at hv; simp; omega)]
  simp only [List.take_zero, List.nil_append, Nat.zero_add]
  rw [List.take_left' (by simp only [Slice.length] at hv; omega)]

theorem digest_as_ref_spec (d : high.digest.Digest) :
    high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d ⦃ s =>
      s.length = outLen d.algorithm ∧ bv s.val = digestBytes d ⦄ := by
  obtain ⟨n, hn, hnv, hn64⟩ := output_len_eq d.algorithm
  unfold high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref
  simp only [hn, bind_ok]
  step*
  refine ⟨by rw [s_post1, hnv], ?_⟩
  rw [digestBytes, s_post, ← hnv]
  simp [List.slice, Array.val_to_slice]

theorem outLen_le (a : high.digest.Algorithm) : outLen a ≤ 64 := by
  obtain ⟨n, -, hnv, hn64⟩ := output_len_eq a; omega

/-! ## The `Hash` impls, `high::hash` -/

/-- What a `Hash` impl computes: hash function `H` with `L`-byte outputs over
`B`-byte blocks, for inputs up to `max` bytes. `Abs p s` says state `s` has
absorbed `p`, and `CAbs p c` that context `c` has been given `p`. HMAC's
proofs rely on nothing else of a hash. -/
structure HashSpec {Self C S : Type} (inst : high.hash.Hash Self C S)
    (H : List Byte → List Byte) (B L max : Nat)
    (Abs : List U8 → S → Prop) (CAbs : List U8 → C → Prop) : Prop where
  out : L ≤ B ∧ L ≤ 64 ∧ B ≤ 128 ∧ 2 * B ≤ max ∧ ∀ m, (H m).length = L
  initial : inst.initial ⦃ s => Abs [] s ⦄
  update_blocks : ∀ p s (b : Slice U8), Abs p s → b.length % B = 0 → p.length + b.length ≤ max →
    inst.HashStateInst.update_blocks s b ⦃ s' => Abs (p ++ b.val) s' ⦄
  finish_with : ∀ p s (m : Slice U8), Abs p s → p.length + m.length ≤ max →
    inst.HashStateInst.finish_with s m ⦃ d =>
      outLen d.algorithm = L ∧ digestBytes d = H (bv (p ++ m.val)) ⦄
  /-- Whether `finish_with` takes the long compressor for `m`. Only 32-bit
  portable SHA-256 ever returns true; other hashes return false. -/
  finish_uses_long : ∀ (m : Slice U8), inst.HashStateInst.finish_uses_long m ⦃ _ => True ⦄
  /-- Like `finish_with`, staying on the long compressor. Semantically the
  same digest; HMAC's outer hash uses this after a long inner. -/
  finish_with_after_long : ∀ p s (m : Slice U8), Abs p s → p.length + m.length ≤ max →
    inst.HashStateInst.finish_with_after_long s m ⦃ d =>
      outLen d.algorithm = L ∧ digestBytes d = H (bv (p ++ m.val)) ⦄
  clone : ∀ p s, Abs p s → inst.HashStateInst.corecloneCloneInst.clone s ⦃ s' => Abs p s' ⦄
  resume : ∀ p s, Abs p s → inst.HashStateInst.resume s ⦃ c => CAbs p c ⦄
  update : ∀ p c (b : Slice U8), CAbs p c → p.length + b.length ≤ max →
    inst.HashContextInst.update c b ⦃ c' => CAbs (p ++ b.val) c' ⦄
  finish : ∀ p c, CAbs p c → p.length ≤ max → inst.HashContextInst.finish c ⦃ d =>
    outLen d.algorithm = L ∧ digestBytes d = H (bv p) ⦄
  zeroed_block : inst.zeroed_block ⦃ hb => hb.len.val = B ∧ hb.buf.val = List.replicate 128 0#u8 ⦄
  hash_default : inst.hash = high.hash.Hash.hash.default inst
  cclone : ∀ p c, CAbs p c → inst.HashContextInst.corecloneCloneInst.clone c ⦃ c' => CAbs p c' ⦄

theorem blockwise_clone_spec {N : Usize} (bw : low.generic.blockwise.Blockwise N) :
    low.generic.blockwise.Blockwise.Insts.CoreCloneClone.clone bw ⦃ bw' => bw' = bw ⦄ := by
  unfold low.generic.blockwise.Blockwise.Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneUsize.clone, lift, bind_ok]
  step*
  subst_vars
  rfl

theorem sha256_ctx_clone_spec (c : high.hash.Sha256Context) :
    high.hash.Sha256Context.Insts.CoreCloneClone.clone c ⦃ c' => c' = c ⦄ := by
  simp only [high.hash.Sha256Context.Insts.CoreCloneClone.clone,
    mid.sha2.Sha256Context.Insts.CoreCloneClone.clone, mid.sha2.Sha256State.Insts.CoreCloneClone.clone,
    core.clone.impls.CloneU64.clone, lift, bind_ok]
  step*
  step with blockwise_clone_spec as ⟨bw, hbw⟩
  subst_vars
  rfl

theorem sha1_ctx_clone_spec (c : high.hash.Sha1Context) :
    high.hash.Sha1Context.Insts.CoreCloneClone.clone c ⦃ c' => c' = c ⦄ := by
  simp only [high.hash.Sha1Context.Insts.CoreCloneClone.clone,
    mid.sha1.Sha1Context.Insts.CoreCloneClone.clone, mid.sha1.Sha1State.Insts.CoreCloneClone.clone,
    core.clone.impls.CloneU64.clone, lift, bind_ok]
  step*
  step with blockwise_clone_spec as ⟨bw, hbw⟩
  subst_vars
  rfl

theorem sha256_compress_length (H : List (BitVec 32)) (b : List Byte) (h : H.length = 8) :
    (sha256.compress H b).length = 8 := by
  simp only [sha256.compress, List.length_zipWith, h]
  rw [show 64 = 63 + 1 from rfl, List.range_succ, List.foldl_append]
  simp

theorem foldl_length {α : Type} (f : List (BitVec 32) → α → List (BitVec 32)) (n : Nat)
    (hf : ∀ H b, H.length = n → (f H b).length = n) (H : List (BitVec 32)) (l : List α)
    (h : H.length = n) : (l.foldl f H).length = n := by
  induction l generalizing H with
  | nil => exact h
  | cons b l ih => exact ih _ (hf H b h)

theorem sha256_hash_length (m : List Byte) : (sha256.hash m).length = 32 := by
  simp only [sha256.hash, List.length_flatMap, BitVec.toBEBytes_length]
  rw [List.map_const', List.sum_replicate,
    foldl_length _ 8 sha256_compress_length _ _ (by simp [sha256.H0])]
  rfl

/-- SHA-256's `Hash` impl computes FIPS 180-4's SHA-256, given `Sha256Blocks`. -/
theorem sha256_hashSpec (hb : Sha256Blocks) :
    HashSpec high.hash.Sha256.Insts.RindHighHashHashSha256ContextSha256State sha256.hash 64 32
      maxInput Sha256Absorbed Sha256Ctx where
  out := ⟨by decide, by decide, by decide, by unfold maxInput; scalar_tac, sha256_hash_length⟩
  initial := by
    simp only [high.hash.Sha256.Insts.RindHighHashHashSha256ContextSha256State.initial]
    step with sha256_new_spec as ⟨s, hs⟩
    exact hs
  update_blocks := fun p s b hs hl hm => by
    simp only [high.hash.Sha256State.Insts.RindHighHashHashStateSha256Context.update_blocks]
    step with sha256_update_blocks_spec hb p s b hs hl (by unfold maxInput at hm; omega) as ⟨s', h⟩
    exact h
  finish_with := fun p s m hs hm => by
    simp only [high.hash.Sha256State.Insts.RindHighHashHashStateSha256Context.finish_with,
      high.hash.Sha256.Insts.RindHighHashHashSha256ContextSha256State.ALGORITHM, high.digest.SHA256]
    step with sha256_finish_with_spec hb p s m hs (by unfold maxInput at hm; omega) as ⟨r, hr⟩
    step*
    apply WP.spec_mono (digest_new_spec _ s (by rw [s_post]; simp [outLen]))
    rintro d ⟨hd1, hd2⟩
    refine ⟨by rw [hd1]; rfl, ?_⟩
    rw [hd2, s_post, Array.val_to_slice, hr]
  finish_uses_long := fun m => by
    simp only [high.hash.Sha256State.Insts.RindHighHashHashStateSha256Context.finish_uses_long]
    exact sha256_finish_uses_long_spec m
  finish_with_after_long := fun p s m hs hm => by
    simp only [high.hash.Sha256State.Insts.RindHighHashHashStateSha256Context.finish_with_after_long,
      high.hash.Sha256.Insts.RindHighHashHashSha256ContextSha256State.ALGORITHM, high.digest.SHA256]
    step with sha256_finish_with_long_spec hb p s m hs (by unfold maxInput at hm; omega) as ⟨r, hr⟩
    step*
    apply WP.spec_mono (digest_new_spec _ s (by rw [s_post]; simp [outLen]))
    rintro d ⟨hd1, hd2⟩
    refine ⟨by rw [hd1]; rfl, ?_⟩
    rw [hd2, s_post, Array.val_to_slice, hr]
  clone := fun p s hs => by
    simp only [high.hash.Sha256State.Insts.CoreCloneClone.clone,
      mid.sha2.Sha256State.Insts.CoreCloneClone.clone]
    step*
    simp only [core.clone.impls.CloneU64.clone, lift, bind_ok, WP.spec_ok]
    rw [← x_post]
    exact hs
  resume := fun p s hs => by
    simp only [high.hash.Sha256State.Insts.RindHighHashHashStateSha256Context.resume,
      mid.sha2.Sha256State.Insts.CoreCloneClone.clone]
    step*
    simp only [core.clone.impls.CloneU64.clone, lift, bind_ok]
    rw [← x_post]
    step with sha256_resume_spec p _ hs as ⟨c, hc⟩
    exact hc
  update := fun p c b hc hm => by
    simp only [high.hash.Sha256Context.Insts.RindHighHashHashContext.update]
    step with sha256_ctx_update_spec hb p c b hc hm as ⟨c', h⟩
    exact h
  finish := fun p c hc hm => by
    simp only [high.hash.Sha256Context.Insts.RindHighHashHashContext.finish,
      high.hash.Sha256.Insts.RindHighHashHashSha256ContextSha256State.ALGORITHM, high.digest.SHA256]
    step with sha256_ctx_finish_spec hb p c hc hm as ⟨r, hr⟩
    step*
    apply WP.spec_mono (digest_new_spec _ s (by rw [s_post]; simp [outLen]))
    rintro d ⟨hd1, hd2⟩
    refine ⟨by rw [hd1]; rfl, ?_⟩
    rw [hd2, s_post, Array.val_to_slice, hr]
  zeroed_block := by
    simp only [high.hash.Sha256.Insts.RindHighHashHashSha256ContextSha256State.zeroed_block,
      high.hash.HashBlock.new, mid.sha2.Sha256Context.BLOCK_SZ]
    simp
  hash_default := rfl
  cclone := fun p c hc => WP.spec_mono (sha256_ctx_clone_spec c) fun _ h => h ▸ hc

/-! ## SHA-1, as SHA-256 above -/

/-! ## `mid::sha1::Sha1State` -/

/-- A SHA-1 state that has absorbed `P`, a whole number of blocks. -/
def Sha1Absorbed (P : List U8) (s : mid.sha1.Sha1State) : Prop :=
  Absorbed sha1.compress sha1.H0 P s.h ∧ s.nblocks.val * 64 = P.length

theorem sha1_finish_with_spec (hb : Sha1Blocks) (P : List U8) (s : mid.sha1.Sha1State)
    (message : Slice U8) (hs : Sha1Absorbed P s)
    (hlen : 8 * (P.length + message.length) ≤ U64.max) :
    mid.sha1.Sha1State.finish_with s message ⦃ r =>
      bv r.val = sha1.hash (bv (P ++ message.val)) ⦄ := by
  obtain ⟨⟨hh, hP⟩, hn⟩ := hs
  have hml : message.len.val = message.length := by simp [Slice.len, Slice.length]
  unfold mid.sha1.Sha1State.finish_with
  step*
  have hi : i.val = 64 := by
    rw [i_post]
    simp [mid.sha1.Sha1State.finish_with.BLOCK_SZ, mid.sha1.Sha1Context.BLOCK_SZ]
  rcases o with _ | z
  · simp only at o_post; rw [hi] at o_post; omega
  simp only at o_post
  have hz : z.val = P.length := by rw [o_post.2.1, hi, hn]
  simp only [core.option.Option.and_then,
    mid.sha1.Sha1State.finish_with.closure.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64.call_once]
  step*
  have hx : x.val = message.length := by rw [x_post, ← hml]; simp
  have ha := U64.checked_add_bv_spec z x
  rcases hz2 : z.checked_add x with _ | z2
  · rw [hz2] at ha; simp only at ha; omega
  rw [hz2] at ha
  simp only at ha
  simp only [mid.sha1.Sha1State.finish_with.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64.call_once,
    bind_ok]
  have hm := U64.checked_mul_bv_spec z2 8#u64
  have h8 : (8#u64).val = 8 := by simp
  rcases hz3 : z2.checked_mul 8#u64 with _ | bits
  · rw [hz3] at hm; simp only at hm; rw [h8] at hm; omega
  rw [hz3] at hm
  simp only at hm
  have hbits : bits.val = 8 * (P.length + message.length) := by rw [hm.2.1, h8, ha.2.1]; omega
  simp only [core.option.Option.expect, Result.ofOption, bind_ok, hb.held]
  step*
  step with sha1_compress_padded_spec hb P s.h message a ⟨hh, hP⟩ as ⟨h', hh'⟩
  simp only [core.slice.Slice.iter]
  step*
  have hv : (h'.val).length = 5 := h'.property
  apply WP.spec_mono (sha1_out_loop_spec iter _ h'.val hv ?_ ?_ ?_ ?_)
  · intro r hr
    rw [hr, bv_flatMap_beBytes, hh'.1, a_post, pad_bv P message.val bits hP hbits]
    rfl
  all_goals simp [iter_post, iter_post1, s_post, Array.val_to_slice]

theorem sha1_update_blocks_spec (hb : Sha1Blocks) (P : List U8) (s : mid.sha1.Sha1State)
    (blk : Slice U8) (hs : Sha1Absorbed P s) (hl : blk.length % 64 = 0)
    (hbound : P.length + blk.length ≤ U64.max) :
    mid.sha1.Sha1State.Insts.RindLowGenericBlockwiseUpdateBlocks.update_blocks s blk ⦃ s' => Sha1Absorbed (P ++ blk.val) s' ⦄ := by
  obtain ⟨hh, hn⟩ := hs
  have hbl : blk.len.val = blk.length := by simp [Slice.len, Slice.length]
  have h64 : mid.sha1.Sha1Context.BLOCK_SZ.val = 64 := by simp [mid.sha1.Sha1Context.BLOCK_SZ]
  obtain ⟨e, he⟩ := hb.entry
  unfold mid.sha1.Sha1State.Insts.RindLowGenericBlockwiseUpdateBlocks.update_blocks
  step*
  case h2 =>
    rw [he, bind_ok]
    step with sha1_block_spec hb s.h blk hl as ⟨a, ha⟩
    step*
    have hi3 : i3.val = blk.length / 64 := by
      rw [i3_post]; simp only [UScalar.cast_val_eq, i2_post, hbl, h64]
      apply Nat.mod_eq_of_lt; scalar_tac
    simp only [lift, bind_ok, WP.spec_ok]
    refine ⟨absorbed_append hh hl ha, ?_⟩
    simp only
    rw [saturating_add_val _ _ (by rw [hi3]; omega), hi3, List.length_append]
    simp only [Slice.length] at *
    omega
  all_goals
    rename_i h0
    have : blk.val = [] := List.eq_nil_of_length_eq_zero (by simpa [b1_post] using h0)
    simp only [this, List.append_nil]
    exact ⟨hh, hn⟩

theorem sha1_new_spec : mid.sha1.Sha1State.new ⦃ s => Sha1Absorbed [] s ⦄ := by
  unfold mid.sha1.Sha1State.new
  simp only [WP.spec_ok]
  refine ⟨⟨?_, by simp⟩, by simp⟩
  rw [bv, List.map_nil, blocks_nil, List.foldl_nil]
  simp [words, Std.Array.make, sha1.H0]

/-! ## `mid::sha1::Sha1Context` -/

/-- A SHA-1 context that has been given `p`. -/
def Sha1Ctx (p : List U8) (c : mid.sha1.Sha1Context) : Prop :=
  Buffered Sha1Absorbed p c.blockwise c.state

theorem sha1_resume_spec (P : List U8) (s : mid.sha1.Sha1State) (hs : Sha1Absorbed P s) :
    mid.sha1.Sha1Context.resume s ⦃ c => Sha1Ctx P c ⦄ := by
  unfold mid.sha1.Sha1Context.resume
  step with blockwise_new_spec as ⟨bw, hbw⟩
  exact ⟨by simp [hbw], P, hs, by simp [hbw]⟩

theorem sha1_ctx_update_spec (hb : Sha1Blocks) (p : List U8) (c : mid.sha1.Sha1Context)
    (bytes : Slice U8) (hc : Sha1Ctx p c) (hlen : p.length + bytes.length ≤ maxInput) :
    mid.sha1.Sha1Context.update c bytes ⦃ c' => Sha1Ctx (p ++ bytes.val) c' ⦄ := by
  unfold mid.sha1.Sha1Context.update
  step with update_spec (N := 64#usize)
    mid.sha1.Sha1State.Insts.RindLowGenericBlockwiseUpdateBlocks Sha1Absorbed maxInput
    (fun p s b hs hl hb' => sha1_update_blocks_spec hb p s b hs hl
      (by unfold maxInput at hb'; omega))
    p c.blockwise bytes c.state hc (by decide) hlen as ⟨bw, s', h⟩
  exact h

theorem sha1_ctx_finish_spec (hb : Sha1Blocks) (p : List U8) (c : mid.sha1.Sha1Context)
    (hc : Sha1Ctx p c) (hlen : p.length ≤ maxInput) :
    mid.sha1.Sha1Context.finish c ⦃ r => bv r.val = sha1.hash (bv p) ⦄ := by
  obtain ⟨hu, q, hq, hqp⟩ := hc
  unfold mid.sha1.Sha1Context.finish
  step with buffered_spec c.blockwise hu as ⟨m, hm⟩
  have hpl : q.length + m.length = p.length := by
    rw [← hqp]; simp only [Slice.length, hm, List.length_append]
  have := sha1_finish_with_spec hb q c.state m hq (by unfold maxInput at hlen; omega)
  rw [hm, hqp] at this
  exact this

theorem sha1_compress_length (H : List (BitVec 32)) (b : List Byte) (h : H.length = 5) :
    (sha1.compress H b).length = 5 := by
  simp only [sha1.compress, List.length_zipWith, h]
  rw [show 80 = 79 + 1 from rfl, List.range_succ, List.foldl_append]
  simp

theorem sha1_hash_length (m : List Byte) : (sha1.hash m).length = 20 := by
  simp only [sha1.hash, List.length_flatMap, BitVec.toBEBytes_length]
  rw [List.map_const', List.sum_replicate,
    foldl_length _ 5 sha1_compress_length _ _ (by simp [sha1.H0])]
  rfl

/-- SHA-1's `Hash` impl computes FIPS 180-4's SHA-1, given `Sha1Blocks`. -/
theorem sha1_hashSpec (hb : Sha1Blocks) :
    HashSpec high.hash.LegacySha1.Insts.RindHighHashHashSha1ContextSha1State sha1.hash 64 20
      maxInput Sha1Absorbed Sha1Ctx where
  out := ⟨by decide, by decide, by decide, by unfold maxInput; scalar_tac, sha1_hash_length⟩
  initial := by
    simp only [high.hash.LegacySha1.Insts.RindHighHashHashSha1ContextSha1State.initial]
    step with sha1_new_spec as ⟨s, hs⟩
    exact hs
  update_blocks := fun p s b hs hl hm => by
    simp only [high.hash.Sha1State.Insts.RindHighHashHashStateSha1Context.update_blocks]
    step with sha1_update_blocks_spec hb p s b hs hl (by unfold maxInput at hm; omega) as ⟨s', h⟩
    exact h
  finish_with := fun p s m hs hm => by
    simp only [high.hash.Sha1State.Insts.RindHighHashHashStateSha1Context.finish_with,
      high.hash.LegacySha1.Insts.RindHighHashHashSha1ContextSha1State.ALGORITHM, high.digest.SHA1]
    step with sha1_finish_with_spec hb p s m hs (by unfold maxInput at hm; omega) as ⟨r, hr⟩
    step*
    apply WP.spec_mono (digest_new_spec _ s (by rw [s_post]; simp [outLen]))
    rintro d ⟨hd1, hd2⟩
    refine ⟨by rw [hd1]; rfl, ?_⟩
    rw [hd2, s_post, Array.val_to_slice, hr]
  finish_uses_long := fun m => by
    simp only [high.hash.Sha1State.Insts.RindHighHashHashStateSha1Context.finish_uses_long]
    step*
  finish_with_after_long := fun p s m hs hm => by
    simp only [high.hash.Sha1State.Insts.RindHighHashHashStateSha1Context.finish_with_after_long]
    try simp only [high.hash.HashState.finish_with_after_long.default]
    simp only [high.hash.Sha1State.Insts.RindHighHashHashStateSha1Context.finish_with,
      high.hash.LegacySha1.Insts.RindHighHashHashSha1ContextSha1State.ALGORITHM, high.digest.SHA1]
    step with sha1_finish_with_spec hb p s m hs (by unfold maxInput at hm; omega) as ⟨r, hr⟩
    step*
    apply WP.spec_mono (digest_new_spec _ s (by rw [s_post]; simp [outLen]))
    rintro d ⟨hd1, hd2⟩
    refine ⟨by rw [hd1]; rfl, ?_⟩
    rw [hd2, s_post, Array.val_to_slice, hr]
  clone := fun p s hs => by
    simp only [high.hash.Sha1State.Insts.CoreCloneClone.clone,
      mid.sha1.Sha1State.Insts.CoreCloneClone.clone]
    step*
    simp only [core.clone.impls.CloneU64.clone, lift, bind_ok, WP.spec_ok]
    rw [← x_post]
    exact hs
  resume := fun p s hs => by
    simp only [high.hash.Sha1State.Insts.RindHighHashHashStateSha1Context.resume,
      mid.sha1.Sha1State.Insts.CoreCloneClone.clone]
    step*
    simp only [core.clone.impls.CloneU64.clone, lift, bind_ok]
    rw [← x_post]
    step with sha1_resume_spec p _ hs as ⟨c, hc⟩
    exact hc
  update := fun p c b hc hm => by
    simp only [high.hash.Sha1Context.Insts.RindHighHashHashContext.update]
    step with sha1_ctx_update_spec hb p c b hc hm as ⟨c', h⟩
    exact h
  finish := fun p c hc hm => by
    simp only [high.hash.Sha1Context.Insts.RindHighHashHashContext.finish,
      high.hash.LegacySha1.Insts.RindHighHashHashSha1ContextSha1State.ALGORITHM, high.digest.SHA1]
    step with sha1_ctx_finish_spec hb p c hc hm as ⟨r, hr⟩
    step*
    apply WP.spec_mono (digest_new_spec _ s (by rw [s_post]; simp [outLen]))
    rintro d ⟨hd1, hd2⟩
    refine ⟨by rw [hd1]; rfl, ?_⟩
    rw [hd2, s_post, Array.val_to_slice, hr]
  zeroed_block := by
    simp only [high.hash.LegacySha1.Insts.RindHighHashHashSha1ContextSha1State.zeroed_block,
      high.hash.HashBlock.new, mid.sha1.Sha1Context.BLOCK_SZ]
    simp
  hash_default := rfl
  cclone := fun p c hc => WP.spec_mono (sha1_ctx_clone_spec c) fun _ h => h ▸ hc

end rind.x86_64
