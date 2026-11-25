import Rind.X86_64.ChaCha20Avx2
open Aeneas Aeneas.Std Result rind.spec

/-!
# `cipher::ChaCha20` on x86_64, at every length

`ChaCha20::cipher` picks one of four routines by the CPU and the buffer's
length: where `new` picked a VG routine (the CPU-feature checks found AVX2 or
AVX-512 VL), pyca/verified-garbage's (VG's) from 256 bytes, with rind's
two-block kernel over a remainder of 65 to 255 bytes after the last whole
512-byte group, and the kernel alone from 65 bytes; where it picked none but
found SSSE3, aws-lc's `ChaCha20_ctr32_ssse3_4x` from 129 bytes; and HACL*'s
rounds, in rind's loop, otherwise. `Rind.X86_64.VgChaCha20` proves VG's path
over axioms restating VG's theorems, `Rind.X86_64.ChaCha20Avx2` the kernel,
and this file HACL*'s loop, `cipher`, and the API's `apply_keystream`, at
every length.

aws-lc's SSSE3 routine has no proof yet, so the theorems take its contract as
the hypothesis `Ssse3`, which [the x86_64 cipher
quest](/quest/m4/verified/chacha20-poly1305-x86/cipher.md) is to prove. A call
where `new` picked a VG routine never runs it.
-/

namespace rind.x86_64.generic
/-! ## HACL*'s rounds over a message, `low::generic::chacha20::cipher` -/

/-- The loop that XORs a block's keystream is the kernel's, statement for
statement. -/
theorem xor_loop_eq :
    low.generic.chacha20.cipher_loop0_loop0 = low.x86_64.chacha20.core_2x_loop1 := by
  funext it b ks
  rfl

/-- RFC 8439's encryption of up to one block: the message XOR its keystream. -/
theorem encrypt_one (key nonce msg : List (BitVec 8)) (c : BitVec 32) (hk : key.length = 32)
    (hn : nonce.length = 12) (hm : msg.length ≤ 64) :
    chacha20.encrypt key c nonce msg = List.zipWith (· ^^^ ·) msg (chacha20.block key c nonce) := by
  have hb : (chacha20.block key c nonce).length = 64 := s2n.length_block _ _ _ hk hn
  rw [avx2.encrypt_two _ _ _ _ hk hn (by omega), ← vg.zipWith_take_length,
    List.take_append_of_le_length (by omega), vg.zipWith_take_length]

/-- The input words for block counter `c`. -/
def inputOf (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize) (c : U32) : List U32 :=
  low.generic.chacha20.SIGMA.val ++ key.val ++ [c] ++ cn.val.drop 1

theorem keystream_inputOf (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize) (c : U32) :
    (List.zipWith (· + ·) (chacha20.innerBlock^[10] ((inputOf key cn c).map (·.bv)))
        ((inputOf key cn c).map (·.bv))).flatMap BitVec.toLEBytes =
      chacha20.block (wordBytes key.val) c.bv (wordBytes (cn.val.drop 1)) := by
  simp only [inputOf, chacha20.block, wordBytes, vg.words_flatMap, List.map_append, SIGMA_bv,
    List.map_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem length_inputOf (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize) (c : U32) :
    (inputOf key cn c).length = 16 := by
  simp [inputOf]

theorem inputOf_set (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize) (c x : U32) :
    (inputOf key cn c).set 12 x = inputOf key cn x := by
  simp [inputOf]

theorem inputOf_get (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize) (c : U32) :
    (inputOf key cn c)[12]! = c := by
  simp [inputOf]


/-- `cipher`'s loop: if the bytes before `done` are encrypted, the rest are the
message's, and the state holds the block counter for `done`, the whole buffer
ends encrypted. -/
theorem cipher_loop0_spec (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize)
    (msg : List (BitVec 8)) (buffer : Slice U8) (input : Std.Array U32 16#usize) (done : Usize)
    (hm : msg.length = buffer.length) (hd : done.val ≤ buffer.length)
    (hc : (done.val % 64 = 0 ∧ ∃ c : U32, input.val = inputOf key cn c ∧
        c.bv = cn.val[0]!.bv + BitVec.ofNat 32 (done.val / 64)) ∨
      done.val = buffer.length)
    (hpre : (bvs buffer.val).take done.val =
      chacha20.encrypt (wordBytes key.val) cn.val[0]!.bv (wordBytes (cn.val.drop 1)) (msg.take done.val))
    (hpost : (bvs buffer.val).drop done.val = msg.drop done.val) :
    low.generic.chacha20.cipher_loop0 buffer input done ⦃ r =>
      bvs r.val = chacha20.encrypt (wordBytes key.val) cn.val[0]!.bv (wordBytes (cn.val.drop 1)) msg ⦄ := by
  unfold low.generic.chacha20.cipher_loop0
  apply loop.spec_decr_nat (fun x => buffer.length - x.2.2.val)
    (fun x => x.1.length = buffer.length ∧ x.2.2.val ≤ buffer.length ∧
      ((x.2.2.val % 64 = 0 ∧ ∃ c : U32, x.2.1.val = inputOf key cn c ∧
          c.bv = cn.val[0]!.bv + BitVec.ofNat 32 (x.2.2.val / 64)) ∨
        x.2.2.val = buffer.length) ∧
      (bvs x.1.val).take x.2.2.val =
        chacha20.encrypt (wordBytes key.val) cn.val[0]!.bv (wordBytes (cn.val.drop 1)) (msg.take x.2.2.val) ∧
      (bvs x.1.val).drop x.2.2.val = msg.drop x.2.2.val)
  · rintro ⟨buf, inp, dn⟩ ⟨h0, h1, h2, h3, h4⟩
    simp only at h0 h1 h2 h3 h4 ⊢
    have hbl : buf.val.length = buf.length := rfl
    unfold low.generic.chacha20.cipher_loop0.body
    by_cases hlt : dn.val < buf.length
    · obtain ⟨h64, c, hinp, hc⟩ : dn.val % 64 = 0 ∧ ∃ c : U32, inp.val = inputOf key cn c ∧
          c.bv = cn.val[0]!.bv + BitVec.ofNat 32 (dn.val / 64) := by
        rcases h2 with h2 | h2
        · exact h2
        · omega
      rw [xor_loop_eq]
      step*
      split <;> step*
      all_goals try scalar_tac
      all_goals
        have hi3 : i3.val ≤ buf.length := by scalar_tac
        have hn64 : i3.val - dn.val ≤ 64 := by scalar_tac
        have hbm : (bvs buf.val).length = msg.length := by rw [bvs, List.length_map]; omega
        have hlen : buf.len.val = buf.length := by simp
        have hk32 : (wordBytes key.val).length = 32 := by simp [length_wordBytes]
        have hn12 : (wordBytes (cn.val.drop 1)).length = 12 := by simp [length_wordBytes]
        have hks : bvs ks.val = chacha20.block (wordBytes key.val) c.bv (wordBytes (cn.val.drop 1)) := by
          rw [← keystream_inputOf, ← hinp]; exact ks_post
        have hblk : bvs block.val = (msg.drop dn.val).take (i3.val - dn.val) := by
          rw [block_post]; simp [bvs, List.slice, ← h4, List.map_take, List.map_drop]
        have hk1 : bvs ks1.val = (bvs ks.val).take ks1.length := by
          rw [ks1_post1, ks1_post]; simp [bvs, List.slice, List.map_take]
        have hkb : ks1.val.length = block.val.length := by scalar_tac
        have hb := avx2.chunk_step (wordBytes key.val) (wordBytes (cn.val.drop 1)) (bvs buf.val) msg
          (bvs block1.val) cn.val[0]!.bv dn.val i3.val hbm (by omega)
          (by omega) (by simp [bvs, block1_post, block_post1]) (by omega) h3 h4 (by
            rw [block1_post1, hk1, show ks1.length = (bvs block.val).length by simp [bvs, hkb],
              vg.zipWith_take_length, hks, ← hc, hblk,
              encrypt_one _ _ _ _ hk32 hn12 (by simp only [List.length_take, List.length_drop]; omega)])
        simp only [block_post2, Slice.setSlice!_val, bvs, List.map_setSlice!] at hb ⊢
        have hd2 : done2.val = i3.val := by omega
        refine ⟨by simp [h0], by omega, ?_, by rw [hd2]; exact hb.1, by rw [hd2]; exact hb.2, by omega⟩
        by_cases hfull : done2.val = buffer.length
        · exact Or.inr hfull
        · have h64' : done2.val = dn.val + 64 := by omega
          refine Or.inl ⟨by omega, i6, by simp [a_post, hinp, inputOf_set], ?_⟩
          rw [i6_post, core.num.U32.wrapping_add_bv_eq, i5_post, ← getElem!_pos inp.val 12 (by simp), hinp,
            inputOf_get, hc, h64', show (dn.val + 64) / 64 = dn.val / 64 + 1 by omega, BitVec.ofNat_add,
            BitVec.add_assoc]
          rfl
    · simp only [Slice.len, show ¬ dn < buf.len from by scalar_tac, ite_false, WP.spec_ok]
      have hdn : dn.val = buffer.length := by omega
      have hl : (bvs buf.val).length = dn.val := by simp [bvs]; omega
      have hml : msg.length ≤ dn.val := by omega
      rw [← hl, List.take_length, hl, List.take_of_length_le hml] at h3
      exact h3
  · exact ⟨rfl, hd, hc, hpre, hpost⟩


/-- HACL*'s rounds, in rind's loop, encrypt the buffer as the Lean model's
`chacha20.encrypt` does, the block counter wrapping past 2^32 - 1 as that
model's does; the API refuses such a buffer before it gets here. -/
theorem cipher_spec (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize) (buffer : Slice U8) :
    low.generic.chacha20.cipher key cn buffer ⦃ r =>
      bvs r.val = chacha20.encrypt (wordBytes key.val) cn.val[0]!.bv (wordBytes (cn.val.drop 1))
        (bvs buffer.val) ⦄ := by
  unfold low.generic.chacha20.cipher
  step*
  have hin : (index_mut_back2 s8).val = inputOf key cn cn.val[0]! := by
    obtain ⟨n0, n1, n2, n3, hn⟩ := avx2.list4 cn.val (by simp)
    have hs : low.generic.chacha20.SIGMA.val.length = 4 := by simp
    have hk : key.val.length = 8 := by simp
    rw [s6_post2, s3_post2, s_post2, s8_post, s7_post, s5_post, s4_post, s2_post, s1_post]
    simp only [Array.val_to_slice]
    rw [avx2.setSlice!_split _ _ _ (by simp), avx2.setSlice!_split _ _ _ (by simp [hk]),
      avx2.setSlice!_split _ _ _ (by simp [hs])]
    simp [inputOf, hn, hs, hk, List.take_append, List.drop_append, List.take_of_length_le]
  apply cipher_loop0_spec key cn (bvs buffer.val) buffer _ 0#usize (by simp [bvs]) (by simp)
    (Or.inl ⟨by simp, cn.val[0]!, hin, by simp⟩) (by simp [avx2.encrypt_nil]) (by simp)

end rind.x86_64.generic

namespace rind.x86_64

open low.x86_64.chacha20 (VgState)

/-! ## The dispatch, `ChaCha20::cipher` -/

/-- aws-lc's `ChaCha20_ctr32_ssse3_4x`, as `cipher_ssse3_4x` calls it, XORs
RFC 8439's keystream into a nonempty buffer, as its safety contract requires,
for as many blocks as remain before the block counter wraps. -/
def Ssse3 : Prop :=
  ∀ (t : low.x86_64.cpu.HaveSsse3) (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize)
    (buffer : Slice U8), 0 < buffer.length →
    counter_nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32 →
    low.x86_64.chacha20.cipher_ssse3_4x t key counter_nonce buffer ⦃ r =>
      bvs r.val = chacha20.encrypt (wordBytes key.val) counter_nonce.val[0]!.bv
        (wordBytes (counter_nonce.val.drop 1)) (bvs buffer.val) ⦄

/-- `cipher` XORs RFC 8439's keystream into the buffer, for as many blocks as
remain before the block counter wraps, on whichever routine it picks: VG's
and the kernel where `new` picked a VG routine, aws-lc's SSSE3 routine where
it did not and found SSSE3, and HACL*'s rounds otherwise. -/
theorem cipher_all_spec (hu : ∃ s, VgState.uninit = ok s) (c : low.x86_64.chacha20.ChaCha20)
    (hs : c.vg.isSome ∨ Ssse3) (buffer : Slice U8)
    (hl : c.counter_nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32) :
    low.x86_64.chacha20.ChaCha20.cipher c buffer ⦃ _ r =>
      bvs r.val = chacha20.encrypt (wordBytes c.key.val) c.counter_nonce.val[0]!.bv
        (wordBytes (c.counter_nonce.val.drop 1)) (bvs buffer.val) ⦄ := by
  by_cases hv : c.vg.isSome ∧ 256 ≤ buffer.length
  · exact cipher_spec hu avx2.kernel c hv.1 buffer hv.2 hl
  unfold low.x86_64.chacha20.ChaCha20.cipher
  refine WP.spec_bind (Pₘ := fun b1 : Slice U8 => bvs b1.val = chacha20.encrypt (wordBytes c.key.val)
    c.counter_nonce.val[0]!.bv (wordBytes (c.counter_nonce.val.drop 1)) (bvs buffer.val)) ?_ ?_
  rotate_left
  · intro b1 hb1
    simp only [core.num.Usize.div_ceil, lift, show ¬ (64#usize : Usize).val = 0 by decide, ↓reduceDIte,
      bind_ok]
    step*
  rcases hvg : c.vg with _ | v
  · rcases hss : c.ssse3 with _ | t
    · exact generic.cipher_spec _ _ _
    · simp only
      split
      · rcases hs with hs | hs
        · simp [hvg] at hs
        · exact hs t _ _ _ (by scalar_tac) hl
      · exact generic.cipher_spec _ _ _
  · simp only
    have h256 : ¬ 256 ≤ buffer.length := fun h => hv ⟨by simp [hvg], h⟩
    split
    · exfalso; scalar_tac
    split
    · exact avx2.kernel _ _ _ hl
    · exact generic.cipher_spec _ _ _

/-! ## The API, `mid::chacha20` -/

/-- rind runs VG's routines for ChaCha20 on this CPU: the entry guard admits
the call, a state can be made, and the CPU-feature checks find AVX2, or
AVX-512 VL. None reads an input. -/
def RunsVg : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ (∃ s, VgState.uninit = ok s) ∧
  ∃ a b s, low.x86_64.cpu.HaveAvx512Vl.check = ok a ∧ low.x86_64.cpu.HaveAvx2.check = ok b ∧
    low.x86_64.cpu.HaveSsse3.check = ok s ∧ (a.isSome ∨ b.isSome)

/-- rind runs ChaCha20 on this CPU: the entry guard admits the call, a VG
state can be made, and the CPU-feature checks return, whatever they find.
None reads an input. -/
def RunsCipher : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ (∃ s, VgState.uninit = ok s) ∧
  ∃ a b s, low.x86_64.cpu.HaveAvx512Vl.check = ok a ∧ low.x86_64.cpu.HaveAvx2.check = ok b ∧
    low.x86_64.cpu.HaveSsse3.check = ok s

/-- ChaCha20 on a CPU where `new` picks a VG routine, or aws-lc's SSSE3
routine meets its contract: RFC 8439's encryption of the buffer under the key,
the block counter, and the nonce, if the counter covers it before it wraps;
otherwise `WrongLength`, with the buffer unchanged. -/
theorem apply_keystream_spec (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hu : ∃ s, VgState.uninit = ok s)
    (a : Option low.x86_64.cpu.HaveAvx512Vl) (b : Option low.x86_64.cpu.HaveAvx2)
    (s : Option low.x86_64.cpu.HaveSsse3) (ha : low.x86_64.cpu.HaveAvx512Vl.check = ok a)
    (hb : low.x86_64.cpu.HaveAvx2.check = ok b) (hs : low.x86_64.cpu.HaveSsse3.check = ok s)
    (hab : (a.isSome ∨ b.isSome) ∨ Ssse3) (k : mid.chacha20.ChaCha20)
    (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8) :
    k.apply_keystream nonce counter inout ⦃ r inout' =>
      if counter.val + (inout.length + 63) / 64 ≤ 2 ^ 32 then
        r = .Ok () ∧
          bvs inout'.val = chacha20.encrypt (bvs k.key.val) counter.bv (bvs nonce.val) (bvs inout.val)
      else r = .Err .WrongLength ∧ inout' = inout ⦄ := by
  obtain ⟨e, he⟩ := he
  unfold mid.chacha20.ChaCha20.apply_keystream
  simp only [he, bind_ok, low.ct.secret_slice, low.ct.public_slice]
  step*
  · rw [Slice.len_val] at r_post
    split_ifs at r_post with hc
    · subst r_post
      simp only [hc, ↓reduceIte]
      have hT : counter.bv.toLEBytes.length = 4 := by simp [BitVec.toLEBytes_length]
      have hB : wordBytes cc.counter_nonce.val = counter.bv.toLEBytes ++ bvs nonce.val := by
        rw [cc_post1, s3_post2, s5_post, s4_post, s_post2, s2_post, s1_post]
        have hnl : nonce.val.length = 12 := nonce.property
        simp [List.setSlice!, a_post, hT, bvs, Function.comp_def]
        rw [List.take_of_length_le (by rw [hT]), List.take_of_length_le (by simp [hnl])]
      have hcn0 : cc.counter_nonce.val[0]!.bv = counter.bv := by
        rw [← wordLE_wordBytes _ (by simp), hB]
        conv_rhs => rw [← vg.wordLE_toLEBytes counter.bv]
        simp only [VG.Spec.ChaCha20.wordLE, List.getD_eq_getElem?_getD, Nat.mul_zero, Nat.zero_add]
        rw [List.getElem?_append_left (by simp [BitVec.toLEBytes_length]),
          List.getElem?_append_left (by simp [BitVec.toLEBytes_length]),
          List.getElem?_append_left (by simp [BitVec.toLEBytes_length]),
          List.getElem?_append_left (by simp [BitVec.toLEBytes_length])]
      have hcnd : wordBytes (cc.counter_nonce.val.drop 1) = bvs nonce.val := by
        rw [← wordBytes_drop_one, hB, List.drop_left' hT]
      have hcv : cc.counter_nonce.val[0]!.val = counter.val := by
        have := congrArg BitVec.toNat hcn0
        simpa only [UScalar.bv_toNat] using this
      step with cipher_all_spec hu cc (hab.imp_left cc_post2.mpr) inout (by rw [hcv]; exact hc)
        as ⟨c', inout1, h1⟩
      step*
    · subst r_post
      simp_all
  · rw [Slice.len_val] at r_post
    split_ifs at r_post ⊢ <;> subst r_post <;> simp_all

/-- ChaCha20 where the CPU-feature checks find AVX2 or AVX-512 VL: RFC 8439's
encryption of the buffer under the key, the block counter, and the nonce, if
the counter covers it before it wraps; otherwise `WrongLength`, with the
buffer unchanged. -/
theorem chacha20_apply_keystream (h : RunsVg) (k : mid.chacha20.ChaCha20)
    (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8) :
    k.apply_keystream nonce counter inout ⦃ r inout' =>
      if counter.val + (inout.length + 63) / 64 ≤ 2 ^ 32 then
        r = .Ok () ∧
          bvs inout'.val = chacha20.encrypt (bvs k.key.val) counter.bv (bvs nonce.val) (bvs inout.val)
      else r = .Err .WrongLength ∧ inout' = inout ⦄ :=
  let ⟨he, hu, a, b, s, ha, hb, hs, hab⟩ := h
  apply_keystream_spec he hu a b s ha hb hs (Or.inl hab) k nonce counter inout

/-- ChaCha20 on any x86_64 CPU, if aws-lc's SSSE3 routine meets its
contract: RFC 8439's encryption of the buffer under the key, the block
counter, and the nonce, if the counter covers it before it wraps; otherwise
`WrongLength`, with the buffer unchanged. -/
theorem chacha20_apply_keystream_ssse3 (h : RunsCipher) (hs : Ssse3) (k : mid.chacha20.ChaCha20)
    (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8) :
    k.apply_keystream nonce counter inout ⦃ r inout' =>
      if counter.val + (inout.length + 63) / 64 ≤ 2 ^ 32 then
        r = .Ok () ∧
          bvs inout'.val = chacha20.encrypt (bvs k.key.val) counter.bv (bvs nonce.val) (bvs inout.val)
      else r = .Err .WrongLength ∧ inout' = inout ⦄ :=
  let ⟨he, hu, a, b, s, ha, hb, hs'⟩ := h
  apply_keystream_spec he hu a b s ha hb hs' (Or.inr hs) k nonce counter inout

end rind.x86_64
