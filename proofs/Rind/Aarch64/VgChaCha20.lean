import Rind.Aarch64.ChaCha20
import Rind.VgChaCha20Glue
open Aeneas Aeneas.Std Result rind.spec
open VG.Spec.ChaCha20 (bytesAt keyAt leftAt restAt keystreamOf wordLE)

/-!
# `cipher::ChaCha20` on aarch64, on pyca/verified-garbage's routines

`cipher::ChaCha20` runs pyca/verified-garbage's (VG's) routines over the
whole request: where the CPU has SVE2, `vg_chacha20_apply_sve2` from 128
bytes, and otherwise `vg_chacha20_apply_neon` from 192 to 256 bytes and from
448, each after `vg_chacha20_init`. Every other request runs rind's NEON
code. The axioms below restate VG's Lean theorems about those three
routines about the Rust wrappers that call them, `VgState::init`,
`VgState::apply_neon`, and `VgState::apply_sve2`, over VG's own spec,
`VerifiedGarbage.Spec.ChaCha20`, which `admin/import-vg-models` vendors byte
for byte. `cipher_vg_spec` composes them, and `chacha20_apply_keystream_vg`
proves the API's result from them on the requests VG runs: RFC 8439's
encryption, as `Rind.Spec` transliterates it.

rind's NEON code has no proof yet, so `chacha20_apply_keystream`, at every
length, takes its contract as the hypothesis `Neon`, which [the aarch64
ChaCha20-Poly1305 quest](/quest/m4/verified/chacha20-poly1305-aarch64.md) is
to prove. A request VG runs never reaches it.

Trusted: each restatement, and that each wrapper passes the routine its
state's 768 bytes, which `Rind.Aarch64.TypesExternal` models as the state,
and the key's and counter and nonce's words as the little-endian bytes VG
reads, which they are on aarch64. That VG's definitions of the state's key
and keystream read only those 768 bytes is proven (`Rind.VgChaCha20`'s
`keyAt_congr`, `leftAt_congr`, and `restAt_congr`), so the axioms, which
hold for any memory holding them, say no more than VG's theorems. VG's
theorems rest on its models of the instructions, which `admin/prove vg`
cosimulates for each instruction of VG's code rind runs, on the CPU or,
where it lacks SVE2, under qemu-aarch64, but for `b`, static addresses, and
a lone `ret`, which its check that rind's copies are VG's text covers; and on
VG's own Lean kernel check, at the commit `admin/import-vg` pins.
-/

namespace rind.aarch64

open low.aarch64.chacha20 (VgState)

export vg (wordBytes length_wordBytes wordBytes_drop_one wordLE_wordBytes)

/-! ## verified-garbage's routines, restated

VG's contracts (`Spec/ChaCha20/Contract.lean`) are over its model's memory
`m` before the call and `m'` after, with the state at `p`: each axiom holds
for any `m` and `m'` holding the state's 768 bytes at `p` before and after
the call, and reads the key's and counter and nonce's words for the bytes at
theirs, and the data's bytes for those at the data. Each precondition holds
for every call safe Rust makes: the state is 768 bytes; the state and the
data, which the routines write, are objects distinct from every other
argument, so neither overlaps another argument or the stack below the stack
pointer; no argument wraps the address space; rind requires NEON; and
the token proves SVE2. VG's contracts hold for any bytes of the state, so
these do too, and need no premise that `init` has run. A slice's length is
its own, which no call changes. -/

/-- VG's `vg_chacha20_init` on aarch64 meets `VG.Spec.ChaCha20.initContract`
([`Stream.initCleared_verified`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20/AArch64/Stream/Init.lean#L356),
which [`Artifacts/ChaCha20/AArch64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/ChaCha20/AArch64.lean)
registers as the code VG emits for `initApi`): the state holds the key and
the whole keystream for the counter and nonce. -/
@[step]
axiom vg_chacha20_init_spec (st : VgState) (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize) :
    VgState.init st key counter_nonce ⦃ st' =>
      ∀ (m' : VG.Mem) (p : VG.Addr), bytesAt m' p 768 = bvs st'.val →
        keyAt m' p = wordBytes key.val ∧
        restAt m' p = keystreamOf (wordBytes key.val) (wordBytes counter_nonce.val) ⦄

/-- VG's `vg_chacha20_apply_neon` on aarch64 meets
`VG.Spec.ChaCha20.applyContract`
([`Stream.apply_verified`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20/AArch64/Stream/ApplyCT.lean#L330)
at its `neon` variant, which
[`Artifacts/ChaCha20/AArch64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/ChaCha20/AArch64.lean)
registers as the code VG emits for `applyApi` with the suffix `neon`): if at
least the data's length of keystream is left, it XORs the next bytes of it
into the data, keeps the rest, and returns 1; otherwise it returns 0 and
changes neither. -/
@[step]
axiom vg_chacha20_apply_neon_spec (st : VgState) (data : Slice U8) :
    VgState.apply_neon st data ⦃ r st' data' =>
      data'.length = data.length ∧
      ∀ (m m' : VG.Mem) (p : VG.Addr), bytesAt m p 768 = bvs st.val → bytesAt m' p 768 = bvs st'.val →
        keyAt m' p = keyAt m p ∧
        if data.length ≤ leftAt m p then
          r.val = 1 ∧
            bvs data'.val = List.zipWith (· ^^^ ·) (bvs data.val) ((restAt m p).take data.length) ∧
            restAt m' p = (restAt m p).drop data.length
        else
          r.val = 0 ∧ bvs data'.val = bvs data.val ∧ restAt m' p = restAt m p ⦄

/-- VG's `vg_chacha20_apply_sve2` on aarch64 meets
`VG.Spec.ChaCha20.applyContract`, as `vg_chacha20_apply_neon_spec` states,
at `Stream.apply_verified`'s `sve2` variant. -/
@[step]
axiom vg_chacha20_apply_sve2_spec (st : VgState) (t : low.aarch64.cpu.HaveSve2) (data : Slice U8) :
    VgState.apply_sve2 st t data ⦃ r st' data' =>
      data'.length = data.length ∧
      ∀ (m m' : VG.Mem) (p : VG.Addr), bytesAt m p 768 = bvs st.val → bytesAt m' p 768 = bvs st'.val →
        keyAt m' p = keyAt m p ∧
        if data.length ≤ leftAt m p then
          r.val = 1 ∧
            bvs data'.val = List.zipWith (· ^^^ ·) (bvs data.val) ((restAt m p).take data.length) ∧
            restAt m' p = (restAt m p).drop data.length
        else
          r.val = 0 ∧ bvs data'.val = bvs data.val ∧ restAt m' p = restAt m p ⦄

/-! ## Composing the routines, `cipher_vg` -/

/-- VG's routines XOR RFC 8439's keystream for the key and the counter and
nonce into a buffer, for as many blocks as remain before the block counter
wraps, on either routine. -/
@[step]
theorem cipher_vg_spec (hu : ∃ s, VgState.uninit = ok s) (sve2 : Option low.aarch64.cpu.HaveSve2)
    (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize) (buffer : Slice U8)
    (hl : counter_nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32) :
    low.aarch64.chacha20.cipher_vg sve2 key counter_nonce buffer ⦃ r =>
      bvs r.val = chacha20.encrypt (wordBytes key.val) counter_nonce.val[0]!.bv
        (wordBytes (counter_nonce.val.drop 1)) (bvs buffer.val) ⦄ := by
  obtain ⟨s, hs⟩ := hu
  unfold low.aarch64.chacha20.cipher_vg
  simp only [hs, bind_ok]
  step as ⟨st, hst⟩
  have hm := vg.bytesAt_mem_state
  obtain ⟨-, hr⟩ := hst _ 0 (hm st)
  have hn := vg.leftAt_init _ _ key counter_nonce hr buffer.length hl
  have he := vg.keystream_encrypt key counter_nonce (bvs buffer.val) (by rw [length_bvs]; exact hl)
  rw [length_bvs] at he
  cases sve2 <;>
  · step as ⟨r, _, happ⟩
    obtain ⟨r1, st', b'⟩ := r
    simp only at happ
    obtain ⟨-, hif⟩ := happ _ _ 0 (hm st) (hm st')
    rw [ite_eq_left hn, hr] at hif
    obtain ⟨hr1, hb, -⟩ := hif
    have hr1' : r1 = 1#u32 := by scalar_tac
    subst hr1'
    step*

/-! ## The key and the counter and nonce as words, `ChaCha20::new` -/

theorem words_loop_spec {B W : Usize} (bytes : Std.Array U8 B) (iter : core.ops.range.Range Usize)
    (ws : Std.Array U32 W) (F : List (BitVec 32)) (hB : B.val = 4 * W.val) (hs : iter.start.val ≤ W.val)
    (he : iter.end.val = W.val)
    (hF : (List.range' iter.start.val (W.val - iter.start.val)).foldl
      (fun l i => l.set i (chacha20.words (bvs bytes.val))[i]!) (ws.val.map (·.bv)) = F) :
    low.aarch64.chacha20.words_loop iter bytes ws ⦃ r => r.val.map (·.bv) = F ⦄ := by
  unfold low.aarch64.chacha20.words_loop
  apply loop.spec_decr_nat (fun x => W.val - x.1.start.val)
    (fun x => x.1.start.val ≤ W.val ∧ x.1.end.val = W.val ∧
      (List.range' x.1.start.val (W.val - x.1.start.val)).foldl
        (fun l i => l.set i (chacha20.words (bvs bytes.val))[i]!) (x.2.val.map (·.bv)) = F)
  · rintro ⟨it, ws⟩ ⟨hs, he, hF⟩
    simp only at hs he hF ⊢
    unfold low.aarch64.chacha20.words_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      have hb : (bytes.val.length) = B.val := bytes.property
      step*
      refine ⟨by agrind, by agrind, ?_, by agrind⟩
      have hr : List.range' it.start.val (W.val - it.start.val) =
          it.start.val :: List.range' it'.start.val (W.val - it'.start.val) := by
        rw [hst, show W.val - it.start.val = (W.val - (it.start.val + 1)) + 1 by agrind]
        rfl
      rw [hr, List.foldl_cons] at hF
      rw [← hF]
      congr 1
      simp only [a_post, Array.set_val_eq, List.map_set]
      congr 1
      rw [i9_post]
      refine (fromLEBytes_le32 i2 i4 i6 i8).trans ?_
      rw [words_getElem! _ _ (by simp [bvs]; agrind)]
      simp only [i2_post, i4_post, i6_post, i8_post, i7_post, i5_post, i3_post, i1_post, bv_getElem, bvs]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have hW : it.start.val = W.val := by agrind
      simpa [hW] using hF
  · exact ⟨hs, he, hF⟩

@[step]
theorem words_spec {B : Usize} (W : Usize) (bytes : Std.Array U8 B) (hB : B.val = 4 * W.val) :
    low.aarch64.chacha20.words W bytes ⦃ r => r.val.map (·.bv) = chacha20.words (bvs bytes.val) ⦄ := by
  unfold low.aarch64.chacha20.words
  have hb : (bvs bytes.val).length = 4 * W.val := by simp [bvs, hB]
  have hw : (chacha20.words (bvs bytes.val)).length = W.val := by simp [chacha20.words, hb]
  step*
  apply words_loop_spec bytes _ _ _ hB (by simp) (by simp)
  rw [vg.foldl_set_range' _ _ _ _ (by simp)]
  apply List.ext_getElem (by simp [hw])
  intro i h1 h2
  simp [List.getElem_range', List.getElem?_eq_getElem h2]

/-- `ChaCha20::new` holds the key and the counter and nonce as words, and
SVE2's token where the CPU has it. -/
@[step]
theorem new_spec (key : Std.Array U8 32#usize) (counter_nonce : Std.Array U8 16#usize)
    (s : Option low.aarch64.cpu.HaveSve2) (hs : low.aarch64.cpu.HaveSve2.check = ok s) :
    low.aarch64.chacha20.ChaCha20.new key counter_nonce ⦃ c =>
      wordBytes c.key.val = bvs key.val ∧ wordBytes c.counter_nonce.val = bvs counter_nonce.val ∧
      c.sve2 = s ⦄ := by
  unfold low.aarch64.chacha20.ChaCha20.new
  simp only [hs, bind_ok]
  step with words_spec 8#usize key (by simp) as ⟨k, hk⟩
  step with words_spec 4#usize counter_nonce (by simp) as ⟨cn, hcn⟩
  have e1 := vg.wordBytes_of_words _ _ 8 (by simp [bvs]) hk
  have e2 := vg.wordBytes_of_words _ _ 4 (by simp [bvs]) hcn
  simp [e1, e2]

/-! ## Which routine runs, `ChaCha20::cipher` -/

/-- rind's NEON code's contract: for as many blocks as remain before the
32-bit block counter wraps, it XORs RFC 8439's keystream for the key and the
counter and nonce into the buffer, as `cipher` calls it. -/
def Neon : Prop :=
  ∀ (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize) (buffer : Slice U8),
    counter_nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32 →
    low.aarch64.chacha20.cipher_neon key counter_nonce buffer ⦃ r =>
      bvs r.val = chacha20.encrypt (wordBytes key.val) counter_nonce.val[0]!.bv
        (wordBytes (counter_nonce.val.drop 1)) (bvs buffer.val) ⦄

/-- `cipher` runs VG's routines on this request: from 128 bytes where the
CPU has SVE2, and otherwise from 192 to 256 bytes and from 448. -/
def RunsVgAt (sve2 : Option low.aarch64.cpu.HaveSve2) (len : Nat) : Prop :=
  match sve2 with
  | some _ => 128 ≤ len
  | none => (192 ≤ len ∧ len ≤ 256) ∨ 448 ≤ len

/-- `cipher` XORs RFC 8439's keystream into the buffer, for as many blocks as
remain before the block counter wraps, on VG's routines where `RunsVgAt`
says it runs them, and on rind's NEON code, if it meets `Neon`, otherwise. -/
theorem cipher_spec (hu : ∃ s, VgState.uninit = ok s) (c : low.aarch64.chacha20.ChaCha20)
    (buffer : Slice U8) (hn : RunsVgAt c.sve2 buffer.length ∨ Neon)
    (hl : c.counter_nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32) :
    low.aarch64.chacha20.ChaCha20.cipher c buffer ⦃ _ r =>
      bvs r.val = chacha20.encrypt (wordBytes c.key.val) c.counter_nonce.val[0]!.bv
        (wordBytes (c.counter_nonce.val.drop 1)) (bvs buffer.val) ⦄ := by
  unfold low.aarch64.chacha20.ChaCha20.cipher
  refine WP.spec_bind (Pₘ := fun b1 : Slice U8 => bvs b1.val = chacha20.encrypt (wordBytes c.key.val)
    c.counter_nonce.val[0]!.bv (wordBytes (c.counter_nonce.val.drop 1)) (bvs buffer.val)) ?_ ?_
  rotate_left
  · intro b1 hb1
    simp only [core.num.Usize.div_ceil, lift, show ¬ (64#usize : Usize).val = 0 by decide, ↓reduceDIte,
      bind_ok]
    step*
  have hvg := cipher_vg_spec hu c.sve2 c.key c.counter_nonce buffer hl
  have hneon : ¬ RunsVgAt c.sve2 buffer.length → _ := fun h =>
    (hn.resolve_left h) c.key c.counter_nonce buffer hl
  rcases hs : c.sve2 with _ | t <;> simp only [hs, RunsVgAt] at hvg hneon ⊢ <;>
    split_ifs <;> first | exact hvg | exact hneon (by scalar_tac)

/-! ## The API, `mid::chacha20` -/

/-- The 32-bit block counter `counter` covers `len` bytes, or the check fails. -/
@[step]
theorem check_counter_spec (counter : U32) (len : Usize) :
    mid.chacha20.check_counter counter len ⦃ r =>
      r = if counter.val + (len.val + 63) / 64 ≤ 2 ^ 32 then .Ok () else .Err .WrongLength ⦄ := by
  unfold mid.chacha20.check_counter core.num.Usize.div_ceil
  simp only [lift, bind_ok, show ¬ (64#usize : Usize).val = 0 by decide, ↓reduceDIte]
  have h1 : (core.convert.num.FromU64U32.from counter : U64).val = counter.val :=
    core.convert.num.FromU64U32.from_val_eq counter
  have hb : len.val < 2 ^ 64 := by
    have := len.hmax
    rcases System.Platform.numBits_eq with h | h
    · simp_all [UScalarTy.Usize_numBits_eq]; omega
    · simp_all [UScalarTy.Usize_numBits_eq]
  have hm : (len.val + 64 - 1) / 64 % 2 ^ UScalarTy.U64.numBits = (len.val + 63) / 64 := by
    rw [UScalarTy.U64_numBits_eq]; apply Nat.mod_eq_of_lt; omega
  have hc := counter.hBounds
  step*
  all_goals simp only [h1, UScalar.cast_val_eq, UScalar.ofNatCore_val_eq] at *
  all_goals simp only [hm] at *
  all_goals have h4 : i4.val = 2 ^ 32 := by rw [i4_post]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
  all_goals split_ifs <;> first | rfl | (exfalso; scalar_tac)

/-- ChaCha20 on a CPU whose SVE2 check returns `s`, for a request VG's
routines run or any request if rind's NEON code meets its contract: RFC
8439's encryption of the buffer under the key, the block counter, and the
nonce, if the counter covers it before it wraps; otherwise `WrongLength`,
with the buffer unchanged. -/
theorem apply_keystream_spec (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hu : ∃ s, VgState.uninit = ok s) (s : Option low.aarch64.cpu.HaveSve2)
    (hs : low.aarch64.cpu.HaveSve2.check = ok s) (k : mid.chacha20.ChaCha20)
    (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8)
    (hn : RunsVgAt s inout.length ∨ Neon) :
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
      step with cipher_spec hu cc inout (by simp_all) (by rw [hcv]; exact hc)
        as ⟨c', inout1, h1⟩
      step*
    · subst r_post
      simp_all
  · rw [Slice.len_val] at r_post
    split_ifs at r_post ⊢ <;> subst r_post <;> simp_all

/-- rind runs ChaCha20 on this CPU: the entry guard admits the call, a VG
state can be made, and the SVE2 check returns, whatever it finds. None reads
an input. -/
def RunsCipher : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ (∃ s, VgState.uninit = ok s) ∧
  ∃ s, low.aarch64.cpu.HaveSve2.check = ok s

/-- ChaCha20 on a request pyca/verified-garbage's routines run, from 128
bytes where the CPU has SVE2, and otherwise from 192 to 256 bytes and from
448: RFC 8439's encryption of the buffer under the key, the block counter,
and the nonce, if the counter covers it before it wraps; otherwise
`WrongLength`, with the buffer unchanged. -/
theorem chacha20_apply_keystream_vg (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hu : ∃ s, VgState.uninit = ok s) (s : Option low.aarch64.cpu.HaveSve2)
    (hs : low.aarch64.cpu.HaveSve2.check = ok s) (k : mid.chacha20.ChaCha20)
    (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8) (hv : RunsVgAt s inout.length) :
    k.apply_keystream nonce counter inout ⦃ r inout' =>
      if counter.val + (inout.length + 63) / 64 ≤ 2 ^ 32 then
        r = .Ok () ∧
          bvs inout'.val = chacha20.encrypt (bvs k.key.val) counter.bv (bvs nonce.val) (bvs inout.val)
      else r = .Err .WrongLength ∧ inout' = inout ⦄ :=
  apply_keystream_spec he hu s hs k nonce counter inout (Or.inl hv)

/-- ChaCha20 on any aarch64 CPU, at every length, if rind's NEON code meets
its contract: RFC 8439's encryption of the buffer under the key, the block
counter, and the nonce, if the counter covers it before it wraps; otherwise
`WrongLength`, with the buffer unchanged. -/
theorem chacha20_apply_keystream (h : RunsCipher) (hn : Neon) (k : mid.chacha20.ChaCha20)
    (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8) :
    k.apply_keystream nonce counter inout ⦃ r inout' =>
      if counter.val + (inout.length + 63) / 64 ≤ 2 ^ 32 then
        r = .Ok () ∧
          bvs inout'.val = chacha20.encrypt (bvs k.key.val) counter.bv (bvs nonce.val) (bvs inout.val)
      else r = .Err .WrongLength ∧ inout' = inout ⦄ :=
  let ⟨he, hu, s, hs⟩ := h
  apply_keystream_spec he hu s hs k nonce counter inout (Or.inr hn)

end rind.aarch64
