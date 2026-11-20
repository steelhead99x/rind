import Rind.Aarch64.ChaCha20
import Rind.Aarch64.AesKey
import Rind.VgChaCha20
open Aeneas Aeneas.Std Result rind.spec
open VG.Spec.ChaCha20 (bytesAt keyAt leftAt restAt keystreamOf wordLE)

/-!
# `cipher::ChaCha20` on pyca/verified-garbage's routines on aarch64

On aarch64, `cipher::ChaCha20` runs pyca/verified-garbage's (VG's) SVE2
routine from 128 bytes where the CPU has SVE2, and its NEON routine from 192
to 256 bytes and from 448 bytes where it does not, each over the whole buffer
with no tail on rind's code; every other length runs rind's NEON code, which
no theorem here is about. The axioms below restate VG's Lean theorems about
`vg_chacha20_init`, `vg_chacha20_apply_neon`, and `vg_chacha20_apply_sve2`
about the Rust wrappers that call them, `VgState::init`,
`VgState::apply_neon`, and `VgState::apply_sve2`, over VG's own spec,
`VerifiedGarbage.Spec.ChaCha20`, which `admin/import-vg-models` vendors byte
for byte. `cipher_vg_spec` composes them, `cipher_spec` proves `cipher`'s
result from them at the lengths that run them, and `apply_keystream_spec`
proves the API's: RFC 8439's encryption, as `Rind.Spec` transliterates it.

Trusted: each restatement, and that each wrapper passes the routine its
state's 768 bytes, which `Rind.Aarch64.TypesExternal` models as the state,
and the key's and counter and nonce's words as the little-endian bytes VG
reads, which are the words' bytes on aarch64. That VG's definitions of the
state's key and keystream read only those 768 bytes is proven
(`Rind.VgChaCha20`'s `keyAt_congr`, `leftAt_congr`, and `restAt_congr`), so
the axioms, which hold for any memory holding them, say no more than VG's
theorems. VG's theorems rest on its models of the instructions, which
`admin/prove vg` cosimulates for each instruction of VG's code rind runs,
under qemu-aarch64 where the CPU lacks a feature, but for `b`, static
addresses, and a lone `ret`, which its check that rind's copies are VG's
text covers; and on VG's own Lean kernel check, at the commit
`admin/import-vg` pins.
-/

namespace rind.aarch64

open low.aarch64.chacha20 (VgState)

/-- Words as memory holds them: each one's little-endian bytes. -/
def wordBytes (ws : List U32) : List (BitVec 8) := (ws.map (·.bv)).flatMap BitVec.toLEBytes

/-! ## verified-garbage's routines, restated

VG's contracts (`Spec/ChaCha20/Contract.lean`) are over its model's memory
`m` before the call and `m'` after, with the state at `p`: each axiom holds
for any `m` and `m'` holding the state's 768 bytes at `p` before and after
the call, and reads the key's and counter and nonce's words for the bytes at
theirs, and the data's bytes for those at the data. Each precondition holds
for every call safe Rust makes: the state is 768 bytes; the state and the data,
which the routines write, are objects distinct from every other argument, so
neither overlaps another argument, the stack, or the return address; no
argument wraps the address space; and the token proves the CPU features. VG's
contracts hold for any bytes of the state, so these do too, and need no
premise that `init` has run. A slice's length is its own, which no call
changes. -/

/-- VG's `vg_chacha20_init` on aarch64 meets `VG.Spec.ChaCha20.initContract`
([`Stream.initCleared_verified`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20/AArch64/Stream/Init.lean#L356),
which [`Artifacts/ChaCha20/AArch64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/ChaCha20/AArch64.lean)
registers for `initApi`, of the code VG emits): the state holds the key and
the whole keystream for the counter and nonce. -/
@[step]
axiom vg_chacha20_init_spec (st : VgState) (key : Std.Array U32 8#usize) (nonce : Std.Array U32 4#usize) :
    VgState.init st key nonce ⦃ st' =>
      ∀ (m' : VG.Mem) (p : VG.Addr), bytesAt m' p 768 = bvs st'.val →
        keyAt m' p = wordBytes key.val ∧
        restAt m' p = keystreamOf (wordBytes key.val) (wordBytes nonce.val) ⦄

/-- VG's `vg_chacha20_apply_neon` on aarch64 meets
`VG.Spec.ChaCha20.applyContract` ([`Stream.apply_verified`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20/AArch64/Stream/ApplyCT.lean#L330)
at the NEON implementation, which
[`Artifacts/ChaCha20/AArch64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/ChaCha20/AArch64.lean)
registers for `applyApi` as `vg_chacha20_apply_neon`, of the code VG emits): if at least the
data's length of keystream is left, it XORs the next bytes of it into the
data, keeps the rest, and returns 1; otherwise it returns 0 and changes
neither. -/
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
`VG.Spec.ChaCha20.applyContract`, as `vg_chacha20_apply_neon_spec` states, at
the SVE2 implementation (`vg_chacha20_apply_sve2`). -/
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

/-! ## Words and bytes -/

theorem length_wordBytes (ws : List U32) : (wordBytes ws).length = 4 * ws.length := by
  rw [wordBytes, vg.length_flatMap_toLEBytes, List.length_map]

theorem wordBytes_drop_one (ws : List U32) : (wordBytes ws).drop 4 = wordBytes (ws.drop 1) := by
  cases ws with
  | nil => simp [wordBytes]
  | cons w ws =>
    simp only [wordBytes, List.map_cons, List.flatMap_cons, List.drop_one, List.tail_cons]
    rw [List.drop_append_of_le_length (by simp [BitVec.toLEBytes_length]),
      List.drop_eq_nil_of_le (by simp [BitVec.toLEBytes_length]), List.nil_append]

theorem wordLE_wordBytes (ws : List U32) (h : 0 < ws.length) : wordLE (wordBytes ws) 0 = ws[0]!.bv := by
  rw [wordBytes, vg.wordLE_flatMap _ 0 (by simpa using h)]
  cases ws with
  | nil => simp at h
  | cons w ws => rfl

/-- Words read from bytes, as `Rind.Spec`'s `words` reads them, written back
out are those bytes. -/
theorem wordBytes_of_words (ws : List U32) (b : List (BitVec 8)) (n : Nat) (hb : b.length = 4 * n)
    (hw : ws.map (·.bv) = chacha20.words b) : wordBytes ws = b := by
  rw [wordBytes, hw, vg.flatMap_words b n hb]

/-! ## Composing the routines, `cipher_vg` -/

theorem bvs_list_length (x : List U8) : (bvs x).length = x.length := by simp [bvs]

/-- What a state `init` started holds, for a buffer the keystream covers. -/
theorem leftAt_init (m : VG.Mem) (p : VG.Addr) (key : Std.Array U32 8#usize)
    (counter_nonce : Std.Array U32 4#usize)
    (hr : restAt m p = keystreamOf (wordBytes key.val) (wordBytes counter_nonce.val)) (n : Nat)
    (hl : counter_nonce.val[0]!.val + (n + 63) / 64 ≤ 2 ^ 32) : n ≤ leftAt m p := by
  rw [← vg.length_restAt, hr, vg.length_keystreamOf _ _ (by simp [length_wordBytes])
    (by simp [length_wordBytes]), wordLE_wordBytes _ (by simp)]
  simp only [UScalar.bv_toNat]
  omega

/-- The keystream `init` sets up, XORed into a buffer it covers. -/
theorem keystream_encrypt (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize)
    (msg : List (BitVec 8)) (hl : counter_nonce.val[0]!.val + (msg.length + 63) / 64 ≤ 2 ^ 32) :
    List.zipWith (· ^^^ ·) msg
        ((keystreamOf (wordBytes key.val) (wordBytes counter_nonce.val)).take msg.length) =
      chacha20.encrypt (wordBytes key.val) counter_nonce.val[0]!.bv
        (wordBytes (counter_nonce.val.drop 1)) msg := by
  have hk : (wordBytes key.val).length = 32 := by simp [length_wordBytes]
  have hn : (wordBytes counter_nonce.val).length = 16 := by simp [length_wordBytes]
  rw [vg.keystreamOf_encrypt _ _ _ hk hn, wordLE_wordBytes _ (by simp), wordBytes_drop_one]
  rw [vg.length_keystreamOf _ _ hk hn, wordLE_wordBytes _ (by simp)]
  simp only [UScalar.bv_toNat]
  omega

/-- VG's routines XOR RFC 8439's keystream for the key and the counter and
nonce into a buffer, for as many blocks as remain before the block counter
wraps, on either routine. -/
@[step]
theorem cipher_vg_spec (hu : ∃ s, VgState.uninit = ok s) (sve2 : Option low.aarch64.cpu.HaveSve2)
    (key : Std.Array U32 8#usize) (nonce : Std.Array U32 4#usize) (buffer : Slice U8)
    (hl : nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32) :
    low.aarch64.chacha20.cipher_vg sve2 key nonce buffer ⦃ r =>
      r.length = buffer.length ∧
      bvs r.val = chacha20.encrypt (wordBytes key.val) nonce.val[0]!.bv
        (wordBytes (nonce.val.drop 1)) (bvs buffer.val) ⦄ := by
  obtain ⟨s, hs⟩ := hu
  unfold low.aarch64.chacha20.cipher_vg
  simp only [hs, bind_ok]
  step as ⟨st, hst⟩
  -- VG's theorems hold for any memory holding the state: take memory holding
  -- only it, from address 0.
  have hm : ∀ x : VgState, bytesAt (vg.mem (bvs x.val)) 0 768 = bvs x.val := fun x => by
    have hx : (bvs x.val).length = 768 := by simp [bvs]
    simpa [hx] using vg.bytesAt_mem (bvs x.val) (by rw [hx]; decide)
  obtain ⟨-, hr⟩ := hst _ 0 (hm st)
  have hn := leftAt_init _ _ key nonce hr buffer.length hl
  have he := keystream_encrypt key nonce (bvs buffer.val) (by rw [bvs_list_length]; exact hl)
  rw [bvs_list_length] at he
  cases sve2 <;>
  · step as ⟨r, hlen, happ⟩
    obtain ⟨r1, st', b'⟩ := r
    simp only at happ hlen
    obtain ⟨-, hif⟩ := happ _ _ 0 (hm st) (hm st')
    rw [ite_eq_left hn, hr] at hif
    obtain ⟨hr1, hb, -⟩ := hif
    have hr1' : r1 = 1#u32 := by scalar_tac
    subst hr1'
    step*

/-! ## The key and the counter and nonce as words, `ChaCha20::new` -/

/-- Setting each index of a list from `k` on to `f`'s value there. -/
theorem foldl_set_range' {α : Type} (f : Nat → α) (a : List α) (k m : Nat) (h : k + m = a.length) :
    (List.range' k m).foldl (fun l i => l.set i (f i)) a = a.take k ++ (List.range' k m).map f := by
  induction m generalizing k a with
  | zero => simp [List.take_of_length_le (by omega : a.length ≤ k)]
  | succ m ih =>
    have hk : k < a.length := by omega
    rw [List.range'_succ, List.foldl_cons, ih _ (k + 1) (by simp; omega), List.map_cons, List.take_add_one,
      List.take_set_of_le (Nat.le_refl k), List.getElem?_set_self hk]
    simp

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
      rw [words_getElem! _ _ (by simp; agrind)]
      simp only [i2_post, i4_post, i6_post, i8_post, i7_post, i5_post, i3_post, i1_post, bv_getElem]
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
  rw [foldl_set_range' _ _ _ _ (by simp)]
  apply List.ext_getElem (by simp [hw])
  intro i h1 h2
  simp [List.getElem_range', List.getElem?_eq_getElem h2]

/-- `ChaCha20::new` holds the key and the counter and nonce as words, and
the SVE2 token the CPU check finds. -/
@[step]
theorem new_spec (key : Std.Array U8 32#usize) (nonce : Std.Array U8 16#usize)
    (s : Option low.aarch64.cpu.HaveSve2) (hs : low.aarch64.cpu.HaveSve2.check = ok s) :
    low.aarch64.chacha20.ChaCha20.new key nonce ⦃ c =>
      wordBytes c.key.val = bvs key.val ∧ wordBytes c.nonce.val = bvs nonce.val ∧ c.sve2 = s ⦄ := by
  unfold low.aarch64.chacha20.ChaCha20.new
  simp only [hs, bind_ok]
  step with words_spec 8#usize key (by simp) as ⟨k, hk⟩
  step with words_spec 4#usize nonce (by simp) as ⟨cn, hcn⟩
  have e1 := wordBytes_of_words _ _ 8 (by simp [bvs]) hk
  have e2 := wordBytes_of_words _ _ 4 (by simp [bvs]) hcn
  simp [e1, e2]

/-! ## The cipher's VG path, `ChaCha20::cipher` -/

/-- The lengths at which `cipher` runs VG's routines: from 128 bytes where
the CPU has SVE2, and from 192 to 256 bytes and from 448 bytes where it
does not. -/
def RunsVgAt (sve2 : Bool) (len : Nat) : Prop :=
  if sve2 then 128 ≤ len else (192 ≤ len ∧ len ≤ 256) ∨ 448 ≤ len

/-- At a length that runs VG's routines, `cipher` XORs RFC 8439's keystream
into the buffer: VG's routines over the whole buffer, partial final block
included. -/
theorem cipher_spec (hu : ∃ s, VgState.uninit = ok s) (c : low.aarch64.chacha20.ChaCha20)
    (buffer : Slice U8) (hv : RunsVgAt c.sve2.isSome buffer.length)
    (hl : c.nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32) :
    low.aarch64.chacha20.ChaCha20.cipher c buffer ⦃ _ r =>
      bvs r.val = chacha20.encrypt (wordBytes c.key.val) c.nonce.val[0]!.bv
        (wordBytes (c.nonce.val.drop 1)) (bvs buffer.val) ⦄ := by
  have hcn : c.nonce.val.length = 4 := c.nonce.property
  have hvg := cipher_vg_spec hu c.sve2 c.key c.nonce buffer hl
  unfold low.aarch64.chacha20.ChaCha20.cipher
  refine WP.spec_bind (Pₘ := fun b1 : Slice U8 => b1.length = buffer.length ∧
    bvs b1.val = chacha20.encrypt (wordBytes c.key.val) c.nonce.val[0]!.bv
      (wordBytes (c.nonce.val.drop 1)) (bvs buffer.val)) ?_ ?_
  rotate_left
  · intro b1 hb1
    simp only [core.num.Usize.div_ceil, lift, show ¬ (64#usize : Usize).val = 0 by decide,
      ↓reduceDIte, bind_ok]
    step*
  · simp only [RunsVgAt] at hv
    rcases hs : c.sve2 with _ | t <;> rw [hs] at hvg <;>
      simp only [hs, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
        ↓reduceIte] at hv <;> split_ifs <;> first
      | exact hvg
      | (exfalso; scalar_tac)

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

end rind.aarch64
