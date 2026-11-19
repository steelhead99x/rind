import Rind.X86_64.ChaCha20
import Rind.X86_64.ChaCha20Poly1305
import Rind.VgChaCha20
open Aeneas Aeneas.Std Result rind.spec
open VG.Spec.ChaCha20 (bytesAt keyAt leftAt restAt keystreamOf wordLE)

/-!
# `cipher::ChaCha20` on pyca/verified-garbage's routines, from 256 bytes on x86_64

Where the CPU-feature checks find AVX2 or AVX-512 VL,
`cipher::ChaCha20` runs pyca/verified-garbage's (VG's) AVX2 routine, or its
AVX-512 VL one, from 256 bytes, and a remainder of 65 to 255 bytes after the
last whole 512-byte group on rind's two-block kernel. The axioms
below restate VG's Lean theorems about `vg_chacha20_init`,
`vg_chacha20_apply_avx2`, and `vg_chacha20_apply_avx512vl` about the Rust
wrappers that call them, `VgState::init`, `VgState::apply_avx2`, and
`VgState::apply_avx512vl`, over VG's own spec,
`VerifiedGarbage.Spec.ChaCha20`, which `admin/import-vg-models` vendors byte
for byte. `cipher_vg_spec` composes them, and `cipher_spec` proves `cipher`'s
result from them over 256 bytes: RFC 8439's encryption, as `Rind.Spec`
transliterates it.

`cipher_spec` takes the kernel's contract as the hypothesis `Kernel`, which
`Rind.X86_64.ChaCha20Avx2` proves, and `Rind.X86_64.ChaCha20Cipher` composes
the two at every length and up to the API.

Trusted: each restatement, and that each wrapper passes the routine its
state's 768 bytes, which `Rind.X86_64.TypesExternal` models as the state, and
the key's and counter and nonce's words as the little-endian bytes VG reads.
That VG's definitions of the state's key and keystream read only those 768
bytes is proven (`Rind.VgChaCha20`'s `keyAt_congr`, `leftAt_congr`, and
`restAt_congr`), so the axioms, which hold for any memory holding them, say
no more than VG's theorems. VG's theorems rest on its models of the
instructions, which `admin/prove vg` cosimulates for each instruction of VG's
code rind runs, on the CPU or, where it lacks a feature, under Intel SDE, but
for `jmp`, static addresses, and a lone `ret`, which its check that rind's
copies are VG's text covers; and on VG's own Lean kernel check, at the commit
`admin/import-vg` pins.
-/

namespace rind.x86_64

open low.x86_64.chacha20 (VgState)

/-- Words as memory holds them: each one's little-endian bytes. -/
def wordBytes (ws : List U32) : List (BitVec 8) := (ws.map (·.bv)).flatMap BitVec.toLEBytes

/-! ## verified-garbage's routines, restated

VG's contracts (`Spec/ChaCha20/Contract.lean`) are over its model's memory
`m` before the call and `m'` after, with the state at `p`: each axiom holds
for any `m` and `m'` holding the state's 768 bytes at `p` before and after
the call, and reads the key's and counter and nonce's words for the bytes at
theirs, and the data's bytes for those at the data. Each precondition holds
for every call safe Rust makes: the state is 768 bytes; the state and the data, which
the routines write, are objects distinct from every other argument, so
neither overlaps another argument, the return address, or the stack below it;
no argument wraps the address space; and the token proves the CPU features.
VG's contracts hold for any bytes of the state, so these do too, and need no
premise that `init` has run. A slice's length is its own, which no call
changes. -/

/-- VG's `vg_chacha20_init` on x86_64 meets `VG.Spec.ChaCha20.initContract`
([`Stream.init_verified`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20/X86_64/Stream/Init.lean),
which [`Artifacts/ChaCha20/X86_64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/ChaCha20/X86_64.lean)
registers as `Scrub.initReg`
([`ScrubInit.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20/X86_64/ScrubInit.lean)), which wraps it with `withScrub`, of
the code VG emits): the state holds the key and
the whole keystream for the counter and nonce. -/
@[step]
axiom vg_chacha20_init_spec (st : VgState) (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize) :
    VgState.init st key counter_nonce ⦃ st' =>
      ∀ (m' : VG.Mem) (p : VG.Addr), bytesAt m' p 768 = bvs st'.val →
        keyAt m' p = wordBytes key.val ∧
        restAt m' p = keystreamOf (wordBytes key.val) (wordBytes counter_nonce.val) ⦄

/-- VG's `vg_chacha20_apply_avx2` on x86_64 meets
`VG.Spec.ChaCha20.applyContract` ([`Stream.apply_verified`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20/X86_64/Stream/ApplyCT.lean)
for its AVX2 `vg_chacha20_xor`, which
[`Artifacts/ChaCha20/X86_64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/ChaCha20/X86_64.lean)
registers as `Scrub.applyReg avx2`
([`Scrub.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20/X86_64/Scrub.lean)), which wraps it with `withScrub`, of the
code VG emits): if at least the data's
length of keystream is left, it XORs the next bytes of it into the data,
keeps the rest, and returns 1; otherwise it returns 0 and changes neither. -/
@[step]
axiom vg_chacha20_apply_avx2_spec (st : VgState) (t : low.x86_64.cpu.HaveAvx2) (data : Slice U8) :
    VgState.apply_avx2 st t data ⦃ r st' data' =>
      data'.length = data.length ∧
      ∀ (m m' : VG.Mem) (p : VG.Addr), bytesAt m p 768 = bvs st.val → bytesAt m' p 768 = bvs st'.val →
        keyAt m' p = keyAt m p ∧
        if data.length ≤ leftAt m p then
          r.val = 1 ∧
            bvs data'.val = List.zipWith (· ^^^ ·) (bvs data.val) ((restAt m p).take data.length) ∧
            restAt m' p = (restAt m p).drop data.length
        else
          r.val = 0 ∧ bvs data'.val = bvs data.val ∧ restAt m' p = restAt m p ⦄

/-- VG's `vg_chacha20_apply_avx512vl` on x86_64 meets
`VG.Spec.ChaCha20.applyContract`, as `vg_chacha20_apply_avx2_spec` states, for its AVX-512
VL `vg_chacha20_xor` (`Scrub.applyReg avx512Vl`). -/
@[step]
axiom vg_chacha20_apply_avx512vl_spec (st : VgState) (t : low.x86_64.cpu.HaveAvx512Vl) (data : Slice U8) :
    VgState.apply_avx512vl st t data ⦃ r st' data' =>
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

/-- The kernel's contract, which `Rind.X86_64.ChaCha20Avx2`'s `kernel`
proves: for as many blocks as remain before the 32-bit block counter wraps,
it XORs RFC 8439's keystream for the key and the counter and nonce into the
buffer, as `cipher` calls it. -/
def Kernel : Prop :=
  ∀ (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize) (buffer : Slice U8),
    counter_nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32 →
    low.x86_64.chacha20.cipher_avx2 key counter_nonce buffer ⦃ r =>
      bvs r.val = chacha20.encrypt (wordBytes key.val) counter_nonce.val[0]!.bv
        (wordBytes (counter_nonce.val.drop 1)) (bvs buffer.val) ⦄

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
theorem cipher_vg_spec (hu : ∃ s, VgState.uninit = ok s) (v : low.x86_64.chacha20.Vg)
    (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize) (buffer : Slice U8)
    (hl : counter_nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32) :
    low.x86_64.chacha20.cipher_vg v key counter_nonce buffer ⦃ r =>
      r.length = buffer.length ∧
      bvs r.val = chacha20.encrypt (wordBytes key.val) counter_nonce.val[0]!.bv
        (wordBytes (counter_nonce.val.drop 1)) (bvs buffer.val) ⦄ := by
  obtain ⟨s, hs⟩ := hu
  unfold low.x86_64.chacha20.cipher_vg
  simp only [hs, bind_ok]
  step as ⟨st, hst⟩
  -- VG's theorems hold for any memory holding the state: take memory holding
  -- only it, from address 0.
  have hm : ∀ x : VgState, bytesAt (vg.mem (bvs x.val)) 0 768 = bvs x.val := fun x => by
    have hx : (bvs x.val).length = 768 := by simp [bvs]
    simpa [hx] using vg.bytesAt_mem (bvs x.val) (by rw [hx]; decide)
  obtain ⟨-, hr⟩ := hst _ 0 (hm st)
  have hn := leftAt_init _ _ key counter_nonce hr buffer.length hl
  have he := keystream_encrypt key counter_nonce (bvs buffer.val) (by rw [bvs_length]; exact hl)
  rw [bvs_length] at he
  cases v <;>
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
    low.x86_64.chacha20.words_loop iter bytes ws ⦃ r => r.val.map (·.bv) = F ⦄ := by
  unfold low.x86_64.chacha20.words_loop
  apply loop.spec_decr_nat (fun x => W.val - x.1.start.val)
    (fun x => x.1.start.val ≤ W.val ∧ x.1.end.val = W.val ∧
      (List.range' x.1.start.val (W.val - x.1.start.val)).foldl
        (fun l i => l.set i (chacha20.words (bvs bytes.val))[i]!) (x.2.val.map (·.bv)) = F)
  · rintro ⟨it, ws⟩ ⟨hs, he, hF⟩
    simp only at hs he hF ⊢
    unfold low.x86_64.chacha20.words_loop.body
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
    low.x86_64.chacha20.words W bytes ⦃ r => r.val.map (·.bv) = chacha20.words (bvs bytes.val) ⦄ := by
  unfold low.x86_64.chacha20.words
  have hb : (bvs bytes.val).length = 4 * W.val := by simp [bvs, hB]
  have hw : (chacha20.words (bvs bytes.val)).length = W.val := by simp [chacha20.words, hb]
  step*
  apply words_loop_spec bytes _ _ _ hB (by simp) (by simp)
  rw [foldl_set_range' _ _ _ _ (by simp)]
  apply List.ext_getElem (by simp [hw])
  intro i h1 h2
  simp [List.getElem_range', List.getElem?_eq_getElem h2]

/-- `ChaCha20::new` holds the key and the counter and nonce as words, and
picks a VG routine where the CPU has AVX2. -/
@[step]
theorem new_spec (key : Std.Array U8 32#usize) (counter_nonce : Std.Array U8 16#usize)
    (a : Option low.x86_64.cpu.HaveAvx512Vl) (b : Option low.x86_64.cpu.HaveAvx2)
    (s : Option low.x86_64.cpu.HaveSsse3) (ha : low.x86_64.cpu.HaveAvx512Vl.check = ok a)
    (hb : low.x86_64.cpu.HaveAvx2.check = ok b) (hs : low.x86_64.cpu.HaveSsse3.check = ok s) :
    low.x86_64.chacha20.ChaCha20.new key counter_nonce ⦃ c =>
      wordBytes c.key.val = bvs key.val ∧ wordBytes c.counter_nonce.val = bvs counter_nonce.val ∧
      (c.vg.isSome ↔ (a.isSome ∨ b.isSome)) ⦄ := by
  unfold low.x86_64.chacha20.ChaCha20.new
  simp only [ha, hb, hs, bind_ok]
  step with words_spec 8#usize key (by simp) as ⟨k, hk⟩
  step with words_spec 4#usize counter_nonce (by simp) as ⟨cn, hcn⟩
  have e1 := wordBytes_of_words _ _ 8 (by simp [bvs]) hk
  have e2 := wordBytes_of_words _ _ 4 (by simp [bvs]) hcn
  rcases a with _ | a <;> rcases b with _ | b <;> simp [e1, e2]

/-! ## The cipher's VG path, `ChaCha20::cipher` -/

/-- From 256 bytes, on a CPU where `new` picked a VG routine, `cipher` XORs
RFC 8439's keystream into the buffer: VG's routines over the whole buffer,
partial final block included, unless `len % 512` is 65 to 255, when they take
the bytes before that remainder and the kernel takes the remainder, from the
block counter past them. -/
theorem cipher_spec (hu : ∃ s, VgState.uninit = ok s) (hk : Kernel) (c : low.x86_64.chacha20.ChaCha20)
    (hv : c.vg.isSome) (buffer : Slice U8) (h256 : 256 ≤ buffer.length)
    (hl : c.counter_nonce.val[0]!.val + (buffer.length + 63) / 64 ≤ 2 ^ 32) :
    low.x86_64.chacha20.ChaCha20.cipher c buffer ⦃ _ r =>
      bvs r.val = chacha20.encrypt (wordBytes c.key.val) c.counter_nonce.val[0]!.bv
        (wordBytes (c.counter_nonce.val.drop 1)) (bvs buffer.val) ⦄ := by
  obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
  have hcn : c.counter_nonce.val.length = 4 := c.counter_nonce.property
  unfold low.x86_64.chacha20.ChaCha20.cipher
  simp only [hv']
  rw [ite_eq_left (by scalar_tac)]
  refine WP.spec_bind (Pₘ := fun b1 : Slice U8 => bvs b1.val = chacha20.encrypt (wordBytes c.key.val)
    c.counter_nonce.val[0]!.bv (wordBytes (c.counter_nonce.val.drop 1)) (bvs buffer.val)) ?_ ?_
  rotate_left
  · intro b1 hb1
    simp only [core.num.Usize.div_ceil, lift, show ¬ (64#usize : Usize).val = 0 by decide, ↓reduceDIte,
      bind_ok]
    step*
  step as ⟨tail, htail⟩
  refine WP.spec_bind (Pₘ := fun t1 : Usize =>
    t1.val ≤ buffer.length ∧ (t1.val = 0 ∨ (buffer.length - t1.val) % 64 = 0)) ?_ ?_
  · rw [Slice.len_val] at htail
    split_ifs <;> simp only [WP.spec_ok] <;> scalar_tac
  intro t1 ⟨ht1, ht1'⟩
  step as ⟨i, hi⟩
  step as ⟨whole, rest, back, hwl, hrl, hwv, hrv, hback⟩
  rw [Slice.len_val] at hi htail
  step with cipher_vg_spec hu v c.key c.counter_nonce whole (by rw [hwl, hi]; omega) as ⟨whole1, hw1l, hw1⟩
  step as ⟨b, hb⟩
  split
  · -- `tail` is zero: VG took the whole buffer.
    rename_i hb'
    have hr0 : rest.length = 0 := by simpa [hb'] using hb
    obtain ⟨hbv, -⟩ := hback whole1 rest (by omega) (by omega)
    have hwb : whole.val = buffer.val := by
      rw [hwv, List.take_of_length_le (by simp only [Slice.length] at *; omega)]
    have hre : rest.val = [] := List.eq_nil_of_length_eq_zero hr0
    rw [WP.spec_ok, hbv, hre, List.append_nil, hw1, hwb]
  · rename_i hb'
    have hr0 : rest.length ≠ 0 := by simpa [hb'] using hb
    have hq : i.val % 64 = 0 := by omega
    step*
    have hk32 : (wordBytes c.key.val).length = 32 := by simp [length_wordBytes]
    have hn12 : (wordBytes (c.counter_nonce.val.drop 1)).length = 12 := by simp [length_wordBytes]
    have hba : ∀ x y : List U8, bvs (x ++ y) = bvs x ++ bvs y := by simp [bvs]
    have h0 : c.counter_nonce.val[0]! = c.counter_nonce.val[0] := getElem!_pos _ _ (by omega)
    have hi5 : i5.val = c.counter_nonce.val[0]!.val + i.val / 64 := by
      rw [i5_post, core.num.U32.wrapping_add_val_eq, i1_post, i4_post, UScalar.cast_val_eq, i3_post,
        Slice.len_val, hw1l, hwl, h0]
      rw [h0] at hl
      simp only [UScalar.size, UScalarTy.numBits]
      omega
    have hcn0 : counter_nonce.val[0]! = i5 := by rw [counter_nonce_post]; simp [hcn]
    have hcnd : counter_nonce.val.drop 1 = c.counter_nonce.val.drop 1 := by
      rw [counter_nonce_post]
      simp only [Std.Array.set_val_eq, List.drop_one]
      generalize c.counter_nonce.val = l
      cases l <;> rfl
    have hbound : counter_nonce.val[0]!.val + (rest.length + 63) / 64 ≤ 2 ^ 32 := by rw [hcn0, hi5]; omega
    apply WP.spec_bind (hk c.key counter_nonce rest hbound)
    intro rest1 hr1
    have hr1l : rest1.length = rest.length := by
      have := congrArg List.length hr1
      rwa [bvs_length, vg.length_encrypt _ _ _ _ hk32 (by rw [hcnd]; exact hn12), bvs_length] at this
    obtain ⟨hbv, -⟩ := hback whole1 rest1 (by omega) (by omega)
    have hc : i5.bv = c.counter_nonce.val[0]!.bv + BitVec.ofNat 32 (i.val / 64) := by
      apply BitVec.eq_of_toNat_eq
      simp only [UScalar.bv_toNat, BitVec.toNat_add, BitVec.toNat_ofNat, hi5]
      have := c.counter_nonce.val[0]!.hBounds
      omega
    rw [WP.spec_ok, hbv, hba, hw1, hr1, hcnd, hcn0, hc,
      ← vg.encrypt_append _ _ _ _ _ (i.val / 64) (by rw [bvs_length]; simp only [Slice.length] at hwl; omega),
      ← hba, hwv, hrv, List.take_append_drop]

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

end rind.x86_64
