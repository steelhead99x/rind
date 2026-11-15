import Rind.X86_64.AesModesLow
import Rind.AesModesBytes
open Aeneas Aeneas.Std Result rind.vale rind.simd rind.modes

/-!
# `cipher::AesCtr`, `AesCbcEncryptingKey`, and `AesCbcDecryptingKey`

The public CTR and CBC APIs, from `Rind.X86_64.AesModesLow`'s theorems about
the low-level modes alone: `expand_key_mode_spec`, `dec_key_new_mode_spec`,
`aes_ctr_apply_spec`, `aes_cbc_encrypt_spec`, and `aes_cbc_decrypt_spec`, and
the predicates `ModeKeyIs` and `ModeDecKeyIs`. `admin/prove` writes the
aarch64 copy of this file, whose `Rind.Aarch64.AesModesLow` proves the same
names on that target.
-/

namespace rind.x86_64

/-! ## CBC on whole blocks -/

theorem length_cbcEncrypt (alg : Algorithm) (key : List (BitVec 8)) (n : Nat) :
    ∀ iv p : List (BitVec 8), p.length ≤ n → (cbcEncrypt alg key iv p).length = p.length / 16 * 16 := by
  induction n with
  | zero =>
    intro iv p hp
    rw [cbcEncrypt, ite_eq_left (by omega)]
    simp only [List.length_nil]
    omega
  | succ n ih =>
    intro iv p hp
    rw [cbcEncrypt]
    by_cases h : p.length < 16
    · rw [ite_eq_left h]
      simp only [List.length_nil]
      omega
    · rw [ite_eq_right h]
      simp only [List.length_append]
      rw [ih _ _ (by rw [List.length_drop]; omega), List.length_drop]
      simp only [aesBlock, leQuad32ToBytes, List.length_map, List.length_range]
      omega

theorem length_cbcDecrypt (alg : Algorithm) (key : List (BitVec 8)) (n : Nat) :
    ∀ iv c : List (BitVec 8), iv.length = 16 → c.length ≤ n →
      (cbcDecrypt alg key iv c).length = c.length / 16 * 16 := by
  induction n with
  | zero =>
    intro iv c _ hc
    rw [cbcDecrypt, ite_eq_left (by omega)]
    simp only [List.length_nil]
    omega
  | succ n ih =>
    intro iv c hiv hc
    rw [cbcDecrypt]
    by_cases h : c.length < 16
    · rw [ite_eq_left h]
      simp only [List.length_nil]
      omega
    · rw [ite_eq_right h]
      simp only [List.length_append, List.length_zipWith]
      rw [ih _ _ (by rw [List.length_take]; omega) (by rw [List.length_drop]; omega), List.length_drop]
      simp only [aesBlockDecrypt, leQuad32ToBytes, List.length_map, List.length_range, hiv]
      omega

theorem flatMap_bvs_blocks (l : List (Std.Array U8 16#usize)) :
    l.flatMap (fun b => bvs b.val) = bvs (l.flatMap (·.val)) := by
  simp [bvs, List.map_flatMap]

/-- The low-level CBC encryption as this file's callers use it. On x86_64 the
routine needs the blocks' byte count to fit a `usize` and on aarch64 it does
not, so the first form applies on one target and the second on the other. -/
theorem cbc_encrypt_low (alg : Algorithm) (key : List (BitVec 8)) (k : low.x86_64.aes.AesKey)
    (hk : ModeKeyIs alg key k) (iv : Std.Array U8 16#usize) (blocks : Slice (Std.Array U8 16#usize))
    (hn : 16 * blocks.length ≤ Usize.max) :
    low.x86_64.aes_cbc.encrypt k iv blocks ⦃ r => r.length = blocks.length ∧
      bvs (r.val.flatMap (·.val)) = cbcEncrypt alg key (bvs iv.val) (bvs (blocks.val.flatMap (·.val))) ⦄ := by
  have h : low.x86_64.aes_cbc.encrypt k iv blocks ⦃ r =>
      r.val.flatMap (fun b => bvs b.val) =
        cbcEncrypt alg key (bvs iv.val) (blocks.val.flatMap fun b => bvs b.val) ⦄ := by
    first
    | exact aes_cbc_encrypt_spec alg key k hk iv blocks hn
    | exact aes_cbc_encrypt_spec alg key k hk iv blocks
  apply WP.spec_mono h
  intro r hr
  rw [flatMap_bvs_blocks, flatMap_bvs_blocks] at hr
  refine ⟨?_, hr⟩
  have hlen := congrArg List.length hr
  rw [length_cbcEncrypt alg key _ _ _ (le_refl _)] at hlen
  simp only [bvs, List.length_map, length_flatMap16] at hlen
  show r.val.length = blocks.val.length
  omega

/-- The low-level CBC decryption as this file's callers use it; see
`cbc_encrypt_low`. -/
theorem cbc_decrypt_low (alg : Algorithm) (key : List (BitVec 8)) (k : low.x86_64.aes.AesDecKey)
    (hk : ModeDecKeyIs alg key k) (iv : Std.Array U8 16#usize) (blocks : Slice (Std.Array U8 16#usize))
    (hn : 16 * blocks.length ≤ Usize.max) :
    low.x86_64.aes_cbc.decrypt k iv blocks ⦃ r => r.length = blocks.length ∧
      bvs (r.val.flatMap (·.val)) = cbcDecrypt alg key (bvs iv.val) (bvs (blocks.val.flatMap (·.val))) ⦄ := by
  have h : low.x86_64.aes_cbc.decrypt k iv blocks ⦃ r =>
      r.val.flatMap (fun b => bvs b.val) =
        cbcDecrypt alg key (bvs iv.val) (blocks.val.flatMap fun b => bvs b.val) ⦄ := by
    first
    | exact aes_cbc_decrypt_spec alg key k hk iv blocks hn
    | exact aes_cbc_decrypt_spec alg key k hk iv blocks
  apply WP.spec_mono h
  intro r hr
  rw [flatMap_bvs_blocks, flatMap_bvs_blocks] at hr
  refine ⟨?_, hr⟩
  have hlen := congrArg List.length hr
  rw [length_cbcDecrypt alg key _ _ _ (by simp [bvs]) (le_refl _)] at hlen
  simp only [bvs, List.length_map, length_flatMap16] at hlen
  show r.val.length = blocks.val.length
  omega

/-! ## CBC -/

/-- A CBC key is refused unless it is the algorithm's length, and otherwise
holds the round keys of its bytes. -/
theorem aes_cbc_encrypting_key_new_spec (h : RunsAesHw) (alg : Algorithm) (algorithm : cipher.Algorithm)
    (hlen : algorithm.key_len.val = 4 * nk alg) (key : Slice U8) :
    mid.aes_cbc.AesCbcEncryptingKey.new algorithm key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok k ∧ ModeKeyIs alg (bvs key.val) k.key
      else r = .Err .WrongLength ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.aes_cbc.AesCbcEncryptingKey.new
  rw [he, bind_ok]
  by_cases hk : key.length = 4 * nk alg
  · have hne : ¬ (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac
    simp only [hne, ite_eq_left hk]
    apply WP.spec_bind (expand_key_mode_spec h alg key hk)
    intro ak hak
    exact (WP.spec_ok _).2 ⟨_, rfl, hak⟩
  · have hne : (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hk; rw [← hlen, ← he]; simp
    simp only [hne, ite_true, ite_eq_right hk, WP.spec_ok]

/-- A CBC decryption key is refused unless it is the algorithm's length, and
otherwise holds the inverse cipher's round keys of its bytes. -/
theorem aes_cbc_decrypting_key_new_spec (h : RunsAesHw) (alg : Algorithm) (algorithm : cipher.Algorithm)
    (hlen : algorithm.key_len.val = 4 * nk alg) (key : Slice U8) :
    mid.aes_cbc.AesCbcDecryptingKey.new algorithm key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok k ∧ ModeDecKeyIs alg (bvs key.val) k.key
      else r = .Err .WrongLength ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.aes_cbc.AesCbcDecryptingKey.new
  rw [he, bind_ok]
  by_cases hk : key.length = 4 * nk alg
  · have hne : ¬ (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac
    simp only [hne, ite_eq_left hk]
    have hnk : nk alg ≤ 8 := by cases alg <;> decide
    step*
    · simp only [copy_key1_post, low.ct.secret_slice, bind_ok]
      apply WP.spec_bind (dec_key_new_mode_spec h alg key hk)
      intro adk hadk
      exact (WP.spec_ok _).2 ⟨_, rfl, hadk⟩
  · have hne : (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hk; rw [← hlen, ← he]; simp
    simp only [hne, ite_true, ite_eq_right hk, WP.spec_ok]

theorem chunks_back {s : Slice U8} {p : Slice (Std.Array U8 16#usize) × Slice U8}
    {back : Slice (Std.Array U8 16#usize) × Slice U8 → Slice U8}
    (hl : p.1.length = s.length / 16)
    (hb : ∀ i (h : i < p.1.val.length), (p.1.val[i]).val = (s.val.drop (i * 16)).take 16)
    (hr : p.2.val = s.val.drop (s.length / 16 * 16))
    (hback : ∀ c t, (c.val.flatMap (·.val) ++ t.val).length ≤ Usize.max →
      (back (c, t)).val = c.val.flatMap (·.val) ++ t.val) :
    p.1.val.flatMap (·.val) = s.val.take (s.length / 16 * 16) ∧ back (p.1, p.2) = s := by
  have hf := rind.modes.flatMap_chunks s.val p.1.val hl hb
  refine ⟨hf, Slice.ext _ _ ?_⟩
  rw [hback _ _ (by rw [hf, hr, List.take_append_drop]; exact Slice.length_ineq s), hf, hr,
    List.take_append_drop]

/-- A bind whose result destructures as `((a, b), c)`: its matcher needs
reducing at default transparency, which `simp` does not do. -/
theorem spec_bind3 {α β γ δ : Type} {m : Result ((α × β) × γ)} {k : α → β → γ → Result δ}
    {P : α × β → γ → Prop} {Q : δ → Prop}
    (h1 : m ⦃ p c => P p c ⦄) (h2 : ∀ a b c, P (a, b) c → k a b c ⦃ Q ⦄) :
    (do let ((a, b), c) ← m; k a b c) ⦃ Q ⦄ := by
  apply WP.spec_bind h1
  rintro ⟨⟨a, b⟩, c⟩ hp
  exact h2 a b c hp

/-- `as_chunks_mut::<16>` of a byte slice: its whole blocks, which flatten to
its leading bytes, the rest, and a write-back that rebuilds it. -/
theorem as_chunks16 (N : Usize) (hN : N.val = 16) (s : Slice U8) :
    core.slice.Slice.as_chunks_mut N s ⦃ p back =>
      p.1.val.length = s.val.length / 16 ∧
      p.1.val.flatMap (fun b : Std.Array U8 N => b.val) = s.val.take (s.val.length / 16 * 16) ∧
      p.2.val.length = s.val.length % 16 ∧ back p = s ∧
      ∀ (c : Slice (Std.Array U8 N)) (t : Slice U8),
        (c.val.flatMap (fun b : Std.Array U8 N => b.val) ++ t.val).length ≤ Usize.max →
        (back (c, t)).val = c.val.flatMap (fun b : Std.Array U8 N => b.val) ++ t.val ⦄ := by
  obtain rfl : N = 16#usize := (UScalar.eq_equiv _ _).2 hN
  apply WP.spec_mono (rind.modes.as_chunks_mut_spec (T := U8) 16#usize (by decide) s)
  rintro ⟨⟨blocks, rest⟩, back⟩ ⟨hl, hb, hr, hback⟩
  simp only [show ((16#usize : Usize) : Nat) = 16 from rfl] at hl hb hr
  obtain ⟨hf, hid⟩ := chunks_back (s := s) (p := (blocks, rest)) (back := back) hl hb hr hback
  try simp only [WP.uncurry'_pair]
  refine ⟨hl, hf, ?_, hid, hback⟩
  rw [hr, List.length_drop]
  have : s.length = s.val.length := rfl
  omega

/-- CBC encryption of whole blocks: refused unless the buffer is whole
blocks, and otherwise SP 800-38A's CBC encryption of it. -/
theorem aes_cbc_encrypt_blocks_spec (h : RunsAesHw) (alg : Algorithm) (key : List (BitVec 8))
    (k : mid.aes_cbc.AesCbcEncryptingKey) (hk : ModeKeyIs alg key k.key) (iv : mid.aes_cbc.CbcIv)
    (in_out : Slice U8) :
    k.encrypt_blocks iv in_out ⦃ r =>
      if in_out.length % 16 = 0 then
        r.1 = .Ok () ∧ bvs r.2.val = cbcEncrypt alg key (bvs iv.val) (bvs in_out.val)
      else r = (.Err .WrongLength, in_out) ⦄ := by
  obtain ⟨e, he⟩ := h.1
  have hmax := Slice.length_ineq in_out
  unfold mid.aes_cbc.AesCbcEncryptingKey.encrypt_blocks mid.aes_cbc.AesCbcEncryptingKey.encrypt_in_place
  simp only [he, bind_ok]
  refine spec_bind3 (as_chunks16 _ (by rfl) in_out) ?_
  rintro blocks rest back ⟨hl, hf, hrl, hid, hback⟩
  have hl' : blocks.val.length = in_out.val.length / 16 := hl
  have hrl' : rest.val.length = in_out.val.length % 16 := hrl
  have hf' : blocks.val.flatMap (fun b => b.val) = in_out.val.take (in_out.val.length / 16 * 16) := hf
  have hid' : back (blocks, rest) = in_out := hid
  simp only [bind_ok, low.ct.secret_slice, low.ct.public_slice, core.slice.Slice.is_empty, bind_assoc_eq]
  by_cases h16 : in_out.length % 16 = 0
  · have h16' : in_out.val.length % 16 = 0 := h16
    have hd : decide (rest.val.length = 0) = true := decide_eq_true (by omega)
    simp only [hd, h16, ↓reduceIte]
    refine WP.spec_bind (WP.spec_bind (cbc_encrypt_low alg key k.key hk iv blocks
      (by show 16 * blocks.val.length ≤ Usize.max; omega)) (fun b hb => (WP.spec_ok _).2 hb)) ?_
    rintro blocks1 ⟨hl1, henc⟩
    have hl1' : blocks1.val.length = blocks.val.length := hl1
    refine (WP.spec_ok _).2 ⟨rfl, ?_⟩
    have hrn : rest.val = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hback _ _ (by rw [List.length_append, length_flatMap16, hrn, List.length_nil]; omega), hrn,
      List.append_nil, henc, hf', List.take_of_length_le (by omega)]
  · have h16' : ¬ in_out.val.length % 16 = 0 := h16
    have hd : decide (rest.val.length = 0) = false := decide_eq_false (by omega)
    simp only [hd, h16, Bool.false_eq_true, ↓reduceIte, WP.spec_ok, hid']

/-- CBC decryption of whole blocks: refused unless the buffer is whole
blocks, and otherwise SP 800-38A's CBC decryption of it. -/
theorem aes_cbc_decrypt_blocks_spec (h : RunsAesHw) (alg : Algorithm) (key : List (BitVec 8))
    (k : mid.aes_cbc.AesCbcDecryptingKey) (hk : ModeDecKeyIs alg key k.key) (iv : Std.Array U8 16#usize)
    (in_out : Slice U8) :
    k.decrypt_blocks iv in_out ⦃ r =>
      if in_out.length % 16 = 0 then
        r.1 = .Ok () ∧ bvs r.2.val = cbcDecrypt alg key (bvs iv.val) (bvs in_out.val)
      else r = (.Err .DecryptFailed, in_out) ⦄ := by
  obtain ⟨e, he⟩ := h.1
  have hmax := Slice.length_ineq in_out
  unfold mid.aes_cbc.AesCbcDecryptingKey.decrypt_blocks
  simp only [he, bind_ok]
  refine spec_bind3 (as_chunks16 _ (by rfl) in_out) ?_
  rintro blocks rest back ⟨hl, hf, hrl, hid, hback⟩
  have hl' : blocks.val.length = in_out.val.length / 16 := hl
  have hrl' : rest.val.length = in_out.val.length % 16 := hrl
  have hf' : blocks.val.flatMap (fun b => b.val) = in_out.val.take (in_out.val.length / 16 * 16) := hf
  have hid' : back (blocks, rest) = in_out := hid
  simp only [bind_ok, low.ct.public_slice, core.slice.Slice.is_empty]
  by_cases h16 : in_out.length % 16 = 0
  · have h16' : in_out.val.length % 16 = 0 := h16
    have hd : decide (rest.val.length = 0) = true := decide_eq_true (by omega)
    simp only [hd, h16, ↓reduceIte]
    apply WP.spec_bind (cbc_decrypt_low alg key k.key hk iv blocks
      (by show 16 * blocks.val.length ≤ Usize.max; omega))
    rintro blocks1 ⟨hl1, hdec⟩
    have hl1' : blocks1.val.length = blocks.val.length := hl1
    refine (WP.spec_ok _).2 ⟨rfl, ?_⟩
    have hrn : rest.val = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hback _ _ (by rw [List.length_append, length_flatMap16, hrn, List.length_nil]; omega), hrn,
      List.append_nil, hdec, hf', List.take_of_length_le (by omega)]
  · have h16' : ¬ in_out.val.length % 16 = 0 := h16
    have hd : decide (rest.val.length = 0) = false := decide_eq_false (by omega)
    simp only [hd, h16, Bool.false_eq_true, ↓reduceIte, WP.spec_ok, hid']

/-! ## The PKCS#7 check -/

theorem setSlice!_zero {α : Type _} (s s' : List α) (h : s'.length ≤ s.length) :
    s.setSlice! 0 s' = s' ++ s.drop s'.length := by
  simp only [List.setSlice!, List.take_zero, List.nil_append, Nat.sub_zero, Nat.min_eq_left h,
    List.take_length, Nat.zero_add]

/-- PKCS#7 unpadding of bytes ending in a 16-byte block reads only that block. -/
theorem pkcs7Unpad_last (pre l : List (BitVec 8)) (h16 : l.length = 16) :
    pkcs7Unpad (pre ++ l) =
      if 1 ≤ l[15]!.toNat ∧ l[15]!.toNat ≤ 16 ∧ ∀ i < 16, i < l[15]!.toNat → l[15 - i]! = l[15]! then
        some ((pre ++ l).take (pre.length + 16 - l[15]!.toNat))
      else none := by
  have hlast : (pre ++ l).getLast? = some l[15]! := by
    rw [List.getLast?_eq_getElem?, List.length_append, h16, List.getElem?_append_right (by omega),
      show pre.length + 16 - 1 - pre.length = 15 by omega, getElem!_pos l 15 (by omega),
      List.getElem?_eq_getElem]
  simp only [pkcs7Unpad, hlast, List.length_append, h16]
  generalize l[15]!.toNat = n
  by_cases hc : 1 ≤ n ∧ n ≤ 16 ∧ ∀ i < 16, i < n → l[15 - i]! = l[15]!
  · rw [if_pos hc, if_pos]
    refine ⟨hc.1, hc.2.1, by omega, ?_⟩
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    have hjn : j < n := by simp only [List.length_drop, List.length_append, h16] at hj; omega
    rw [List.getElem_drop, List.getElem_append_right (by omega)]
    have := hc.2.2 (n - 1 - j) (by omega) (by omega)
    rw [getElem!_pos l _ (by omega)] at this
    have e : pre.length + 16 - n + j - pre.length = 15 - (n - 1 - j) := by omega
    simp only [e]
    exact this
  · rw [if_neg hc, if_neg]
    rintro ⟨h1, h2, -, hall⟩
    apply hc
    refine ⟨h1, h2, fun i hi hin => ?_⟩
    apply hall
    rw [getElem!_pos l _ (by omega)]
    apply List.mem_iff_getElem.2
    refine ⟨n - 1 - i, by simp only [List.length_drop, List.length_append, h16]; omega, ?_⟩
    rw [List.getElem_drop, List.getElem_append_right (by omega)]
    have e : pre.length + 16 - n + (n - 1 - i) - pre.length = 15 - i := by omega
    simp only [e]

theorem bvs_getElem!_lt (l : List U8) {j : Nat} (hj : j < l.length) : (bvs l)[j]! = (l[j]!).bv := by
  rw [getElem!_pos _ j (by rw [List.length_map]; exact hj), getElem!_pos l j hj, List.getElem_map]

/-- `pkcs7Unpad_last` on a block of `U8`s. -/
theorem pkcs7Unpad_block (pre : List (BitVec 8)) (last : Std.Array U8 16#usize) :
    pkcs7Unpad (pre ++ bvs last.val) =
      if 1 ≤ last.val[15]!.val ∧ last.val[15]!.val ≤ 16 ∧
          ∀ i < 16, i < last.val[15]!.val → last.val[15 - i]! = last.val[15]! then
        some ((pre ++ bvs last.val).take (pre.length + 16 - last.val[15]!.val))
      else none := by
  have hl : last.val.length = 16 := last.property
  have hn : (bvs last.val)[15]!.toNat = last.val[15]!.val :=
    congrArg BitVec.toNat (bvs_getElem!_lt _ (show 15 < last.val.length by omega))
  have hc : (∀ i < 16, i < last.val[15]!.val → (bvs last.val)[15 - i]! = (bvs last.val)[15]!) ↔
      (∀ i < 16, i < last.val[15]!.val → last.val[15 - i]! = last.val[15]!) := by
    refine forall_congr' fun i => imp_congr_right fun hi => imp_congr_right fun _ => ?_
    rw [bvs_getElem!_lt _ (by omega), bvs_getElem!_lt _ (by omega), U8.eq_equiv_bv_eq]
  rw [pkcs7Unpad_last pre (bvs last.val) (by rw [List.length_map, hl]), hn]
  simp only [hc]

theorem mask_eq (m : U8) (c : Bool) (h : m.val = if c then 255 else 0) :
    m = if c then 255#u8 else 0#u8 := by
  apply UScalar.eq_of_val_eq
  rw [h]
  cases c <;> rfl

theorem or_masks_eq_zero (m1 m2 : U8) (c1 c2 : Bool) (h1 : m1.val = if c1 then 255 else 0)
    (h2 : m2.val = if c2 then 255 else 0) : (m1 ||| m2) = 0#u8 ↔ c1 = false ∧ c2 = false := by
  rw [mask_eq m1 c1 h1, mask_eq m2 c2 h2]
  cases c1 <;> cases c2 <;> decide

theorem mask_or_eq_zero (bad m x p : U8) (c : Bool) (hm : m.val = if c then 255 else 0) :
    (bad ||| (m &&& (x ^^^ p))) = 0#u8 ↔ bad = 0#u8 ∧ (c = true → x = p) := by
  rw [mask_eq m c hm]
  have e0 : UScalar.bv (0#u8 : U8) = 0#8 := rfl
  have e255 : UScalar.bv (255#u8 : U8) = BitVec.allOnes 8 := by decide
  cases c <;> simp [UScalar.eq_equiv_bv_eq, e0, e255, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]

/-- `ct_mask_lt` is all ones when `a < b` and zero otherwise. -/
theorem ct_mask_lt_spec (a b : U8) :
    mid.aes_cbc.ct_mask_lt a b ⦃ m => m.val = if a.val < b.val then 255 else 0 ⦄ := by
  unfold mid.aes_cbc.ct_mask_lt
  simp only [lift, bind_ok]
  apply WP.spec_bind (U32.ShiftRight_IScalar_spec _ 8#i32 (by decide) (by decide))
  rintro z ⟨hz, -⟩
  refine (WP.spec_ok _).2 ?_
  have ha : a.val < 256 := by scalar_tac
  have hb : b.val < 256 := by scalar_tac
  have h8 : (8#i32 : I32).toNat = 8 := by decide
  rw [UScalar.cast_val_eq, hz, core.num.U32.wrapping_sub_val_eq, core.convert.num.FromU32U8.from_val_eq,
    core.convert.num.FromU32U8.from_val_eq, h8, Nat.shiftRight_eq_div_pow]
  simp only [UScalar.size, UScalarTy.numBits, Nat.reducePow]
  split <;> omega

/-- The padding check's loop leaves `bad` zero exactly when it was and each
of the last `pad` bytes, up to 16, is `pad`. -/
theorem decrypt_loop_spec (last : Std.Array U8 16#usize) (pad bad : U8) :
    mid.aes_cbc.AesCbcDecryptingKey.decrypt_loop { start := 0#usize, «end» := 16#usize } last pad bad
      ⦃ r => (r = 0#u8 ↔ bad = 0#u8 ∧ ∀ i < 16, i < pad.val → last.val[15 - i]! = pad) ⦄ := by
  have hl16 : last.val.length = 16 := last.property
  have h15 : (15#usize : Usize).val = 15 := rfl
  unfold mid.aes_cbc.AesCbcDecryptingKey.decrypt_loop
  apply loop.spec_decr_nat (fun x => 16 - x.1.start.val)
    (fun x => x.1.«end» = 16#usize ∧ x.1.start.val ≤ 16 ∧
      (x.2 = 0#u8 ↔ bad = 0#u8 ∧ ∀ i < x.1.start.val, i < pad.val → last.val[15 - i]! = pad))
  · rintro ⟨it, b⟩ ⟨hend, hle, hinv⟩
    simp only at hend hle hinv ⊢
    unfold mid.aes_cbc.AesCbcDecryptingKey.decrypt_loop.body
    have hE : it.«end».val = 16 := by rw [hend]; all_goals rfl
    step as ⟨o, iter1, ho, hend1⟩
    by_cases hlt : it.start.val < it.«end».val
    · simp only [hlt, ↓reduceIte] at ho
      obtain ⟨rfl, hst⟩ := ho
      simp only [lift, bind_ok]
      have hc : (UScalar.cast .U8 it.start).val = it.start.val := by
        rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simp only [UScalarTy.numBits]; omega)
      apply WP.spec_bind (ct_mask_lt_spec _ pad)
      intro m hm
      rw [hc] at hm
      apply WP.spec_bind (Usize.sub_spec (x := 15#usize) (y := it.start) (by rw [h15]; omega))
      rintro i3 ⟨hi3, -⟩
      have hb3 : i3.val < last.val.length := by rw [hl16, hi3, h15]; omega
      apply WP.spec_bind (Array.index_usize_spec last i3 hb3)
      rintro i4 rfl
      have hx : last.val[i3.val] = last.val[15 - it.start.val]! := by
        rw [getElem!_pos last.val (15 - it.start.val) (by omega)]
        simp only [hi3, h15]
      refine (WP.spec_ok _).2 ?_
      dsimp only
      try simp only [and_assoc]
      refine ⟨by rw [hend1, hend], by omega, ?_, by omega⟩
      rw [mask_or_eq_zero b m _ pad (decide (it.start.val < pad.val)) (by simpa using hm), hinv, hst, hx]
      constructor
      · rintro ⟨⟨hb, hall⟩, hs⟩
        refine ⟨hb, fun i hi hp => ?_⟩
        by_cases hi' : i < it.start.val
        · exact hall i hi' hp
        · have : i = it.start.val := by omega
          subst this
          exact hs (by simpa using hp)
      · rintro ⟨hb, hall⟩
        exact ⟨⟨hb, fun i hi hp => hall i (by omega) hp⟩,
          fun hp => hall _ (by omega) (by simpa using hp)⟩
    · simp only [hlt, ↓reduceIte] at ho
      obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val = 16 := by omega
      rw [hinv, this]
  · dsimp only
    exact ⟨rfl, by decide, by simp⟩

/-- CBC decryption with PKCS#7 padding. A buffer of whole blocks, at least
one, decrypts; if its padding is good, the result is the message, and the
buffer holds the decryption with the message part written back; if not,
decryption fails and the buffer is zeroed. Any other buffer fails unchanged. -/
theorem aes_cbc_decrypting_key_decrypt_spec (h : RunsAesHw) (alg : Algorithm) (key : List (BitVec 8))
    (k : mid.aes_cbc.AesCbcDecryptingKey) (hk : ModeDecKeyIs alg key k.key) (iv : Std.Array U8 16#usize)
    (in_out : Slice U8) :
    k.decrypt iv in_out ⦃ r back =>
      if in_out.length % 16 = 0 ∧ in_out.length ≠ 0 then
        (∀ m, pkcs7Unpad (cbcDecrypt alg key (bvs iv.val) (bvs in_out.val)) = some m →
          ∃ s, r = .Ok s ∧ bvs s.val = m ∧ ∀ s' : Slice U8, s'.length = s.length →
            bvs (back (.Ok s')).val = bvs s'.val ++
              (cbcDecrypt alg key (bvs iv.val) (bvs in_out.val)).drop m.length) ∧
        (pkcs7Unpad (cbcDecrypt alg key (bvs iv.val) (bvs in_out.val)) = none →
          r = .Err .DecryptFailed ∧ ∀ r', (back r').val = List.replicate in_out.length 0#u8)
      else r = .Err .DecryptFailed ∧ ∀ r', back r' = in_out ⦄ := by
  obtain ⟨e, he⟩ := h.1
  have hmax := Slice.length_ineq in_out
  unfold mid.aes_cbc.AesCbcDecryptingKey.decrypt
  simp only [he, bind_ok]
  refine spec_bind3 (as_chunks16 _ (by rfl) in_out) ?_
  rintro blocks rest back ⟨hl, hf, hrl, hid, hback⟩
  have hl' : blocks.val.length = in_out.val.length / 16 := hl
  have hrl' : rest.val.length = in_out.val.length % 16 := hrl
  have hf' : blocks.val.flatMap (fun b => b.val) = in_out.val.take (in_out.val.length / 16 * 16) := hf
  have hid' : back (blocks, rest) = in_out := hid
  simp only [bind_ok, core.slice.Slice.is_empty]
  by_cases h16 : in_out.val.length % 16 = 0
  swap
  · have hd : decide (rest.val.length = 0) = false := decide_eq_false (by omega)
    simp only [hd, Bool.false_eq_true, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
    rw [ite_eq_right (show ¬ (in_out.length % 16 = 0 ∧ in_out.length ≠ 0) from fun hc => h16 hc.1)]
    exact ⟨by trivial, fun _ => hid'⟩
  have hd : decide (rest.val.length = 0) = true := decide_eq_true (by omega)
  simp only [hd, ↓reduceIte]
  by_cases h0 : in_out.val.length = 0
  · have hd0 : decide (blocks.val.length = 0) = true := decide_eq_true (by omega)
    simp only [hd0, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
    rw [ite_eq_right (show ¬ (in_out.length % 16 = 0 ∧ in_out.length ≠ 0) from fun hc => hc.2 h0)]
    exact ⟨by trivial, fun _ => hid'⟩
  have hd0 : decide (blocks.val.length = 0) = false := decide_eq_false (by omega)
  simp only [hd0, Bool.false_eq_true, ↓reduceIte]
  apply WP.spec_bind (cbc_decrypt_low alg key k.key hk iv blocks
    (by show 16 * blocks.val.length ≤ Usize.max; omega))
  rintro blocks1 ⟨hl1, hdec⟩
  have hl1' : blocks1.val.length = blocks.val.length := hl1
  rw [hf', List.take_of_length_le (by omega)] at hdec
  have hrn : rest.val = [] := List.length_eq_zero_iff.mp (by omega)
  have hout := hback blocks1 rest (by rw [List.length_append, length_flatMap16, hrn]; simp; omega)
  rw [hrn, List.append_nil] at hout
  generalize cbcDecrypt alg key (bvs iv.val) (bvs in_out.val) = D at hdec ⊢
  have hbo : bvs (back (blocks1, rest)).val = D := by rw [hout, hdec]
  rcases List.eq_nil_or_concat blocks1.val with hn | ⟨pre, last, hsplit⟩
  · exfalso; have := congrArg List.length hn; simp only [List.length_nil] at this; omega
  rw [List.concat_eq_append] at hsplit
  have hD : D = bvs (pre.flatMap (·.val)) ++ bvs last.val := by
    rw [← hdec, hsplit]
    simp only [bvs, List.flatMap_append, List.flatMap_singleton, List.map_append]
  have hol : (back (blocks1, rest)).val.length = 16 * pre.length + 16 := by
    rw [hout, length_flatMap16, hsplit, List.length_append, List.length_singleton]; ring
  have hlast16 : last.val.length = 16 := last.property
  simp only [core.slice.Slice.last, hsplit, List.getLast?_concat, bind_ok, core.option.Option.unwrap,
    Result.ofOption]
  apply WP.spec_bind (Array.index_usize_spec last 15#usize (by show (15#usize : Usize).val < last.val.length; rw [hlast16]; decide))
  rintro pad hpad
  have hpad' : pad = last.val[15]! := by
    rw [hpad, getElem!_pos last.val 15 (by rw [hlast16]; omega)]; all_goals rfl
  subst hpad'
  simp only [core.hint.black_box, bind_ok]
  apply WP.spec_bind (ct_mask_lt_spec _ _)
  intro m1 hm1
  apply WP.spec_bind (ct_mask_lt_spec _ _)
  intro m2 hm2
  simp only [lift, bind_ok]
  apply WP.spec_bind (decrypt_loop_spec last _ _)
  intro bad1 hbad1
  simp only [core.hint.black_box, low.ct.into_public, bind_ok]
  rw [show (16#u8 : U8).val = 16 from rfl] at hm1
  rw [show (1#u8 : U8).val = 1 from rfl] at hm2
  have hbad0 : (m1 ||| m2) = 0#u8 ↔ ¬ 16 < last.val[15]!.val ∧ ¬ last.val[15]!.val < 1 := by
    rw [or_masks_eq_zero m1 m2 (decide (16 < last.val[15]!.val)) (decide (last.val[15]!.val < 1))
      (by simpa using hm1) (by simpa using hm2)]
    simp
  have hok : bad1 = 0#u8 ↔ 1 ≤ last.val[15]!.val ∧ last.val[15]!.val ≤ 16 ∧
      ∀ i < 16, i < last.val[15]!.val → last.val[15 - i]! = last.val[15]! := by
    rw [hbad1, hbad0]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, by omega, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
  have hPU := pkcs7Unpad_block (bvs (pre.flatMap (·.val))) last
  rw [← hD] at hPU
  have hcond : in_out.length % 16 = 0 ∧ in_out.length ≠ 0 := ⟨h16, h0⟩
  by_cases hb : bad1 = 0#u8
  · have hbne : (bad1 != 0#u8) = false := by simp [hb]
    have hp16 := (hok.1 hb).2.1
    rw [if_pos (hok.1 hb)] at hPU
    simp only [hbne, Bool.false_eq_true, ↓reduceIte, low.ct.into_public, low.ct.public_slice, bind_ok,
      lift, Slice.index_mut_SliceIndexRangeToUsizeSliceInst]
    apply WP.spec_bind (Usize.sub_spec (x := Slice.len (back (blocks1, rest)))
      (y := core.convert.num.FromUsizeU8.from last.val[15]!)
      (by rw [Slice.len_val, core.convert.num.FromUsizeU8.from_val_eq]; simp only [Slice.length, hol]; omega))
    rintro len ⟨hlen, -⟩
    have hlen' : len.val = 16 * pre.length + 16 - last.val[15]!.val := by
      rw [hlen, Slice.len_val, core.convert.num.FromUsizeU8.from_val_eq]; simp only [Slice.length, hol]
    apply WP.spec_bind (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec { «end» := len }
      (back (blocks1, rest)) (by show len.val ≤ _; simp only [Slice.length, hol]; omega))
    rintro ⟨s, imb⟩ ⟨hs, hsl, himb⟩
    refine (WP.spec_ok _).2 ?_
    simp only [WP.uncurry'_pair]
    rw [ite_eq_left hcond]
    refine ⟨fun m hm => ?_, fun hn => by rw [hPU] at hn; simp at hn⟩
    rw [hPU] at hm
    obtain rfl := Option.some.inj hm
    simp only [Slice.length] at hsl
    refine ⟨s, rfl, ?_, fun s' hs' => ?_⟩
    · rw [hs, ← hbo]
      simp only [List.slice, List.drop_zero, Nat.sub_zero, bvs, List.map_take, hlen', List.length_map,
        length_flatMap16]
    · simp only [Slice.length] at hs'
      show bvs (imb s').val = _
      rw [himb, setSlice!_zero _ _ (by rw [hol, hs', hsl]; show len.val ≤ _; omega), ← hbo]
      simp only [bvs, List.map_append, List.map_drop, List.length_take, List.length_map,
        length_flatMap16]
      congr 2
      rw [hs', hsl, hol]
      show len.val = _
      omega
  · have hbne : (bad1 != 0#u8) = true := by simpa using hb
    rw [if_neg (fun hc => hb (hok.2 hc))] at hPU
    simp only [hbne, ↓reduceIte]
    apply WP.spec_bind (core.slice.Slice.fill.spec core.clone.CloneU8 (back (blocks1, rest)) 0#u8
      (by simp [WP.spec_ok]))
    rintro z ⟨-, hz⟩
    refine (WP.spec_ok _).2 ?_
    simp only [WP.uncurry'_pair]
    rw [ite_eq_left hcond]
    refine ⟨fun m hm => by rw [hPU] at hm; simp at hm, fun _ => ⟨by trivial, fun _ => ?_⟩⟩
    rw [hz]
    congr 1
    simp only [Slice.length, hol]
    rw [hsplit, List.length_append, List.length_singleton] at hl1'
    omega

/-! ## CTR -/

/-- An AES-CTR key: the AES key's round keys, counting over the low `m` bits
of each counter block. -/
def AesCtrIs (alg : Algorithm) (key : List (BitVec 8)) (m : Nat) (c : mid.aes.AesCtr) : Prop :=
  ModeKeyIs alg key c.key ∧ m ≤ 128 ∧ c.counter_mask.val = 2 ^ m - 1

theorem shr_max (s : Nat) (hs : s ≤ 128) : (2 ^ 128 - 1) / 2 ^ s = 2 ^ (128 - s) - 1 := by
  have hp : 2 ^ (128 - s) * 2 ^ s = 2 ^ 128 := by rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (128 - s) := Nat.one_le_two_pow
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, hp]; omega
  · rw [Nat.sub_add_cancel h2, hp]; omega

theorem contains_u8 (lo hi x : U8) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU8 core.cmp.PartialOrdU8
      core.cmp.PartialOrdU8 ⟨lo, hi, false⟩ x = ok (decide (lo.val ≤ x.val ∧ x.val ≤ hi.val)) := by
  by_cases h1 : lo.val ≤ x.val <;>
    simp [core.ops.range.RangeInclusive.contains, core.cmp.impls.PartialOrdU8.le, h1]

/-- An AES-CTR key is refused unless it is the algorithm's length and its
counter 1 to 128 bits, and otherwise holds the key's round keys and counts
over that many low bits. -/
theorem aes_ctr_new_spec (h : RunsAesHw) (alg : Algorithm) (algorithm : cipher.Algorithm)
    (hlen : algorithm.key_len.val = 4 * nk alg) (key : Slice U8) (counter_bits : U8) :
    mid.aes.AesCtr.new algorithm key counter_bits ⦃ r =>
      if key.length = 4 * nk alg ∧ 1 ≤ counter_bits.val ∧ counter_bits.val ≤ 128 then
        ∃ c, r = .Ok c ∧ AesCtrIs alg (bvs key.val) counter_bits.val c
      else r = .Err .WrongLength ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.aes.AesCtr.new
  rw [he, bind_ok]
  by_cases hk : key.length = 4 * nk alg
  · have hne : ¬ (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac
    simp only [hne, Bool.false_eq_true, ↓reduceIte, core.ops.range.RangeInclusive.new, bind_ok,
      contains_u8]
    by_cases hc : 1 ≤ counter_bits.val ∧ counter_bits.val ≤ 128
    · have hc' : (1#u8 : U8).val ≤ counter_bits.val ∧ counter_bits.val ≤ (128#u8 : U8).val := hc
      simp only [decide_eq_true hc', ↓reduceIte, ite_eq_left (show key.length = 4 * nk alg ∧ 1 ≤ counter_bits.val ∧
        counter_bits.val ≤ 128 from ⟨hk, hc⟩)]
      apply WP.spec_bind (expand_key_mode_spec h alg key hk)
      intro ak hak
      apply WP.spec_bind (U8.sub_spec (x := 128#u8) (y := counter_bits) (by scalar_tac))
      rintro i1 ⟨hi1, -⟩
      apply WP.spec_bind (U128.ShiftRight_spec core.num.U128.MAX i1 (by scalar_tac))
      rintro i2 ⟨hi2, -⟩
      refine (WP.spec_ok _).2 ⟨_, rfl, hak, hc.2, ?_⟩
      have hmax : (core.num.U128.MAX).val = 2 ^ 128 - 1 := by decide
      have hi1' : i1.val = 128 - counter_bits.val := by rw [hi1]; all_goals rfl
      show i2.val = _
      rw [hi2, hmax, hi1', Nat.shiftRight_eq_div_pow, shr_max _ (by omega)]
      congr 2; omega
    · have hc' : ¬ ((1#u8 : U8).val ≤ counter_bits.val ∧ counter_bits.val ≤ (128#u8 : U8).val) := hc
      simp only [decide_eq_false hc', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      rw [ite_eq_right (fun h' => hc h'.2)]
      trivial
  · have hne : (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hk; rw [← hlen, ← he]; simp
    simp only [hne, ↓reduceIte, WP.spec_ok]
    rw [ite_eq_right (fun h' => hk h'.1)]
    trivial

/-! ## CBC encryption of a `Vec<u8>` -/

theorem cbc_slice_next_lt {T : Type} (s : Slice T) (i : Nat) (h : i < s.length) :
    core.slice.iter.IteratorSliceIter.next ⟨s, i⟩ = ok (some s.val[i], ⟨s, i + 1⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  rw [dite_eq_left (by simpa [Slice.len, Slice.length] using h)]
  rfl

theorem cbc_slice_next_ge {T : Type} (s : Slice T) (i : Nat) (h : ¬ i < s.length) :
    core.slice.iter.IteratorSliceIter.next ⟨s, i⟩ = ok (none, ⟨s, i⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  rw [dite_eq_right (by simpa [Slice.len, Slice.length] using h)]

/-- A slice's iterator from `i` yields the elements from `i`. -/
theorem cbc_iterToList_slice {T : Type} (s : Slice T) (i : Nat) (acc : List T) :
    alloc.vec.FromIteratorVec.iterToList (core.iter.traits.iterator.IteratorSliceIter T) ⟨s, i⟩ acc =
      ok (acc.reverse ++ s.val.drop i) := by
  rw [alloc.vec.FromIteratorVec.iterToList]
  by_cases h : i < s.length
  · simp only [core.iter.traits.iterator.IteratorSliceIter, cbc_slice_next_lt s i h, bind_ok]
    show alloc.vec.FromIteratorVec.iterToList (core.iter.traits.iterator.IteratorSliceIter T)
      ⟨s, i + 1⟩ (s.val[i] :: acc) = _
    rw [cbc_iterToList_slice s (i + 1)]
    have hi : i < s.val.length := h
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hi]
  · simp only [core.iter.traits.iterator.IteratorSliceIter, cbc_slice_next_ge s i h, bind_ok]
    show ok acc.reverse = _
    simp [List.drop_eq_nil_of_le (show s.val.length ≤ i by simp [Slice.length] at h; omega)]
termination_by s.length - i
decreasing_by omega

/-- `Vec<u8>`'s `extend` of a slice appends it. -/
theorem cbc_vec_extend_spec (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.val.length + s.val.length ≤ Usize.max) :
    (alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT alloc.alloc.Global core.marker.CopyU8).extend
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) v s ⦃ w => w.val = v.val ++ s.val ⦄ := by
  simp only [alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok, cbc_iterToList_slice,
    List.reverse_nil, List.nil_append, List.drop_zero]
  rw [dite_eq_left (by simpa [Slice.length, alloc.vec.Vec.length] using h)]
  simp [WP.spec_ok]

/-- CBC encryption of a `Vec<u8>`: it always succeeds, since padding grows a
vector to whole blocks, and the vector becomes SP 800-38A's CBC encryption
of its PKCS#7 padding. -/
theorem aes_cbc_encrypt_vec_spec (h : RunsAesHw) (alg : Algorithm) (key : List (BitVec 8))
    (k : mid.aes_cbc.AesCbcEncryptingKey) (hk : ModeKeyIs alg key k.key) (iv : mid.aes_cbc.CbcIv)
    (in_out : alloc.vec.Vec U8) (hroom : in_out.val.length + 16 ≤ Usize.max) :
    k.encrypt (alloc.vec.Vec.Insts.CoreConvertAsMutSlice U8 alloc.alloc.Global)
      (alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT alloc.alloc.Global core.marker.CopyU8) iv in_out
      ⦃ r => r.1 = .Ok () ∧ bvs r.2.val = cbcEncrypt alg key (bvs iv.val) (pkcs7Pad (bvs in_out.val)) ⦄ := by
  unfold mid.aes_cbc.AesCbcEncryptingKey.encrypt
  simp only [bind_ok, alloc.vec.Vec.Insts.CoreConvertAsMutSlice.as_mut, alloc.vec.Vec.deref_mut]
  have h16 : (16#usize : Usize).val = 16 := rfl
  apply WP.spec_bind (Usize.rem_spec (Slice.len in_out.slice) (y := 16#usize) (by rw [h16]; omega))
  intro i1 hi1
  have hi1' : i1.val = in_out.val.length % 16 := by rw [hi1, Slice.len_val, h16]; all_goals rfl
  apply WP.spec_bind (Usize.sub_spec (x := 16#usize) (y := i1) (by rw [hi1', h16]; omega))
  rintro pad ⟨hpad, -⟩
  have hpad' : pad.val = 16 - in_out.val.length % 16 := by rw [hpad, hi1', h16]
  simp only [lift, bind_ok, Array.index_SliceIndexRangeToUsizeSlice]
  have hrep : ((Std.Array.repeat 16#usize (UScalar.cast .U8 pad)).to_slice).val =
      List.replicate 16 (UScalar.cast .U8 pad) := by
    simp only [Std.Array.to_slice, Slice.from_val, Std.Array.repeat_val, h16]
  apply WP.spec_bind (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec { «end» := pad }
    (Std.Array.repeat 16#usize (UScalar.cast .U8 pad)).to_slice
    (by show pad.val ≤ (Std.Array.to_slice _).val.length; rw [hrep, List.length_replicate]; omega))
  rintro s1 ⟨hs1, hs1l⟩
  have hs1v : s1.val = List.replicate pad.val (UScalar.cast .U8 pad) := by
    rw [hs1, hrep]
    simp only [List.slice, List.drop_zero, Nat.sub_zero, List.take_replicate]
    rw [Nat.min_eq_left (by omega)]
  have hv0 : ({ slice := in_out.slice } : alloc.vec.Vec U8).val = in_out.val := rfl
  apply WP.spec_bind (cbc_vec_extend_spec _ s1 (by rw [hv0, hs1v, List.length_replicate]; omega))
  intro w hw
  rw [hv0, hs1v] at hw
  have hwv : w.slice.val = in_out.val ++ List.replicate pad.val (UScalar.cast .U8 pad) := hw
  have hwl : w.slice.val.length = in_out.val.length + (16 - in_out.val.length % 16) := by
    rw [hwv, List.length_append, List.length_replicate, hpad']
  have hw16 : w.slice.val.length % 16 = 0 := by rw [hwl]; omega
  apply WP.spec_bind (aes_cbc_encrypt_blocks_spec h alg key k hk iv w.slice)
  rintro ⟨r, s3⟩ hr
  have hw16' : w.slice.length % 16 = 0 := hw16
  simp only [hw16', ↓reduceIte] at hr
  obtain ⟨hok, henc⟩ := hr
  refine (WP.spec_ok _).2 ⟨hok, ?_⟩
  have hcast : (UScalar.cast .U8 pad).bv = BitVec.ofNat 8 (16 - in_out.val.length % 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [show (UScalar.cast .U8 pad).bv.toNat = (UScalar.cast .U8 pad).val from rfl, UScalar.cast_val_eq,
      hpad']
    simp only [BitVec.toNat_ofNat, UScalarTy.numBits]
  show bvs s3.val = _
  rw [henc, hwv]
  simp only [bvs, List.map_append, List.map_replicate, hcast, pkcs7Pad, List.length_map, hpad']

/-! ## CTR's counter arithmetic -/

/-- Within a segment that does not carry out of its low 32 bits, or out of
its low `m` bits, counting in the low 32 bits counts in the low `m`. -/
theorem ctr_segment (m t q j : Nat) (hj : j < 2 ^ min m 32 - ctrBlock m t q % 2 ^ min m 32) :
    ctrBlock 32 (ctrBlock m t q) j = ctrBlock m t (q + j) := by
  have hP := Nat.two_pow_pos m
  have hW := Nat.two_pow_pos 32
  have e : (t % 2 ^ m + (q + j)) % 2 ^ m = ((t % 2 ^ m + q) % 2 ^ m + j) % 2 ^ m := by
    rw [← Nat.add_assoc, Nat.add_mod (t % 2 ^ m + q) j, Nat.add_mod ((t % 2 ^ m + q) % 2 ^ m) j, Nat.mod_mod]
  have hrP := Nat.mod_lt (t % 2 ^ m + q) hP
  unfold ctrBlock at hj ⊢
  rw [e]
  generalize (t % 2 ^ m + q) % 2 ^ m = r at hrP hj ⊢
  generalize t / 2 ^ m = a at hj ⊢
  have h5 := Nat.div_add_mod' (a * 2 ^ m + r) (2 ^ 32)
  by_cases hm : m ≤ 32
  · rw [Nat.min_eq_left hm] at hj
    have hK : 2 ^ 32 = 2 ^ (32 - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
    have h1 : (a * 2 ^ m + r) % 2 ^ m = r := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrP]
    rw [h1] at hj
    have hrj : (r + j) % 2 ^ m = r + j := Nat.mod_eq_of_lt (by omega)
    have h2 : (a * 2 ^ m) % 2 ^ 32 = (a % 2 ^ (32 - m)) * 2 ^ m := by rw [hK, Nat.mul_mod_mul_right]
    have h3 : (a % 2 ^ (32 - m)) * 2 ^ m + 2 ^ m ≤ 2 ^ 32 := by
      rw [hK, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (Nat.mod_lt _ (Nat.two_pow_pos _))
    have h4 : (a * 2 ^ m + r) % 2 ^ 32 = (a % 2 ^ (32 - m)) * 2 ^ m + r := by
      rw [Nat.add_mod, h2, Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hrj, h4]
    rw [h4] at h5
    generalize (a % 2 ^ (32 - m)) * 2 ^ m = c at h3 h5 ⊢
    rw [Nat.mod_eq_of_lt (show c + r + j < 2 ^ 32 by omega)]
    generalize (a * 2 ^ m + r) / 2 ^ 32 * 2 ^ 32 = D at h5 ⊢
    omega
  · rw [Nat.min_eq_right (by omega)] at hj
    have hK : 2 ^ m = 2 ^ (m - 32) * 2 ^ 32 := by rw [← pow_add]; congr 1; omega
    have h4 : (a * 2 ^ m + r) % 2 ^ 32 = r % 2 ^ 32 := by
      rw [hK, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h4] at hj h5
    rw [h4]
    have h7 : (r / 2 ^ 32 + 1) * 2 ^ 32 ≤ 2 ^ m := by
      rw [hK]
      exact Nat.mul_le_mul_right _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hK]; exact hrP))
    have h6 := Nat.div_add_mod' r (2 ^ 32)
    have hrm := Nat.mod_lt r hW
    rw [Nat.mod_eq_of_lt (show r % 2 ^ 32 + j < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show r + j < 2 ^ m by rw [Nat.add_mul] at h7; omega)]
    generalize (a * 2 ^ m + r) / 2 ^ 32 * 2 ^ 32 = D at h5 ⊢
    omega

/-- After a segment of `s` blocks, the next counter block. -/
theorem ctrBlock_next (m t q s : Nat) :
    2 ^ m * (ctrBlock m t q / 2 ^ m) + (ctrBlock m t q + s) % 2 ^ m = ctrBlock m t (q + s) := by
  have hP := Nat.two_pow_pos m
  have hr := Nat.mod_lt (t % 2 ^ m + q) hP
  have e : ((t % 2 ^ m + q) % 2 ^ m + s) % 2 ^ m = (t % 2 ^ m + (q + s)) % 2 ^ m := by
    rw [← Nat.add_assoc, Nat.add_mod (t % 2 ^ m + q) s, Nat.add_mod ((t % 2 ^ m + q) % 2 ^ m) s, Nat.mod_mod]
  unfold ctrBlock
  rw [Nat.add_comm (t / 2 ^ m * 2 ^ m), Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr, Nat.zero_add,
    Nat.add_assoc, Nat.add_comm (t / 2 ^ m * 2 ^ m) s, ← Nat.add_assoc, Nat.add_mul_mod_self_right, e,
    Nat.mul_comm (2 ^ m)]

theorem ctrBlock_lt (m t q : Nat) (ht : t < 2 ^ 128) (hm : m ≤ 128) : ctrBlock m t q < 2 ^ 128 := by
  have hP := Nat.two_pow_pos m
  have hK : 2 ^ 128 = 2 ^ (128 - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
  have h1 : t / 2 ^ m < 2 ^ (128 - m) := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hK]; exact ht)
  have h2 : (t / 2 ^ m + 1) * 2 ^ m ≤ 2 ^ 128 := by rw [hK]; exact Nat.mul_le_mul_right _ h1
  have h3 := Nat.mod_lt (t % 2 ^ m + q) hP
  unfold ctrBlock
  rw [Nat.add_mul] at h2
  omega

/-- Merging a counter's high bits with another's low `m`. -/
theorem merge_ctr (m : Nat) (x c M : BitVec 128) (hM : M.toNat = 2 ^ m - 1) :
    ((x &&& ~~~M) ||| (c &&& M)).toNat = 2 ^ m * (x.toNat / 2 ^ m) + c.toNat % 2 ^ m := by
  have hMi : ∀ i, M.getLsbD i = decide (i < m) := fun i => by
    rw [← BitVec.testBit_toNat, hM, Nat.testBit_two_pow_sub_one]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos m)), BitVec.testBit_toNat]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hMi, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, BitVec.testBit_toNat]
  by_cases him : i < m
  · simp [him]
  · rw [Nat.sub_add_cancel (by omega : m ≤ i)]
    by_cases h128 : i < 128
    · simp [him, h128]
    · have hx : x.getLsbD i = false := BitVec.getLsbD_of_ge x i (by omega)
      have hc : c.getLsbD i = false := BitVec.getLsbD_of_ge c i (by omega)
      simp [him, hx, hc]

/-- The low-32-bit mask of a low-`m`-bit mask. -/
theorem word_mask_eq (m : Nat) : (2 ^ m - 1) % 2 ^ 32 = 2 ^ min m 32 - 1 := by
  by_cases hm : m ≤ 32
  · rw [Nat.min_eq_left hm]
    apply Nat.mod_eq_of_lt
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm
    have := Nat.two_pow_pos m
    omega
  · rw [Nat.min_eq_right (by omega)]
    have hK : 2 ^ m = 2 ^ (m - 32) * 2 ^ 32 := by rw [← pow_add]; congr 1; omega
    have h1 := Nat.two_pow_pos (m - 32)
    have h2 : 2 ^ m - 1 = (2 ^ 32 - 1) + (2 ^ (m - 32) - 1) * 2 ^ 32 := by
      have h3 : 2 ^ 32 ≤ 2 ^ (m - 32) * 2 ^ 32 := Nat.le_mul_of_pos_left _ h1
      rw [hK, Nat.sub_one_mul]
      generalize 2 ^ (m - 32) * 2 ^ 32 = X at h3 ⊢
      omega
    rw [h2, Nat.add_mul_mod_self_right]
    rfl

/-- SP 800-38A's CTR over a segment equals CTR with the segment's own
counter, when they agree on the segment's counter blocks. -/
theorem aesCtr_segment (alg : Algorithm) (key : List (BitVec 8)) (m : Nat) (t0 t' data : List (BitVec 8))
    (off len : Nat) (hoff : off % 16 = 0) (hlen : off + len ≤ data.length)
    (hseg : ∀ j, j * 16 < len → ctrBlock 32 (ofBe t') j = ctrBlock m (ofBe t0) (off / 16 + j)) :
    aesCtr alg key 32 t' ((data.drop off).take len) = ((aesCtr alg key m t0 data).drop off).take len := by
  apply List.ext_getElem
  · simp only [aesCtr, List.length_map, List.length_range, List.length_take, List.length_drop]
  · intro i h1 h2
    have hi : i < len := by
      simp only [aesCtr, List.length_map, List.length_range, List.length_take, List.length_drop] at h1; omega
    simp only [aesCtr, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    have hd : ((data.drop off).take len)[i]! = data[off + i]! := by
      rw [getElem!_pos _ i (by simp only [List.length_take, List.length_drop]; omega),
        getElem!_pos data (off + i) (by omega), List.getElem_take, List.getElem_drop]
    have hq : (off + i) / 16 = off / 16 + i / 16 := by omega
    have hr : (off + i) % 16 = i % 16 := by omega
    rw [hd, hq, hr, hseg (i / 16) (by omega)]

/-! ## CTR's bytes -/

theorem ofBe_toBEBytes (w : Nat) : ∀ (b : BitVec w), w % 8 = 0 → ofBe b.toBEBytes = b.toNat := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b hw
    rw [BitVec.toBEBytes, BitVec.toLEBytes]
    by_cases h0 : w > 0
    · rw [ite_eq_left h0, List.reverse_cons, rind.modes.ofBe_append, ← BitVec.toBEBytes,
        ih (w - 8) (by omega) _ (by omega)]
      have h1 : ofBe [b.setWidth 8] = b.toNat % 2 ^ 8 := by simp [ofBe, BitVec.toNat_setWidth]
      rw [h1, List.length_singleton, pow_one, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
      have hlt : b.toNat / 2 ^ 8 < 2 ^ (w - 8) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 8), ← pow_add, Nat.sub_add_cancel (by omega)]
        exact b.isLt
      rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [ite_eq_right h0]
      have hb := b.isLt
      have hw0 : w = 0 := by omega
      subst hw0
      simp only [List.reverse_nil, ofBe, List.foldl_nil, pow_zero] at hb ⊢
      omega

theorem toNat_fromLEBytes : ∀ l : List (BitVec 8), (BitVec.fromLEBytes l).toNat = ofBe l.reverse
  | [] => by simp [BitVec.fromLEBytes, ofBe]
  | b :: l => by
    have hy := rind.modes.ofBe_lt l.reverse
    rw [List.length_reverse] at hy
    have hb := b.isLt
    have hp : 2 ^ (8 * (b :: l).length) = 256 ^ l.length * 256 := by
      rw [List.length_cons, Nat.mul_succ, pow_add, pow_mul]; norm_num
    have h1 : ofBe [b] = b.toNat := by simp [ofBe]
    rw [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, toNat_fromLEBytes l, List.reverse_cons, rind.modes.ofBe_append, h1, List.length_singleton,
      pow_one, Nat.shiftLeft_eq, hp]
    generalize ofBe l.reverse = y at hy ⊢
    have hP : 256 ≤ 256 ^ l.length * 256 := Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)
    have hy2 : y * 256 < 256 ^ l.length * 256 := Nat.mul_lt_mul_of_pos_right hy (by norm_num)
    have hb' : b.toNat < 256 := hb
    rw [Nat.mod_eq_of_lt (show b.toNat < 256 ^ l.length * 256 by omega),
      Nat.mod_eq_of_lt (show y < 256 ^ l.length * 256 by omega),
      Nat.mod_eq_of_lt (show y * 2 ^ 8 < 256 ^ l.length * 256 by rw [show (2 : Nat) ^ 8 = 256 by norm_num]; omega),
      Nat.lor_comm, show y * 2 ^ 8 = 2 ^ 8 * y by ring, ← Nat.two_pow_add_eq_or_of_lt hb]
    ring

theorem toNat_fromBEBytes (l : List (BitVec 8)) : (BitVec.fromBEBytes l).toNat = ofBe l := by
  rw [BitVec.fromBEBytes, BitVec.toNat_cast, toNat_fromLEBytes, List.reverse_reverse]

theorem from_be_bytes128 (a : Std.Array U8 16#usize) :
    (core.num.U128.from_be_bytes a).val = ofBe (bvs a.val) := by
  unfold core.num.U128.from_be_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact toNat_fromBEBytes _

theorem from_be_bytes32 (a : Std.Array U8 4#usize) :
    (core.num.U32.from_be_bytes a).val = ofBe (bvs a.val) := by
  unfold core.num.U32.from_be_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  exact toNat_fromBEBytes _

theorem bvs_to_be_bytes128 (x : U128) : bvs (core.num.U128.to_be_bytes x).val = x.bv.toBEBytes := by
  simp only [core.num.U128.to_be_bytes, Std.Array.from_val, bvs, List.map_map]
  exact List.map_id _

theorem ofBe_nonce_counter (l : List (BitVec 8)) (hl : l.length = 16) :
    ofBe (l.take 12 ++ be32 (ofBe (l.drop 12))) = ofBe l := by
  have hd : (l.drop 12).length = 4 := by rw [List.length_drop, hl]
  have hlt := rind.modes.ofBe_lt (l.drop 12)
  rw [hd] at hlt
  conv_rhs => rw [← List.take_append_drop 12 l]
  rw [rind.modes.ofBe_append, rind.modes.ofBe_append, rind.modes.ofBe_be32, rind.modes.length_be32, hd,
    Nat.mod_eq_of_lt (lt_of_lt_of_eq hlt (by norm_num))]

theorem split_first_chunk12_spec (N : Usize) (hN : N.val = 12) (s : Slice U8) (h : 12 ≤ s.val.length) :
    core.slice.Slice.split_first_chunk N s ⦃ o =>
      ∃ (a : Std.Array U8 N) (t : Slice U8), o = some (a, t) ∧ a.val = s.val.take 12 ∧
        t.val = s.val.drop 12 ⦄ := by
  unfold core.slice.Slice.split_first_chunk
  rw [dif_pos (show N.val ≤ s.length by rw [hN]; exact h)]
  exact (WP.spec_ok _).2 ⟨_, _, rfl, by rw [Std.Array.from_val, hN], by rw [Slice.from_val, hN]⟩

theorem try_from4_spec (N : Usize) (hN : N.val = 4) (t : Slice U8) (h : t.val.length = 4) :
    core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 t ⦃ r =>
      ∃ a : Std.Array U8 N, r = .Ok a ∧ a.val = t.val ⦄ := by
  unfold core.array.TryFromArrayCopySlice.try_from
  rw [dif_pos (show t.length = N.val by rw [hN]; exact h)]
  exact (WP.spec_ok _).2 ⟨_, rfl, Std.Array.from_val _ _⟩

theorem merge_ctr_u128 (m : Nat) (x c M : U128) (hM : M.val = 2 ^ m - 1) :
    ((x &&& ~~~M) ||| (c &&& M)).val = 2 ^ m * (x.val / 2 ^ m) + c.val % 2 ^ m :=
  merge_ctr m x.bv c.bv M.bv hM

theorem usize_lt_2_64 : Usize.max < 2 ^ 64 := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

theorem sat_cast_val (x : Usize) :
    (core.num.U128.saturating_sub (UScalar.cast .U128 x) 1#u128).val = x.val - 1 := by
  have hx : x.val ≤ Usize.max := by scalar_tac
  have h64 := usize_lt_2_64
  show (BitVec.ofNat _ (max 0 ((UScalar.cast .U128 x).val - (1#u128 : U128).val))).toNat = _
  rw [BitVec.toNat_ofNat, Nat.zero_max, UScalar.cast_val_eq]
  show (x.val % 2 ^ 128 - 1) % 2 ^ 128 = x.val - 1
  rw [Nat.mod_eq_of_lt (show x.val < 2 ^ 128 by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## CTR -/

/-- `apply_keystream`'s loop, over the segments of `rest` that its 32-bit
counter covers without carrying: each XORs CTR's keystream for its offset
into the buffer, which `back` writes after what came before. -/
theorem apply_keystream_loop_spec (alg : Algorithm) (key : List (BitVec 8)) (m : Nat) (hm : m ≤ 128)
    (ak : low.x86_64.aes.AesKey) (hak : ModeKeyIs alg key ak) (counter_mask word_mask : U128)
    (hcm : counter_mask.val = 2 ^ m - 1) (hwm : word_mask.val = 2 ^ min m 32 - 1)
    (t0 data : List (BitVec 8)) (N : Nat) (hN : data.length = N)
    (back : Slice U8 → Slice U8) (block : U128) (rest : Slice U8)
    (hr : bvs rest.val = data.drop (N - rest.val.length)) (hrl : rest.val.length ≤ N)
    (hb : rest.val ≠ [] → (N - rest.val.length) % 16 = 0 ∧
      block.val = ctrBlock m (ofBe t0) ((N - rest.val.length) / 16))
    (hbk : ∀ s : Slice U8, s.val.length = rest.val.length →
      bvs (back s).val = (aesCtr alg key m t0 data).take (N - rest.val.length) ++ bvs s.val) :
    mid.aes.AesCtr.apply_keystream_loop back ak counter_mask word_mask block rest
      ⦃ r => bvs r.val = aesCtr alg key m t0 data ⦄ := by
  have hAl : (aesCtr alg key m t0 data).length = N := by simp [aesCtr, hN]
  unfold mid.aes.AesCtr.apply_keystream_loop
  apply loop.spec_decr_nat (fun x => x.2.2.val.length)
    (fun x => bvs x.2.2.val = data.drop (N - x.2.2.val.length) ∧ x.2.2.val.length ≤ N ∧
      (x.2.2.val ≠ [] → (N - x.2.2.val.length) % 16 = 0 ∧
        x.2.1.val = ctrBlock m (ofBe t0) ((N - x.2.2.val.length) / 16)) ∧
      ∀ s : Slice U8, s.val.length = x.2.2.val.length →
        bvs (x.1 s).val = (aesCtr alg key m t0 data).take (N - x.2.2.val.length) ++ bvs s.val)
  · rintro ⟨bk, b, r⟩ ⟨hr, hrl, hb, hbk⟩
    simp only at hr hrl hb hbk ⊢
    unfold mid.aes.AesCtr.apply_keystream_loop.body
    simp only [core.slice.Slice.is_empty, bind_ok, Slice.length]
    by_cases h0 : r.val.length = 0
    · simp only [decide_eq_true h0, ↓reduceIte, WP.spec_ok]
      have hrn : r.val = [] := List.length_eq_zero_iff.mp h0
      rw [hbk r rfl]
      simp only [hrn, List.length_nil, Nat.sub_zero, bvs, List.map_nil, List.append_nil]
      exact List.take_of_length_le (le_of_eq hAl)
    simp only [decide_eq_false h0, Bool.false_eq_true, ↓reduceIte, lift, bind_ok]
    have hne : r.val ≠ [] := fun h => h0 (by rw [h]; rfl)
    obtain ⟨hoff, hbv⟩ := hb hne
    have hw32 : 2 ^ min m 32 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)
    have hwpos := Nat.two_pow_pos (min m 32)
    have hmodlt := Nat.mod_lt b.val hwpos
    have hbw : (b &&& word_mask).val = b.val % 2 ^ min m 32 := by
      show (b.bv &&& word_mask.bv).toNat = _
      rw [BitVec.toNat_and, show word_mask.bv.toNat = word_mask.val from rfl, hwm,
        Nat.and_two_pow_sub_one_eq_mod]
      all_goals rfl
    apply WP.spec_bind (U128.sub_spec (x := word_mask) (y := b &&& word_mask) (by rw [hbw, hwm]; omega))
    rintro i1 ⟨hi1, -⟩
    rw [hbw, hwm] at hi1
    have h3664 : (2 : Nat) ^ 32 * 16 < 2 ^ 64 := by norm_num
    have h64 : (2 : Nat) ^ 64 < 2 ^ 128 := by norm_num
    apply WP.spec_bind (U128.add_spec (x := i1) (y := 1#u128)
      (by rw [hi1, U128.max_eq]; show _ + 1 ≤ _; omega))
    rintro i2 hi2
    obtain ⟨seg, hsegd⟩ : ∃ seg, seg = 2 ^ min m 32 - b.val % 2 ^ min m 32 := ⟨_, rfl⟩
    have hseg : i2.val = seg := by rw [hi2, hi1, hsegd]; show _ + 1 = _; omega
    have hseg1 : 1 ≤ seg := by omega
    have hsegw : seg ≤ 2 ^ 32 := by omega
    have hc64 : (UScalar.cast .U64 i2).val = seg := by
      rw [UScalar.cast_val_eq, ← hseg]
      exact Nat.mod_eq_of_lt (by rw [hseg]; show _ < 2 ^ 64; omega)
    apply WP.spec_bind (U64.mul_spec (x := UScalar.cast .U64 i2) (y := 16#u64)
      (by rw [hc64, U64.max_eq]; show _ * 16 ≤ _; omega))
    rintro i3 hi3
    have hi3' : i3.val = 16 * seg := by rw [hi3, hc64]; show _ * 16 = _; omega
    have hrmax := Slice.length_ineq r
    apply WP.spec_bind (Pₘ := fun res : core.result.Result Usize core.num.error.TryFromIntError =>
      (∀ l, res = .Ok l → l.val = i3.val) ∧ (∀ e, res = .Err e → Usize.max < i3.val))
    · simp only [Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from, core.num.tryFromUScalar]
      split
      · rename_i hfit
        refine (WP.spec_ok _).2 ⟨fun l hl => ?_, fun e he => by cases he⟩
        cases hl
        have := UScalar.cast_inBounds_spec .Usize i3 hfit
        simpa [lift, WP.spec_ok] using this
      · rename_i hfit
        refine (WP.spec_ok _).2 ⟨fun l hl => (by cases hl), fun e _ => ?_⟩
        rw [← UScalar.max_USize_eq]
        omega
    rintro res ⟨hres1, hres2⟩
    apply WP.spec_bind (Pₘ := fun len : Usize => len.val = min (16 * seg) r.val.length)
    · cases res with
      | Ok l =>
        have hl := hres1 l rfl
        dsimp only
        by_cases hlt : l < Slice.len r
        · simp only [hlt, ↓reduceIte, WP.spec_ok]
          have : l.val < (Slice.len r).val := hlt
          rw [Slice.len_val] at this
          simp only [Slice.length] at this
          omega
        · simp only [hlt, ↓reduceIte, WP.spec_ok, Slice.len_val, Slice.length]
          have : ¬ l.val < (Slice.len r).val := hlt
          rw [Slice.len_val] at this
          simp only [Slice.length] at this
          omega
      | Err e =>
        have := hres2 e rfl
        simp only [WP.spec_ok, Slice.len_val, Slice.length]
        omega
    rintro len hlen
    have hlenr : len.val ≤ r.val.length := by omega
    have hlen1 : 1 ≤ len.val := by have := List.length_pos_iff.mpr hne; omega
    apply WP.spec_bind (core.slice.Slice.split_at_mut.spec r len (by simp only [Slice.length]; omega))
    rintro ⟨⟨segment, next⟩, sback⟩ ⟨hsl, hnl, hsv, hnv, hsback⟩
    try simp only [Slice.length] at hsl hnl
    have hbl : (core.num.U128.to_be_bytes b).val.length = 16 := (core.num.U128.to_be_bytes b).property
    have hsl16 : (Std.Array.to_slice (core.num.U128.to_be_bytes b)).val = (core.num.U128.to_be_bytes b).val :=
      Slice.from_val _ _
    refine WP.spec_bind (split_first_chunk12_spec _ (by rfl) _ (by rw [hsl16, hbl]; omega)) ?_
    rintro o ⟨nonce, cs, rfl, hnonce, hcs⟩
    simp only [core.option.Option.unwrap, Result.ofOption, bind_ok]
    refine WP.spec_bind (try_from4_spec _ (by rfl) cs (by rw [hcs, List.length_drop, hsl16, hbl])) ?_
    rintro r1 ⟨a, rfl, hav⟩
    simp only [core.result.Result.unwrap, bind_ok]
    apply WP.spec_bind (aes_ctr_apply_spec alg key ak hak nonce _ segment)
    intro segment1 hseg1v
    simp only [core.convert.IntoFrom.into, core.convert.FromU128U64, bind_ok, lift]
    refine (WP.spec_ok _).2 ?_
    dsimp only
    -- the bytes of `b`
    have hbb : bvs (core.num.U128.to_be_bytes b).val = b.bv.toBEBytes := bvs_to_be_bytes128 b
    have hbbl : (bvs (core.num.U128.to_be_bytes b).val).length = 16 := by rw [List.length_map, hbl]
    have hob : ofBe (bvs (core.num.U128.to_be_bytes b).val) = b.val := by
      rw [hbb]; exact ofBe_toBEBytes 128 _ (by norm_num)
    have ht' : ofBe (bvs nonce.val ++ be32 (core.num.U32.from_be_bytes a).val) = b.val := by
      rw [from_be_bytes32, hav, hcs, hnonce, hsl16, ← hob]
      simp only [bvs, List.map_take, List.map_drop]
      exact ofBe_nonce_counter _ (by rw [List.length_map, hbl])
    -- the segment's keystream
    have hoffN : N - r.val.length + len.val ≤ data.length := by omega
    have hsegks : bvs segment1.val =
        ((aesCtr alg key m t0 data).drop (N - r.val.length)).take len.val := by
      rw [hseg1v, hsv]
      simp only [bvs, List.map_take]
      rw [show List.map (fun x : U8 => x.bv) r.val = bvs r.val from rfl, hr]
      apply aesCtr_segment alg key m t0 _ data _ _ hoff hoffN
      intro j hj
      rw [ht', hbv]
      apply ctr_segment
      rw [← hbv]
      omega
    have hs1l : segment1.val.length = len.val := by
      have h1 := congrArg List.length hsegks
      rw [List.length_take, List.length_drop, hAl] at h1
      have h2 : (bvs segment1.val).length = segment1.val.length := List.length_map _
      omega
    have hdl : (List.drop len.val r.val).length = r.val.length - len.val := List.length_drop
    simp only at hsv hnv
    try simp only [and_assoc]
    refine ⟨?_, by omega, fun hn => ?_, fun s hs => ?_, by omega⟩
    · rw [hnv]
      simp only [bvs, List.map_drop]
      rw [show List.map (fun x : U8 => x.bv) r.val = bvs r.val from rfl, hr, List.drop_drop]
      congr 1
      omega
    · have hlt : len.val < r.val.length := by
        by_contra hge; apply hn; rw [hnv]; exact List.drop_eq_nil_of_le (by omega)
      have hl16 : len.val = 16 * seg := by omega
      refine ⟨by omega, ?_⟩
      rw [merge_ctr_u128 m _ _ _ hcm, core.num.U128.wrapping_add_val_eq,
        core.convert.num.FromU128U64.from_val_eq, hc64]
      simp only [UScalar.size, UScalarTy.numBits]
      rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hm), hbv, ctrBlock_next]
      congr 1
      omega
    · obtain ⟨hsb, -⟩ := hsback segment1 s (by simp only [Slice.length]; exact hs1l)
        (by simp only [Slice.length]; omega)
      rw [hbk _ (by rw [hsb, List.length_append, hs1l]; omega), hsb]
      simp only [bvs, List.map_append] at hsegks ⊢
      rw [hsegks, ← List.append_assoc, ← List.take_add]
      congr 2
      omega
  · exact ⟨hr, hrl, hb, hbk⟩

/-- AES-CTR keystream application. It is refused, leaving the buffer
unchanged, when the buffer has more blocks than the counter's `m` bits can
count; otherwise the buffer becomes SP 800-38A's CTR mode of it, from the
counter block, counting over its low `m` bits. -/
theorem aes_ctr_apply_keystream_spec (h : RunsAesHw) (alg : Algorithm) (key : List (BitVec 8)) (m : Nat)
    (c : mid.aes.AesCtr) (hc : AesCtrIs alg key m c) (counter_block : Std.Array U8 16#usize)
    (inout : Slice U8) :
    c.apply_keystream counter_block inout ⦃ r =>
      (2 ^ m < (inout.length + 15) / 16 → r = (.Err .WrongLength, inout)) ∧
      (¬ 2 ^ m < (inout.length + 15) / 16 →
        r.1 = .Ok () ∧ bvs r.2.val = aesCtr alg key m (bvs counter_block.val) (bvs inout.val)) ⦄ := by
  obtain ⟨e, he⟩ := h.1
  obtain ⟨hk, hm, hcm⟩ := hc
  have hmax := Slice.length_ineq inout
  have h64 := usize_lt_2_64
  unfold mid.aes.AesCtr.apply_keystream
  simp only [he, bind_ok, core.num.Usize.div_ceil, lift]
  rw [dif_neg (show ¬ (16#usize : Usize).val = 0 by decide)]
  simp only [bind_ok]
  have hD : ∀ x : Usize, x.val = 16 →
      ((Slice.len inout).val + x.val - 1) / x.val = (inout.length + 15) / 16 := by
    intro x hx; rw [hx, Slice.len_val]; omega
  split
  · rename_i hgt
    have hgt' : c.counter_mask.val < (core.num.U128.saturating_sub (UScalar.cast .U128 _) 1#u128).val := hgt
    rw [sat_cast_val, UScalar.ofNatCore_val_eq, hD _ (by rfl), hcm] at hgt'
    refine (WP.spec_ok _).2 ⟨fun _ => rfl, fun hn => absurd ?_ hn⟩
    have := Nat.two_pow_pos m
    omega
  · rename_i hgt
    have hgt' : ¬ c.counter_mask.val < (core.num.U128.saturating_sub (UScalar.cast .U128 _) 1#u128).val := hgt
    rw [sat_cast_val, UScalar.ofNatCore_val_eq, hD _ (by rfl), hcm] at hgt'
    have hnot : ¬ 2 ^ m < (inout.length + 15) / 16 := by have := Nat.two_pow_pos m; omega
    simp only [low.ct.secret_slice, bind_ok]
    have hwm : (c.counter_mask &&& core.convert.num.FromU128U32.from core.num.U32.MAX).val = 2 ^ min m 32 - 1 := by
      show (c.counter_mask.bv &&& (core.convert.num.FromU128U32.from core.num.U32.MAX).bv).toNat = _
      rw [BitVec.toNat_and, show (core.convert.num.FromU128U32.from core.num.U32.MAX).bv.toNat =
        (core.convert.num.FromU128U32.from core.num.U32.MAX).val from rfl,
        core.convert.num.FromU128U32.from_val_eq, show (core.num.U32.MAX).val = 2 ^ 32 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, show c.counter_mask.bv.toNat = c.counter_mask.val from rfl, hcm,
        word_mask_eq]
    refine WP.spec_bind (apply_keystream_loop_spec alg key m hm c.key hk c.counter_mask _ hcm hwm
      (bvs counter_block.val) (bvs inout.val) inout.val.length (by simp [bvs]) (fun s => s)
      (core.num.U128.from_be_bytes counter_block) inout (by simp [bvs]) (le_refl _) ?_ ?_) ?_
    · intro _
      refine ⟨by simp, ?_⟩
      rw [from_be_bytes128, Nat.sub_self, Nat.zero_div]
      unfold ctrBlock
      rw [Nat.add_zero, Nat.mod_mod, Nat.div_add_mod']
    · intro s _
      simp
    · intro back' hback'
      simp only [low.ct.public_slice, bind_ok]
      exact (WP.spec_ok _).2 ⟨fun hn => absurd hn hnot, fun _ => ⟨rfl, hback'⟩⟩

end rind.x86_64
