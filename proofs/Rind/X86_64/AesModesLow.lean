import Rind.X86_64.AesCipher
import Rind.AesModesBytes
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.vale rind.simd rind.modes

/-!
# AES-CTR and AES-CBC on AES-NI

`low::x86_64::aes_ctr::apply` and `low::x86_64::aes_cbc::{encrypt, decrypt}`
run aws-lc's `aes_hw_ctr32_encrypt_blocks` and `aes_hw_cbc_encrypt` for a key
`expand_key` or `AesDecKey::new` expanded on the AES instructions. The axioms
below assume HOL Light theorems of both routines, as rind's build emits them,
that are not proven yet: `proofs/hol-light/x86_64/aes_hw_cbc_encrypt.ml`
proves CBC encryption and part of decryption, and CTR has no proof, so
`Axioms.lean` lists none of them and [the AES modes
quest](/quest/m4/verified/aes-modes.md) owns the rest. Each states its block's
result in `proofs/hol-light/x86_64/aes_hw_spec.ml`'s `aes_hw_encrypt`,
`aes_hw_decrypt`, and `aes_ctr32_block`: the round keys `ks`, read
little-endian from the `AES_KEY` 16 bytes apart, and its round count `r`, the
32-bit word at byte 240, with `ks` of length `r + 2` and `r` 9, 11, or 13. The
axioms restate those theorems about the Rust wrappers `hw_ctr32`,
`hw_encrypt`, and `hw_decrypt`, over Lean's definitions here of
`aes_hw_encrypt`, `aes_hw_decrypt`, and `aes_ctr32_block`. Trusted: the
restatement; that HOL Light's `aesenc`, `aesenclast`, `aesdec`, and
`aesdeclast` (s2n-bignum's `x86/proofs/aes.ml`) are `Rind.X86_64.Simd`'s
`_mm_aesenc_si128` and the others, both Intel's definitions; and that each
wrapper passes the pointers, count, and direction the theorem names, its key's
round keys and `rounds` field being the `AES_KEY`'s. The rest is proven: that
those blocks are FIPS 197's cipher and inverse cipher of the key, through
`Rind.X86_64.AesKey`, and that `ctr::blocks` and the wrappers compute
`Rind.AesModes`'s SP 800-38A modes.
-/

namespace rind.x86_64

/-! ## HOL Light's specs, over Lean's models of the instructions -/

/-- HOL Light's `aes_hw_encrypt`: the block XORed with the first round key,
`AESENC` with each round key but the first and last, then `AESENCLAST` with
the last. `evalRound` is `_mm_aesenc_si128` (`aesenc_eq`), and
`shiftRows (subBytes s) ^^^ k` is `_mm_aesenclast_si128` (`aesenclast_eq`). -/
def aesHwEncrypt (ks : List Quad32) (b : Quad32) : Quad32 :=
  shiftRows (subBytes (ks.tail.dropLast.foldl evalRound (b ^^^ ks.head!))) ^^^ ks.getLast!

/-- HOL Light's `aes_hw_decrypt`: the same with `AESDEC` and `AESDECLAST`.
`eqInvRound` is `_mm_aesdec_si128` (`aesdec_eq`), and
`invShiftRows (invSubBytes s) ^^^ k` is `_mm_aesdeclast_si128`
(`invSubBytes_invShiftRows`). -/
def aesHwDecrypt (ks : List Quad32) (b : Quad32) : Quad32 :=
  invShiftRows (invSubBytes (ks.tail.dropLast.foldl eqInvRound (b ^^^ ks.head!))) ^^^ ks.getLast!

/-- HOL Light's `word_bytereverse` on a 32-bit word. -/
def bswap32 (w : BitVec 32) : BitVec 32 :=
  w.extractLsb' 0 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 24 8

/-- HOL Light's `aes_ctr32_block`: the counter block `i` after `iv`, whose top
32 bits, bytes 12 to 15 read big-endian, add `i` modulo `2^32`. -/
def aesCtr32Block (iv : Quad32) (i : Nat) : Quad32 :=
  bswap32 (bswap32 (iv.extractLsb' 96 32) + BitVec.ofNat 32 i) ++ iv.extractLsb' 0 96

/-- An `AES_KEY`'s round keys and round count, as the HOL Light theorems
require them: `r + 2` round keys, `r` being 9, 11, or 13. -/
def HwSchedule (ks : List Quad32) (r : Nat) : Prop :=
  ks.length = r + 2 ∧ (r = 9 ∨ r = 11 ∨ r = 13)

/-- The round keys an AES-NI encryption key holds, as its `AES_KEY` holds them. -/
def hwRoundKeys : low.x86_64.aes.HwKey → List Quad32
  | .Aes128 k => k.round_keys.val
  | .Aes192 k => k.round_keys.val
  | .Aes256 k => k.round_keys.val

/-- An AES-NI encryption key's `rounds`, its `AES_KEY`'s round count. -/
def hwRounds : low.x86_64.aes.HwKey → Nat
  | .Aes128 k => k.rounds.val
  | .Aes192 k => k.rounds.val
  | .Aes256 k => k.rounds.val

/-- The round keys an AES-NI decryption key holds, as its `AES_KEY` holds them. -/
def hwDecRoundKeys : low.x86_64.aes.HwDecKey → List Quad32
  | .Aes128 k => k.round_keys.val
  | .Aes192 k => k.round_keys.val
  | .Aes256 k => k.round_keys.val

/-- An AES-NI decryption key's `rounds`, its `AES_KEY`'s round count. -/
def hwDecRounds : low.x86_64.aes.HwDecKey → Nat
  | .Aes128 k => k.rounds.val
  | .Aes192 k => k.rounds.val
  | .Aes256 k => k.rounds.val

/-! ## The routines, restated -/

/-- `aes_hw_ctr32_encrypt_blocks`' theorem, not yet proven: block `i`, read
little-endian, becomes itself XORed with `aes_hw_encrypt ks
(aes_ctr32_block iv i)`, for `iv` the counter block read little-endian. -/
@[step]
axiom hw_ctr32_spec (k : low.x86_64.aes.HwKey) (ivec : Std.Array U8 16#usize)
    (blocks : Slice (Std.Array U8 16#usize)) (hk : HwSchedule (hwRoundKeys k) (hwRounds k))
    (hn : 16 * blocks.length < 2 ^ 64) :
    low.x86_64.aes_ctr.hw_ctr32 k ivec blocks ⦃ r => r.length = blocks.length ∧
      ∀ i < blocks.length, loadBytes r.val[i]!.val = loadBytes blocks.val[i]!.val ^^^
        aesHwEncrypt (hwRoundKeys k) (aesCtr32Block (loadBytes ivec.val) i) ⦄

/-- `aes_hw_cbc_encrypt`'s theorem for encryption, which
`proofs/hol-light/x86_64/aes_hw_cbc_encrypt.ml` proves as
`AES_HW_CBC_ENCRYPT_ENCRYPT_SUBROUTINE_CORRECT`: block `i`, read
little-endian, becomes `aes_hw_encrypt ks` of itself XORed with the IV for the
first and the previous output block for the rest. -/
@[step]
axiom hw_cbc_encrypt_spec (k : low.x86_64.aes.HwKey) (iv : Std.Array U8 16#usize)
    (blocks : Slice (Std.Array U8 16#usize)) (hk : HwSchedule (hwRoundKeys k) (hwRounds k))
    (hn : 16 * blocks.length < 2 ^ 64) :
    low.x86_64.aes_cbc.hw_encrypt k iv blocks ⦃ r => r.length = blocks.length ∧
      ∀ i < blocks.length, loadBytes r.val[i]!.val = aesHwEncrypt (hwRoundKeys k)
        (loadBytes blocks.val[i]!.val ^^^
          if i = 0 then loadBytes iv.val else loadBytes r.val[i - 1]!.val) ⦄

/-- `aes_hw_cbc_encrypt`'s theorem for decryption, not yet proven: block `i`, read
little-endian, becomes `aes_hw_decrypt ks` of itself XORed with the IV for the
first and the previous input block for the rest. -/
@[step]
axiom hw_cbc_decrypt_spec (k : low.x86_64.aes.HwDecKey) (iv : Std.Array U8 16#usize)
    (blocks : Slice (Std.Array U8 16#usize)) (hk : HwSchedule (hwDecRoundKeys k) (hwDecRounds k))
    (hn : 16 * blocks.length < 2 ^ 64) :
    low.x86_64.aes_cbc.hw_decrypt k iv blocks ⦃ r => r.length = blocks.length ∧
      ∀ i < blocks.length, loadBytes r.val[i]!.val =
        aesHwDecrypt (hwDecRoundKeys k) (loadBytes blocks.val[i]!.val) ^^^
          if i = 0 then loadBytes iv.val else loadBytes blocks.val[i - 1]!.val ⦄

/-! ## The block cipher -/

theorem head!_eq {α : Type} [Inhabited α] (l : List α) (h : 0 < l.length) : l.head! = l[0]! := by
  cases l <;> simp_all

theorem getLast!_eq {α : Type} [Inhabited α] (l : List α) {n : Nat} (h : l.length = n + 1) :
    l.getLast! = l[n]! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem!_eq_getElem?_getD, h]
  rfl

theorem aesHwEncrypt_eq (alg : Algorithm) (ks : List Quad32) (hl : ks.length = nr alg + 1) (b : Quad32) :
    aesHwEncrypt ks b = evalCipher alg b ks := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  rw [aesHwEncrypt, evalCipher, evalRounds_foldl _ _ (show nr alg - 1 + 1 ≤ ks.length by omega),
    List.dropLast_eq_take, ← List.drop_one, List.length_drop, hl, head!_eq _ (by omega),
    getLast!_eq _ hl]
  simp

theorem aesHwDecrypt_eq (alg : Algorithm) (ks : List Quad32) (hl : ks.length = nr alg + 1) (b : Quad32) :
    aesHwDecrypt ks b = eqInvCipher alg b ks.reverse := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  have hrl : ks.reverse.length = nr alg + 1 := by simp [hl]
  rw [aesHwDecrypt, eqInvCipher, eqInvRounds_foldl _ _ _ (show nr alg - 1 + 1 ≤ ks.reverse.length by omega),
    show nr alg - 1 + 1 = nr alg by omega, ← reverse_slice ks.reverse hrl, List.reverse_reverse,
    List.dropLast_eq_take, ← List.drop_one, List.length_drop, hl, head!_eq _ (by omega),
    getLast!_eq _ hl]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_reverse (show nr alg < ks.length by omega),
    List.getElem?_reverse (show 0 < ks.length by omega), hl]
  simp

/-! ## Bytes and blocks -/

theorem bvs_eq_of_load {a : Std.Array U8 16#usize} {q : Quad32} (h : loadBytes a.val = q) :
    bvs a.val = leQuad32ToBytes q := by
  rw [← h, loadBytes, leQuad32ToBytes_leBytesToQuad32 _ (by simp)]

theorem toNat_app {m n : Nat} (x : BitVec m) (y : BitVec n) : (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem toNat_bswap32 (w : BitVec 32) : (bswap32 w).toNat =
    w.toNat % 256 * 2 ^ 24 + w.toNat / 2 ^ 8 % 256 * 2 ^ 16 + w.toNat / 2 ^ 16 % 256 * 2 ^ 8 +
      w.toNat / 2 ^ 24 % 256 := by
  simp only [bswap32, toNat_app, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem toNat_leBytesToQuad32_ctr (n : List (BitVec 8)) (hn : n.length = 12) (c : Nat) :
    (leBytesToQuad32 (n ++ be32 c)).toNat = Nat.ofDigits 256 (n.map BitVec.toNat) +
      2 ^ 96 * (c / 2 ^ 24 % 256 + 256 * (c / 2 ^ 16 % 256 + 256 * (c / 2 ^ 8 % 256 + 256 * (c % 256)))) := by
  have hN : Nat.ofDigits 256 (n.map BitVec.toNat) < 2 ^ 96 := by
    have := Nat.ofDigits_lt_base_pow_length (b := 256) (l := n.map BitVec.toNat) (by norm_num)
      (by simp only [List.mem_map]; rintro _ ⟨x, -, rfl⟩; exact x.isLt)
    simpa [hn] using this
  rw [leBytesToQuad32, BitVec.toNat_setWidth, rind.spec.toNat_fromLEBytes, List.map_append,
    Nat.ofDigits_append, be32_eq]
  simp only [List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil, BitVec.toNat_ofNat,
    List.length_map, hn]
  omega

/-- A 32-bit number's bytes, most significant first, read back least
significant first and byte-reversed, are the number. -/
theorem bswap_digits (x : Nat) (hx : x < 2 ^ 32) :
    let D := x / 2 ^ 24 % 256 + 256 * (x / 2 ^ 16 % 256 + 256 * (x / 2 ^ 8 % 256 + 256 * (x % 256)))
    D % 256 * 2 ^ 24 + D / 2 ^ 8 % 256 * 2 ^ 16 + D / 2 ^ 16 % 256 * 2 ^ 8 + D / 2 ^ 24 % 256 = x ∧
      D < 2 ^ 32 := by
  intro D
  have e : x = x / 2 ^ 24 % 256 * 2 ^ 24 + x / 2 ^ 16 % 256 * 2 ^ 16 + x / 2 ^ 8 % 256 * 2 ^ 8 + x % 256 := by
    omega
  have ha : x / 2 ^ 24 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hb : x / 2 ^ 16 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hc : x / 2 ^ 8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hd : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
  simp only [D]
  generalize x / 2 ^ 24 % 256 = a at *
  generalize x / 2 ^ 16 % 256 = b at *
  generalize x / 2 ^ 8 % 256 = c at *
  generalize x % 256 = d at *
  subst e
  have q1 : (a + 256 * (b + 256 * (c + 256 * d))) / 256 = b + 256 * (c + 256 * d) := by omega
  have q2 : (b + 256 * (c + 256 * d)) / 256 = c + 256 * d := by omega
  have q3 : (c + 256 * d) / 256 = d := by omega
  have h0 : (a + 256 * (b + 256 * (c + 256 * d))) % 256 = a := by omega
  have h1 : (a + 256 * (b + 256 * (c + 256 * d))) / 2 ^ 8 % 256 = b := by
    rw [show (2 : Nat) ^ 8 = 256 from rfl, q1]; omega
  have h2 : (a + 256 * (b + 256 * (c + 256 * d))) / 2 ^ 16 % 256 = c := by
    rw [show (2 : Nat) ^ 16 = 256 * 256 from rfl, ← Nat.div_div_eq_div_mul, q1, q2]; omega
  have h3 : (a + 256 * (b + 256 * (c + 256 * d))) / 2 ^ 24 % 256 = d := by
    rw [show (2 : Nat) ^ 24 = 256 * 256 * 256 from rfl, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, q1,
      q2, q3]; omega
  exact ⟨by rw [h0, h1, h2, h3], by omega⟩

/-- The counter blocks `aes_ctr32_block` counts from `n ++ be32 c` are those
of `n` followed by the big-endian count, modulo `2^32`. -/
theorem aesCtr32Block_bytes (n : List (BitVec 8)) (hn : n.length = 12) (c i : Nat) (hc : c < 2 ^ 32) :
    aesCtr32Block (leBytesToQuad32 (n ++ be32 c)) i = leBytesToQuad32 (n ++ be32 ((c + i) % 2 ^ 32)) := by
  have hiv := toNat_leBytesToQuad32_ctr n hn c
  have hiv' := toNat_leBytesToQuad32_ctr n hn ((c + i) % 2 ^ 32)
  have hN : Nat.ofDigits 256 (n.map BitVec.toNat) < 2 ^ 96 := by
    have := Nat.ofDigits_lt_base_pow_length (b := 256) (l := n.map BitVec.toNat) (by norm_num)
      (by simp only [List.mem_map]; rintro _ ⟨x, -, rfl⟩; exact x.isLt)
    simpa [hn] using this
  generalize Nat.ofDigits 256 (n.map BitVec.toNat) = N at *
  generalize leBytesToQuad32 (n ++ be32 c) = iv at *
  obtain ⟨hD, hDl⟩ := bswap_digits c hc
  generalize c / 2 ^ 24 % 256 + 256 * (c / 2 ^ 16 % 256 + 256 * (c / 2 ^ 8 % 256 + 256 * (c % 256))) = D at *
  have hhi : iv.toNat / 2 ^ 96 % 2 ^ 32 = D := by omega
  have hlo : iv.toNat / 2 ^ 0 % 2 ^ 96 = N := by omega
  have h1 : (bswap32 (iv.extractLsb' 96 32)).toNat = c := by
    rw [toNat_bswap32, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, hhi, hD]
  have h2 : (bswap32 (iv.extractLsb' 96 32) + BitVec.ofNat 32 i).toNat = (c + i) % 2 ^ 32 := by
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [aesCtr32Block, toNat_app, toNat_bswap32, h2, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, hlo, hiv']
  ring

/-! ## The keys -/

/-- An AES key holding FIPS 197's round keys for the key bytes `key`, which
`alg` sizes, on the AES instructions, with the round count aws-lc's routines
read. -/
def ModeKeyIs (alg : Algorithm) (key : List (BitVec 8)) (k : low.x86_64.aes.AesKey) : Prop :=
  key.length = 4 * nk alg ∧
    ∃ hk, k = .Hw hk ∧ HwKeyIs alg (seqNat8ToSeqNat32LE key) hk ∧ hwRounds hk = nr alg - 1

/-- An AES decryption key holding `KeyExpansionEIC`'s round keys for the key
bytes `key`, which `alg` sizes, on the AES instructions, with the round count
aws-lc's routines read. -/
def ModeDecKeyIs (alg : Algorithm) (key : List (BitVec 8)) (k : low.x86_64.aes.AesDecKey) : Prop :=
  key.length = 4 * nk alg ∧
    ∃ hk, k = .Hw hk ∧ HwDecKeyIs alg (seqNat8ToSeqNat32LE key) hk ∧ hwDecRounds hk = nr alg - 1

theorem hw_key_schedule {alg : Algorithm} {kw : List (BitVec 32)} {hk : low.x86_64.aes.HwKey}
    (h : HwKeyIs alg kw hk) (hr : hwRounds hk = nr alg - 1) :
    HwSchedule (hwRoundKeys hk) (hwRounds hk) ∧ ∀ b, aesHwEncrypt (hwRoundKeys hk) b = aesEncrypt alg kw b := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl : k.round_keys.val.length = nr .AES_128 + 1 := k.round_keys.property
    simp only [hwRounds] at hr
    refine ⟨⟨by simp [hwRoundKeys, hwRounds, hl, hr, nr], by simp [hwRounds, hr, nr]⟩, fun b => ?_⟩
    rw [hwRoundKeys, aesHwEncrypt_eq _ _ hl, hrk]; rfl
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl : k.round_keys.val.length = nr .AES_192 + 1 := k.round_keys.property
    simp only [hwRounds] at hr
    refine ⟨⟨by simp [hwRoundKeys, hwRounds, hl, hr, nr], by simp [hwRounds, hr, nr]⟩, fun b => ?_⟩
    rw [hwRoundKeys, aesHwEncrypt_eq _ _ hl, hrk]; rfl
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl : k.round_keys.val.length = nr .AES_256 + 1 := k.round_keys.property
    simp only [hwRounds] at hr
    refine ⟨⟨by simp [hwRoundKeys, hwRounds, hl, hr, nr], by simp [hwRounds, hr, nr]⟩, fun b => ?_⟩
    rw [hwRoundKeys, aesHwEncrypt_eq _ _ hl, hrk]; rfl

theorem hw_dec_key_schedule {alg : Algorithm} {kw : List (BitVec 32)} {hk : low.x86_64.aes.HwDecKey}
    (h : HwDecKeyIs alg kw hk) (hr : hwDecRounds hk = nr alg - 1) :
    HwSchedule (hwDecRoundKeys hk) (hwDecRounds hk) ∧
      ∀ b, aesHwDecrypt (hwDecRoundKeys hk) b = aesDecrypt alg kw b := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl : k.round_keys.val.length = nr .AES_128 + 1 := k.round_keys.property
    simp only [hwDecRounds] at hr
    refine ⟨⟨by simp [hwDecRoundKeys, hwDecRounds, hl, hr, nr], by simp [hwDecRounds, hr, nr]⟩, fun b => ?_⟩
    rw [hwDecRoundKeys, aesHwDecrypt_eq _ _ hl, hrk]; rfl
  | Aes192 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl : k.round_keys.val.length = nr .AES_192 + 1 := k.round_keys.property
    simp only [hwDecRounds] at hr
    refine ⟨⟨by simp [hwDecRoundKeys, hwDecRounds, hl, hr, nr], by simp [hwDecRounds, hr, nr]⟩, fun b => ?_⟩
    rw [hwDecRoundKeys, aesHwDecrypt_eq _ _ hl, hrk]; rfl
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    have hl : k.round_keys.val.length = nr .AES_256 + 1 := k.round_keys.property
    simp only [hwDecRounds] at hr
    refine ⟨⟨by simp [hwDecRoundKeys, hwDecRounds, hl, hr, nr], by simp [hwDecRounds, hr, nr]⟩, fun b => ?_⟩
    rw [hwDecRoundKeys, aesHwDecrypt_eq _ _ hl, hrk]; rfl

theorem expand_key128_mode_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 16) :
    mid.aes.expand_key key ⦃ k => ∃ k128, k = .Hw (.Aes128 k128) ∧
      k128.round_keys.val = keyToRoundKeys .AES_128 (seqNat8ToSeqNat32LE (bvs key.val)) ∧
      k128.rounds = 9#u32 ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  unfold mid.aes.expand_key low.x86_64.aes.AesKey.new low.x86_64.aes.AesKey128.new
  step*
  have hl : copy_key1.len.val = 16 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 16#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, hss, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, low.x86_64.aes.zero,
    core.core_arch.x86.sse2._mm_setzero_si128]
  apply WP.spec_bind (aes128_expand_spec _ _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_, rfl⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

theorem expand_key256_mode_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 32) :
    mid.aes.expand_key key ⦃ k => ∃ k256, k = .Hw (.Aes256 k256) ∧
      k256.round_keys.val = keyToRoundKeys .AES_256 (seqNat8ToSeqNat32LE (bvs key.val)) ∧
      k256.rounds = 13#u32 ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  unfold mid.aes.expand_key low.x86_64.aes.AesKey.new low.x86_64.aes.AesKey256.new
  step*
  have hl : copy_key1.len.val = 32 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 32#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, hss, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, low.x86_64.aes.zero,
    core.core_arch.x86.sse2._mm_setzero_si128]
  apply WP.spec_bind (aes256_expand_spec _ _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_, rfl⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

theorem expand_key192_mode_spec (h : RunsAesHw) (key : Slice U8) (hk : key.length = 24) :
    mid.aes.expand_key key ⦃ k => ∃ k192, k = .Hw (.Aes192 k192) ∧
      k192.round_keys.val = keyToRoundKeys .AES_192 (seqNat8ToSeqNat32LE (bvs key.val)) ∧
      k192.rounds = 11#u32 ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  unfold mid.aes.expand_key low.x86_64.aes.AesKey.new low.x86_64.aes.AesKey192.new
  step*
  have hl : copy_key1.len.val = 24 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 24#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, hss, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, low.x86_64.aes.zero,
    core.core_arch.x86.sse2._mm_setzero_si128]
  apply WP.spec_bind (aes192_expand_spec _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_, rfl⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

/-- `expand_key` of a key of `alg`'s length holds its round keys and round
count for aws-lc's AES-NI routines. -/
theorem expand_key_mode_spec (h : RunsAesHw) (alg : Algorithm) (key : Slice U8)
    (hk : key.length = 4 * nk alg) :
    mid.aes.expand_key key ⦃ k => ModeKeyIs alg (bvs key.val) k ⦄ := by
  have hl : (bvs key.val).length = 4 * nk alg := by simpa using hk
  cases alg
  · exact WP.spec_mono (expand_key128_mode_spec h key (by simpa [nk] using hk))
      fun k ⟨k128, hk1, hk2, hk3⟩ => ⟨hl, _, hk1, ⟨rfl, hk2⟩, by simp [hwRounds, hk3, nr]⟩
  · exact WP.spec_mono (expand_key192_mode_spec h key (by simpa [nk] using hk))
      fun k ⟨k192, hk1, hk2, hk3⟩ => ⟨hl, _, hk1, ⟨rfl, hk2⟩, by simp [hwRounds, hk3, nr]⟩
  · exact WP.spec_mono (expand_key256_mode_spec h key (by simpa [nk] using hk))
      fun k ⟨k256, hk1, hk2, hk3⟩ => ⟨hl, _, hk1, ⟨rfl, hk2⟩, by simp [hwRounds, hk3, nr]⟩

/-- `AesDecKey::new` of a key of `alg`'s length holds `KeyExpansionEIC`'s round
keys and the round count for aws-lc's AES-NI routines. -/
theorem dec_key_new_mode_spec (h : RunsAesHw) (alg : Algorithm) (key : Slice U8)
    (hk : key.length = 4 * nk alg) :
    low.x86_64.aes.AesDecKey.new key ⦃ k => ModeDecKeyIs alg (bvs key.val) k ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  have hl : key.len.val = 4 * nk alg := by simpa using hk
  have hb : (bvs key.val).length = 4 * nk alg := by simpa using hk
  unfold low.x86_64.aes.AesDecKey.new
  cases alg
  · have hl' : key.len = 16#usize := by simp [nk] at hl; scalar_tac
    have hv : key.len.val = 16 := by simp [nk] at hl; exact hl
    simp only [hhw, hss, bind_ok, hl', show ((16#usize : Usize) : Nat) = 16 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte,
      core.result.Result.unwrap, low.x86_64.aes.AesKey128.new, low.x86_64.aes.AesKey128.inverse,
      low.x86_64.aes.zero, core.core_arch.x86.sse2._mm_setzero_si128]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_128 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨hb, _, rfl, ⟨rfl, ?_⟩, rfl⟩
    rw [hout, x_post, Std.Array.from_val]
  · have hl' : key.len = 24#usize := by simp [nk] at hl; scalar_tac
    have hv : key.len.val = 24 := by simp [nk] at hl; exact hl
    simp only [hhw, hss, bind_ok, hl', show ((24#usize : Usize) : Nat) = 24 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte,
      core.result.Result.unwrap, low.x86_64.aes.AesKey192.new, low.x86_64.aes.AesKey192.inverse,
      low.x86_64.aes.zero, core.core_arch.x86.sse2._mm_setzero_si128]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_192 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨hb, _, rfl, ⟨rfl, ?_⟩, rfl⟩
    rw [hout, x_post, Std.Array.from_val]
  · have hl' : key.len = 32#usize := by simp [nk] at hl; scalar_tac
    have hv : key.len.val = 32 := by simp [nk] at hl; exact hl
    simp only [hhw, hss, bind_ok, hl', show ((32#usize : Usize) : Nat) = 32 from rfl,
      core.array.TryFromSharedArraySlice.try_from, ↓reduceDIte,
      core.result.Result.unwrap, low.x86_64.aes.AesKey256.new, low.x86_64.aes.AesKey256.inverse,
      low.x86_64.aes.zero, core.core_arch.x86.sse2._mm_setzero_si128]
    step*
    apply WP.spec_bind (invert_round_keys_spec .AES_256 rfl _)
    intro out hout
    rw [WP.spec_ok]
    refine ⟨hb, _, rfl, ⟨rfl, ?_⟩, rfl⟩
    rw [hout, x_post, Std.Array.from_val]

/-! ## Whole blocks -/

theorem bvs_toBEBytes32 (x : U32) : bvs (x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)) = be32 x.val := by
  rw [be32_eq]
  simp only [bvs, List.map_map]
  simp [BitVec.toBEBytes, BitVec.toLEBytes]
  and_intros <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] <;> omega

/-! ## CTR -/

theorem usize_max_lt : Usize.max < 2 ^ 64 := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

theorem getElem!_bvs (l : List U8) {j : Nat} (hj : j < l.length) : (bvs l)[j]! = (l[j]!).bv := by
  simp [bvs, hj]

/-- A block whose bytes, read little-endian, are another's XORed with `K`
holds that block's bytes XORed with `K`'s. -/
theorem getElem_of_load_xor {o i : Std.Array U8 16#usize} {K : Quad32}
    (h : loadBytes o.val = loadBytes i.val ^^^ K) {k : Nat} (hk : k < 16) :
    (o.val[k]!).bv = (i.val[k]!).bv ^^^ (leQuad32ToBytes K)[k]! := by
  have ho : o.val.length = 16 := o.property
  have hi : i.val.length = 16 := i.property
  have := congrArg (byte · k) h
  simp only [byte_xor, loadBytes, byte_leBytesToQuad32 _ hk] at this
  rw [leQuad32ToBytes_getElem! _ hk, ← getElem!_bvs _ (by omega), ← getElem!_bvs _ (by omega)]
  exact this

theorem load_nonce_counter (nonce : Std.Array U8 12#usize) (a : List U8) (c : U32)
    (ha : a = c.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)) :
    loadBytes (nonce.val ++ a) = leBytesToQuad32 (bvs nonce.val ++ be32 c.val) := by
  rw [loadBytes, List.map_append, ha]
  show leBytesToQuad32 (bvs nonce.val ++ bvs (List.map UScalar.mk c.bv.toBEBytes)) = _
  rw [bvs_toBEBytes32]

theorem ivec_eq (nonce : Std.Array U8 12#usize) (x : List U8) (hx : x.length = 4) :
    ((Std.Array.repeat 16#usize 0#u8).val.setSlice! 0 nonce.val).setSlice! 12 x = nonce.val ++ x := by
  have hn : nonce.val.length = 12 := nonce.property
  simp [List.setSlice!, Std.Array.repeat_val, hn, hx, List.take_of_length_le]

theorem ivec_eq2 (n x y : List U8) (hn : n.length = 12) (hx : x.length = 4) (hy : y.length = 4) :
    (n ++ y).setSlice! 12 x = n ++ x := by
  simp [List.setSlice!, hn, hx, hy]

theorem buf_eq (t : List U8) (ht : t.length ≤ 16) {m : Nat} (hm : m < t.length) :
    ((Std.Array.repeat 16#usize 0#u8).val.setSlice! 0 t)[m]! = t[m]! := by
  rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by simp [Std.Array.repeat_val]; omega⟩]
  simp

theorem toBEBytes_length (c : U32) : (c.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)).length = 4 := by
  simp [BitVec.toBEBytes, BitVec.toLEBytes]

/-- `ctr::blocks` on the AES-NI key XORs byte `j` with byte `j % 16` of the
cipher of counter block `j / 16`: the nonce, then the count from `counter`,
big-endian, modulo `2^32`. -/
theorem ctr_blocks_spec (hk : low.x86_64.aes.HwKey) (hs : HwSchedule (hwRoundKeys hk) (hwRounds hk))
    (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8) :
    low.generic.ctr.blocks low.x86_64.aes.HwKey.Insts.RindLowGenericCtrCtr32 hk nonce counter inout ⦃ r =>
      r.length = inout.length ∧ ∀ j < inout.length, (r.val[j]!).bv = (inout.val[j]!).bv ^^^
        (leQuad32ToBytes (aesHwEncrypt (hwRoundKeys hk)
          (leBytesToQuad32 (bvs nonce.val ++ be32 ((counter.val + j / 16) % 2 ^ 32)))))[j % 16]! ⦄ := by
  have hin : inout.length ≤ Usize.max := Slice.length_ineq inout
  have hU := usize_max_lt
  have hnl : nonce.val.length = 12 := nonce.property
  have hcl : counter.val < 2 ^ 32 := counter.hBounds
  have hil : inout.val.length = inout.length := rfl
  unfold low.generic.ctr.blocks
  simp only [low.x86_64.aes.HwKey.Insts.RindLowGenericCtrCtr32.ctr32]
  step*
  case hn => simp [s11_post]
  all_goals try (
    have htl : tail.val.length < 16 := by rw [blocks_post2, List.length_drop]; omega
    first
      | (show tail.len ≤ 16#usize; scalar_tac)
      | (have : (from_mut_back s12).to_slice.length = 16 := by simp
         show tail.len.val ≤ _; rw [this]; scalar_tac))
  all_goals
    have hivl : (index_mut_back1 s5).val = nonce.val ++ a.val := by
      rw [s3_post2, s5_post, s4_post, s2_post, s1_post, s_post2, Std.Array.val_to_slice,
        Std.Array.val_to_slice, ivec_eq nonce a.val (by rw [a_post]; exact toBEBytes_length counter)]
    have hiv : loadBytes (index_mut_back1 s5).val = leBytesToQuad32 (bvs nonce.val ++ be32 counter.val) := by
      rw [hivl, load_nonce_counter nonce a.val counter a_post]
    have hnb : blocks.val.length = inout.length / 16 := blocks_post
    have hnb1 : blocks1.val.length = inout.length / 16 := by rw [← hnb]; exact blocks1_post
    have hblk : ∀ j < 16 * (inout.length / 16), ((blocks1.val.flatMap (fun b : Std.Array U8 16#usize => b.val))[j]!).bv = (inout.val[j]!).bv ^^^
        (leQuad32ToBytes (aesHwEncrypt (hwRoundKeys hk)
          (leBytesToQuad32 (bvs nonce.val ++ be32 ((counter.val + j / 16) % 2 ^ 32)))))[j % 16]! := by
      intro j hj
      rw [getElem!_flatMap16 _ (by rw [hnb1]; exact hj)]
      have hi : j / 16 < blocks.length := by simp only [Slice.length]; rw [hnb]; omega
      have hx := blocks1_post1 (j / 16) hi
      rw [hiv, aesCtr32Block_bytes _ (by simp [hnl]) _ _ hcl] at hx
      rw [getElem_of_load_xor hx (Nat.mod_lt _ (by norm_num)),
        getElem!_pos blocks.val (j / 16) (by rw [hnb]; omega), blocks_post1 (j / 16) (by rw [hnb]; omega)]
      congr 2
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
        show j % 16 < 16 from Nat.mod_lt _ (by norm_num), ite_true, show j / 16 * 16 + j % 16 = j by omega]
  case h1 =>
    have htl0 : tail.val.length = 0 := by
      have : tail.length = 0 := by rwa [← b_post]
      exact this
    have hres : (as_chunks_mut_back (blocks1, tail)).val = blocks1.val.flatMap (fun b : Std.Array U8 16#usize => b.val) ++ tail.val :=
      blocks_post3 _ _ (by rw [List.length_append, length_flatMap16, hnb1, htl0]; omega)
    have hlen : inout.length = 16 * (inout.length / 16) := by
      rw [blocks_post2, List.length_drop] at htl0; omega
    refine ⟨?_, fun j hj => ?_⟩
    · show (as_chunks_mut_back (blocks1, tail)).val.length = _
      rw [hres, List.length_append, length_flatMap16, hnb1, htl0]; omega
    · rw [hres, getElem!_append_left' _ _ (by rw [length_flatMap16, hnb1]; omega)]
      exact hblk j (by omega)
  · have htl : tail.val.length = inout.length - inout.length / 16 * 16 := by
      rw [blocks_post2, List.length_drop]
    have ht1 : tail1.val.length = tail.val.length := by
      rw [tail1_post]; exact s13_post1
    have hres : (as_chunks_mut_back (blocks1, tail1)).val =
        blocks1.val.flatMap (fun b : Std.Array U8 16#usize => b.val) ++ tail1.val :=
      blocks_post3 _ _ (by rw [List.length_append, length_flatMap16, hnb1, ht1, htl]; omega)
    have hs11 : s11.val.length = 1 := by rw [s11_post]; rfl
    have hs12 : s12.val.length = 1 := by rw [← hs11]; exact s12_post
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hs12
    have hfm : from_mut_back s12 = x := by rw [s11_post1, hx]; rfl
    have hx0 := s12_post1 0 (by simp only [Slice.length]; omega)
    rw [hx, s11_post] at hx0
    simp only [List.getElem!_cons_zero, s10_post] at hx0
    have hbuf : (index_mut_back3 tail).val = (Std.Array.repeat 16#usize 0#u8).val.setSlice! 0 tail.val :=
      s9_post2 tail
    have hc1 : counter1.val = (counter.val + inout.length / 16) % 2 ^ 32 := by
      rw [counter1_post, core.num.U32.wrapping_add_val_eq, i1_post, UScalar.cast_val_eq, Slice.len_val,
        show blocks1.length = inout.length / 16 from hnb1]
      simp only [UScalar.size, UScalarTy.numBits]
      omega
    have hiv3 : loadBytes (index_mut_back2 s8).val =
        leBytesToQuad32 (bvs nonce.val ++ be32 counter1.val) := by
      rw [s6_post2, s8_post, s7_post, Std.Array.val_to_slice, hivl,
        ivec_eq2 _ _ _ hnl (by rw [a1_post]; exact toBEBytes_length counter1)
          (by rw [a_post]; exact toBEBytes_length counter),
        load_nonce_counter nonce a1.val counter1 a1_post]
    rw [hiv3, aesCtr32Block_bytes _ (by simp [hnl]) _ _ counter1.hBounds] at hx0
    refine ⟨?_, fun j hj => ?_⟩
    · show (as_chunks_mut_back (blocks1, tail1)).val.length = _
      rw [hres, List.length_append, length_flatMap16, hnb1, ht1, htl]; omega
    · rw [hres]
      by_cases hjb : j < 16 * (inout.length / 16)
      · rw [getElem!_append_left' _ _ (by rw [length_flatMap16, hnb1]; omega)]
        exact hblk j hjb
      · have hm : j - 16 * (inout.length / 16) < tail.val.length := by omega
        have hjm : j % 16 = j - 16 * (inout.length / 16) := by omega
        have hjd : j / 16 = inout.length / 16 := by omega
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by rw [length_flatMap16, hnb1]; omega),
          ← List.getElem!_eq_getElem?_getD, length_flatMap16, hnb1, tail1_post, s13_post, hfm,
          List.getElem!_slice _ _ _ _ ⟨by simp; omega, by simp only [Slice.len_val, Slice.length]; omega⟩, Nat.zero_add, Std.Array.val_to_slice,
          getElem_of_load_xor hx0 (by omega), hbuf, buf_eq _ (by omega) hm, blocks_post2, hjm, hjd,
          show (counter1.val + 0) % 2 ^ 32 = (counter.val + inout.length / 16) % 2 ^ 32 by
            rw [hc1]; omega]
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_drop,
          show inout.length / 16 * 16 + (j - 16 * (inout.length / 16)) = j by omega]

/-- `aes_ctr::apply` is SP 800-38A's CTR mode under the key, from the counter
block of the nonce and the big-endian `counter`, counting in its last 32 bits. -/
theorem aes_ctr_apply_spec (alg : Algorithm) (key : List (BitVec 8)) (k : low.x86_64.aes.AesKey)
    (hk : ModeKeyIs alg key k) (nonce : Std.Array U8 12#usize) (counter : U32) (inout : Slice U8) :
    low.x86_64.aes_ctr.apply k nonce counter inout ⦃ r =>
      bvs r.val = aesCtr alg key 32 (bvs nonce.val ++ be32 counter.val) (bvs inout.val) ⦄ := by
  obtain ⟨-, hw, rfl, hwk, hr⟩ := hk
  obtain ⟨hs, he⟩ := hw_key_schedule hwk hr
  have hnl : (bvs nonce.val).length = 12 := by simp
  simp only [low.x86_64.aes_ctr.apply]
  apply WP.spec_mono (ctr_blocks_spec hw hs nonce counter inout)
  rintro r ⟨hl, hj⟩
  have hrl : r.val.length = inout.val.length := hl
  apply List.ext_getElem (by simp [aesCtr, bvs, hrl])
  intro j h1 h2
  have hj' : j < inout.length := by simpa [bvs, hrl] using h1
  simp only [aesCtr, List.getElem_map, List.getElem_range]
  rw [be128_ctrBlock _ hnl, aesBlock, ← he, getElem!_bvs _ hj', ← hj j hj',
    getElem!_pos r.val j (by rw [hrl]; exact hj')]

/-- `aes_cbc::encrypt` is SP 800-38A's CBC encryption of the blocks under the
key, from `iv`. -/
theorem aes_cbc_encrypt_spec (alg : Algorithm) (key : List (BitVec 8)) (k : low.x86_64.aes.AesKey)
    (hk : ModeKeyIs alg key k) (iv : Std.Array U8 16#usize) (blocks : Slice (Std.Array U8 16#usize))
    (hn : 16 * blocks.length ≤ Usize.max) :
    low.x86_64.aes_cbc.encrypt k iv blocks ⦃ r =>
      r.val.flatMap (fun b => bvs b.val) =
        cbcEncrypt alg key (bvs iv.val) (blocks.val.flatMap fun b => bvs b.val) ⦄ := by
  obtain ⟨-, hw, rfl, hwk, hr⟩ := hk
  obtain ⟨hs, he⟩ := hw_key_schedule hwk hr
  simp only [low.x86_64.aes_cbc.encrypt]
  apply WP.spec_mono (hw_cbc_encrypt_spec hw iv blocks hs (by have := usize_max_lt; omega))
  rintro r ⟨hl, h⟩
  have e : ∀ l : List (Std.Array U8 16#usize), l.flatMap (fun b => bvs b.val) = bvs (l.flatMap (·.val)) :=
    fun l => by simp [bvs, List.map_flatMap]
  rw [e, e, bvs_eq_of_load rfl]
  exact cbc_encrypt_chain alg key _ he blocks.val r.val (loadBytes iv.val) hl h

/-- `aes_cbc::decrypt` is SP 800-38A's CBC decryption of the blocks under the
key, from `iv`. -/
theorem aes_cbc_decrypt_spec (alg : Algorithm) (key : List (BitVec 8)) (k : low.x86_64.aes.AesDecKey)
    (hk : ModeDecKeyIs alg key k) (iv : Std.Array U8 16#usize) (blocks : Slice (Std.Array U8 16#usize))
    (hn : 16 * blocks.length ≤ Usize.max) :
    low.x86_64.aes_cbc.decrypt k iv blocks ⦃ r =>
      r.val.flatMap (fun b => bvs b.val) =
        cbcDecrypt alg key (bvs iv.val) (blocks.val.flatMap fun b => bvs b.val) ⦄ := by
  obtain ⟨-, hw, rfl, hwk, hr⟩ := hk
  obtain ⟨hs, hd⟩ := hw_dec_key_schedule hwk hr
  simp only [low.x86_64.aes_cbc.decrypt]
  apply WP.spec_mono (hw_cbc_decrypt_spec hw iv blocks hs (by have := usize_max_lt; omega))
  rintro r ⟨hl, h⟩
  have e : ∀ l : List (Std.Array U8 16#usize), l.flatMap (fun b => bvs b.val) = bvs (l.flatMap (·.val)) :=
    fun l => by simp [bvs, List.map_flatMap]
  rw [e, e, bvs_eq_of_load rfl]
  exact cbc_decrypt_chain alg key _ hd blocks.val r.val (loadBytes iv.val) hl h

end rind.x86_64
