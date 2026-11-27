-- Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
--
-- A transliteration of s2n-bignum's GCM-AE, GCM-AD, and AES key-schedule
-- specs; see LICENSE.

import Rind.S2nGcm

/-!
# s2n-bignum's GCM-AE and GCM-AD, and Vale's

s2n-bignum's SP 800-38D in `common/gcm.ml`, `inc32`, `gctr`, `gcm_ae`, and
`gcm_ad`, and its FIPS 197 key schedules in `common/fips197.ml` over
`common/aes.ml`'s `aes_subword`, at rind's pin (`3f01260f`), transliterated
as `Rind/S2nGcm.lean` transliterates the ciphers and GHASH they run, with
`word_add` as `+`, `word_rol` as `rotateLeft`, and `word n` as
`BitVec.ofNat`. They are Vale's, each block's bytes reversed:

- `aes128KeyExpansion_eq` and `aes256KeyExpansion_eq`: the key schedules are
  Vale's `key_to_round_keys_LE`, so `aes128_cipher` and `aes256_cipher` under
  them are Vale's `aes_encrypt_LE` (`isValeAes_aes128`, `isValeAes_aes256`);
- `nistGhash_zero`: GHASH from zero is Vale's `ghash_LE`;
- `gctr_eq`: GCTR from any counter block is Vale's `gctr_encrypt_LE`'s blocks
  from it;
- `gcmAe_eq` and `gcmAd_eq`: with a 96-bit IV and whole-block AAD and
  message, all `gcm_ae` and `gcm_ad` take, `gcm_ae` is `gcm_encrypt_LE`, and
  `gcm_ad` refuses the tags `gcm_decrypt_LE` refuses and otherwise returns its
  plaintext, for any cipher that is Vale's AES under the key; and
  `gcmAe_aes128`, `gcmAd_aes128`, `gcmAe_aes256`, and `gcmAd_aes256` for
  FIPS 197's AES-128 and AES-256 under s2n-bignum's own key schedules.
-/

namespace rind.s2n.gcm

open rind.vale (Quad32 byte reverseBytesQuad32 toPoly)

/-! ## AES's key schedule, `common/aes.ml` and `common/fips197.ml` -/

/-- `aes_subword`: the S-box on each byte. -/
def aesSubword (op : BitVec 32) : BitVec 32 :=
  aesSubByte joinedGf2 (op.extractLsb' 24 8) ++ (aesSubByte joinedGf2 (op.extractLsb' 16 8) ++
    (aesSubByte joinedGf2 (op.extractLsb' 8 8) ++ aesSubByte joinedGf2 (op.extractLsb' 0 8)))

/-- Four words, as the key schedule's steps pass them. -/
abbrev Words4 := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- `aes_kexp_core`: `back` XOR `SubWord(RotWord(prev))` XOR `rcon`. -/
def aesKexpCore (rcon prev back : BitVec 32) : BitVec 32 :=
  back ^^^ (aesSubword (prev.rotateLeft 8) ^^^ rcon)

/-- `aes_kexp_sub`: `back` XOR `SubWord(prev)`. -/
def aesKexpSub (prev back : BitVec 32) : BitVec 32 := back ^^^ aesSubword prev

/-- `aes_rcon`: FIPS 197's round constants. -/
def aesRcon : List (BitVec 32) :=
  [0x01000000, 0x02000000, 0x04000000, 0x08000000, 0x10000000,
   0x20000000, 0x40000000, 0x80000000, 0x1b000000, 0x36000000]

/-- `aes128_kexp_round`. -/
def aes128KexpRound (i : Nat) : Words4 → Words4
  | (w0, w1, w2, w3) =>
    let w4 := aesKexpCore aesRcon[i]! w3 w0
    let w5 := w1 ^^^ w4
    let w6 := w2 ^^^ w5
    let w7 := w3 ^^^ w6
    (w4, w5, w6, w7)

/-- `aes256_kexp_round`. -/
def aes256KexpRound (i : Nat) : Words4 × Words4 → Words4 × Words4
  | ((w0, w1, w2, w3), (w4, w5, w6, w7)) =>
    let w8 := aesKexpCore aesRcon[i]! w7 w0
    let w9 := w1 ^^^ w8
    let w10 := w2 ^^^ w9
    let w11 := w3 ^^^ w10
    let w12 := aesKexpSub w11 w4
    let w13 := w5 ^^^ w12
    let w14 := w6 ^^^ w13
    let w15 := w7 ^^^ w14
    ((w8, w9, w10, w11), (w12, w13, w14, w15))

/-- `aes256_kexp_last`. -/
def aes256KexpLast (i : Nat) : Words4 × Words4 → Words4
  | ((w0, w1, w2, w3), (_, _, _, w7)) =>
    let w8 := aesKexpCore aesRcon[i]! w7 w0
    let w9 := w1 ^^^ w8
    let w10 := w2 ^^^ w9
    let w11 := w3 ^^^ w10
    (w8, w9, w10, w11)

/-- `word_join4_32_128`: four words, the first most significant. -/
def wordJoin4 : Words4 → BitVec 128
  | (w0, w1, w2, w3) => w0 ++ (w1 ++ (w2 ++ w3))

/-- `word_split128_4x32`: a block's four words, the most significant first. -/
def wordSplit4 (k : BitVec 128) : Words4 :=
  (k.extractLsb' 96 32, k.extractLsb' 64 32, k.extractLsb' 32 32, k.extractLsb' 0 32)

/-- `aes128_key_expansion`: the 11 round keys. -/
def aes128KeyExpansion (key : BitVec 128) : List (BitVec 128) :=
  let k0 := wordSplit4 key
  let k1 := aes128KexpRound 0 k0
  let k2 := aes128KexpRound 1 k1
  let k3 := aes128KexpRound 2 k2
  let k4 := aes128KexpRound 3 k3
  let k5 := aes128KexpRound 4 k4
  let k6 := aes128KexpRound 5 k5
  let k7 := aes128KexpRound 6 k6
  let k8 := aes128KexpRound 7 k7
  let k9 := aes128KexpRound 8 k8
  let k10 := aes128KexpRound 9 k9
  [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10].map wordJoin4

/-- `aes256_key_expansion`: the 15 round keys of the key whose first 128 bits
are `keyHi`. -/
def aes256KeyExpansion (keyHi keyLo : BitVec 128) : List (BitVec 128) :=
  let h0 := wordSplit4 keyHi
  let l0 := wordSplit4 keyLo
  let r1 := aes256KexpRound 0 (h0, l0)
  let r2 := aes256KexpRound 1 r1
  let r3 := aes256KexpRound 2 r2
  let r4 := aes256KexpRound 3 r3
  let r5 := aes256KexpRound 4 r4
  let r6 := aes256KexpRound 5 r5
  let r7 := aes256KexpLast 6 r6
  [keyHi, keyLo, wordJoin4 r1.1, wordJoin4 r1.2, wordJoin4 r2.1, wordJoin4 r2.2,
   wordJoin4 r3.1, wordJoin4 r3.2, wordJoin4 r4.1, wordJoin4 r4.2,
   wordJoin4 r5.1, wordJoin4 r5.2, wordJoin4 r6.1, wordJoin4 r6.2, wordJoin4 r7]

/-! ## GCM, `common/gcm.ml` -/

/-- `inc32`: the low 32 bits plus one, wrapping. -/
def inc32 (cb : BitVec 128) : BitVec 128 :=
  let top96 : BitVec 96 := cb.extractLsb' 32 96
  let bot32 : BitVec 32 := cb.extractLsb' 0 32
  top96 ++ (bot32 + 1)

/-- A block cipher as s2n-bignum's specs take it: a block and the round keys. -/
abbrev Cipher := BitVec 128 → List (BitVec 128) → BitVec 128

/-- `gctr`: SP 800-38D's GCTR on whole blocks. -/
def gctr (enc : Cipher) (ks : List (BitVec 128)) : BitVec 128 → List (BitVec 128) → List (BitVec 128)
  | _, [] => []
  | icb, x :: rest => (x ^^^ enc icb ks) :: gctr enc ks (inc32 icb) rest

/-- `gcm_ae`: SP 800-38D's GCM-AE for a 96-bit IV and whole blocks. -/
def gcmAe (enc : Cipher) (ks : List (BitVec 128)) (iv : BitVec 96) (P A : List (BitVec 128)) :
    List (BitVec 128) × BitVec 128 :=
  let H := enc 0 ks
  let J0 : BitVec 128 := iv ++ (1 : BitVec 32)
  let C := gctr enc ks (inc32 J0) P
  let lenBlock : BitVec 128 := BitVec.ofNat 64 (128 * A.length) ++ BitVec.ofNat 64 (128 * C.length)
  let S := nistGhash H 0 (A ++ (C ++ [lenBlock]))
  let tag := S ^^^ enc J0 ks
  (C, tag)

/-- `gcm_ad`: SP 800-38D's GCM-AD for a 96-bit IV and whole blocks. -/
def gcmAd (enc : Cipher) (ks : List (BitVec 128)) (iv : BitVec 96) (C A : List (BitVec 128))
    (tag : BitVec 128) : Option (List (BitVec 128)) :=
  let H := enc 0 ks
  let J0 : BitVec 128 := iv ++ (1 : BitVec 32)
  let P := gctr enc ks (inc32 J0) C
  let lenBlock : BitVec 128 := BitVec.ofNat 64 (128 * A.length) ++ BitVec.ofNat 64 (128 * C.length)
  let S := nistGhash H 0 (A ++ (C ++ [lenBlock]))
  let tag' := S ^^^ enc J0 ks
  if tag' = tag then some P else none

/-! ## Words -/

theorem extractLsb'_append_lo {m n : Nat} (x : BitVec m) (y : BitVec n) {s k : Nat} (h : s + k ≤ n) :
    (x ++ y).extractLsb' s k = y.extractLsb' s k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [BitVec.getLsbD_append, hj, show s + j < n by omega]

theorem extractLsb'_append_hi {m n : Nat} (x : BitVec m) (y : BitVec n) {s k : Nat} (h : n ≤ s) :
    (x ++ y).extractLsb' s k = x.extractLsb' (s - n) k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [BitVec.getLsbD_append, hj, show ¬ s + j < n by omega, show s + j - n = s - n + j by omega]

theorem extractLsb'_self {n s : Nat} (x : BitVec n) (h : s = 0) : x.extractLsb' s n = x := by
  subst h; apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

theorem extractLsb'_extractLsb' {m : Nat} (x : BitVec m) {a n b k : Nat} (h : b + k ≤ n) :
    (x.extractLsb' a n).extractLsb' b k = x.extractLsb' (a + b) k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj, show b + j < n by omega, Nat.add_assoc]

/-! ## GHASH -/

/-- `nist_dot` is Vale's `gf128_mul_LE`, its blocks' bytes reversed. -/
theorem nistDot_eq (a b : BitVec 128) :
    nistDot a b = reverseBytesQuad32 (vale.gf128MulLE (reverseBytesQuad32 a) (reverseBytesQuad32 b)) := by
  apply vale.toPoly_inj
  rw [toPoly_nistDot]
  show _ = vale.polyLE _
  rw [vale.polyLE_mulLE]
  simp only [vale.polyLE, vale.reverseBytesQuad32_involutive]

/-- `nist_ghash` from any accumulator is Vale's Horner rule, its blocks' bytes reversed. -/
theorem nistGhash_eq (h : BitVec 128) : ∀ (acc : BitVec 128) (xs : List (BitVec 128)),
    nistGhash h acc xs = reverseBytesQuad32 ((xs.map reverseBytesQuad32).foldl
      (fun y x => vale.gf128MulLE (y ^^^ x) (reverseBytesQuad32 h)) (reverseBytesQuad32 acc))
  | acc, [] => by simp [nistGhash, vale.reverseBytesQuad32_involutive]
  | acc, x :: xs => by
    rw [nistGhash, nistGhash_eq h _ xs, nistDot_eq, vale.reverseBytesQuad32_involutive, vale.reverseBytes_xor,
      List.map_cons, List.foldl_cons]

/-- `nist_ghash` from zero is Vale's `ghash_LE`, its blocks' bytes reversed. -/
theorem nistGhash_zero (h : BitVec 128) (xs : List (BitVec 128)) :
    nistGhash h 0 xs = reverseBytesQuad32 (vale.ghashLE (reverseBytesQuad32 h) (xs.map reverseBytesQuad32)) := by
  rw [nistGhash_eq, rev_zero]; rfl

/-! ## GCTR -/

/-- A cipher that is Vale's AES under the key words `key`, through the byte
reversal: what s2n-bignum's GCM takes as `enc` and `ks`. -/
def IsValeAes (enc : Cipher) (ks : List (BitVec 128)) (alg : vale.Algorithm) (key : List (BitVec 32)) : Prop :=
  ∀ x, enc x ks = reverseBytesQuad32 (vale.aesEncrypt alg key (reverseBytesQuad32 x))

theorem inc32_eq (cb : BitVec 128) : inc32 cb = vale.inc32 cb 1 := rfl

/-- GCTR from counter block `inc32 icb i` is Vale's blocks from `icb`, from
block `i`, their bytes reversed. -/
theorem gctr_eq {enc : Cipher} {ks : List (BitVec 128)} {alg : vale.Algorithm} {key : List (BitVec 32)}
    (he : IsValeAes enc ks alg key) (icb : Quad32) : ∀ (xs : List (BitVec 128)) (i : Nat),
    gctr enc ks (vale.inc32 icb i) xs =
      (vale.gctrEncryptRecursive icb alg key (xs.map reverseBytesQuad32) i).map reverseBytesQuad32
  | [], _ => rfl
  | x :: xs, i => by
    rw [gctr, inc32_eq, vale.inc32_inc32, gctr_eq he icb xs (i + 1), he]
    simp only [List.map_cons, vale.gctrEncryptRecursive, vale.gctrEncryptBlock, vale.reverseBytes_xor,
      vale.reverseBytesQuad32_involutive]

/-! ## GCM -/

/-- 16 bytes as SP 800-38D reads a block, the first most significant. -/
def beBlock (b : List (BitVec 8)) : BitVec 128 := reverseBytesQuad32 (vale.leBytesToQuad32 b)

/-- Bytes as SP 800-38D's blocks, 16 a block. -/
def beBlocks (b : List (BitVec 8)) : List (BitVec 128) := (vale.leBytesToSeqQuad32 b).map reverseBytesQuad32

/-- A 96-bit IV's 12 bytes as SP 800-38D reads them, the first most significant. -/
def ivWord (iv : List (BitVec 8)) : BitVec 96 := (beBlock (iv ++ List.replicate 4 0)).extractLsb' 32 96

theorem leQuad32ToBytes_leBytesToQuad32 (l : List (BitVec 8)) (hl : l.length = 16) :
    vale.leQuad32ToBytes (vale.leBytesToQuad32 l) = l := by
  apply List.ext_getElem (by simp [vale.leQuad32ToBytes, hl])
  intro i h1 h2
  have hi : i < 16 := by simpa [vale.leQuad32ToBytes] using h1
  have := vale.leQuad32ToBytes_getElem! (vale.leBytesToQuad32 l) hi
  rw [vale.byte_leBytesToQuad32 _ hi] at this
  simpa [List.getElem!_eq_getElem?_getD, h1, h2] using this

theorem beBlock_inj {a b : List (BitVec 8)} (ha : a.length = 16) (hb : b.length = 16) :
    beBlock a = beBlock b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h' := congrArg (fun q => vale.leQuad32ToBytes (reverseBytesQuad32 q)) h
  simp only [beBlock, vale.reverseBytesQuad32_involutive] at h'
  rwa [leQuad32ToBytes_leBytesToQuad32 _ ha, leQuad32ToBytes_leBytesToQuad32 _ hb] at h'

theorem leBytesToSeqQuad32_leSeqQuad32ToBytes : ∀ qs : List Quad32,
    vale.leBytesToSeqQuad32 (vale.leSeqQuad32ToBytes qs) = qs
  | [] => by simp [vale.leBytesToSeqQuad32, vale.leSeqQuad32ToBytes, vale.seqToSeqFourLE, vale.seqNat8ToSeqNat32LE]
  | q :: qs => by
    have hl : (vale.leQuad32ToBytes q).length = 16 := by simp [vale.leQuad32ToBytes]
    have ih := leBytesToSeqQuad32_leSeqQuad32ToBytes qs
    rw [vale.leBytesToSeqQuad32_eq] at ih ⊢
    rw [vale.leSeqQuad32ToBytes, List.flatMap_cons, ← vale.leSeqQuad32ToBytes,
      vale.chunksOf_cons (by omega) (by simp [hl]), List.take_left' hl, List.drop_left' hl, List.map_cons, ih,
      vale.leBytesToQuad32_leQuad32ToBytes]

theorem padTo128Bits_of_mod (b : List (BitVec 8)) (h : b.length % 16 = 0) : vale.padTo128Bits b = b := by
  simp [vale.padTo128Bits, h]

theorem length_beBlocks (b : List (BitVec 8)) : (beBlocks b).length = b.length / 16 := by
  rw [beBlocks, List.length_map, vale.leBytesToSeqQuad32_eq, List.length_map, vale.chunksOf_length]

theorem map_rev_beBlocks (b : List (BitVec 8)) : (beBlocks b).map reverseBytesQuad32 = vale.leBytesToSeqQuad32 b := by
  simp [beBlocks, Function.comp_def, vale.reverseBytesQuad32_involutive]

theorem lengths_block (a c : Nat) :
    vale.insertNat64 (vale.insertNat64 (vale.mkfour 0 0 0 0) a 1) c 0 = BitVec.ofNat 64 a ++ BitVec.ofNat 64 c := by
  simp only [vale.insertNat64, Nat.one_ne_zero, ↓reduceIte]
  rw [extractLsb'_append_hi _ _ (le_refl 64), extractLsb'_self _ rfl]

theorem mkfour_zero : vale.mkfour 0 0 0 0 = 0 := rfl

/-- The hash key: the cipher of the zero block. -/
theorem hashKey_eq {enc : Cipher} {ks : List (BitVec 128)} {alg : vale.Algorithm} {kw : List (BitVec 32)}
    (he : IsValeAes enc ks alg kw) :
    enc 0 ks = reverseBytesQuad32 (vale.aesEncrypt alg kw (vale.mkfour 0 0 0 0)) := by
  rw [he, rev_zero, mkfour_zero]

/-- `J0` for a 96-bit IV is Vale's `compute_iv_BE`'s. -/
theorem j0_eq (hLE : Quad32) (iv : List (BitVec 8)) (hiv : iv.length = 12) :
    ivWord iv ++ (1 : BitVec 32) = vale.computeIvBE hLE iv := by
  rw [vale.computeIvBE_96 _ _ hiv]; rfl

/-- GCTR from `inc32 j0` on whole blocks is Vale's `gctr_encrypt_LE` from `inc32 j0 1`. -/
theorem gctr_bytes {enc : Cipher} {ks : List (BitVec 128)} {alg : vale.Algorithm} {kw : List (BitVec 32)}
    (he : IsValeAes enc ks alg kw) (j0 : Quad32) (m : List (BitVec 8)) (hm : m.length % 16 = 0) :
    gctr enc ks (inc32 j0) (beBlocks m) = beBlocks (vale.gctrEncrypt (vale.inc32 j0 1) m alg kw) := by
  have h0 : inc32 j0 = vale.inc32 (vale.inc32 j0 1) 0 := by rw [vale.inc32_zero, inc32_eq]
  rw [h0, gctr_eq he, map_rev_beBlocks, vale.gctrEncrypt, ite_eq_left hm, beBlocks,
    leBytesToSeqQuad32_leSeqQuad32ToBytes]

/-- The tag: GHASH of the AAD, the ciphertext, and the lengths, XOR the
counter block's keystream, is Vale's, GCTR from `j0` on `gcm_hash`. -/
theorem tag_eq {enc : Cipher} {ks : List (BitVec 128)} {alg : vale.Algorithm} {kw : List (BitVec 32)}
    (he : IsValeAes enc ks alg kw) (j0 : Quad32) (auth c : List (BitVec 8)) (ha : auth.length % 16 = 0)
    (hc : c.length % 16 = 0) :
    let hLE := vale.aesEncrypt alg kw (vale.mkfour 0 0 0 0)
    nistGhash (enc 0 ks) 0 (beBlocks auth ++ (beBlocks c ++
        [BitVec.ofNat 64 (128 * (beBlocks auth).length) ++ BitVec.ofNat 64 (128 * (beBlocks c).length)])) ^^^
      enc j0 ks = beBlock (vale.gctrEncrypt j0 (vale.leQuad32ToBytes (vale.gcmHash hLE auth c)) alg kw) := by
  intro hLE
  rw [hashKey_eq he, nistGhash_zero, vale.reverseBytesQuad32_involutive, he, ← vale.reverseBytes_xor,
    vale.gctr_block, beBlock, vale.leBytesToQuad32_leQuad32ToBytes, length_beBlocks, length_beBlocks,
    show 128 * (auth.length / 16) = 8 * auth.length by omega, show 128 * (c.length / 16) = 8 * c.length by omega,
    vale.gcmHash, padTo128Bits_of_mod _ ha, padTo128Bits_of_mod _ hc, lengths_block]
  simp only [List.map_append, map_rev_beBlocks, List.map_cons, List.map_nil]
  rfl

/-- `gcm_ae` with a 96-bit IV and whole-block AAD and message is Vale's
`gcm_encrypt_LE`, for any cipher that is Vale's AES under the key. -/
theorem gcmAe_eq {enc : Cipher} {ks : List (BitVec 128)} {alg : vale.Algorithm} {key : List (BitVec 8)}
    (he : IsValeAes enc ks alg (vale.seqNat8ToSeqNat32LE key)) (iv plain auth : List (BitVec 8))
    (hiv : iv.length = 12) (hp : plain.length % 16 = 0) (ha : auth.length % 16 = 0) :
    gcmAe enc ks (ivWord iv) (beBlocks plain) (beBlocks auth) =
      (beBlocks (vale.gcmEncrypt alg key iv plain auth).1, beBlock (vale.gcmEncrypt alg key iv plain auth).2) := by
  have hc := vale.length_gctrEncrypt
    (vale.inc32 (vale.computeIvBE (vale.aesEncrypt alg (vale.seqNat8ToSeqNat32LE key) (vale.mkfour 0 0 0 0)) iv) 1)
    plain alg (vale.seqNat8ToSeqNat32LE key)
  simp only [gcmAe, vale.gcmEncrypt]
  rw [j0_eq _ _ hiv, hashKey_eq he] at *
  rw [gctr_bytes he _ _ hp, ← hashKey_eq he, tag_eq he _ _ _ ha (by rw [hc]; exact hp)]

/-- `gcm_ad` with a 96-bit IV and whole-block AAD and ciphertext is Vale's
`gcm_decrypt_LE`: the plaintext when Vale accepts the tag, and nothing when it
refuses it, for any cipher that is Vale's AES under the key. -/
theorem gcmAd_eq {enc : Cipher} {ks : List (BitVec 128)} {alg : vale.Algorithm} {key : List (BitVec 8)}
    (he : IsValeAes enc ks alg (vale.seqNat8ToSeqNat32LE key)) (iv cipher auth tag : List (BitVec 8))
    (hiv : iv.length = 12) (hc : cipher.length % 16 = 0) (ha : auth.length % 16 = 0) (ht : tag.length = 16) :
    gcmAd enc ks (ivWord iv) (beBlocks cipher) (beBlocks auth) (beBlock tag) =
      if (vale.gcmDecrypt alg key iv cipher auth tag).2 then
        some (beBlocks (vale.gcmDecrypt alg key iv cipher auth tag).1)
      else none := by
  simp only [gcmAd, vale.gcmDecrypt]
  rw [j0_eq (vale.aesEncrypt alg (vale.seqNat8ToSeqNat32LE key) (vale.mkfour 0 0 0 0)) _ hiv,
    gctr_bytes he _ _ hc, tag_eq he _ _ _ ha hc]
  have hl : ∀ j0 z, (vale.gctrEncrypt j0 (vale.leQuad32ToBytes z) alg (vale.seqNat8ToSeqNat32LE key)).length = 16 :=
    fun _ _ => by rw [vale.length_gctrEncrypt]; simp [vale.leQuad32ToBytes]
  simp only [beBlock_inj (hl _ _) ht, beq_iff_eq]

/-! ## The key schedules -/

/-- A word's bytes in the other order: Vale's words hold the key's first byte
least significant, s2n-bignum's most. -/
def bswap (w : BitVec 32) : BitVec 32 :=
  w.extractLsb' 0 8 ++ (w.extractLsb' 8 8 ++ (w.extractLsb' 16 8 ++ w.extractLsb' 24 8))

theorem wbyte_bswap (w : BitVec 32) {b : Nat} (hb : b < 4) : vale.wbyte (bswap w) b = vale.wbyte w (3 - b) := by
  unfold bswap vale.wbyte
  interval_cases b <;> simp (disch := omega) only [extractLsb'_append_lo, extractLsb'_append_hi, extractLsb'_self]

theorem bswap_xor (a b : BitVec 32) : bswap (a ^^^ b) = bswap a ^^^ bswap b := by
  apply vale.eq_of_wbyte_eq; intro i hi
  rw [vale.wbyte_xor, wbyte_bswap _ hi, wbyte_bswap _ hi, wbyte_bswap _ hi, vale.wbyte_xor]

theorem wbyte_rotateLeft (w : BitVec 32) {b : Nat} (hb : b < 4) :
    vale.wbyte (w.rotateLeft 8) b = vale.wbyte w ((b + 3) % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vale.wbyte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_rotateLeft]
  interval_cases b <;> interval_cases j <;> simp

/-- `aes_subword` is Vale's `sub_word`. -/
theorem aesSubword_eq (w : BitVec 32) : aesSubword w = vale.subWord w := by
  apply vale.eq_of_wbyte_eq; intro b hb
  rw [vale.wbyte_subWord _ hb]
  unfold aesSubword vale.wbyte
  simp only [aesSubByte_eq]
  interval_cases b <;> simp (disch := omega) only [extractLsb'_append_lo, extractLsb'_append_hi, extractLsb'_self]

theorem subWord_bswap (w : BitVec 32) : vale.subWord (bswap w) = bswap (vale.subWord w) := by
  apply vale.eq_of_wbyte_eq; intro b hb
  rw [vale.wbyte_subWord _ hb, wbyte_bswap _ hb, wbyte_bswap _ hb, vale.wbyte_subWord _ (by omega)]

theorem rotateLeft_bswap (w : BitVec 32) : (bswap w).rotateLeft 8 = bswap (vale.rotWord w) := by
  apply vale.eq_of_wbyte_eq; intro b hb
  rw [wbyte_rotateLeft _ hb, wbyte_bswap _ (by omega), wbyte_bswap _ hb, vale.wbyte_rotWord _ (by omega)]
  congr 1; omega

theorem aesRcon_bswap {r : Nat} (hr : r < 10) : aesRcon[r]! = bswap (vale.aesRcon r) := by
  interval_cases r <;> rfl

theorem aesKexpCore_bswap {r : Nat} (hr : r < 10) (p b : BitVec 32) :
    aesKexpCore aesRcon[r]! (bswap p) (bswap b) =
      bswap (b ^^^ (vale.subWord (vale.rotWord p) ^^^ vale.aesRcon r)) := by
  rw [aesKexpCore, aesRcon_bswap hr, rotateLeft_bswap, aesSubword_eq, subWord_bswap, bswap_xor, bswap_xor]

theorem aesKexpSub_bswap (p b : BitVec 32) : aesKexpSub (bswap p) (bswap b) = bswap (b ^^^ vale.subWord p) := by
  rw [aesKexpSub, aesSubword_eq, subWord_bswap, bswap_xor]

theorem rev_mkfour (a b c d : BitVec 32) :
    reverseBytesQuad32 (vale.mkfour a b c d) = wordJoin4 (bswap a, bswap b, bswap c, bswap d) := by
  apply vale.eq_of_byte_eq; intro i hi
  rw [vale.byte_reverseBytes _ hi]
  unfold wordJoin4 bswap byte vale.mkfour
  interval_cases i <;> simp (disch := omega) only [extractLsb'_append_lo, extractLsb'_append_hi, extractLsb'_self]

theorem wordSplit4_wordJoin4 (a b c d : BitVec 32) : wordSplit4 (wordJoin4 (a, b, c, d)) = (a, b, c, d) := by
  unfold wordSplit4 wordJoin4
  simp (disch := omega) only [extractLsb'_append_lo, extractLsb'_append_hi, extractLsb'_self]

theorem leBytesToQuad32_words (kb : List (BitVec 8)) (hk : kb.length = 16) :
    let kw := vale.seqNat8ToSeqNat32LE kb
    vale.leBytesToQuad32 kb = vale.mkfour kw[0]! kw[1]! kw[2]! kw[3]! := by
  intro kw
  have h := vale.leBytesToSeqQuad32_eq kb
  have hl : kw.length = 4 := by simp [kw, vale.seqNat8ToSeqNat32LE, hk]
  have h4 : (vale.seqNat8ToSeqNat32LE kb).length / 4 = 1 := by rw [show vale.seqNat8ToSeqNat32LE kb = kw from rfl, hl]
  rw [vale.chunksOf_16 kb hk, List.map_singleton, vale.leBytesToSeqQuad32, vale.seqToSeqFourLE, h4] at h
  simpa using h.symm

theorem wordSplit4_beBlock (kb : List (BitVec 8)) (hk : kb.length = 16) :
    let kw := vale.seqNat8ToSeqNat32LE kb
    wordSplit4 (beBlock kb) = (bswap kw[0]!, bswap kw[1]!, bswap kw[2]!, bswap kw[3]!) := by
  intro kw
  rw [beBlock, leBytesToQuad32_words kb hk, rev_mkfour, wordSplit4_wordJoin4]

/-- Word `i` of Vale's key schedule, `expand_key_def`'s recurrence. -/
def scheduleWord (alg : vale.Algorithm) (key : List (BitVec 32)) (i : Nat) : BitVec 32 :=
  if _h : i < vale.nk alg then key[i]!
  else
    let prev := scheduleWord alg key (i - 1)
    let temp :=
      if i % vale.nk alg = 0 then vale.subWord (vale.rotWord prev) ^^^ vale.aesRcon (i / vale.nk alg - 1)
      else if vale.nk alg > 6 ∧ i % vale.nk alg = 4 then vale.subWord prev
      else prev
    scheduleWord alg key (i - vale.nk alg) ^^^ temp
termination_by i
decreasing_by
  all_goals have : 0 < vale.nk alg := by cases alg <;> decide
  all_goals omega

theorem getElem!_concat_lt {l : List (BitVec 32)} (x : BitVec 32) {i : Nat} (h : i < l.length) :
    (l ++ [x])[i]! = l[i]! := by
  simp [List.getElem?_append_left h]

theorem getElem!_concat_eq {l : List (BitVec 32)} (x : BitVec 32) {i : Nat} (h : l.length = i) :
    (l ++ [x])[i]! = x := by
  subst h; simp

/-- Vale's `expand_key_def` is `scheduleWord`'s words. -/
theorem expandKey_spec (alg : vale.Algorithm) (key : List (BitVec 32)) : ∀ n,
    (vale.expandKey alg key n).length = n ∧ ∀ i < n, (vale.expandKey alg key n)[i]! = scheduleWord alg key i
  | 0 => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hl, hw⟩ := expandKey_spec alg key n
    have hnk : 0 < vale.nk alg := by cases alg <;> decide
    simp only [vale.expandKey]
    split
    · next hn =>
      refine ⟨by simp [hl], fun i hi => ?_⟩
      by_cases hin : i < n
      · rw [getElem!_concat_lt _ (by omega), hw i hin]
      · obtain rfl : i = n := by omega
        rw [getElem!_concat_eq _ hl, scheduleWord, dite_eq_left hn]
    · next hn =>
      refine ⟨by simp [hl], fun i hi => ?_⟩
      by_cases hin : i < n
      · rw [getElem!_concat_lt _ (by omega), hw i hin]
      · obtain rfl : i = n := by omega
        rw [getElem!_concat_eq _ hl, hw _ (by omega), hw _ (by omega)]
        conv_rhs => rw [scheduleWord, dite_eq_right hn]

theorem scheduleWord_lt (alg : vale.Algorithm) (key : List (BitVec 32)) {i : Nat} (h : i < vale.nk alg) :
    scheduleWord alg key i = key[i]! := by
  rw [scheduleWord, dite_eq_left h]

theorem keyScheduleToRoundKeys_eq (w : List (BitVec 32)) : ∀ n, vale.keyScheduleToRoundKeys n w =
    (List.range n).map fun r => vale.mkfour w[4 * r]! w[4 * r + 1]! w[4 * r + 2]! w[4 * r + 3]!
  | 0 => rfl
  | n + 1 => by
    rw [vale.keyScheduleToRoundKeys, keyScheduleToRoundKeys_eq w n, List.range_succ, List.map_append,
      List.map_singleton]

/-- The words of s2n-bignum's AES-128 key schedule after `r` steps. -/
def kexp128 (key : BitVec 128) : Nat → Words4
  | 0 => wordSplit4 key
  | r + 1 => aes128KexpRound r (kexp128 key r)

section aes128
variable (kw : List (BitVec 32)) (r : Nat)

local notation "sw" => scheduleWord vale.Algorithm.AES_128 kw

theorem sw128_4 : sw (4 * r + 4) = sw (4 * r) ^^^ (vale.subWord (vale.rotWord (sw (4 * r + 3))) ^^^ vale.aesRcon r) := by
  rw [scheduleWord]
  simp only [vale.nk, show ¬ 4 * r + 4 < 4 by omega, ↓reduceDIte, show (4 * r + 4) % 4 = 0 by omega, ↓reduceIte,
    show (4 * r + 4) / 4 - 1 = r by omega, show 4 * r + 4 - 1 = 4 * r + 3 by omega,
    show 4 * r + 4 - 4 = 4 * r by omega]

theorem sw128_xor (j : Nat) (hj1 : 1 ≤ j) (hj : j < 4) :
    sw (4 * r + 4 + j) = sw (4 * r + j) ^^^ sw (4 * r + 3 + j) := by
  rw [scheduleWord]
  simp only [vale.nk, show ¬ 4 * r + 4 + j < 4 by omega, ↓reduceDIte, show ¬ (4 * r + 4 + j) % 4 = 0 by omega,
    ↓reduceIte, show ¬ (4 > 6 ∧ (4 * r + 4 + j) % 4 = 4) by omega, show 4 * r + 4 + j - 1 = 4 * r + 3 + j by omega,
    show 4 * r + 4 + j - 4 = 4 * r + j by omega]

end aes128

theorem kexp128_eq (kb : List (BitVec 8)) (hk : kb.length = 16) : ∀ r, r ≤ 10 →
    kexp128 (beBlock kb) r =
      (bswap (scheduleWord .AES_128 (vale.seqNat8ToSeqNat32LE kb) (4 * r)),
       bswap (scheduleWord .AES_128 (vale.seqNat8ToSeqNat32LE kb) (4 * r + 1)),
       bswap (scheduleWord .AES_128 (vale.seqNat8ToSeqNat32LE kb) (4 * r + 2)),
       bswap (scheduleWord .AES_128 (vale.seqNat8ToSeqNat32LE kb) (4 * r + 3)))
  | 0, _ => by
    rw [kexp128, wordSplit4_beBlock kb hk]
    simp only [Nat.mul_zero, Nat.zero_add, scheduleWord_lt _ _ (show 0 < vale.nk .AES_128 by decide),
      scheduleWord_lt _ _ (show 1 < vale.nk .AES_128 by decide), scheduleWord_lt _ _ (show 2 < vale.nk .AES_128 by decide),
      scheduleWord_lt _ _ (show 3 < vale.nk .AES_128 by decide)]
  | r + 1, hr => by
    rw [kexp128, kexp128_eq kb hk r (by omega), aes128KexpRound]
    simp only [show 4 * (r + 1) = 4 * r + 4 by ring]
    rw [aesKexpCore_bswap (by omega), sw128_xor _ r 1 (by omega) (by omega), sw128_xor _ r 2 (by omega) (by omega),
      sw128_xor _ r 3 (by omega) (by omega), sw128_4]
    simp only [bswap_xor, show 4 * r + 3 + 1 = 4 * r + 4 by omega, show 4 * r + 3 + 2 = 4 * r + 4 + 1 by omega,
      show 4 * r + 3 + 3 = 4 * r + 4 + 2 by omega, sw128_xor _ r 1 (by omega) (by omega),
      sw128_xor _ r 2 (by omega) (by omega), sw128_4]

theorem aes128KeyExpansion_rev (kb : List (BitVec 8)) (hk : kb.length = 16) :
    aes128KeyExpansion (beBlock kb) =
      (vale.keyToRoundKeys .AES_128 (vale.seqNat8ToSeqNat32LE kb)).map reverseBytesQuad32 := by
  have hl : aes128KeyExpansion (beBlock kb) = (List.range 11).map fun r => wordJoin4 (kexp128 (beBlock kb) r) := rfl
  obtain ⟨_, hw⟩ := expandKey_spec .AES_128 (vale.seqNat8ToSeqNat32LE kb) 44
  simp only [hl, vale.keyToRoundKeys, vale.nr, vale.nb, Nat.reduceAdd, Nat.reduceMul, keyScheduleToRoundKeys_eq,
    List.map_map]
  apply List.map_congr_left; intro r hr
  have hr := List.mem_range.1 hr
  rw [Function.comp_apply, hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega),
    kexp128_eq kb hk r (by omega), rev_mkfour]

theorem wordJoin4_wordSplit4 (k : BitVec 128) : wordJoin4 (wordSplit4 k) = k := by
  apply vale.eq_of_byte_eq; intro i hi
  unfold wordJoin4 wordSplit4 byte
  interval_cases i <;>
    simp (disch := omega) only [extractLsb'_append_lo, extractLsb'_append_hi, extractLsb'_extractLsb']

theorem seqNat8ToSeqNat32LE_append : ∀ (a b : List (BitVec 8)), a.length % 4 = 0 →
    vale.seqNat8ToSeqNat32LE (a ++ b) = vale.seqNat8ToSeqNat32LE a ++ vale.seqNat8ToSeqNat32LE b
  | [], _, _ => rfl
  | [_], _, h | [_, _], _, h | [_, _, _], _, h => by simp at h
  | x0 :: x1 :: x2 :: x3 :: rest, b, h => by
    rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append, vale.seqNat8ToSeqNat32LE_cons4,
      vale.seqNat8ToSeqNat32LE_cons4, seqNat8ToSeqNat32LE_append rest b (by simp at h; omega), List.cons_append]

theorem getElem!_append_lt {l₁ l₂ : List (BitVec 32)} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂)[i]! = l₁[i]! := by
  simp [List.getElem?_append_left h]

theorem getElem!_append_ge {l₁ l₂ : List (BitVec 32)} {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂)[i]! = l₂[i - l₁.length]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right h]

/-- The words of s2n-bignum's AES-256 key schedule after `t` steps. -/
def kexp256 (keyHi keyLo : BitVec 128) : Nat → Words4 × Words4
  | 0 => (wordSplit4 keyHi, wordSplit4 keyLo)
  | t + 1 => aes256KexpRound t (kexp256 keyHi keyLo t)

/-- Two of s2n-bignum's AES-256 round keys as words: Vale's words `8 t` through `8 t + 7`, bytes reversed. -/
def words8 (sw : Nat → BitVec 32) (t : Nat) : Words4 × Words4 :=
  ((bswap (sw (8 * t)), bswap (sw (8 * t + 1)), bswap (sw (8 * t + 2)), bswap (sw (8 * t + 3))),
   (bswap (sw (8 * t + 4)), bswap (sw (8 * t + 5)), bswap (sw (8 * t + 6)), bswap (sw (8 * t + 7))))

section aes256
variable (kw : List (BitVec 32)) (t : Nat)

local notation "sw" => scheduleWord vale.Algorithm.AES_256 kw

theorem sw256_8 : sw (8 * t + 8) = sw (8 * t) ^^^ (vale.subWord (vale.rotWord (sw (8 * t + 7))) ^^^ vale.aesRcon t) := by
  rw [scheduleWord]
  simp only [vale.nk, show ¬ 8 * t + 8 < 8 by omega, ↓reduceDIte, show (8 * t + 8) % 8 = 0 by omega, ↓reduceIte,
    show (8 * t + 8) / 8 - 1 = t by omega, show 8 * t + 8 - 1 = 8 * t + 7 by omega,
    show 8 * t + 8 - 8 = 8 * t by omega]

theorem sw256_12 : sw (8 * t + 8 + 4) = sw (8 * t + 4) ^^^ vale.subWord (sw (8 * t + 7 + 4)) := by
  rw [scheduleWord]
  simp only [vale.nk, show ¬ 8 * t + 8 + 4 < 8 by omega, ↓reduceDIte,
    ↓reduceIte, show 8 > 6 ∧ (8 * t + 8 + 4) % 8 = 4 by omega, show 8 * t + 8 + 4 - 1 = 8 * t + 7 + 4 by omega,
    show 8 * t + 8 + 4 - 8 = 8 * t + 4 by omega, show ¬ (4 : Nat) = 0 by omega, and_self]

theorem sw256_xor (j : Nat) (hj1 : 1 ≤ j) (hj : j < 8) (hj4 : j ≠ 4) :
    sw (8 * t + 8 + j) = sw (8 * t + j) ^^^ sw (8 * t + 7 + j) := by
  rw [scheduleWord]
  simp only [vale.nk, show ¬ 8 * t + 8 + j < 8 by omega, ↓reduceDIte, show ¬ (8 * t + 8 + j) % 8 = 0 by omega,
    ↓reduceIte, show ¬ (8 > 6 ∧ (8 * t + 8 + j) % 8 = 4) by omega, show 8 * t + 8 + j - 1 = 8 * t + 7 + j by omega,
    show 8 * t + 8 + j - 8 = 8 * t + j by omega]

/-- The words of a step of s2n-bignum's AES-256 key schedule, from Vale's eight before them. -/
theorem kexp256_step (ht : t < 7) : aes256KexpRound t (words8 sw t) = words8 sw (t + 1) := by
  simp only [words8, show 8 * (t + 1) = 8 * t + 8 by ring]
  rw [aes256KexpRound]
  simp only [aesKexpCore_bswap (show t < 10 by omega), ← bswap_xor, aesKexpSub_bswap]
  rw [sw256_xor kw t 7 (by omega) (by omega) (by omega), sw256_xor kw t 6 (by omega) (by omega) (by omega),
    sw256_xor kw t 5 (by omega) (by omega) (by omega), sw256_12, sw256_xor kw t 3 (by omega) (by omega) (by omega),
    sw256_xor kw t 2 (by omega) (by omega) (by omega), sw256_xor kw t 1 (by omega) (by omega) (by omega), sw256_8]

end aes256

theorem kexp256_eq (hi lo : List (BitVec 8)) (hhi : hi.length = 16) (hlo : lo.length = 16) : ∀ t, t ≤ 7 →
    kexp256 (beBlock hi) (beBlock lo) t = words8 (scheduleWord .AES_256 (vale.seqNat8ToSeqNat32LE (hi ++ lo))) t
  | 0, _ => by
    have hw : vale.seqNat8ToSeqNat32LE (hi ++ lo) = vale.seqNat8ToSeqNat32LE hi ++ vale.seqNat8ToSeqNat32LE lo :=
      seqNat8ToSeqNat32LE_append hi lo (by omega)
    have hl : (vale.seqNat8ToSeqNat32LE hi).length = 4 := by simp [vale.seqNat8ToSeqNat32LE, hhi]
    have hs : ∀ i, i < 8 → scheduleWord .AES_256 (vale.seqNat8ToSeqNat32LE (hi ++ lo)) i =
        (vale.seqNat8ToSeqNat32LE (hi ++ lo))[i]! := fun i h =>
      scheduleWord_lt _ _ (by simp only [vale.nk]; omega)
    rw [kexp256, words8, wordSplit4_beBlock hi hhi, wordSplit4_beBlock lo hlo]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [hs 0 (by omega), hs 1 (by omega), hs 2 (by omega), hs 3 (by omega), hs 4 (by omega), hs 5 (by omega),
      hs 6 (by omega), hs 7 (by omega)]
    simp only [hw,
      getElem!_append_lt (show 0 < (vale.seqNat8ToSeqNat32LE hi).length by omega),
      getElem!_append_lt (show 1 < (vale.seqNat8ToSeqNat32LE hi).length by omega),
      getElem!_append_lt (show 2 < (vale.seqNat8ToSeqNat32LE hi).length by omega),
      getElem!_append_lt (show 3 < (vale.seqNat8ToSeqNat32LE hi).length by omega),
      getElem!_append_ge (show (vale.seqNat8ToSeqNat32LE hi).length ≤ 4 by omega),
      getElem!_append_ge (show (vale.seqNat8ToSeqNat32LE hi).length ≤ 5 by omega),
      getElem!_append_ge (show (vale.seqNat8ToSeqNat32LE hi).length ≤ 6 by omega),
      getElem!_append_ge (show (vale.seqNat8ToSeqNat32LE hi).length ≤ 7 by omega), hl]
  | t + 1, ht => by
    rw [kexp256, kexp256_eq hi lo hhi hlo t (by omega), kexp256_step _ t (by omega)]

theorem aes256KexpLast_eq (i : Nat) (x : Words4 × Words4) : aes256KexpLast i x = (aes256KexpRound i x).1 := by
  obtain ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := x; rfl

theorem aes256KeyExpansion_kexp (kh kl : BitVec 128) : aes256KeyExpansion kh kl =
    [wordJoin4 (kexp256 kh kl 0).1, wordJoin4 (kexp256 kh kl 0).2, wordJoin4 (kexp256 kh kl 1).1,
     wordJoin4 (kexp256 kh kl 1).2, wordJoin4 (kexp256 kh kl 2).1, wordJoin4 (kexp256 kh kl 2).2,
     wordJoin4 (kexp256 kh kl 3).1, wordJoin4 (kexp256 kh kl 3).2, wordJoin4 (kexp256 kh kl 4).1,
     wordJoin4 (kexp256 kh kl 4).2, wordJoin4 (kexp256 kh kl 5).1, wordJoin4 (kexp256 kh kl 5).2,
     wordJoin4 (kexp256 kh kl 6).1, wordJoin4 (kexp256 kh kl 6).2, wordJoin4 (kexp256 kh kl 7).1] := by
  simp only [aes256KeyExpansion, aes256KexpLast_eq, kexp256, wordJoin4_wordSplit4]

theorem aes256KeyExpansion_rev (hi lo : List (BitVec 8)) (hhi : hi.length = 16) (hlo : lo.length = 16) :
    aes256KeyExpansion (beBlock hi) (beBlock lo) =
      (vale.keyToRoundKeys .AES_256 (vale.seqNat8ToSeqNat32LE (hi ++ lo))).map reverseBytesQuad32 := by
  obtain ⟨_, hw⟩ := expandKey_spec .AES_256 (vale.seqNat8ToSeqNat32LE (hi ++ lo)) 60
  have hk := kexp256_eq hi lo hhi hlo
  rw [aes256KeyExpansion_kexp, hk 0 (by omega), hk 1 (by omega), hk 2 (by omega), hk 3 (by omega),
    hk 4 (by omega), hk 5 (by omega), hk 6 (by omega), hk 7 (by omega)]
  simp only [vale.keyToRoundKeys, vale.nr, vale.nb, Nat.reduceAdd, Nat.reduceMul, keyScheduleToRoundKeys_eq,
    show List.range 15 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from rfl, List.map_cons, List.map_nil,
    words8, rev_mkfour]
  simp (disch := omega) only [hw]

/-- s2n-bignum's AES-128 key schedule, its blocks' bytes reversed, is Vale's. -/
theorem aes128KeyExpansion_eq (kb : List (BitVec 8)) (hk : kb.length = 16) :
    (aes128KeyExpansion (beBlock kb)).map reverseBytesQuad32 =
      vale.keyToRoundKeys .AES_128 (vale.seqNat8ToSeqNat32LE kb) := by
  rw [aes128KeyExpansion_rev kb hk, List.map_map]
  simp [Function.comp_def, vale.reverseBytesQuad32_involutive]

/-- s2n-bignum's AES-256 key schedule, its blocks' bytes reversed, is Vale's:
the key's first 16 bytes are `keyHi` and its last 16 `keyLo`. -/
theorem aes256KeyExpansion_eq (hi lo : List (BitVec 8)) (hhi : hi.length = 16) (hlo : lo.length = 16) :
    (aes256KeyExpansion (beBlock hi) (beBlock lo)).map reverseBytesQuad32 =
      vale.keyToRoundKeys .AES_256 (vale.seqNat8ToSeqNat32LE (hi ++ lo)) := by
  rw [aes256KeyExpansion_rev hi lo hhi hlo, List.map_map]
  simp [Function.comp_def, vale.reverseBytesQuad32_involutive]

/-- A cipher is Vale's AES under the key words `kw` when it is Vale's
`eval_cipher` on its round keys, as `Rind/S2nGcm.lean`'s `aes128Cipher_eq`
and `aes256Cipher_eq` state, and those are Vale's for `kw`, as the key
schedules' theorems here state, each block's bytes reversed. -/
theorem isValeAes_of {enc : Cipher} {ks : List (BitVec 128)} {alg : vale.Algorithm} {kw : List (BitVec 32)}
    (henc : ∀ x, reverseBytesQuad32 (enc x ks) =
      vale.evalCipher alg (reverseBytesQuad32 x) (ks.map reverseBytesQuad32))
    (hks : ks.map reverseBytesQuad32 = vale.keyToRoundKeys alg kw) : IsValeAes enc ks alg kw := by
  intro x
  rw [vale.aesEncrypt, ← hks, ← henc, vale.reverseBytesQuad32_involutive]

/-- s2n-bignum's AES-128, under the schedule it expands from a key, is Vale's. -/
theorem isValeAes_aes128 (key : List (BitVec 8)) (hk : key.length = 16) :
    IsValeAes aes128Cipher (aes128KeyExpansion (beBlock key)) .AES_128 (vale.seqNat8ToSeqNat32LE key) :=
  isValeAes_of (fun x => aes128Cipher_eq x _) (aes128KeyExpansion_eq key hk)

/-- s2n-bignum's AES-256, under the schedule it expands from a key's two halves, is Vale's. -/
theorem isValeAes_aes256 (key : List (BitVec 8)) (hk : key.length = 32) :
    IsValeAes aes256Cipher (aes256KeyExpansion (beBlock (key.take 16)) (beBlock (key.drop 16))) .AES_256
      (vale.seqNat8ToSeqNat32LE key) := by
  have h := aes256KeyExpansion_eq (key.take 16) (key.drop 16) (by simp [hk]) (by simp [hk])
  rw [List.take_append_drop] at h
  exact isValeAes_of (fun x => aes256Cipher_eq x _) h

/-- s2n-bignum's AES-128-GCM encryption is Vale's. -/
theorem gcmAe_aes128 (key iv plain auth : List (BitVec 8)) (hk : key.length = 16) (hiv : iv.length = 12)
    (hp : plain.length % 16 = 0) (ha : auth.length % 16 = 0) :
    gcmAe aes128Cipher (aes128KeyExpansion (beBlock key)) (ivWord iv) (beBlocks plain) (beBlocks auth) =
      (beBlocks (vale.gcmEncrypt .AES_128 key iv plain auth).1,
        beBlock (vale.gcmEncrypt .AES_128 key iv plain auth).2) :=
  gcmAe_eq (isValeAes_aes128 key hk) iv plain auth hiv hp ha

/-- s2n-bignum's AES-128-GCM decryption is Vale's. -/
theorem gcmAd_aes128 (key iv cipher auth tag : List (BitVec 8)) (hk : key.length = 16) (hiv : iv.length = 12)
    (hc : cipher.length % 16 = 0) (ha : auth.length % 16 = 0) (ht : tag.length = 16) :
    gcmAd aes128Cipher (aes128KeyExpansion (beBlock key)) (ivWord iv) (beBlocks cipher) (beBlocks auth)
        (beBlock tag) =
      if (vale.gcmDecrypt .AES_128 key iv cipher auth tag).2 then
        some (beBlocks (vale.gcmDecrypt .AES_128 key iv cipher auth tag).1)
      else none :=
  gcmAd_eq (isValeAes_aes128 key hk) iv cipher auth tag hiv hc ha ht

/-- s2n-bignum's AES-256-GCM encryption is Vale's. -/
theorem gcmAe_aes256 (key iv plain auth : List (BitVec 8)) (hk : key.length = 32) (hiv : iv.length = 12)
    (hp : plain.length % 16 = 0) (ha : auth.length % 16 = 0) :
    gcmAe aes256Cipher (aes256KeyExpansion (beBlock (key.take 16)) (beBlock (key.drop 16))) (ivWord iv)
        (beBlocks plain) (beBlocks auth) =
      (beBlocks (vale.gcmEncrypt .AES_256 key iv plain auth).1,
        beBlock (vale.gcmEncrypt .AES_256 key iv plain auth).2) :=
  gcmAe_eq (isValeAes_aes256 key hk) iv plain auth hiv hp ha

/-- s2n-bignum's AES-256-GCM decryption is Vale's. -/
theorem gcmAd_aes256 (key iv cipher auth tag : List (BitVec 8)) (hk : key.length = 32) (hiv : iv.length = 12)
    (hc : cipher.length % 16 = 0) (ha : auth.length % 16 = 0) (ht : tag.length = 16) :
    gcmAd aes256Cipher (aes256KeyExpansion (beBlock (key.take 16)) (beBlock (key.drop 16))) (ivWord iv)
        (beBlocks cipher) (beBlocks auth) (beBlock tag) =
      if (vale.gcmDecrypt .AES_256 key iv cipher auth tag).2 then
        some (beBlocks (vale.gcmDecrypt .AES_256 key iv cipher auth tag).1)
      else none :=
  gcmAd_eq (isValeAes_aes256 key hk) iv cipher auth tag hiv hc ha ht

end rind.s2n.gcm
