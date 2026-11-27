-- Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
--
-- A transliteration of s2n-bignum's AES-GCM spec; see LICENSE.

import Rind.GcmSpec
import Rind.AesSbox
open Polynomial

/-!
# s2n-bignum's AES-GCM spec, and Vale's

s2n-bignum's theorems about its aarch64 AES-GCM kernels state SP 800-38D
through its own definitions, at rind's pin (3f01260f): FIPS 197's AES in
`common/fips197.ml` over `common/aes.ml`'s tables, GHASH's `nist_dot` and
`nist_ghash` in `common/ghash_nist_defs.ml` over `common/ghash.ml`'s
reduction, POLYVAL's `polyval_dot`, `h_power`, and `ghash_twist` in
`common/polyval.ml` and `common/polyval_ghash.ml`, and the kernels' counter
blocks, keystream, and GHASH key table in `arm/proofs/utils/aes_gcm_spec.ml`.
This file transliterates them: HOL Light's `word_xor` is `^^^`,
`word_join` is `++`, `word_subword w (pos, len)` is `extractLsb' pos len`,
`word_zx` is `setWidth`, `word_shl` and `word_ushr` are `<<<` and `>>>`,
`val` is `toNat`, `EL n l` is `l[n]!`, `bit i w` is `getLsbD i`, and
`word_pmul` and `word_reversefields` are written out bit by bit, as their
definitions in HOL Light's `Library/words.ml` are.

It then proves them Vale's, which the rest of rind's AES-GCM proofs state:
the AES cipher on a block in SP 800-38D's byte order, its bytes reversed, is
Vale's on Vale's (`aes128Cipher_eq`, `aes256Cipher_eq`), `nist_dot` is
Vale's `gf128_mul_rev` (`toPoly_nistDot`), so `nist_ghash` is `ghashPoly`
(`toPoly_nistGhash`), `h_power` of the twisted key is the shifted power of
H that rind's PMULL table holds (`toPoly_hPower`), and the kernels' counter
blocks are Vale's `inc32` (`inc32_ctrBlock`).
-/

local notation "P" => Polynomial (ZMod 2)

set_option maxRecDepth 20000

namespace rind.s2n

open rind.vale

/-! ## Words, `Library/words.ml` -/

/-- `word_reversefields b w`: `w`'s fields of `b` bits in the other order. -/
def wordReversefields (b : Nat) {n : Nat} (w : BitVec n) : BitVec n :=
  BitVec.ofFnLE fun i => w.getLsbD (if i.val < b * (n / b) then b * (n / b - 1 - i.val / b) + i.val % b else i.val)

/-- `word_pmul`: the carry-less product, its bit `k` the parity of the pairs
of set bits `i` of `x` and `k - i` of `y`, cut to `p` bits. -/
def wordPmul {m n : Nat} (p : Nat) (x : BitVec m) (y : BitVec n) : BitVec p :=
  BitVec.ofFnLE fun k =>
    (List.range (k.val + 1)).countP (fun i => x.getLsbD i && y.getLsbD (k.val - i)) % 2 = 1

/-! ## GHASH, `common/ghash.ml` and `common/ghash_nist_defs.ml` -/

/-- `bit_reflect128`. -/
def bitReflect128 (a : BitVec 128) : BitVec 128 := wordReversefields 1 a

/-- `ghash_reduce1`, on 256 bits. -/
def ghashReduce1 (x : BitVec 256) : BitVec 256 :=
  (x.extractLsb' 0 128).setWidth 256 ^^^ wordPmul 256 (x >>> 128) (0x87#256)

/-- `ghash_reduce`. -/
def ghashReduce (x : BitVec 256) : BitVec 128 := (ghashReduce1 (ghashReduce1 x)).setWidth 128

/-- `nist_dot`: SP 800-38D's product in GF(2^128). -/
def nistDot (a b : BitVec 128) : BitVec 128 :=
  bitReflect128 (ghashReduce (wordPmul 256 (bitReflect128 a) (bitReflect128 b)))

/-- `nist_ghash`: SP 800-38D's GHASH from `acc`. -/
def nistGhash (h : BitVec 128) : BitVec 128 → List (BitVec 128) → BitVec 128
  | acc, [] => acc
  | acc, x :: xs => nistGhash h (nistDot (acc ^^^ x) h) xs

/-! ## POLYVAL and the key table, `common/polyval.ml` and `common/polyval_ghash.ml` -/

/-- `polyval_reduce_prop3`. -/
def polyvalReduceProp3 (t : BitVec 256) : BitVec 128 :=
  let a : BitVec 64 := t.extractLsb' 0 64
  let b : BitVec 64 := t.extractLsb' 64 64
  let c : BitVec 64 := t.extractLsb' 128 64
  let d : BitVec 64 := t.extractLsb' 192 64
  let w : BitVec 64 := 0xC200000000000000#64
  let wa : BitVec 128 := wordPmul 128 a w
  let wa_lo : BitVec 64 := wa.extractLsb' 0 64
  let wa_hi : BitVec 64 := wa.extractLsb' 64 64
  let v : BitVec 64 := b ^^^ wa_lo
  let u : BitVec 64 := (c ^^^ a) ^^^ wa_hi
  let wv : BitVec 128 := wordPmul 128 v w
  let wv_lo : BitVec 64 := wv.extractLsb' 0 64
  let wv_hi : BitVec 64 := wv.extractLsb' 64 64
  let f : BitVec 64 := u ^^^ wv_lo
  let g : BitVec 64 := (d ^^^ v) ^^^ wv_hi
  g ++ f

/-- `polyval_dot`. -/
def polyvalDot (a b : BitVec 128) : BitVec 128 := polyvalReduceProp3 (wordPmul 256 a b)

/-- `h_power`. -/
def hPower (h : BitVec 128) : Nat → BitVec 128
  | 0 => h
  | n + 1 => polyvalDot (hPower h n) h

/-- `karatsuba_mid`. -/
def karatsubaMid (h : BitVec 128) : BitVec 64 := h.extractLsb' 0 64 ^^^ h.extractLsb' 64 64

/-- `byteswap128`. -/
def byteswap128 (x : BitVec 128) : BitVec 128 := x.extractLsb' 0 64 ++ x.extractLsb' 64 64

/-- `POLYVAL_TWIST_CONST`. -/
def polyvalTwistConst : BitVec 128 := 0xC2000000000000000000000000000001#128

/-- `ghash_twist`. -/
def ghashTwist (h : BitVec 128) : BitVec 128 :=
  if h.getLsbD 127 then (h <<< 1) ^^^ polyvalTwistConst else h <<< 1

/-! ## FIPS 197, `common/aes.ml` and `common/fips197.ml` -/

/-- `word_join_list_16_8`: the first byte most significant. -/
def wordJoinList16x8 (l : List (BitVec 8)) : BitVec 128 :=
  l[0]! ++ (l[1]! ++ (l[2]! ++ (l[3]! ++ (l[4]! ++ (l[5]! ++ (l[6]! ++ (l[7]! ++ (l[8]! ++ (l[9]! ++
    (l[10]! ++ (l[11]! ++ (l[12]! ++ (l[13]! ++ (l[14]! ++ l[15]!))))))))))))))

/-- `word_join_list_16_128`: the first word most significant. -/
def wordJoinList16x128 (l : List (BitVec 128)) : BitVec 2048 :=
  l[0]! ++ (l[1]! ++ (l[2]! ++ (l[3]! ++ (l[4]! ++ (l[5]! ++ (l[6]! ++ (l[7]! ++ (l[8]! ++ (l[9]! ++
    (l[10]! ++ (l[11]! ++ (l[12]! ++ (l[13]! ++ (l[14]! ++ l[15]!))))))))))))))

/-- `GF2`: the S-box, its last byte the image of 0. -/
def gf2 : List (BitVec 128) :=
  [0x16bb54b00f2d99416842e6bf0d89a18c#128, 0xdf2855cee9871e9b948ed9691198f8e1#128,
   0x9e1dc186b95735610ef6034866b53e70#128, 0x8a8bbd4b1f74dde8c6b4a61c2e2578ba#128,
   0x08ae7a65eaf4566ca94ed58d6d37c8e7#128, 0x79e4959162acd3c25c2406490a3a32e0#128,
   0xdb0b5ede14b8ee4688902a22dc4f8160#128, 0x73195d643d7ea7c41744975fec130ccd#128,
   0xd2f3ff1021dab6bcf5389d928f40a351#128, 0xa89f3c507f02f94585334d43fbaaefd0#128,
   0xcf584c4a39becb6a5bb1fc20ed00d153#128, 0x842fe329b3d63b52a05a6e1b1a2c8309#128,
   0x75b227ebe28012079a059618c323c704#128, 0x1531d871f1e5a534ccf73f362693fdb7#128,
   0xc072a49cafa2d4adf04759fa7dc982ca#128, 0x76abd7fe2b670130c56f6bf27b777c63#128]

/-- `joined_GF2`. -/
def joinedGf2 : BitVec 2048 := wordJoinList16x128 gf2

/-- `FFmul_02`: multiplication by 2 in FIPS 197's field. -/
def ffmulTable02 : List (BitVec 128) :=
  [0xE5E7E1E3EDEFE9EBF5F7F1F3FDFFF9FB#128, 0xC5C7C1C3CDCFC9CBD5D7D1D3DDDFD9DB#128,
   0xA5A7A1A3ADAFA9ABB5B7B1B3BDBFB9BB#128, 0x858781838D8F898B959791939D9F999B#128,
   0x656761636D6F696B757771737D7F797B#128, 0x454741434D4F494B555751535D5F595B#128,
   0x252721232D2F292B353731333D3F393B#128, 0x050701030D0F090B151711131D1F191B#128,
   0xFEFCFAF8F6F4F2F0EEECEAE8E6E4E2E0#128, 0xDEDCDAD8D6D4D2D0CECCCAC8C6C4C2C0#128,
   0xBEBCBAB8B6B4B2B0AEACAAA8A6A4A2A0#128, 0x9E9C9A98969492908E8C8A8886848280#128,
   0x7E7C7A78767472706E6C6A6866646260#128, 0x5E5C5A58565452504E4C4A4846444240#128,
   0x3E3C3A38363432302E2C2A2826242220#128, 0x1E1C1A18161412100E0C0A0806040200#128]

/-- `FFmul_03`: multiplication by 3 in FIPS 197's field. -/
def ffmulTable03 : List (BitVec 128) :=
  [0x1A191C1F16151013020104070E0D080B#128, 0x2A292C2F26252023323134373E3D383B#128,
   0x7A797C7F76757073626164676E6D686B#128, 0x4A494C4F46454043525154575E5D585B#128,
   0xDAD9DCDFD6D5D0D3C2C1C4C7CECDC8CB#128, 0xEAE9ECEFE6E5E0E3F2F1F4F7FEFDF8FB#128,
   0xBAB9BCBFB6B5B0B3A2A1A4A7AEADA8AB#128, 0x8A898C8F86858083929194979E9D989B#128,
   0x818287848D8E8B88999A9F9C95969390#128, 0xB1B2B7B4BDBEBBB8A9AAAFACA5A6A3A0#128,
   0xE1E2E7E4EDEEEBE8F9FAFFFCF5F6F3F0#128, 0xD1D2D7D4DDDEDBD8C9CACFCCC5C6C3C0#128,
   0x414247444D4E4B48595A5F5C55565350#128, 0x717277747D7E7B78696A6F6C65666360#128,
   0x212227242D2E2B28393A3F3C35363330#128, 0x111217141D1E1B18090A0F0C05060300#128]

/-- `aes_sub_byte`: the byte `pos` of the table. -/
def aesSubByte (gf : BitVec 2048) (pos : BitVec 8) : BitVec 8 := gf.extractLsb' (pos.toNat * 8) 8

/-- `aes_sub_bytes_select`. -/
def aesSubBytesSelect (gf : BitVec 2048) (op : BitVec 128) (i : Nat) : BitVec 8 :=
  aesSubByte gf (op.extractLsb' (i * 8) 8)

/-- `aes_sub_bytes`. -/
def aesSubBytes (gf : BitVec 2048) (op : BitVec 128) : BitVec 128 :=
  wordJoinList16x8 ((List.range 16).map fun j => aesSubBytesSelect gf op (15 - j))

/-- `FFmul`. -/
def ffmul (tb : BitVec 2048) (b : BitVec 8) : BitVec 8 := tb.extractLsb' (b.toNat * 8) 8

/-- `FFmul02`. -/
def ffmul02 : BitVec 8 → BitVec 8 := ffmul (wordJoinList16x128 ffmulTable02)

/-- `FFmul03`. -/
def ffmul03 : BitVec 8 → BitVec 8 := ffmul (wordJoinList16x128 ffmulTable03)

/-- `aes_mix_word`. -/
def aesMixWord (op : BitVec 128) (a b c d : Nat) : BitVec 8 :=
  ffmul02 (op.extractLsb' a 8) ^^^ (ffmul03 (op.extractLsb' b 8) ^^^ (op.extractLsb' c 8 ^^^ op.extractLsb' d 8))

/-- `fips197_sub_bytes`. -/
def fips197SubBytes (s : BitVec 128) : BitVec 128 := aesSubBytes joinedGf2 s

/-- `fips197_shift_rows`. -/
def fips197ShiftRows (op : BitVec 128) : BitVec 128 :=
  wordJoinList16x8 ([120, 80, 40, 0, 88, 48, 8, 96, 56, 16, 104, 64, 24, 112, 72, 32].map fun p => op.extractLsb' p 8)

/-- `fips197_mix_columns`. -/
def fips197MixColumns (op : BitVec 128) : BitVec 128 :=
  wordJoinList16x8
    [aesMixWord op 120 112 104 96, aesMixWord op 112 104 96 120, aesMixWord op 104 96 120 112,
     aesMixWord op 96 120 112 104, aesMixWord op 88 80 72 64, aesMixWord op 80 72 64 88,
     aesMixWord op 72 64 88 80, aesMixWord op 64 88 80 72, aesMixWord op 56 48 40 32,
     aesMixWord op 48 40 32 56, aesMixWord op 40 32 56 48, aesMixWord op 32 56 48 40,
     aesMixWord op 24 16 8 0, aesMixWord op 16 8 0 24, aesMixWord op 8 0 24 16, aesMixWord op 0 24 16 8]

/-- `fips197_round`. -/
def fips197Round (state roundKey : BitVec 128) : BitVec 128 :=
  fips197MixColumns (fips197ShiftRows (fips197SubBytes state)) ^^^ roundKey

/-- `fips197_final_round`. -/
def fips197FinalRound (state roundKey : BitVec 128) : BitVec 128 :=
  fips197ShiftRows (fips197SubBytes state) ^^^ roundKey

/-- `aes128_cipher`. -/
def aes128Cipher (plaintext : BitVec 128) (ks : List (BitVec 128)) : BitVec 128 :=
  let s0 := plaintext ^^^ ks[0]!
  let s1 := fips197Round s0 ks[1]!
  let s2 := fips197Round s1 ks[2]!
  let s3 := fips197Round s2 ks[3]!
  let s4 := fips197Round s3 ks[4]!
  let s5 := fips197Round s4 ks[5]!
  let s6 := fips197Round s5 ks[6]!
  let s7 := fips197Round s6 ks[7]!
  let s8 := fips197Round s7 ks[8]!
  let s9 := fips197Round s8 ks[9]!
  fips197FinalRound s9 ks[10]!

/-- `aes256_cipher`. -/
def aes256Cipher (plaintext : BitVec 128) (ks : List (BitVec 128)) : BitVec 128 :=
  let s0 := plaintext ^^^ ks[0]!
  let s1 := fips197Round s0 ks[1]!
  let s2 := fips197Round s1 ks[2]!
  let s3 := fips197Round s2 ks[3]!
  let s4 := fips197Round s3 ks[4]!
  let s5 := fips197Round s4 ks[5]!
  let s6 := fips197Round s5 ks[6]!
  let s7 := fips197Round s6 ks[7]!
  let s8 := fips197Round s7 ks[8]!
  let s9 := fips197Round s8 ks[9]!
  let s10 := fips197Round s9 ks[10]!
  let s11 := fips197Round s10 ks[11]!
  let s12 := fips197Round s11 ks[12]!
  let s13 := fips197Round s12 ks[13]!
  fips197FinalRound s13 ks[14]!

/-! ## The kernels' vocabulary, `arm/proofs/utils/aes_gcm_spec.ml` -/

/-- `ctr_block`: a 96-bit nonce, then a 32-bit counter. -/
def ctrBlock (nonce : BitVec 96) (ctr : Nat) : BitVec 128 := nonce ++ BitVec.ofNat 32 ctr

/-- `aes_ctr_block`: the keystream for data block `i`, in lane order. -/
def aesCtrBlock (enc : BitVec 128 → List (BitVec 128) → BitVec 128) (c : Nat) (nonce : BitVec 96)
    (rk : List (BitVec 128)) (i : Nat) : BitVec 128 :=
  wordReversefields 8 (enc (ctrBlock nonce (i + c)) rk)

/-- `cipher_block`: output block `i`, in lane order. -/
def cipherBlock (enc : BitVec 128 → List (BitVec 128) → BitVec 128) (c : Nat) (nonce : BitVec 96)
    (rk : List (BitVec 128)) (inblock : Nat → BitVec 128) (i : Nat) : BitVec 128 :=
  aesCtrBlock enc c nonce rk i ^^^ inblock i

/-- `nist_cipher_block`: output block `i`, in SP 800-38D's byte order. -/
def nistCipherBlock (enc : BitVec 128 → List (BitVec 128) → BitVec 128) (c : Nat) (nonce : BitVec 96)
    (rk : List (BitVec 128)) (inblock : Nat → BitVec 128) (i : Nat) : BitVec 128 :=
  wordReversefields 8 (cipherBlock enc c nonce rk inblock i)

/-- `nist_input_block`: input block `i`, in SP 800-38D's byte order. -/
def nistInputBlock (inblock : Nat → BitVec 128) (i : Nat) : BitVec 128 := wordReversefields 8 (inblock i)

/-- `list_of_seq f n`: `f 0` to `f (n - 1)`. -/
def listOfSeq {α : Type} (f : Nat → α) (n : Nat) : List α := (List.range n).map f

/-- `htable_mem_4`'s six entries, in memory order. -/
def htable4 (h : BitVec 128) : List (BitVec 128) :=
  [byteswap128 (hPower h 0), karatsubaMid (hPower h 1) ++ karatsubaMid (hPower h 0), byteswap128 (hPower h 1),
   byteswap128 (hPower h 2), karatsubaMid (hPower h 3) ++ karatsubaMid (hPower h 2), byteswap128 (hPower h 3)]

/-- `htable_mem_8`'s twelve entries, in memory order. -/
def htable8 (h : BitVec 128) : List (BitVec 128) :=
  htable4 h ++
  [byteswap128 (hPower h 4), karatsubaMid (hPower h 5) ++ karatsubaMid (hPower h 4), byteswap128 (hPower h 5),
   byteswap128 (hPower h 6), karatsubaMid (hPower h 7) ++ karatsubaMid (hPower h 6), byteswap128 (hPower h 7)]

end rind.s2n

/-! ## FIPS 197's AES is Vale's, bytes reversed -/

namespace rind.s2n

open rind.vale

theorem wordReversefields8 (x : BitVec 128) : wordReversefields 8 x = reverseBytesQuad32 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [wordReversefields, BitVec.getLsbD_ofFnLE, getLsbD_reverseBytesQuad32 _ hi]
  simp only [hi, dite_true, ite_true]

theorem rev_xor (a b : BitVec 128) :
    reverseBytesQuad32 (a ^^^ b) = reverseBytesQuad32 a ^^^ reverseBytesQuad32 b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, getLsbD_reverseBytesQuad32 _ hi]

theorem rev_zero : reverseBytesQuad32 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_reverseBytesQuad32 _ hi]; simp

theorem getElem!_map_rev (ks : List (BitVec 128)) (i : Nat) :
    (ks.map reverseBytesQuad32)[i]! = reverseBytesQuad32 ks[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]?
  · exact rev_zero.symm
  · rfl


theorem getLsbD_wordJoinList16x8 (l : List (BitVec 8)) {k : Nat} (hk : k < 128) :
    (wordJoinList16x8 l).getLsbD k = l[15 - k / 8]!.getLsbD (k % 8) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ k = 8 * q + r :=
    ⟨k / 8, k % 8, Nat.mod_lt _ (by omega), (Nat.div_add_mod k 8).symm⟩
  have e1 : (8 * q + r) / 8 = q := by omega
  have e2 : (8 * q + r) % 8 = r := by omega
  rw [e1, e2]
  simp only [wordJoinList16x8, BitVec.getLsbD_append]
  have hq : q < 16 := by omega
  interval_cases q <;> simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> congr 1 <;> omega

theorem byte_wordJoinList16x8 (l : List (BitVec 8)) {i : Nat} (hi : i < 16) :
    byte (wordJoinList16x8 l) i = l[15 - i]! := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_byte _ _ hj, getLsbD_wordJoinList16x8 _ (by omega)]
  congr 2 <;> omega

theorem byte_rev (x : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (reverseBytesQuad32 x) i = x.extractLsb' (8 * (15 - i)) 8 := byte_reverseBytes x hi

/-! The tables, checked byte by byte. -/

/-- Whether `GF2`, `FFmul_02`, and `FFmul_03` agree with FIPS 197 on byte `n`. -/
def tablesAgree (n : Nat) : Bool :=
  let b := BitVec.ofNat 8 n
  aesSubByte joinedGf2 b == sboxTree b && ffmul02 b == xtime b && ffmul03 b == (xtime b ^^^ b)

theorem tablesAgree_all : (List.range 256).all tablesAgree = true := by decide +kernel

theorem tablesAgree_of (b : BitVec 8) : tablesAgree b.toNat = true := by
  have h := tablesAgree_all
  rw [List.all_eq_true] at h
  exact h b.toNat (List.mem_range.2 b.isLt)

theorem aesSubByte_eq (b : BitVec 8) : aesSubByte joinedGf2 b = sbox b := by
  have h := tablesAgree_of b
  simp only [tablesAgree, BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.1, sbox_eq_tree]

theorem ffmul02_eq (b : BitVec 8) : ffmul02 b = xtime b := by
  have h := tablesAgree_of b
  simp only [tablesAgree, BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem ffmul03_eq (b : BitVec 8) : ffmul03 b = xtime b ^^^ b := by
  have h := tablesAgree_of b
  simp only [tablesAgree, BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2


theorem rev_subBytes (s : BitVec 128) :
    reverseBytesQuad32 (fips197SubBytes s) = subBytes (reverseBytesQuad32 s) := by
  apply eq_of_byte_eq; intro i hi
  rw [byte_reverseBytes _ hi, fips197SubBytes, aesSubBytes, byte_wordJoinList16x8 _ (by omega),
    byte_subBytes _ hi, byte_reverseBytes _ hi, show 15 - (15 - i) = i by omega, getElem!_range_map _ hi,
    aesSubBytesSelect, aesSubByte_eq, byte, Nat.mul_comm]

theorem rev_shiftRows (s : BitVec 128) :
    reverseBytesQuad32 (fips197ShiftRows s) = shiftRows (reverseBytesQuad32 s) := by
  apply eq_of_byte_eq; intro i hi
  rw [byte_reverseBytes _ hi, fips197ShiftRows, byte_wordJoinList16x8 _ (by omega), byte_shiftRows _ hi,
    byte_reverseBytes _ (by omega)]
  interval_cases i <;> rfl

theorem rev_mixColumns (s : BitVec 128) :
    reverseBytesQuad32 (rind.s2n.fips197MixColumns s) = mixColumns (reverseBytesQuad32 s) := by
  rw [mixColumns_eq]
  apply eq_of_byte_eq; intro i hi
  rw [byte_reverseBytes _ hi, rind.s2n.fips197MixColumns, byte_wordJoinList16x8 _ (by omega),
    rind.vale.fips197MixColumns, byte_ofBytes _ hi]
  interval_cases i <;>
    simp (disch := omega) only [byte_rev, aesMixWord, ffmul02_eq, ffmul03_eq, Nat.reduceMul, Nat.reduceSub,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, List.getElem!_cons_succ, List.getElem!_cons_zero] <;>
    ac_rfl

theorem rev_round (s k : BitVec 128) :
    reverseBytesQuad32 (fips197Round s k) = evalRound (reverseBytesQuad32 s) (reverseBytesQuad32 k) := by
  rw [fips197Round, rev_xor, rev_mixColumns, rev_shiftRows, rev_subBytes, evalRound]

theorem rev_finalRound (s k : BitVec 128) :
    reverseBytesQuad32 (fips197FinalRound s k) =
      shiftRows (subBytes (reverseBytesQuad32 s)) ^^^ reverseBytesQuad32 k := by
  rw [fips197FinalRound, rev_xor, rev_shiftRows, rev_subBytes]

/-- `aes128_cipher`, bytes reversed, is Vale's AES-128 on the reversed round keys. -/
theorem aes128Cipher_eq (x : BitVec 128) (ks : List (BitVec 128)) :
    reverseBytesQuad32 (aes128Cipher x ks) =
      evalCipher .AES_128 (reverseBytesQuad32 x) (ks.map reverseBytesQuad32) := by
  simp only [aes128Cipher, evalCipher, nr, evalRounds, rev_finalRound, rev_round, rev_xor, getElem!_map_rev]

/-- `aes256_cipher`, bytes reversed, is Vale's AES-256 on the reversed round keys. -/
theorem aes256Cipher_eq (x : BitVec 128) (ks : List (BitVec 128)) :
    reverseBytesQuad32 (aes256Cipher x ks) =
      evalCipher .AES_256 (reverseBytesQuad32 x) (ks.map reverseBytesQuad32) := by
  simp only [aes256Cipher, evalCipher, nr, evalRounds, rev_finalRound, rev_round, rev_xor, getElem!_map_rev]

/-! ## The counter blocks -/

/-- A counter block is `ctr_block` of its high 96 bits and its low word. -/
theorem ctrBlock_split (j : BitVec 128) : ctrBlock (j.extractLsb' 32 96) (j.extractLsb' 0 32).toNat = j := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [ctrBlock, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : k < 32
  · simp [h]
  · simp [h, show k - 32 < 96 by omega, show 32 + (k - 32) = k by omega]

/-- `inc32` advances `ctr_block`'s counter. -/
theorem inc32_ctrBlock (nonce : BitVec 96) (c i : Nat) : inc32 (ctrBlock nonce c) i = ctrBlock nonce (i + c) := by
  have hhi : (ctrBlock nonce c).extractLsb' 32 96 = nonce := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, ctrBlock, BitVec.getLsbD_append,
      show ¬ 32 + k < 32 by omega, ite_false, show 32 + k - 32 = k by omega]
  have hlo : (ctrBlock nonce c).extractLsb' 0 32 = BitVec.ofNat 32 c := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, ctrBlock, BitVec.getLsbD_append,
      Nat.zero_add, ite_true]
  rw [inc32, hhi, hlo, ctrBlock, BitVec.ofNat_add, BitVec.add_comm]


/-! ## GHASH's product is Vale's -/

/-- A polynomial with no terms from `X ^ n` up. -/
def Below (p : P) (n : Nat) : Prop := ∀ j, n ≤ j → p.coeff j = 0

theorem below_toPoly {m : Nat} (x : BitVec m) : Below (toPoly x) m := fun j hj => by
  rw [coeff_toPoly, BitVec.getLsbD_of_ge x j hj]; rfl

theorem below_mono {p : P} {m n : Nat} (h : Below p m) (hmn : m ≤ n) : Below p n := fun j hj => h j (by omega)

theorem below_mul {a b : P} {na nb : Nat} (ha : Below a na) (hb : Below b nb) : Below (a * b) (na + nb - 1) := by
  intro k hk
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero; rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : na ≤ i
  · rw [ha i hi, zero_mul]
  · rw [hb j (by omega), mul_zero]

theorem below_add {a b : P} {n : Nat} (ha : Below a n) (hb : Below b n) : Below (a + b) n := fun j hj => by
  rw [Polynomial.coeff_add, ha j hj, hb j hj, add_zero]

theorem sum_ite_countP (g : Nat → Bool) (n : Nat) :
    (∑ i ∈ Finset.range n, if g i then (1 : ZMod 2) else 0) = ((List.range n).countP g : ZMod 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.countP_append]
    cases h : g n <;> simp [h]

theorem natCast_zmod2 (c : Nat) : (c : ZMod 2) = if c % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

theorem coeff_mul_toPoly {m n : Nat} (x : BitVec m) (y : BitVec n) (k : Nat) :
    (toPoly x * toPoly y).coeff k =
      ((List.range (k + 1)).countP (fun i => x.getLsbD i && y.getLsbD (k - i)) : ZMod 2) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← sum_ite_countP]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [coeff_toPoly]
  cases x.getLsbD i <;> cases y.getLsbD (k - i) <;> simp

/-- `word_pmul` is the product, when the product fits. -/
theorem toPoly_wordPmul {m n : Nat} (p : Nat) (x : BitVec m) (y : BitVec n) (h : Below (toPoly x * toPoly y) p) :
    toPoly (wordPmul p x y) = toPoly x * toPoly y := by
  ext k
  rw [coeff_toPoly, wordPmul, BitVec.getLsbD_ofFnLE]
  by_cases hk : k < p
  · rw [dite_eq_left hk, coeff_mul_toPoly, natCast_zmod2]
    simp
  · rw [dite_eq_right hk, h k (by omega)]; rfl

theorem toPoly_wordPmul_of {m n : Nat} (p : Nat) (x : BitVec m) (y : BitVec n) (hp : m + n ≤ p + 1) :
    toPoly (wordPmul p x y) = toPoly x * toPoly y :=
  toPoly_wordPmul p x y (below_mono (below_mul (below_toPoly x) (below_toPoly y)) (by omega))

theorem getLsbD_bitReflect128 (a : BitVec 128) {j : Nat} (hj : j < 128) :
    (bitReflect128 a).getLsbD j = a.getLsbD (127 - j) := by
  rw [bitReflect128, wordReversefields, BitVec.getLsbD_ofFnLE]
  simp only [hj, dite_true, ite_true]
  all_goals (congr 1; omega)

theorem toPoly_bitReflect128 (a : BitVec 128) : toPoly (bitReflect128 a) = reverse (toPoly a) 127 := by
  ext j
  rw [coeff_toPoly, coeff_reverse]
  by_cases hj : j < 128
  · rw [getLsbD_bitReflect128 _ hj, ite_eq_left (show j ≤ 127 by omega), coeff_toPoly]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), ite_eq_right (show ¬ j ≤ 127 by omega)]; rfl

theorem toPoly_0x87 : toPoly (0x87#256) = gf128ModulusLowTerms := by
  rw [gf128ModulusLowTerms]
  ext j
  simp only [coeff_toPoly, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]
  by_cases h : j < 8
  · interval_cases j <;> decide
  · rw [BitVec.getLsbD_ofNat, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (show 8 ≤ j by omega)))]
    simp [show j ≠ 0 by omega, show j ≠ 2 by omega, show j ≠ 7 by omega,
      show (1 : Nat) ≠ j by omega]

theorem toPoly_split256 (x : BitVec 256) :
    toPoly x = toPoly ((x.extractLsb' 0 128).setWidth 256) + X ^ 128 * toPoly (x >>> 128) := by
  ext j
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', coeff_toPoly, coeff_toPoly, coeff_toPoly]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases h : j < 128
  · simp [h, show ¬ 128 ≤ j by omega, show j < 256 by omega]
  · simp only [h, decide_false, Bool.false_and, Bool.and_false, show 128 ≤ j by omega, ite_true]
    rw [show 128 + (j - 128) = j by omega]
    simp

theorem toPoly_ghashReduce1 (x : BitVec 256) {n : Nat} (hx : Below (toPoly x) n) (hn : 128 ≤ n) (hn' : n ≤ 256) :
    toPoly (ghashReduce1 x) = toPoly x + gf128Modulus * toPoly (x >>> 128) ∧
      Below (toPoly (ghashReduce1 x)) (max 128 (n - 120)) := by
  have hhi : Below (toPoly (x >>> 128)) (n - 128) := fun j hj => by
    rw [coeff_toPoly, BitVec.getLsbD_ushiftRight]
    have := hx (128 + j) (by omega)
    rwa [coeff_toPoly] at this
  have hlow : Below gf128ModulusLowTerms 8 := by
    rw [← toPoly_0x87]
    intro j hj
    rw [coeff_toPoly, BitVec.getLsbD_ofNat, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) hj))]
    simp
  have hp : toPoly (wordPmul 256 (x >>> 128) (0x87#256)) = toPoly (x >>> 128) * gf128ModulusLowTerms := by
    rw [toPoly_wordPmul, toPoly_0x87]
    rw [toPoly_0x87]
    exact below_mono (below_mul (below_mono hhi (show n - 128 ≤ 128 by omega)) hlow) (by norm_num)
  have he : toPoly (ghashReduce1 x) = toPoly ((x.extractLsb' 0 128).setWidth 256) +
      toPoly (x >>> 128) * gf128ModulusLowTerms := by
    rw [ghashReduce1, toPoly_xor, hp]
  refine ⟨?_, ?_⟩
  · have hs := toPoly_split256 x
    rw [he]
    generalize toPoly ((x.extractLsb' 0 128).setWidth 256) = L at hs ⊢
    generalize toPoly (x >>> 128) = H at hs ⊢
    rw [hs]
    unfold gf128Modulus
    linear_combination (-(X ^ 128 * H)) * two_eq_zero_P
  · rw [he]
    refine below_add (below_mono (fun j hj => ?_) (le_max_left _ _)) ?_
    · rw [coeff_toPoly, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']; simp [show ¬ j < 128 by omega]
    · exact below_mono (below_mul hhi hlow) (by omega)

theorem toPoly_ghashReduce (x : BitVec 256) : toPoly (ghashReduce x) = toPoly x %ₘ gf128Modulus := by
  obtain ⟨h1, b1⟩ := toPoly_ghashReduce1 x (below_toPoly x) (by norm_num) le_rfl
  obtain ⟨h2, b2⟩ := toPoly_ghashReduce1 (ghashReduce1 x) b1 (by norm_num) (by norm_num)
  have hs : toPoly (ghashReduce x) = toPoly (ghashReduce1 (ghashReduce1 x)) := by
    ext j
    rw [ghashReduce, coeff_toPoly, coeff_toPoly, BitVec.getLsbD_setWidth]
    by_cases hj : j < 128
    · simp [hj]
    · have := b2 j (by norm_num; omega)
      rw [coeff_toPoly] at this
      have hb : (ghashReduce1 (ghashReduce1 x)).getLsbD j = false := by
        by_contra hc; simp [hc] at this
      simp [hj, hb]
  have hd := Polynomial.modByMonic_add_div (toPoly x) gf128Modulus
  apply eq_of_dvd (small_toPoly _) (small_mod _)
  refine ⟨toPoly (x >>> 128) + toPoly (ghashReduce1 x >>> 128) + toPoly x /ₘ gf128Modulus, ?_⟩
  rw [hs, h2, h1]
  linear_combination (-1 : P) * hd

/-- `nist_dot` is Vale's `gf128_mul_rev`. -/
theorem toPoly_nistDot (a b : BitVec 128) : toPoly (nistDot a b) = gf128MulRev (toPoly a) (toPoly b) := by
  rw [nistDot, toPoly_bitReflect128, toPoly_ghashReduce, toPoly_wordPmul_of 256 _ _ (by norm_num),
    toPoly_bitReflect128, toPoly_bitReflect128]
  rfl

/-- `nist_ghash` is Vale's GHASH. -/
theorem toPoly_nistGhash (h : BitVec 128) : ∀ (acc : BitVec 128) (xs : List (BitVec 128)),
    toPoly (nistGhash h acc xs) = ghashPoly (toPoly h) (toPoly acc) (xs.map toPoly)
  | acc, [] => by rw [nistGhash, List.map_nil, ghashPoly_nil]
  | acc, x :: xs => by
    rw [nistGhash, toPoly_nistGhash h _ xs, List.map_cons, ghashPoly_cons, toPoly_nistDot, toPoly_xor]

/-! ## POLYVAL's product is rind's, so the key table is -/

theorem toPoly_halves' (x : BitVec 128) :
    toPoly x = toPoly (x.extractLsb' 0 64) + X ^ 64 * toPoly (x.extractLsb' 64 64) := by
  have := toPoly_halves x
  unfold lo hi at this
  exact this

theorem toPoly_quarters (t : BitVec 256) :
    toPoly t = toPoly (t.extractLsb' 0 64) + X ^ 64 * toPoly (t.extractLsb' 64 64) +
      X ^ 128 * toPoly (t.extractLsb' 128 64) + X ^ 192 * toPoly (t.extractLsb' 192 64) := by
  ext j
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', coeff_toPoly, BitVec.getLsbD_extractLsb']
  rcases (by omega : j < 64 ∨ (64 ≤ j ∧ j < 128) ∨ (128 ≤ j ∧ j < 192) ∨ (192 ≤ j ∧ j < 256) ∨ 256 ≤ j) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · simp [h, show ¬ 64 ≤ j by omega, show ¬ 128 ≤ j by omega, show ¬ 192 ≤ j by omega]
  · simp [show ¬ j < 64 by omega, h1, show j - 64 < 64 by omega, show ¬ 128 ≤ j by omega,
      show ¬ 192 ≤ j by omega, show 64 + (j - 64) = j by omega]
  · simp [show ¬ j < 64 by omega, show 64 ≤ j by omega, show ¬ j - 64 < 64 by omega, h1,
      show j - 128 < 64 by omega, show ¬ 192 ≤ j by omega, show 128 + (j - 128) = j by omega]
  · simp [show ¬ j < 64 by omega, show 64 ≤ j by omega, show ¬ j - 64 < 64 by omega, show 128 ≤ j by omega,
      show ¬ j - 128 < 64 by omega, h1, show j - 192 < 64 by omega, show 192 + (j - 192) = j by omega]
  · simp [show ¬ j < 64 by omega, show 64 ≤ j by omega, show ¬ j - 64 < 64 by omega, show 128 ≤ j by omega,
      show ¬ j - 128 < 64 by omega, show 192 ≤ j by omega, show ¬ j - 192 < 64 by omega,
      BitVec.getLsbD_of_ge t j h]

/-- `polyval_reduce_prop3` is a Montgomery reduction by the reflected modulus. -/
theorem polyvalReduceProp3_spec (t : BitVec 256) :
    ∃ S, toPoly t + X ^ 128 * toPoly (polyvalReduceProp3 t) = Q * S := by
  have hw : toPoly (0xC200000000000000#64) = X ^ 63 + X ^ 62 + X ^ 57 := toPoly_c64
  have hwa := toPoly_halves' (wordPmul 128 (t.extractLsb' 0 64) (0xC200000000000000#64))
  rw [toPoly_wordPmul_of 128 _ _ (by norm_num), hw] at hwa
  have hwv := toPoly_halves' (wordPmul 128 (t.extractLsb' 64 64 ^^^
    (wordPmul 128 (t.extractLsb' 0 64) (0xC200000000000000#64)).extractLsb' 0 64) (0xC200000000000000#64))
  rw [toPoly_wordPmul_of 128 _ _ (by norm_num), hw, toPoly_xor] at hwv
  refine ⟨toPoly (t.extractLsb' 0 64) + X ^ 64 * toPoly (t.extractLsb' 64 64 ^^^
    (wordPmul 128 (t.extractLsb' 0 64) (0xC200000000000000#64)).extractLsb' 0 64), ?_⟩
  rw [toPoly_quarters t]
  simp only [polyvalReduceProp3, toPoly_append, toPoly_xor]
  unfold Q
  linear_combination (-X ^ 64 : P) * hwa + (-X ^ 128 : P) * hwv +
    (X ^ 128 * toPoly (t.extractLsb' 128 64) + X ^ 192 * toPoly (t.extractLsb' 192 64) -
      X ^ 64 * toPoly ((wordPmul 128 (t.extractLsb' 0 64) (0xC200000000000000#64)).extractLsb' 0 64)) *
      two_eq_zero_P

/-- `polyval_dot` is rind's PMULL product. -/
theorem polyvalDot_eq (a b : BitVec 128) : polyvalDot a b = mulModel a b := by
  apply toPoly_inj
  obtain ⟨S, hS⟩ := mulModel_spec a b
  obtain ⟨S', hS'⟩ := polyvalReduceProp3_spec (wordPmul 256 a b)
  rw [toPoly_wordPmul_of 256 _ _ (by norm_num)] at hS'
  rw [polyvalDot]
  exact mont_unique hS' hS (small_toPoly _) (small_toPoly _)

theorem ghashTwist_eq (h : BitVec 128) : ghashTwist h = skBV h := by
  unfold ghashTwist skBV polyvalTwistConst
  split <;> simp_all

/-- `h_power` of the twisted key is the shifted power of the key Vale's
`gf128_power` names. -/
theorem toPoly_hPower (H : BitVec 128) : ∀ i,
    toPoly (hPower (ghashTwist H) i) = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly H) (i + 1))
  | 0 => by rw [hPower, ghashTwist_eq, toPoly_skBV]; rfl
  | i + 1 => by
    rw [hPower, polyvalDot_eq, mul_shiftKey1 _ _ (small_gPower _ (small_toPoly H) (i + 1)) (small_toPoly H) _ _
      (toPoly_hPower H i) (by rw [ghashTwist_eq, toPoly_skBV]),
      gPower_succ (toPoly H) (n := i + 1) (by omega), mulRev_comm (toPoly H)]

/-! ## The keystream -/

/-- The kernels' keystream block `i` from the counter block `j` is Vale's. -/
theorem aesCtrBlock_eq (enc : BitVec 128 → List (BitVec 128) → BitVec 128) (alg : Algorithm)
    (rk : List (BitVec 128)) (kw : List (BitVec 32))
    (henc : ∀ x, reverseBytesQuad32 (enc x rk) = evalCipher alg (reverseBytesQuad32 x) (rk.map reverseBytesQuad32))
    (hrk : rk.map reverseBytesQuad32 = keyToRoundKeys alg kw) (j : BitVec 128) (i : Nat) :
    aesCtrBlock enc (j.extractLsb' 0 32).toNat (j.extractLsb' 32 96) rk i =
      aesEncrypt alg kw (reverseBytesQuad32 (inc32 j i)) := by
  rw [aesCtrBlock, wordReversefields8, henc, hrk, ← inc32_ctrBlock, ctrBlock_split, aesEncrypt]

end rind.s2n
