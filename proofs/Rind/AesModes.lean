import Rind.Aes
open Aeneas Aeneas.Std

/-!
# SP 800-38A's CTR and CBC modes, on bytes

The modes rind's `cipher::AesCtr`, `AesCbcEncryptingKey`, and
`AesCbcDecryptingKey` compute, over FIPS 197's AES on bytes, `aesBlock` and
`aesBlockDecrypt`, with CBC's PKCS#7 padding (RFC 5652, section 6.3). CTR's
counter blocks are SP 800-38A's standard incrementing function (appendix
B.1): the block read as a big-endian integer, whose low `m` bits count up
modulo `2^m` and whose other bits stay fixed. Nothing here is a target's.
-/

namespace rind.vale

/-- The 16 bytes of the 128-bit big-endian integer `n`. -/
def be128 (n : Nat) : List (BitVec 8) :=
  (List.range 16).map fun i => BitVec.ofNat 8 (n / 256 ^ (15 - i))

/-- The 4 bytes of the 32-bit big-endian integer `n`. -/
def be32 (n : Nat) : List (BitVec 8) := (be128 n).drop 12

/-- The bytes `l` read as a big-endian integer. -/
def ofBe (l : List (BitVec 8)) : Nat :=
  l.foldl (fun a b => 256 * a + b.toNat) 0

/-- SP 800-38A's counter block `j` after `t0`, incrementing its low `m` bits. -/
def ctrBlock (m t0 j : Nat) : Nat :=
  t0 / 2 ^ m * 2 ^ m + (t0 % 2 ^ m + j) % 2 ^ m

/-- SP 800-38A's CTR mode: `data` XORed with the cipher of the counter blocks
from the 16 bytes `t0`, whose low `m` bits count. A final partial block uses
the first bytes of its keystream block. -/
def aesCtr (alg : Algorithm) (key : List (BitVec 8)) (m : Nat) (t0 data : List (BitVec 8)) :
    List (BitVec 8) :=
  (List.range data.length).map fun i =>
    data[i]! ^^^ (aesBlock alg key (be128 (ctrBlock m (ofBe t0) (i / 16))))[i % 16]!

/-- SP 800-38A's CBC encryption of the whole blocks of `p`, the first chained
from `iv`. -/
def cbcEncrypt (alg : Algorithm) (key iv p : List (BitVec 8)) : List (BitVec 8) :=
  if p.length < 16 then [] else
    let c := aesBlock alg key (List.zipWith (· ^^^ ·) (p.take 16) iv)
    c ++ cbcEncrypt alg key c (p.drop 16)
termination_by p.length
decreasing_by simp; omega

/-- SP 800-38A's CBC decryption of the whole blocks of `c`, the first chained
from `iv`. -/
def cbcDecrypt (alg : Algorithm) (key iv c : List (BitVec 8)) : List (BitVec 8) :=
  if c.length < 16 then [] else
    List.zipWith (· ^^^ ·) (aesBlockDecrypt alg key (c.take 16)) iv ++
      cbcDecrypt alg key (c.take 16) (c.drop 16)
termination_by c.length
decreasing_by simp; omega

/-- PKCS#7 padding to a whole number of 16-byte blocks: from one to 16 bytes,
each the count. -/
def pkcs7Pad (p : List (BitVec 8)) : List (BitVec 8) :=
  p ++ List.replicate (16 - p.length % 16) (BitVec.ofNat 8 (16 - p.length % 16))

/-- The message PKCS#7 padded to the nonempty `d`, if its last byte `n` is
from 1 to 16 and its last `n` bytes are each `n`. -/
def pkcs7Unpad (d : List (BitVec 8)) : Option (List (BitVec 8)) :=
  match d.getLast? with
  | none => none
  | some last =>
    let n := last.toNat
    if 1 ≤ n ∧ n ≤ 16 ∧ n ≤ d.length ∧ ∀ b ∈ d.drop (d.length - n), b = last then
      some (d.take (d.length - n))
    else none

-- SP 800-38A's appendix F: F.2.1 CBC-AES128.Encrypt and F.5.1
-- CTR-AES128.Encrypt, their first two blocks.
private def hex (s : String) : List (BitVec 8) :=
  let d (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List (BitVec 8)
    | a :: b :: rest => BitVec.ofNat 8 (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

#guard cbcEncrypt .AES_128 (hex "2b7e151628aed2a6abf7158809cf4f3c") (hex "000102030405060708090a0b0c0d0e0f")
  (hex "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51") ==
  hex "7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b2"
#guard cbcDecrypt .AES_128 (hex "2b7e151628aed2a6abf7158809cf4f3c") (hex "000102030405060708090a0b0c0d0e0f")
  (hex "7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b2") ==
  hex "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51"
#guard aesCtr .AES_128 (hex "2b7e151628aed2a6abf7158809cf4f3c") 128 (hex "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")
  (hex "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51") ==
  hex "874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff"
-- The same, its counter wrapping in its low 8 bits: the second block's counter
-- is `...fe00`, so it differs from the 128-bit count's `...ff00`.
#guard aesCtr .AES_128 (hex "2b7e151628aed2a6abf7158809cf4f3c") 8 (hex "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")
  (hex "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51") ==
  hex "874d6191b620e3261bef6864990db6cee3256531c56fd498e4670c36587faba6"
#guard pkcs7Unpad (pkcs7Pad (hex "0102")) == some (hex "0102")
#guard (pkcs7Pad []).length == 16
#guard pkcs7Unpad (hex "0102030405060708090a0b0c0d0e0f00") == none

end rind.vale
