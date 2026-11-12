module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

/-!
# What rind's SHA-512 computes

FIPS 180-4's SHA-512, SHA-384, and SHA-512/256 of a message of bytes, as
cryptol-specs' `Primitive::Keyless::Hash::SHA` defines them at the revision
aws-lc-verification's proofs import (fba861b8): the message padded, parsed into
128-byte blocks of sixteen big-endian words, each compressed into the chaining
value in turn from the initial value, which is then written out big-endian and
truncated. Its compression function, `processBlock_Common`, is FIPS 180-4
section 6.4.2's, transliterated as `fips512.compressBlock`:
aws-lc-verification's theorems, restated in `Rind.<Arch>.AwsLc`, and rind's
HOL Light proof, restated in `Rind.Aarch64.AwsLc` through `Rind.S2nSha512`, are
what tie it to rind's routines.
-/

namespace rind.spec

/-- The word that eight big-endian bytes encode. -/
def beWord (b : List U8) : U64 :=
  ⟨(BitVec.fromBEBytes (b.map (·.bv))).setWidth 64⟩

/-- The bytes `u64::to_be_bytes` writes. -/
def beBytes (w : U64) : List U8 :=
  w.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)

/-- A 128-byte block's sixteen big-endian words: Cryptol's
`split (join block) : [16][64]`. -/
def blockWords (block : List U8) : List U64 :=
  (List.range 16).map fun i => beWord ((block.drop (8 * i)).take 8)

namespace fips512

/-- FIPS 180-4 section 4.2.3's constants. -/
def K : List (BitVec 64) :=
  [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- FIPS 180-4 section 4.1.3's functions. -/
def ch (x y z : BitVec 64) : BitVec 64 := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : BitVec 64) : BitVec 64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bigSigma0 (x : BitVec 64) : BitVec 64 := x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39
def bigSigma1 (x : BitVec 64) : BitVec 64 := x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41
def smallSigma0 (x : BitVec 64) : BitVec 64 := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> 7
def smallSigma1 (x : BitVec 64) : BitVec 64 := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> 6

/-- FIPS 180-4 section 6.4.2 step 1: the message schedule from a block's 16
words, each further word from the four 2, 7, 15, and 16 before it. -/
def schedule (M : List (BitVec 64)) : List (BitVec 64) :=
  (List.range 64).foldl (fun W t => W ++ [smallSigma1 W[t + 14]! + W[t + 9]! + smallSigma0 W[t + 1]! + W[t]!]) M

/-- FIPS 180-4 section 6.4.2 steps 2 to 4: hash value `H` after the block of
words `M`. -/
def compressBlock (H M : List (BitVec 64)) : List (BitVec 64) :=
  let W := schedule M
  let round := fun (s : List (BitVec 64)) t =>
    let T1 := s[7]! + bigSigma1 s[4]! + ch s[4]! s[5]! s[6]! + K[t]! + W[t]!
    let T2 := bigSigma0 s[0]! + maj s[0]! s[1]! s[2]!
    [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]
  List.zipWith (· + ·) ((List.range 80).foldl round H) H

end fips512

/-- SHA-512's compression function, of the eight-word chaining value and a
block's sixteen words: cryptol-specs' `processBlock_Common`, defined in
`Primitive/Keyless/Hash/SHA.cry` at
https://github.com/GaloisInc/cryptol-specs/blob/fba861b858fc62e6f77e7bc033d81eff6c0af9df/Primitive/Keyless/Hash/SHA.cry#L65
with `SHA512.cry`'s constants and sigma functions, which is FIPS 180-4
section 6.4.2's, `fips512.compressBlock`. Irreducible, so that unification
never unfolds its 80 rounds. -/
@[irreducible]
def processBlock (h w : List U64) : List U64 :=
  (fips512.compressBlock (h.map (·.bv)) (w.map (·.bv))).map (@UScalar.mk UScalarTy.U64)

/-- The chaining value `h` takes after each 128-byte block of `bytes` in
turn: cryptol-specs' `processBlocks h bytes 0 (len / 128)` for at least one
block, which processes blocks from index 0 until `num * 128`, and the identity
for none. -/
def compress (h : List U64) (bytes : List U8) : List U64 :=
  if 128 ≤ bytes.length then
    compress (processBlock h (blockWords (bytes.take 128))) (bytes.drop 128)
  else h
termination_by bytes.length

/-- FIPS 180-4 5.1.2's padding of a message of bytes: a one bit, as the byte
0x80, then the fewest zeros that end it 128 bits short of a whole block, then
its length in bits as 128 big-endian bits. Cryptol's `pad`, for a message of
fewer than 2^125 bytes, whose length in bits fits. -/
def sha512Pad (m : List U8) : List U8 :=
  m ++ 0x80#u8 :: List.replicate ((239 - m.length % 128) % 128) 0#u8 ++
    (BitVec.ofNat 128 (8 * m.length)).toBEBytes.map (@UScalar.mk UScalarTy.U8)

/-- SHA-512's initial value, `SHA512.cry`'s `H0`. -/
def sha512Iv : List U64 :=
  [0x6a09e667f3bcc908#u64, 0xbb67ae8584caa73b#u64, 0x3c6ef372fe94f82b#u64, 0xa54ff53a5f1d36f1#u64,
   0x510e527fade682d1#u64, 0x9b05688c2b3e6c1f#u64, 0x1f83d9abfb41bd6b#u64, 0x5be0cd19137e2179#u64]

/-- SHA-384's initial value, `SHA384.cry`'s `H0`. -/
def sha384Iv : List U64 :=
  [0xcbbb9d5dc1059ed8#u64, 0x629a292a367cd507#u64, 0x9159015a3070dd17#u64, 0x152fecd8f70e5939#u64,
   0x67332667ffc00b31#u64, 0x8eb44a8768581511#u64, 0xdb0c2e0d64f98fa7#u64, 0x47b5481dbefa4fa4#u64]

/-- SHA-512/256's initial value, `SHA512_256.cry`'s `H0`. -/
def sha512_256Iv : List U64 :=
  [0x22312194fc2bf72c#u64, 0x9f555fa3c84c64c2#u64, 0x2393b86b6f53b151#u64, 0x963877195940eabd#u64,
   0x96283ee2a88effe3#u64, 0xbe5e1e2553863992#u64, 0x2b0199fc2c85b8aa#u64, 0x0eb72ddc81c52ca2#u64]

/-- The SHA-512 family's chaining value after a message, from initial value
`iv`, written out big-endian: Cryptol's `join (SHA_2_Common' ...)`. -/
def sha512Words (iv : List U64) (m : List U8) : List U8 :=
  (compress iv (sha512Pad m)).flatMap beBytes

/-- SHA-512, Cryptol's `SHA512::sha` on a message of bytes. -/
def sha512 (m : List U8) : List U8 := sha512Words sha512Iv m

/-- SHA-384, Cryptol's `SHA384::sha`: the first 48 bytes from its own
initial value. -/
def sha384 (m : List U8) : List U8 := (sha512Words sha384Iv m).take 48

/-- SHA-512/256, Cryptol's `SHA512_256::sha`: the first 32 bytes from its own
initial value. -/
def sha512_256 (m : List U8) : List U8 := (sha512Words sha512_256Iv m).take 32

end rind.spec
