module

/-!
# Shared vector AES and binary polynomial values

**Trusted.** FIPS 197's AES transformations and the unreduced 64×64 binary
polynomial product. These definitions are shared by the Arm and Power
instruction models, whose wrappers supply their different lane and round
orderings. Bytes here are numbered from the least significant end; AES
state byte `r + 4c` is FIPS 197's `s[r,c]`.

Extracted without changing the definitions from `TCB/AArch64/Simd.lean`.
-/

@[expose] public section

namespace VG.VectorCrypto

/-- `Elem[x, e, 8]`: byte `e` of `x`. -/
def vbyte (x : BitVec 128) (e : Nat) : BitVec 8 := x.extractLsb' (8 * e) 8

/-- The vector whose byte `e` is `f e`. -/
def ofVBytes (f : Nat → BitVec 8) : BitVec 128 :=
  f 15 ++ f 14 ++ f 13 ++ f 12 ++ f 11 ++ f 10 ++ f 9 ++ f 8 ++
    f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-! ## AES (DDI 0487, J1, "shared/functions/crypto")

The pseudocode's `AESSubBytes`, `AESInvSubBytes`, `AESShiftRows`,
`AESInvShiftRows`, `AESMixColumns` and `AESInvMixColumns` are the
transformations of the AES standard, FIPS 197 (§5), on the state whose
`s[r, c]` (FIPS 197 §3.4) is byte `r + 4c` of the 128-bit operand. They are
defined here from FIPS 197 rather than by the pseudocode's tables (the
S-boxes are FIPS 197's), and `VerifiedGarbageTest/AArch64Simd.lean` checks
them against the instructions. -/

/-- FIPS 197 §4.2, `XTIMES(b)`: `b` shifted left by one bit, XOR `{1b}` if the
bit shifted out was 1. -/
def aesXtimes (b : BitVec 8) : BitVec 8 := (b <<< 1) ^^^ (if b.msb then 0x1b else 0)

/-- FIPS 197 §4.2, the product `b • c` in GF(2⁸): the XOR of `XTIMES` applied
`i` times to `c`, for each bit `i` of `b` that is 1. -/
def aesMul (b c : BitVec 8) : BitVec 8 :=
  (List.range 8).foldl (fun acc i => if b.getLsbD i then acc ^^^ Nat.repeat aesXtimes i c else acc) 0

/-- FIPS 197 §4.4, the inverse `b⁻¹ = b²⁵⁴` in GF(2⁸), with `{00} ↦ {00}`:
`b^254 = b^2 • b^4 • … • b^128`, by repeated squaring. -/
def aesInv (b : BitVec 8) : BitVec 8 :=
  ((List.range 7).foldl (fun (acc, sq) _ => let sq := aesMul sq sq; (aesMul acc sq, sq))
    ((1 : BitVec 8), b)).1

/-- The byte whose bit `i` is `f i`. -/
def ofBits8 (f : Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range 8).foldl (fun acc i => acc + if f i then 2 ^ i else 0) 0)

/-- FIPS 197 §5.1.1, the S-box: `b ↦ b⁻¹`, then `b'ᵢ = bᵢ ⊕ b₍ᵢ₊₄₎ mod 8 ⊕
b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₆₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ cᵢ` with `c = {63}`. -/
def aesSbox (b : BitVec 8) : BitVec 8 :=
  let b := aesInv b
  let c : BitVec 8 := 0x63
  ofBits8 fun i => b.getLsbD i ^^ b.getLsbD ((i + 4) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^
    b.getLsbD ((i + 6) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ c.getLsbD i

/-- FIPS 197 §5.3.2, the inverse S-box: the inverse of the affine
transformation, `b'ᵢ = b₍ᵢ₊₂₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ dᵢ` with
`d = {05}`, then `b ↦ b⁻¹`. -/
def aesInvSbox (b : BitVec 8) : BitVec 8 :=
  let d : BitVec 8 := 0x05
  aesInv (ofBits8 fun i =>
    b.getLsbD ((i + 2) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ d.getLsbD i)

/-- `AESSubBytes` and `AESInvSubBytes`: `f` applied to every byte. -/
def aesMapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => f (vbyte x i)

/-- `AESShiftRows`, FIPS 197 §5.1.2: `s'[r, c] = s[r, (c + r) mod 4]`. -/
def aesShiftRows (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => vbyte x (i % 4 + 4 * ((i / 4 + i % 4) % 4))

/-- `AESInvShiftRows`, FIPS 197 §5.3.1: `s'[r, c] = s[r, (c − r) mod 4]`. -/
def aesInvShiftRows (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => vbyte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4))

/-- FIPS 197 §5.1.3 `MIXCOLUMNS` (with `m = [{02}, {03}, {01}, {01}]`) and
§5.3.3 `INVMIXCOLUMNS` (with `m = [{0e}, {0b}, {0d}, {09}]`):
`s'[r, c] = m₀ • s[r, c] ⊕ m₁ • s[r + 1, c] ⊕ m₂ • s[r + 2, c] ⊕ m₃ • s[r + 3, c]`,
rows modulo 4. -/
def aesMixWith (m₀ m₁ m₂ m₃ : BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i =>
    let a (k : Nat) : BitVec 8 := vbyte x ((i % 4 + k) % 4 + 4 * (i / 4))
    aesMul m₀ (a 0) ^^^ aesMul m₁ (a 1) ^^^ aesMul m₂ (a 2) ^^^ aesMul m₃ (a 3)

/-- `AESMixColumns`. -/
def aesMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x02 0x03 0x01 0x01

/-- `AESInvMixColumns`. -/
def aesInvMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x0e 0x0b 0x0d 0x09

/-! ## Polynomial multiplication -/

/-- `PolynomialMult(op1, op2)` for 64-bit operands: `result = Zeros(128);
extended_op2 = ZeroExtend(op2, 128); for i = 0 to 63: if op1<i> == '1'
then result = result EOR LSL(extended_op2, i)`. -/
def polyMul (a b : BitVec 64) : BitVec 128 :=
  (List.range 64).foldl (fun acc i => if a.getLsbD i then acc ^^^ (b.setWidth 128 <<< i) else acc) 0

end VG.VectorCrypto
