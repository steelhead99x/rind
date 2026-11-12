module
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Basic
public import Aeneas
@[expose] public section

/-!
# Vale's AES-GCM spec

What HACL*'s Vale states its AES-GCM routines compute, and the key and GHASH
key layout their preconditions require, transliterated from `vale/specs` and
`vale/code/crypto/aes` at HACL* f557259007db9933442dde10aa995c1b00bd3446,
which `admin/import-hacl` imports the routines from:

- `Vale.AES.AES_s` and `Vale.AES.AES_common_s`: AES's key expansion and cipher;
- `Vale.Math.Poly2_s`, `Vale.AES.GF128_s`, `Vale.AES.GF128`, and
  `Vale.AES.OptPublic`: GF(2^128) and the GHASH key powers `hkeys_reqs_pub`;
- `Vale.Def.Types_s`: how bytes, words, and `quad32`s convert.

Vale leaves AES's round functions assumed (`assume val`): `sub_bytes`,
`sub_word`, `shift_rows_LE`, `mix_columns_LE`, and `rot_word_LE`. They are
FIPS 197's here, `sbox` and `mixColumns` opaque, so they are the functions the
AES-NI instructions compute in `Rind.X86_64.Simd`. `gcm_encrypt_LE`,
`gcm_decrypt_LE`, and `compute_iv_BE` are opaque: no proof looks inside them.
-/

namespace rind.vale

open Polynomial

/-! ## Words and bytes, `Vale.Def.Types_s` -/

/-- A `quad32`, `Mkfour lo0 lo1 hi2 hi3`, as the number
`lo0 + 2^32 lo1 + 2^64 hi2 + 2^96 hi3`. -/
abbrev Quad32 := BitVec 128

/-- `le_bytes_to_quad32`: 16 bytes, least significant first. -/
def leBytesToQuad32 (b : List (BitVec 8)) : Quad32 := (BitVec.fromLEBytes b).setWidth 128

/-- `le_quad32_to_bytes`: a `quad32`'s 16 bytes, least significant first. -/
def leQuad32ToBytes (q : Quad32) : List (BitVec 8) :=
  (List.range 16).map fun i => q.extractLsb' (8 * i) 8

/-- `le_seq_quad32_to_bytes`. -/
def leSeqQuad32ToBytes (qs : List Quad32) : List (BitVec 8) := qs.flatMap leQuad32ToBytes

/-- `reverse_bytes_quad32`: the bytes in the other order. -/
def reverseBytesQuad32 (q : Quad32) : Quad32 := leBytesToQuad32 (leQuad32ToBytes q).reverse

/-- `seq_nat8_to_seq_nat32_LE`: each 4 bytes, least significant first, as a word. -/
def seqNat8ToSeqNat32LE (b : List (BitVec 8)) : List (BitVec 32) :=
  (List.range (b.length / 4)).map fun i => (BitVec.fromLEBytes ((b.drop (4 * i)).take 4)).setWidth 32

/-- `seq_nat32_to_seq_nat8_LE`: each word as its 4 bytes, least significant first. -/
def seqNat32ToSeqNat8LE (w : List (BitVec 32)) : List (BitVec 8) :=
  w.flatMap fun x => (List.range 4).map fun i => x.extractLsb' (8 * i) 8

/-! ## AES, `Vale.AES.AES_s` -/

/-- `algorithm`. -/
inductive Algorithm where
  | AES_128
  | AES_192
  | AES_256
deriving DecidableEq

/-- `nk`: the key's words. -/
def nk : Algorithm → Nat
  | .AES_128 => 4
  | .AES_192 => 6
  | .AES_256 => 8

/-- `nr`: the rounds. -/
def nr : Algorithm → Nat
  | .AES_128 => 10
  | .AES_192 => 12
  | .AES_256 => 14

/-- `nb`: the block's words. -/
def nb : Nat := 4

/-- `aes_rcon`. -/
def aesRcon (i : Nat) : BitVec 32 :=
  if i = 0 then 0x01 else if i = 1 then 0x02 else if i = 2 then 0x04 else if i = 3 then 0x08 else
  if i = 4 then 0x10 else if i = 5 then 0x20 else if i = 6 then 0x40 else if i = 7 then 0x80 else
  if i = 8 then 0x1b else 0x36

/-- A `quad32` from its 16 bytes, least significant first. -/
def ofBytes (f : Nat → BitVec 8) : Quad32 := leBytesToQuad32 ((List.range 16).map f)

/-- Byte `i` of a `quad32`, least significant first. -/
def byte (q : Quad32) (i : Nat) : BitVec 8 := q.extractLsb' (8 * i) 8

/-- FIPS 197's `xtime` (section 4.2.1): multiplication by `x` in its field. -/
def xtime (b : BitVec 8) : BitVec 8 := b <<< 1 ^^^ if b.msb then 0x1b else 0

/-- FIPS 197's product in its field (section 4.2), by repeated `xtime`. -/
def gfMul (a b : BitVec 8) : BitVec 8 :=
  ((List.range 8).foldl (fun (p, x) i => (if b.getLsbD i then p ^^^ x else p, xtime x)) (0, a)).1

/-- FIPS 197's S-box (section 5.1.1): the field inverse, `b ^ 254`, then the
affine transformation. -/
def fips197Sbox (b : BitVec 8) : BitVec 8 :=
  let i := (List.range 254).foldl (fun p _ => gfMul p b) 1
  i ^^^ i.rotateLeft 1 ^^^ i.rotateLeft 2 ^^^ i.rotateLeft 3 ^^^ i.rotateLeft 4 ^^^ 0x63

/-- FIPS 197's `MixColumns` (section 5.1.3), row `r` of column `c` being byte `r + 4c`. -/
def fips197MixColumns (q : Quad32) : Quad32 := ofBytes fun i =>
  let a k := byte q (i / 4 * 4 + (i % 4 + k) % 4)
  xtime (a 0) ^^^ xtime (a 1) ^^^ a 1 ^^^ a 2 ^^^ a 3

/-- FIPS 197's S-box, opaque so that no proof looks inside its table; Vale's
spec assumes it. `fips197Sbox` is what Lean runs, so `admin/prove` can test
the AES instruction models that call it. -/
opaque sbox : BitVec 8 → BitVec 8 := fips197Sbox

/-- FIPS 197's `MixColumns` on a state laid out as a `quad32`'s bytes, least
significant first, column by column: Vale's `mix_columns_LE`, opaque as its
spec assumes it. `fips197MixColumns` is what Lean runs. -/
opaque mixColumns : Quad32 → Quad32 := fips197MixColumns

/-- `sub_bytes`: the S-box on each byte. -/
def subBytes (q : Quad32) : Quad32 := ofBytes fun i => sbox (byte q i)

/-- `sub_word`: the S-box on each byte. -/
def subWord (w : BitVec 32) : BitVec 32 :=
  sbox (w.extractLsb' 24 8) ++ sbox (w.extractLsb' 16 8) ++ sbox (w.extractLsb' 8 8) ++
    sbox (w.extractLsb' 0 8)

/-- `rot_word_LE`: FIPS 197's `RotWord`, `[a0, a1, a2, a3]` to `[a1, a2, a3, a0]`,
on a word whose least significant byte is `a0`. -/
def rotWord (w : BitVec 32) : BitVec 32 := w.rotateRight 8

/-- `shift_rows_LE`: FIPS 197's `ShiftRows`, row `r` of column `c` being byte
`r + 4c`, which takes row `r` of column `c + r`. -/
def shiftRows (q : Quad32) : Quad32 := ofBytes fun i => byte q (i % 4 + 4 * ((i / 4 + i % 4) % 4))

/-- `Mkfour w0 w1 w2 w3`. -/
def mkfour (w0 w1 w2 w3 : BitVec 32) : Quad32 := w3 ++ w2 ++ w1 ++ w0

/-- `expand_key_def`: the first `size` words of the key schedule. -/
def expandKey (alg : Algorithm) (key : List (BitVec 32)) : Nat → List (BitVec 32)
  | 0 => []
  | size + 1 =>
    let w := expandKey alg key size
    let i := size
    if i < nk alg then w ++ [key[i]!]
    else
      let temp :=
        if i % nk alg = 0 then subWord (rotWord w[i - 1]!) ^^^ aesRcon (i / nk alg - 1)
        else if nk alg > 6 ∧ i % nk alg = 4 then subWord w[i - 1]!
        else w[i - 1]!
      w ++ [w[i - nk alg]! ^^^ temp]

/-- `key_schedule_to_round_keys`. -/
def keyScheduleToRoundKeys : Nat → List (BitVec 32) → List Quad32
  | 0, _ => []
  | rounds + 1, w =>
    keyScheduleToRoundKeys rounds w ++
      [mkfour w[4 * rounds]! w[4 * rounds + 1]! w[4 * rounds + 2]! w[4 * rounds + 3]!]

/-- `key_to_round_keys_LE`. -/
def keyToRoundKeys (alg : Algorithm) (key : List (BitVec 32)) : List Quad32 :=
  keyScheduleToRoundKeys (nr alg + 1) (expandKey alg key (nb * (nr alg + 1)))

/-- `eval_round`. -/
def evalRound (state roundKey : Quad32) : Quad32 :=
  mixColumns (shiftRows (subBytes state)) ^^^ roundKey

/-- `eval_rounds_def`. -/
def evalRounds (init : Quad32) (roundKeys : List Quad32) : Nat → Quad32
  | 0 => init
  | n + 1 => evalRound (evalRounds init roundKeys n) roundKeys[n + 1]!

/-- `eval_cipher_def`. -/
def evalCipher (alg : Algorithm) (input : Quad32) (roundKeys : List Quad32) : Quad32 :=
  let state := input ^^^ roundKeys[0]!
  let state := evalRounds state roundKeys (nr alg - 1)
  let state := subBytes state
  let state := shiftRows state
  state ^^^ roundKeys[nr alg]!

/-- `aes_encrypt_LE_def`. -/
def aesEncrypt (alg : Algorithm) (key : List (BitVec 32)) (input : Quad32) : Quad32 :=
  evalCipher alg input (keyToRoundKeys alg key)

/-! ## GF(2^128), `Vale.Math.Poly2_s`, `Vale.AES.GF128_s`, `Vale.AES.GF128` -/

/-- `poly`: polynomials over GF(2). -/
abbrev Poly := Polynomial (ZMod 2)

/-- `of_quad32`: coefficient `i` is bit `i`. -/
noncomputable def ofQuad32 (q : Quad32) : Poly :=
  ∑ i ∈ Finset.range 128, if q.getLsbD i then X ^ i else 0

/-- `reverse a n`: coefficient `i` becomes coefficient `n - i`, and those past
`n` drop. -/
noncomputable def reverse (a : Poly) (n : Nat) : Poly :=
  ∑ i ∈ Finset.range (n + 1), C (a.coeff (n - i)) * X ^ i

/-- `mask a n`: the coefficients below `n`. -/
noncomputable def mask (a : Poly) (n : Nat) : Poly :=
  ∑ i ∈ Finset.range n, C (a.coeff i) * X ^ i

/-- `shift p n`: times `x^n`, dropping the coefficients that fall below zero. -/
noncomputable def shift (p : Poly) : Int → Poly
  | .ofNat n => X ^ n * p
  | .negSucc n => divX^[n + 1] p

/-- `gf128_modulus_low_terms`: `x^7 + x^2 + x + 1`. -/
@[irreducible] noncomputable def gf128ModulusLowTerms : Poly := 1 + X + X ^ 2 + X ^ 7

/-- `gf128_modulus`: `x^128 + x^7 + x^2 + x + 1`. -/
@[irreducible] noncomputable def gf128Modulus : Poly := X ^ 128 + gf128ModulusLowTerms

/-- `gf128_mul`. -/
noncomputable def gf128Mul (a b : Poly) : Poly := (a * b) %ₘ gf128Modulus

/-- `gf128_mul_rev`, Vale's `*~`: the product with the bits reversed. -/
noncomputable def gf128MulRev (a b : Poly) : Poly :=
  reverse (gf128Mul (reverse a 127) (reverse b 127)) 127

/-- `shift_key_1`. -/
noncomputable def shiftKey1 (n : Nat) (f h : Poly) : Poly :=
  let g := X ^ n + f
  let h1 := shift h 1
  let offset := reverse (shift g (-1)) (n - 1)
  mask h1 n + if h1.coeff n ≠ 0 then offset else 0

/-! ## The GHASH key powers, `Vale.AES.OptPublic` -/

/-- `g_power`. -/
noncomputable def gPower (a : Poly) : Nat → Poly
  | 0 => 0
  | 1 => a
  | n + 1 => gf128MulRev a (gPower a n)

/-- `gf128_power`. -/
noncomputable def gf128Power (h : Poly) (n : Nat) : Poly :=
  shiftKey1 128 gf128ModulusLowTerms (gPower h n)

/-- `hkeys_reqs_pub`: the layout of the GHASH key powers the routines read. -/
def hkeysReqsPub (hkeys : List Quad32) (hBE : Quad32) : Prop :=
  let h := ofQuad32 (reverseBytesQuad32 (reverseBytesQuad32 hBE))
  hkeys.length ≥ 8 ∧
  ofQuad32 hkeys[0]! = gf128Power h 1 ∧
  ofQuad32 hkeys[1]! = gf128Power h 2 ∧
  hkeys[2]! = hBE ∧
  ofQuad32 hkeys[3]! = gf128Power h 3 ∧
  ofQuad32 hkeys[4]! = gf128Power h 4 ∧
  hkeys[5]! = mkfour 0 0 0 0 ∧
  ofQuad32 hkeys[6]! = gf128Power h 5 ∧
  ofQuad32 hkeys[7]! = gf128Power h 6

/-! ## GCM, `Vale.AES.GCM_s` -/

/-- `compute_iv_BE`, the counter block for a nonce, defined in `Vale.AES.GCM_s` at
https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/vale/specs/crypto/Vale.AES.GCM_s.fst#L20 -/
opaque computeIvBE (hLE : Quad32) (iv : List (BitVec 8)) : Quad32

/-- `gcm_encrypt_LE`: AES-GCM's ciphertext and tag, defined in `Vale.AES.GCM_s` at
https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/vale/specs/crypto/Vale.AES.GCM_s.fst#L39
with Vale's AES and GHASH, the round functions read as FIPS 197's. -/
opaque gcmEncrypt (alg : Algorithm) (key iv plain auth : List (BitVec 8)) :
  List (BitVec 8) × List (BitVec 8)

/-- `gcm_decrypt_LE`: AES-GCM's plaintext, and whether the tag matches, defined in
`Vale.AES.GCM_s` at
https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/vale/specs/crypto/Vale.AES.GCM_s.fst#L69 -/
opaque gcmDecrypt (alg : Algorithm) (key iv cipher auth tag : List (BitVec 8)) :
  List (BitVec 8) × Bool

end rind.vale
