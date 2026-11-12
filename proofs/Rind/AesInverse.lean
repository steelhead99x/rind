module
public import Rind.Vale
@[expose] public section

/-!
# FIPS 197's equivalent inverse cipher

Vale's AES spec, `Rind.Vale`, encrypts alone, so this transliterates FIPS 197's
decryption from the standard itself (FIPS 197 Upd1, May 2023): the inverses of
the round functions (sections 5.3.1 to 5.3.3), the equivalent inverse cipher
`EqInvCipher`, and its key schedule `KeyExpansionEIC` (section 5.3.5), on the
state laid out as `Rind.Vale` lays it out: row `r` of column `c` is byte
`r + 4c` of a `quad32`, least significant first. The inverse S-box and
`InvMixColumns` are opaque, as `Rind.Vale`'s S-box and `MixColumns` are, so
they are the functions the AES instructions compute in `Rind.X86_64.Simd` and
`Rind.Aarch64.Neon`; `rind.vale.aesDecrypt`'s known answers in `Rind.Aes` run
the definitions below.
-/

namespace rind.vale

/-- FIPS 197's inverse S-box (section 5.3.2): the inverse of the affine
transformation, then the field inverse, `b ^ 254`. -/
def fips197InvSbox (b : BitVec 8) : BitVec 8 :=
  let a := b.rotateLeft 1 ^^^ b.rotateLeft 3 ^^^ b.rotateLeft 6 ^^^ 0x05
  (List.range 254).foldl (fun p _ => gfMul p a) 1

/-- FIPS 197's `InvMixColumns` (section 5.3.3), row `r` of column `c` being byte `r + 4c`. -/
def fips197InvMixColumns (q : Quad32) : Quad32 := ofBytes fun i =>
  let a k := byte q (i / 4 * 4 + (i % 4 + k) % 4)
  gfMul (a 0) 0x0e ^^^ gfMul (a 1) 0x0b ^^^ gfMul (a 2) 0x0d ^^^ gfMul (a 3) 0x09

/-- FIPS 197's inverse S-box, opaque as `sbox` is. `fips197InvSbox` is what Lean runs. -/
opaque invSbox : BitVec 8 → BitVec 8 := fips197InvSbox

/-- FIPS 197's `InvMixColumns`, opaque as `mixColumns` is. `fips197InvMixColumns`
is what Lean runs. -/
opaque invMixColumns : Quad32 → Quad32 := fips197InvMixColumns

/-- FIPS 197's `InvSubBytes` (section 5.3.2): the inverse S-box on each byte. -/
def invSubBytes (q : Quad32) : Quad32 := ofBytes fun i => invSbox (byte q i)

/-- FIPS 197's `InvShiftRows` (section 5.3.1): row `r` of column `c` takes row
`r` of column `c - r`. -/
def invShiftRows (q : Quad32) : Quad32 := ofBytes fun i => byte q (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4))

/-- `EqInvCipher`'s rounds `n` down to 1, each `InvSubBytes`, `InvShiftRows`,
and `InvMixColumns`, then its round key XORed. -/
def eqInvRounds (dw : List Quad32) (state : Quad32) : Nat → Quad32
  | 0 => state
  | round + 1 => eqInvRounds dw (invMixColumns (invShiftRows (invSubBytes state)) ^^^ dw[round + 1]!) round

/-- FIPS 197's `EqInvCipher` (section 5.3.5), under the round keys `dw`
`KeyExpansionEIC` expands, first `dw[nr]` and last `dw[0]`. -/
def eqInvCipher (alg : Algorithm) (input : Quad32) (dw : List Quad32) : Quad32 :=
  let state := input ^^^ dw[nr alg]!
  let state := eqInvRounds dw state (nr alg - 1)
  invShiftRows (invSubBytes state) ^^^ dw[0]!

/-- FIPS 197's `KeyExpansionEIC` (section 5.3.5) from the cipher's round keys
`w`: `InvMixColumns` of each but the first and last. -/
def eqInvRoundKeys (alg : Algorithm) (w : List Quad32) : List Quad32 :=
  (List.range (nr alg + 1)).map fun r => if r = 0 ∨ r = nr alg then w[r]! else invMixColumns w[r]!

/-- FIPS 197's decryption of `input` under the key `key`, by the equivalent inverse cipher. -/
def aesDecrypt (alg : Algorithm) (key : List (BitVec 32)) (input : Quad32) : Quad32 :=
  eqInvCipher alg input (eqInvRoundKeys alg (keyToRoundKeys alg key))

end rind.vale
