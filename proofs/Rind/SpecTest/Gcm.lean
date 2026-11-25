import Rind.GhashSpec

/-!
# Vale's GCM, computed

Vale's GF(2^128) is Mathlib's polynomials over `ZMod 2`, which do not run.
`gf128MulLEC` multiplies two blocks with the carry-less product and folds
`Rind.Gf128` proves of rind's PCLMULQDQ code (`mul_data`), and
`gf128MulLE_eq` proves it Vale's `gf128_mul_LE`. `gcmEncryptC` and
`gcmDecryptC` are Vale's GCM over it, proven equal to `gcmEncrypt` and
`gcmDecrypt`. The spec tests (`Rind.SpecTest.Server`) run these.
-/

open Polynomial rind.simd

namespace rind.vale

/-- `gf128MulLE`, by `mulModel` on the byte-reversed blocks, the second
shifted by `shift_key_1`. -/
def gf128MulLEC (a b : Quad32) : Quad32 :=
  reverseBytesQuad32 (mulModel (reverseBytesQuad32 a) (skBV (reverseBytesQuad32 b)))

theorem gf128MulLE_eq : gf128MulLE = gf128MulLEC := by
  funext a b
  have hinj : ∀ x y : Quad32, polyLE x = polyLE y → x = y := fun x y h => by
    have := congrArg reverseBytesQuad32 (toPoly_inj h)
    rwa [reverseBytesQuad32_involutive, reverseBytesQuad32_involutive] at this
  apply hinj
  rw [polyLE_mulLE, gf128MulLEC]
  simp only [polyLE, reverseBytesQuad32_involutive]
  rw [mul_data _ _ _ (small_toPoly _) (toPoly_skBV _)]

/-- `ghashLE`, over `gf128MulLEC`. -/
def ghashLEC (h : Quad32) (x : List Quad32) : Quad32 :=
  x.foldl (fun y xi => gf128MulLEC (y ^^^ xi) h) 0

/-- `computeIvBE`, over `ghashLEC`. -/
def computeIvBEC (hLE : Quad32) (iv : List (BitVec 8)) : Quad32 :=
  if 8 * iv.length = 96 then
    let ivLE := leBytesToQuad32 (padTo128Bits iv)
    let ivBE := reverseBytesQuad32 ivLE
    ivBE.extractLsb' 32 96 ++ (1 : BitVec 32)
  else
    let paddedIvQuads := leBytesToSeqQuad32 (padTo128Bits iv)
    let lengthBE := insertNat64 (mkfour 0 0 0 0) (8 * iv.length) 0
    let lengthLE := reverseBytesQuad32 lengthBE
    reverseBytesQuad32 (ghashLEC hLE (paddedIvQuads ++ [lengthLE]))

/-- `gcmHash`, over `ghashLEC`. -/
def gcmHashC (hLE : Quad32) (auth cipher : List (BitVec 8)) : Quad32 :=
  let lengthsBE := insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * auth.length) 1) (8 * cipher.length) 0
  let lengthsLE := reverseBytesQuad32 lengthsBE
  let zeroPaddedC := leBytesToSeqQuad32 (padTo128Bits cipher)
  let zeroPaddedA := leBytesToSeqQuad32 (padTo128Bits auth)
  ghashLEC hLE (zeroPaddedA ++ (zeroPaddedC ++ [lengthsLE]))

/-- `gcmEncrypt`, over `computeIvBEC` and `gcmHashC`. -/
def gcmEncryptC (alg : Algorithm) (key iv plain auth : List (BitVec 8)) :
    List (BitVec 8) × List (BitVec 8) :=
  let keyLE := seqNat8ToSeqNat32LE key
  let hLE := aesEncrypt alg keyLE (mkfour 0 0 0 0)
  let j0BE := computeIvBEC hLE iv
  let c := gctrEncrypt (inc32 j0BE 1) plain alg keyLE
  let t := gctrEncrypt j0BE (leQuad32ToBytes (gcmHashC hLE auth c)) alg keyLE
  (c, t)

/-- `gcmDecrypt`, over `computeIvBEC` and `gcmHashC`. -/
def gcmDecryptC (alg : Algorithm) (key iv cipher auth tag : List (BitVec 8)) :
    List (BitVec 8) × Bool :=
  let keyLE := seqNat8ToSeqNat32LE key
  let hLE := aesEncrypt alg keyLE (mkfour 0 0 0 0)
  let j0BE := computeIvBEC hLE iv
  let p := gctrEncrypt (inc32 j0BE 1) cipher alg keyLE
  let t := gctrEncrypt j0BE (leQuad32ToBytes (gcmHashC hLE auth cipher)) alg keyLE
  (p, t == tag)

theorem gcmEncrypt_eq : gcmEncrypt = gcmEncryptC := by
  funext alg key iv plain auth
  simp only [gcmEncrypt, gcmEncryptC, computeIvBE, computeIvBEC, gcmHash, gcmHashC, ghashLE, ghashLEC,
    gf128MulLE_eq]

theorem gcmDecrypt_eq : gcmDecrypt = gcmDecryptC := by
  funext alg key iv cipher auth tag
  simp only [gcmDecrypt, gcmDecryptC, computeIvBE, computeIvBEC, gcmHash, gcmHashC, ghashLE, ghashLEC,
    gf128MulLE_eq]

end rind.vale
