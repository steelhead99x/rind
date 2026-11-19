module

public import VerifiedGarbage.Spec.Sha3

/-!
# ML-KEM (FIPS 203)

**Trusted** (as every file in `Spec/`). The module-lattice-based
key-encapsulation mechanism ML-KEM, transcribed from FIPS 203,
*Module-Lattice-Based Key-Encapsulation Mechanism Standard* (August 2024);
section, algorithm, table and appendix numbers below refer to it. The
algorithms are written for any parameter set (`Params`); ML-KEM-768 and
ML-KEM-1024 of Table 2, the parameter sets the library implements, are
`mlKem768` and `mlKem1024`.

Byte arrays are lists of bytes, and bit arrays `Array`s of `Bool`s (a bit
`b` is the integer `b.toNat` where the standard does arithmetic with it). An
element of `ℤ_q` is a `Fin q`, whose arithmetic is modulo `q`, and an array
in `ℤ_q²⁵⁶` (a polynomial of `R_q`, or its NTT representation in `T_q`,
§2.4.4) a `Vector` of 256 of them. The integer arrays of `ByteEncode` and
`ByteDecode`, in `ℤ_m²⁵⁶` for `m = 2ᵈ` or `q`, are `Vector`s of natural
numbers less than `m`. A vector of `R_q^k` or `T_q^k` is a list of `k`
polynomials, and a matrix a list of its rows.

`SampleNTT` (Algorithm 7) loops until it has sampled 256 coefficients,
which takes an unbounded number of iterations in the worst case. Appendix B
lets an implementation bound the loop, by at least 280 iterations
(`minIterations`, Table 4), and fail when the bound is reached. So the
algorithms that sample (every one from K-PKE.KeyGen and K-PKE.Encrypt up)
take a bound `iters` on the iterations of each `SampleNTT`, and return
`none` when one of them does not finish within it. The standard's
(unbounded) algorithm returns `x` when the bounded one returns `some x` for
some bound, and a larger bound gives the same result.

The hash functions and XOFs are those of `Spec/Sha3.lean` (§4.1). The
contracts of the functions implemented in assembly are in
`Spec/MlKem/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.MlKem

/-! ## Constants and parameter sets (§2.3, §8) -/

/-- `n = 256`. -/
abbrev n : Nat := 256

/-- The prime `q = 3329 = 2⁸ · 13 + 1`. -/
abbrev q : Nat := 3329

/-- `ℤ_q`: arithmetic on `Fin q` is modulo `q` (§2.4.1). An element is the
integer in `{0, …, q - 1}` that represents it (`.val`). -/
abbrev Zq := Fin q

/-- An element of `ℤ_q²⁵⁶`: the coefficients of a polynomial of `R_q`
(`f[i] = fᵢ`, (2.5)), or an NTT representation of `T_q`
(`ĝ[2i] = ĝ_{i,0}`, `ĝ[2i + 1] = ĝ_{i,1}`, (2.7)). -/
abbrev Poly := Vector Zq n

/-- The integer `x mod q`. -/
def ofNat (x : Nat) : Zq := Fin.ofNat q x

/-- A parameter set (§8): the module dimension `k`, the parameters `η₁` and
`η₂` of the centered binomial distributions, and the compression parameters
`d_u` and `d_v`. -/
structure Params where
  k : Nat
  η₁ : Nat
  η₂ : Nat
  du : Nat
  dv : Nat

/-- ML-KEM-768 (Table 2): `k = 3`, `η₁ = 2`, `η₂ = 2`, `d_u = 10`, `d_v = 4`. -/
def mlKem768 : Params := { k := 3, η₁ := 2, η₂ := 2, du := 10, dv := 4 }

/-- ML-KEM-1024 (Table 2): `k = 4`, `η₁ = 2`, `η₂ = 2`, `d_u = 11`, `d_v = 5`. -/
def mlKem1024 : Params := { k := 4, η₁ := 2, η₂ := 2, du := 11, dv := 5 }

/-- The length of an encapsulation key, `384k + 32` bytes (Algorithm 16). -/
def Params.ekLen (p : Params) : Nat := 384 * p.k + 32

/-- The length of a decapsulation key, `768k + 96` bytes (Algorithm 16). -/
def Params.dkLen (p : Params) : Nat := 768 * p.k + 96

/-- The length of a ciphertext, `32(d_u k + d_v)` bytes (Algorithm 14). -/
def Params.ctLen (p : Params) : Nat := 32 * (p.du * p.k + p.dv)

/-- The least bound an implementation may put on the iterations of the
loop of `SampleNTT` (Appendix B, Table 4). -/
def minIterations : Nat := 280

/-! ## Cryptographic functions (§4.1) -/

/-- `PRF_η(s, b) := SHAKE256(s ‖ b, 8 · 64 · η)` (4.3): `64η` bytes. -/
def prf (η : Nat) (s : List Byte) (b : Byte) : List Byte := Sha3.shake256 (s ++ [b]) (64 * η)

/-- `H(s) := SHA3-256(s)` (4.4). -/
def H (s : List Byte) : List Byte := Sha3.sha3_256 s

/-- `J(s) := SHAKE256(s, 8 · 32)` (4.4): 32 bytes. -/
def J (s : List Byte) : List Byte := Sha3.shake256 s 32

/-- `G(c) := SHA3-512(c)` (4.5), as its two 32-byte halves `(a, b)` with
`G(c) = a ‖ b`. -/
def G (c : List Byte) : List Byte × List Byte :=
  let o := Sha3.sha3_512 c
  (o.take 32, o.drop 32)

/-- The first `ℓ` bytes squeezed from `XOF` after absorbing `B`: by the
equivalence of (4.6), the output of `SHAKE128(B, 8ℓ)`, however it is
squeezed in pieces (`XOF.Squeeze`). -/
def xof (B : List Byte) (ℓ : Nat) : List Byte := Sha3.shake128 B ℓ

/-! ## Conversion and compression (§4.2.1) -/

/-- Algorithm 3, `BitsToBytes(b)`: `B[⌊i/8⌋] ← B[⌊i/8⌋] + b[i] · 2^(i mod 8)`
for each bit `i` of `b`, of length `8ℓ`. -/
def bitsToBytes (b : Array Bool) : List Byte :=
  (List.range (b.size / 8)).map fun i =>
    BitVec.ofNat 8 ((List.range 8).map fun j => (b.getD (8 * i + j) false).toNat * 2 ^ j).sum

/-- Algorithm 4, `BytesToBits(B)`: `b[8i + j]` is `C[i] mod 2` after `j`
halvings `C[i] ← ⌊C[i]/2⌋` of `C[i] = B[i]`, i.e. `⌊B[i]/2ʲ⌋ mod 2`. -/
def bytesToBits (B : List Byte) : Array Bool :=
  (B.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)).toArray

/-- `⌈a/b⌋` for integers `a ≥ 0` and `b > 0`: the rational `a/b` rounded to
the nearest integer, `y + 1/2` to `y + 1` (§2.3); that is `⌊a/b + 1/2⌋`. -/
def roundDiv (a b : Nat) : Nat := (2 * a + b) / (2 * b)

/-- `Compress_d(x) = ⌈(2ᵈ/q) · x⌋ mod 2ᵈ` (4.7), for `d < 12`. -/
def compress (d : Nat) (x : Zq) : Nat := roundDiv (2 ^ d * x.val) q % 2 ^ d

/-- `Decompress_d(y) = ⌈(q/2ᵈ) · y⌋` (4.8), for `y < 2ᵈ` and `d < 12`. -/
def decompress (d : Nat) (y : Nat) : Zq := ofNat (roundDiv (q * y) (2 ^ d))

/-- Algorithm 5, `ByteEncode_d(F)`, for `1 ≤ d ≤ 12` and `F` in `ℤ_m²⁵⁶`
(each entry less than `m`, where `m = 2ᵈ` if `d < 12` and `m = q` if
`d = 12`): `b[i·d + j]` is `a mod 2` after `j` steps `a ← (a - b[i·d + j])/2`
of `a = F[i]`, i.e. `⌊F[i]/2ʲ⌋ mod 2`; then `B ← BitsToBytes(b)`, of
`32d` bytes. -/
def byteEncode (d : Nat) (F : Vector Nat n) : List Byte :=
  bitsToBytes
    (F.toList.flatMap fun a => (List.range d).map fun j => decide (a / 2 ^ j % 2 = 1)).toArray

/-- Algorithm 6, `ByteDecode_d(B)`, for `1 ≤ d ≤ 12` and `B` of `32d` bytes:
`F[i] ← ∑_{j<d} b[i·d + j] · 2ʲ mod m` for `b ← BytesToBits(B)`, where
`m = 2ᵈ` if `d < 12` and `m = q` if `d = 12`. -/
def byteDecode (d : Nat) (B : List Byte) : Vector Nat n :=
  let b := bytesToBits B
  let m := if d < 12 then 2 ^ d else q
  Vector.ofFn fun i =>
    ((List.range d).map fun j => (b.getD (i.val * d + j) false).toNat * 2 ^ j).sum % m

/-- `ByteEncode₁₂` of an array of `ℤ_q²⁵⁶`. -/
def encode12 (f : Poly) : List Byte := byteEncode 12 (f.map Fin.val)

/-- `ByteDecode₁₂`, whose results are in `ℤ_q²⁵⁶`. -/
def decode12 (B : List Byte) : Poly := (byteDecode 12 B).map ofNat

/-- `ByteEncode_d(Compress_d(f))`, for `d < 12`. -/
def compressEncode (d : Nat) (f : Poly) : List Byte := byteEncode d (f.map (compress d))

/-- `Decompress_d(ByteDecode_d(B))`, for `d < 12`. -/
def decodeDecompress (d : Nat) (B : List Byte) : Poly := (byteDecode d B).map (decompress d)

/-! ## Sampling (§4.2.2) -/

/-- Lines 4–16 of Algorithm 7, `SampleNTT`, from the coefficients `a` sampled
so far (`j = |a|`), taking the 3-byte arrays `C` of the loop's iterations
from the XOF output `out`: `some a` once `j = 256`, and `none` if `out` runs
out first. -/
def sampleLoop (a : List Zq) (out : List Byte) : Option (List Zq) :=
  if a.length = n then some a else
  match out with
  | c0 :: c1 :: c2 :: out =>
    let d₁ := c0.toNat + 256 * (c1.toNat % 16)
    let d₂ := c1.toNat / 16 + 16 * c2.toNat
    let a := if d₁ < q then a ++ [ofNat d₁] else a
    let a := if d₂ < q ∧ a.length < n then a ++ [ofNat d₂] else a
    sampleLoop a out
  | _ => none

/-- Algorithm 7, `SampleNTT(B)`, for a 34-byte `B` (a 32-byte seed and two
indices), if its loop ends within `iters` iterations; `none` otherwise. The
iterations squeeze 3 bytes each from `XOF` after absorbing `B`, so the first
`iters` of them take the first `3 · iters` bytes of its output. -/
def sampleNTT (iters : Nat) (B : List Byte) : Option Poly :=
  (sampleLoop [] (xof B (3 * iters))).map fun a => Vector.ofFn fun i => a.getD i.val 0

/-- Algorithm 8, `SamplePolyCBD_η(B)`, for `B` of `64η` bytes:
`f[i] ← x - y mod q` for `x = ∑_{j<η} b[2iη + j]` and
`y = ∑_{j<η} b[2iη + η + j]`, where `b ← BytesToBits(B)`. -/
def samplePolyCBD (η : Nat) (B : List Byte) : Poly :=
  let b := bytesToBits B
  Vector.ofFn fun i =>
    let x := ((List.range η).map fun j => (b.getD (2 * i.val * η + j) false).toNat).sum
    let y := ((List.range η).map fun j => (b.getD (2 * i.val * η + η + j) false).toNat).sum
    ofNat x - ofNat y

/-! ## The number-theoretic transform (§4.3) -/

/-- `ζ = 17`, a primitive 256-th root of unity modulo `q`. -/
def ζ : Zq := 17

/-- `BitRev7(r)`: `r₆ + 2r₅ + 4r₄ + ⋯ + 64r₀` for `r = r₀ + 2r₁ + ⋯ + 64r₆`
(§2.3). -/
def bitRev7 (r : Nat) : Nat := ((List.range 7).map fun i => r / 2 ^ i % 2 * 2 ^ (6 - i)).sum

/-- Algorithm 9, `NTT(f)`. -/
def ntt (f : Poly) : Poly := Id.run do
  let mut f := f
  let mut i := 1
  -- for (len ← 128; len ≥ 2; len ← len/2)
  for len in [128, 64, 32, 16, 8, 4, 2] do
    -- for (start ← 0; start < 256; start ← start + 2·len)
    for start in List.range' 0 (n / (2 * len)) (2 * len) do
      let zeta := ζ ^ bitRev7 i
      i := i + 1
      for j in List.range' start len do
        let t := zeta * f[j + len]!
        f := f.set! (j + len) (f[j]! - t)
        f := f.set! j (f[j]! + t)
  return f

/-- Algorithm 10, `NTT⁻¹(f̂)`. -/
def nttInv (f : Poly) : Poly := Id.run do
  let mut f := f
  let mut i := 127
  -- for (len ← 2; len ≤ 128; len ← 2·len)
  for len in [2, 4, 8, 16, 32, 64, 128] do
    -- for (start ← 0; start < 256; start ← start + 2·len)
    for start in List.range' 0 (n / (2 * len)) (2 * len) do
      let zeta := ζ ^ bitRev7 i
      i := i - 1
      for j in List.range' start len do
        let t := f[j]!
        f := f.set! j (t + f[j + len]!)
        f := f.set! (j + len) (zeta * (f[j + len]! - t))
  -- multiply every entry by 3303 ≡ 128⁻¹ mod q
  return f.map (· * 3303)

/-- Algorithm 12, `BaseCaseMultiply(a₀, a₁, b₀, b₁, γ)`: the product of
`a₀ + a₁X` and `b₀ + b₁X` modulo `X² - γ`. -/
def baseCaseMultiply (a₀ a₁ b₀ b₁ γ : Zq) : Zq × Zq :=
  (a₀ * b₀ + a₁ * b₁ * γ, a₀ * b₁ + a₁ * b₀)

/-- Algorithm 11, `MultiplyNTTs(f̂, ĝ)`: for `i < 128`,
`(ĥ[2i], ĥ[2i + 1]) ← BaseCaseMultiply(f̂[2i], f̂[2i + 1], ĝ[2i], ĝ[2i + 1], ζ^(2BitRev7(i) + 1))`. -/
def multiplyNTTs (f g : Poly) : Poly :=
  Vector.ofFn fun h =>
    let i := h.val / 2
    let c := baseCaseMultiply f[2 * i]! f[2 * i + 1]! g[2 * i]! g[2 * i + 1]!
      (ζ ^ (2 * bitRev7 i + 1))
    if h.val % 2 = 0 then c.1 else c.2

/-! ## Vectors and matrices (§2.4.5–§2.4.7) -/

/-- The array of zeros, the zero of `R_q` and of `T_q`. -/
def zero : Poly := Vector.replicate n 0

/-- Coordinate-wise addition of arrays of `ℤ_q²⁵⁶` (2.3). -/
def add (f g : Poly) : Poly := Vector.zipWith (· + ·) f g

/-- Subtraction, coordinate-wise. -/
def sub (f g : Poly) : Poly := Vector.zipWith (· - ·) f g

/-- The sum of vectors of `R_q^k` or `T_q^k`, coordinate-wise. -/
def addVec (u v : List Poly) : List Poly := List.zipWith add u v

/-- `û^⊺ ∘ v̂ = ∑_j û[j] ×_{T_q} v̂[j]` (2.14). -/
def dot (u v : List Poly) : Poly := (List.zipWith multiplyNTTs u v).foldl add zero

/-- `Â ∘ û`: entry `i` is `∑_j Â[i, j] ×_{T_q} û[j]` (2.12). -/
def mulMatVec (A : List (List Poly)) (u : List Poly) : List Poly := A.map fun row => dot row u

/-- `Â^⊺ ∘ û`: entry `i` is `∑_j Â[j, i] ×_{T_q} û[j]` (2.13). -/
def mulMatTVec (k : Nat) (A : List (List Poly)) (u : List Poly) : List Poly :=
  (List.range k).map fun i => dot (A.map fun row => row.getD i zero) u

/-- Lines 3–7 of Algorithm 13 and 4–8 of Algorithm 14: the `k × k` matrix
`Â` with `Â[i, j] ← SampleNTT(ρ ‖ j ‖ i)` (`j` and `i` bytes 33 and 34 of
the input), as its rows; `none` if a `SampleNTT` does not finish within
`iters` iterations. -/
def sampleMatrix (k iters : Nat) (ρ : List Byte) : Option (List (List Poly)) :=
  (List.range k).mapM fun i => (List.range k).mapM fun j =>
    sampleNTT iters (ρ ++ [BitVec.ofNat 8 j, BitVec.ofNat 8 i])

/-- `k` samples `SamplePolyCBD_η(PRF_η(s, N))`, with the counter `N` running
from `N₀` to `N₀ + k - 1`. -/
def sampleVec (k η : Nat) (s : List Byte) (N₀ : Nat) : List Poly :=
  (List.range k).map fun i => samplePolyCBD η (prf η s (BitVec.ofNat 8 (N₀ + i)))

/-- `ByteEncode₁₂` of each entry of a vector, concatenated (§2.4.8). -/
def encodeVec (v : List Poly) : List Byte := v.flatMap encode12

/-- `ByteDecode₁₂` of each of the `k` consecutive 384-byte pieces of `B`
(2.17). -/
def decodeVec (k : Nat) (B : List Byte) : List Poly :=
  (List.range k).map fun i => decode12 ((B.drop (384 * i)).take 384)

/-! ## K-PKE (§5) -/

/-- Algorithm 13, `K-PKE.KeyGen(d)`: the encryption key `ek_PKE` of
`384k + 32` bytes and the decryption key `dk_PKE` of `384k` bytes; `none`
if a `SampleNTT` does not finish within `iters` iterations. -/
def kpkeKeyGen (p : Params) (iters : Nat) (d : List Byte) : Option (List Byte × List Byte) := do
  let (ρ, σ) := G (d ++ [BitVec.ofNat 8 p.k])
  let A ← sampleMatrix p.k iters ρ
  let s := sampleVec p.k p.η₁ σ 0
  let e := sampleVec p.k p.η₁ σ p.k
  let ŝ := s.map ntt
  let ê := e.map ntt
  let tHat := addVec (mulMatVec A ŝ) ê
  return (encodeVec tHat ++ ρ, encodeVec ŝ)

/-- Algorithm 14, `K-PKE.Encrypt(ek_PKE, m, r)`: the ciphertext `c` of
`32(d_u k + d_v)` bytes; `none` if a `SampleNTT` does not finish within
`iters` iterations. -/
def kpkeEncrypt (p : Params) (iters : Nat) (ek m r : List Byte) : Option (List Byte) := do
  let tHat := decodeVec p.k (ek.take (384 * p.k))
  let ρ := (ek.drop (384 * p.k)).take 32
  let A ← sampleMatrix p.k iters ρ
  let y := sampleVec p.k p.η₁ r 0
  let e₁ := sampleVec p.k p.η₂ r p.k
  let e₂ := samplePolyCBD p.η₂ (prf p.η₂ r (BitVec.ofNat 8 (2 * p.k)))
  let ŷ := y.map ntt
  let u := addVec ((mulMatTVec p.k A ŷ).map nttInv) e₁
  let μ := decodeDecompress 1 m
  let v := add (add (nttInv (dot tHat ŷ)) e₂) μ
  let c₁ := u.flatMap (compressEncode p.du)
  let c₂ := compressEncode p.dv v
  return c₁ ++ c₂

/-- Algorithm 15, `K-PKE.Decrypt(dk_PKE, c)`: the 32-byte message `m`. -/
def kpkeDecrypt (p : Params) (dk c : List Byte) : List Byte :=
  let c₁ := c.take (32 * p.du * p.k)
  let c₂ := (c.drop (32 * p.du * p.k)).take (32 * p.dv)
  let u' := (List.range p.k).map fun i =>
    decodeDecompress p.du ((c₁.drop (32 * p.du * i)).take (32 * p.du))
  let v' := decodeDecompress p.dv c₂
  let ŝ := decodeVec p.k dk
  let w := sub v' (nttInv (dot ŝ (u'.map ntt)))
  compressEncode 1 w

/-! ## The internal algorithms (§6) -/

/-- Algorithm 16, `ML-KEM.KeyGen_internal(d, z)`: the encapsulation key `ek`
of `384k + 32` bytes and the decapsulation key
`dk = dk_PKE ‖ ek ‖ H(ek) ‖ z` of `768k + 96` bytes; `none` if a
`SampleNTT` does not finish within `iters` iterations. -/
def keyGenInternal (p : Params) (iters : Nat) (d z : List Byte) :
    Option (List Byte × List Byte) := do
  let (ekPKE, dkPKE) ← kpkeKeyGen p iters d
  let ek := ekPKE
  let dk := dkPKE ++ ek ++ H ek ++ z
  return (ek, dk)

/-- Algorithm 17, `ML-KEM.Encaps_internal(ek, m)`: the 32-byte shared secret
key `K` and the ciphertext `c`; `none` if a `SampleNTT` does not finish
within `iters` iterations. -/
def encapsInternal (p : Params) (iters : Nat) (ek m : List Byte) :
    Option (List Byte × List Byte) := do
  let (K, r) := G (m ++ H ek)
  let c ← kpkeEncrypt p iters ek m r
  return (K, c)

/-- Algorithm 18, `ML-KEM.Decaps_internal(dk, c)`: the 32-byte shared secret
key `K'`, which is `K̄ = J(z ‖ c)` if the re-encryption `c'` of the
decrypted message differs from `c` ("implicit rejection"); `none` if a
`SampleNTT` does not finish within `iters` iterations. -/
def decapsInternal (p : Params) (iters : Nat) (dk c : List Byte) : Option (List Byte) := do
  let dkPKE := dk.take (384 * p.k)
  let ekPKE := (dk.drop (384 * p.k)).take (384 * p.k + 32)
  let h := (dk.drop (768 * p.k + 32)).take 32
  let z := (dk.drop (768 * p.k + 64)).take 32
  let m' := kpkeDecrypt p dkPKE c
  let (K', r') := G (m' ++ h)
  let Kbar := J (z ++ c)
  let c' ← kpkeEncrypt p iters ekPKE m' r'
  return if c ≠ c' then Kbar else K'

/-! ## Input checking (§7.2)

`ML-KEM.KeyGen`, `ML-KEM.Encaps` and `ML-KEM.Decaps` (Algorithms 19–21) are
the internal algorithms on randomness that the cryptographic module
generates, on inputs that have been checked. Only the encapsulation key
check is here: this library keeps a decapsulation key as the seed `(d, z)`
it is generated from (§3.3), and expands it with `ML-KEM.KeyGen_internal`,
so the decapsulation keys it uses pass the checks of §7.3 by
construction. -/

/-- The encapsulation key check of §7.2: the type check (`ek` is `384k + 32`
bytes) and the modulus check (7.1),
`ByteEncode₁₂(ByteDecode₁₂(ek[0 : 384k])) = ek[0 : 384k]`: every integer
encoded in `ek` is less than `q`. -/
def ekCheck (p : Params) (ek : List Byte) : Bool :=
  ek.length = p.ekLen && encodeVec (decodeVec p.k (ek.take (384 * p.k))) == ek.take (384 * p.k)

/-- The seed `ρ` of the matrix `Â` in an encapsulation key:
`ek[384k : 384k + 32]` (Algorithm 14, line 3). -/
def ekRho (p : Params) (ek : List Byte) : List Byte := (ek.drop (384 * p.k)).take 32

/-- The seed `ρ` of the matrix `Â` in a decapsulation key: that of the
encapsulation key `dk[384k : 768k + 32]` it contains (Algorithm 18, line 2),
`dk[768k : 768k + 32]`. -/
def dkRho (p : Params) (dk : List Byte) : List Byte := (dk.drop (768 * p.k)).take 32

/-- The seed `ρ` of the matrix `Â` that `ML-KEM.KeyGen_internal(d, z)`
samples, and appends to its encapsulation key: the first output of
`G(d ‖ k)` (Algorithm 13, line 1). -/
def keyGenRho (p : Params) (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 p.k])).1

end VG.Spec.MlKem
