module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.Spec.Sha512

/-!
# Ed25519 (RFC 8032)

**Trusted** (as every file in `Spec/`). PureEdDSA Ed25519, transcribed from
RFC 8032 §§5.1 and 6. No context or prehash is used: `dom2` is empty and
`PH(M) = M`. Ed25519ctx, Ed25519ph and Ed448 are separate algorithms and
are not specified here.

The field and its exponentiation are those already specified for X25519:
`Fin (2^255 - 19)`, with arithmetic modulo that prime. Point operations use
the extended coordinates and complete addition formula of §5.1.4. This is
a mathematical specification; its branches on scalars are not an assembly
implementation or a claim about timing.

Verification uses the uncofactored equation explicitly permitted by
§5.1.7: `[S]B = R + [k]A`, with `k = SHA-512(R || A || M) mod L`, reduced
as §6's reference code (`h = sha512_modq(...)`) and OpenSSL reduce it.
Reading §5.1.7 with the full 512-bit SHA-512 integer instead gives a
different predicate: since `L ≡ 5 (mod 8)`, `[k]A` and `[k mod L]A` differ
whenever A has a small-order component. Encodings must be canonical,
including the sign of a zero x-coordinate, and `S < L`. There is no
additional subgroup or small-order rejection. In particular, this policy is
not ZIP 215 and does not promise to reject identity keys. The choice of
equation and of the reduced challenge is part of the contract, not
implementation freedom.
-/

@[expose] public section

namespace VG.Spec.Ed25519

open X25519 (Fe P pow)

/-- The prime-order subgroup's order (§5.1, Table 1). -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- The Edwards curve parameter `-121665 / 121666` (§5.1). -/
def d : Fe := (0 - 121665) * pow 121666 (P - 2)

/-- The square root of -1 used by point decoding (§5.1.3). -/
def sqrtM1 : Fe := pow 2 ((P - 1) / 4)

/-- A little-endian byte string interpreted as an unsigned integer (§5.1.2). -/
def decodeLE : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLE bs

/-- The low `n` bytes of an integer, in little-endian order (§5.1.2). -/
def encodeLE (n x : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (x >>> (8 * i))

/-- Extended coordinates: `x = X/Z`, `y = Y/Z`, `xy = T/Z` (§5.1.4).
Only valid points are passed to group operations by the top-level functions. -/
structure Point where
  X : Fe
  Y : Fe
  Z : Fe
  T : Fe
  deriving DecidableEq

/-- The neutral point (§5.1.4). -/
def identity : Point := ⟨0, 1, 1, 0⟩

/-- The base point from Table 1 (§5.1), with `Z = 1` and `T = XY`. -/
def basePoint : Point :=
  let x : Fe := 15112221349535400772501151409588531511454012693041857206046113283949847762202
  let y : Fe := 46316835694926478169428394003475163141307993866256225615783033603165251855960
  ⟨x, y, 1, x * y⟩

/-- The complete addition formula of §5.1.4, in its stated order. -/
def pointAdd (p q : Point) : Point :=
  let a := (p.Y - p.X) * (q.Y - q.X)
  let b := (p.Y + p.X) * (q.Y + q.X)
  let c := p.T * 2 * d * q.T
  let dd := p.Z * 2 * q.Z
  let e := b - a
  let f := dd - c
  let g := dd + c
  let h := b + a
  ⟨e * f, g * h, f * g, e * h⟩

/-- `[s]p`, using the double-and-add algorithm of §6. The scalar is not
implicitly reduced modulo `L`: a decoded point need not have order `L`. -/
def pointMul (s : Nat) (p : Point) : Point :=
  if s = 0 then identity else
  let q := pointMul (s / 2) (pointAdd p p)
  if s % 2 = 0 then q else pointAdd q p
termination_by s
decreasing_by omega

/-- Equality of affine coordinates without an inversion (§6). -/
def pointEqual (p q : Point) : Bool :=
  p.X * q.Z == q.X * p.Z && p.Y * q.Z == q.Y * p.Z

/-- Encode a valid point as its y-coordinate and the low bit of x (§5.1.2). -/
def encodePoint (p : Point) : List Byte :=
  let zi := pow p.Z (P - 2)
  let x := p.X * zi
  let y := p.Y * zi
  encodeLE 32 (y.val + (x.val % 2) * 2 ^ 255)

/-- Recover x from canonical y and the sign bit (§5.1.3, steps 2–4).
The single-exponentiation formula computes a square root of `u/v`. -/
def recoverX (y : Fe) (sign : Bool) : Option Fe := do
  let u := y * y - 1
  let v := d * y * y + 1
  let x := u * pow v 3 * pow (u * pow v 7) ((P - 5) / 8)
  let vx2 := v * x * x
  let x ← if vx2 = u then some x
    else if vx2 = 0 - u then some (x * sqrtM1) else none
  if x = 0 && sign then none
  else some (if (x.val % 2 == 1) == sign then x else 0 - x)

/-- Decode exactly 32 bytes, rejecting y ≥ p, nonsquares and negative zero
(§5.1.3). In particular, y is checked before conversion to `Fe`. -/
def decodePoint (bs : List Byte) : Option Point := do
  if bs.length != 32 then none else do
    let n := decodeLE bs
    let y := n % 2 ^ 255
    if h : y < P then
      let y : Fe := ⟨y, h⟩
      let x ← recoverX y (n / 2 ^ 255 == 1)
      pure ⟨x, y, 1, x * y⟩
    else none

/-- Prune the first half of the SHA-512 digest (§5.1.5, steps 2–3). -/
def prune (h : List Byte) : Nat :=
  (decodeLE (h.take 32) &&& (2 ^ 254 - 8)) ||| 2 ^ 254

/-- The secret scalar and nonce prefix from a 32-byte seed (§5.1.6, step 1). -/
def expandSecret (seed : List Byte) : Nat × List Byte :=
  let h := Sha512.sha512 seed
  (prune h, h.drop 32)

/-- Reduce a little-endian integer modulo the subgroup order. Used for
64-byte SHA-512 digests (§5.1.6, steps 2–5). -/
def scalarReduce (wide : List Byte) : List Byte := encodeLE 32 (decodeLE wide % L)

/-- `(r + k*s) mod L`, as 32 bytes (§5.1.6, step 5). Inputs are unsigned
little-endian integers and need not be canonical scalars. -/
def scalarMulAdd (r k s : List Byte) : List Byte :=
  encodeLE 32 ((decodeLE r + decodeLE k * decodeLE s) % L)

/-- Encode `[s]B` for an unsigned little-endian scalar. This function does
not prune its input (§5.1.5, steps 3–4; §5.1.6, step 3). -/
def scalarBase (s : List Byte) : List Byte := encodePoint (pointMul (decodeLE s) basePoint)

/-- The public key derived from a 32-byte seed (§5.1.5). -/
def publicKey (seed : List Byte) : List Byte :=
  encodePoint (pointMul (expandSecret seed).1 basePoint)

/-- Deterministic Ed25519 signing with a 32-byte seed (§5.1.6).
There is no separately supplied public key that could disagree with the seed. -/
def sign (seed message : List Byte) : List Byte :=
  let (s, noncePrefix) := expandSecret seed
  let a := encodePoint (pointMul s basePoint)
  let r := decodeLE (Sha512.sha512 (noncePrefix ++ message)) % L
  let rr := encodePoint (pointMul r basePoint)
  let k := decodeLE (Sha512.sha512 (rr ++ a ++ message)) % L
  rr ++ encodeLE 32 ((r + k * s) % L)

/-- Verify canonical encodings and the uncofactored equation of §5.1.7
using the challenge integer `k` supplied by the caller, as 64 little-endian
bytes, in full: it is not reduced modulo `L`. `verify` passes
`SHA-512(R || A || M) mod L` (zero-extended to 64 bytes); passing the
unreduced digest checks a different equation (see the module
documentation). -/
def verifyEquation (pk signature challenge : List Byte) : Bool :=
  if pk.length != 32 || signature.length != 64 || challenge.length != 64 then false else
  match decodePoint pk, decodePoint (signature.take 32) with
  | some a, some r =>
    let s := decodeLE (signature.drop 32)
    s < L && pointEqual (pointMul s basePoint)
      (pointAdd r (pointMul (decodeLE challenge) a))
  | _, _ => false

/-- Ed25519 verification (§5.1.7), including all encoding checks, with the
challenge `k = SHA-512(R || A || M)` reduced modulo `L` as in §6. -/
def verify (pk message signature : List Byte) : Bool :=
  verifyEquation pk signature
    (encodeLE 64 (decodeLE (Sha512.sha512 (signature.take 32 ++ pk ++ message)) % L))

end VG.Spec.Ed25519
