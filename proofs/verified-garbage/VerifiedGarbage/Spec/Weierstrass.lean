module

public import VerifiedGarbage.TCB.Mem

/-!
# Elliptic curves in short Weierstrass form over prime fields (SEC 1)

**Trusted** (as every file in `Spec/`). The curves `y² = x³ + a x + b` over
`GF(p)` for a prime `p > 3`, transcribed from SEC 1 v2.0, *Elliptic Curve
Cryptography* (Certicom Research, May 2009): the group law of §2.2.1, scalar
multiplication, and the conversions between integers and octet strings of
§2.3. Every NIST prime curve (P-192, P-224, P-256, P-384, P-521), secp256k1
and the brainpool `r1` curves are of this form; each is a `Curve`, in its
own file (`Spec/P256.lean`, …), and the algorithms using them (`Spec/Ecdsa.lean`,
…) take the curve as a parameter.

Field elements are `Fin p`, with arithmetic modulo `p`. Division is
multiplication by the inverse `x⁻¹ = x^(p-2)` (Fermat's little theorem,
since `p` is prime; SEC 1 §2.1.1 leaves the method open). Points are the
point at infinity `O` or affine points `(x, y)`. The group operations are
only applied to points on the curve by the algorithms of `Spec/`.

This is a mathematical specification. Its branches on secret values are not
an implementation or a claim about timing: the contracts say what may
affect timing.
-/

@[expose] public section

namespace VG.Spec.Weierstrass

/-- Elliptic curve domain parameters over `GF(p)` (SEC 1 §3.1.1): the prime
`p`, the coefficients `a` and `b` of `y² = x³ + a x + b`, the base point
`G = (gx, gy)` and its order `n`, which is prime. The cofactor is 1 for every
curve specified here (`#E(GF(p)) = n`), so it is not a parameter. `len` is the
length in octets of a field element, `⌈log₂ p / 8⌉` (§2.3.5); every curve
here has the same length for its scalars modulo `n`. -/
structure Curve where
  p : Nat
  a : Nat
  b : Nat
  gx : Nat
  gy : Nat
  n : Nat
  len : Nat
  [p_ne_zero : NeZero p]
  [n_ne_zero : NeZero n]

attribute [instance] Curve.p_ne_zero Curve.n_ne_zero

variable (C : Curve)

/-- An element of `GF(p)`. -/
abbrev Fe := Fin C.p

/-- An integer modulo `n`. -/
abbrev Scalar := Fin C.n

/-- Exponentiation modulo `m` by square-and-multiply; `a ^ 0 = 1`. -/
def pow {m : Nat} [NeZero m] (a : Fin m) (e : Nat) : Fin m :=
  if e = 0 then 1 else
  let r := pow (a * a) (e / 2)
  if e % 2 = 0 then r else a * r
termination_by e
decreasing_by omega

variable {C}

/-- The inverse `x⁻¹ = x^(p-2)` of a nonzero field element (Fermat's little
theorem). -/
def inv (x : Fe C) : Fe C := pow x (C.p - 2)

variable (C)

/-- A point: the point at infinity `O`, or an affine point `(x, y)`
(SEC 1 §2.2.1). -/
inductive Point
  | infinity
  | affine (x y : Fe C)
  deriving DecidableEq

/-- The point satisfies the curve equation `y² = x³ + a x + b`, and so is on
the curve (`O` is too). -/
def onCurve : Point C → Bool
  | .infinity => true
  | .affine x y => y * y = x * x * x + Fin.ofNat C.p C.a * x + Fin.ofNat C.p C.b

/-- The base point `G`. -/
def G : Point C := .affine (Fin.ofNat C.p C.gx) (Fin.ofNat C.p C.gy)

variable {C}

/-- The group law of SEC 1 §2.2.1, for points on the curve:

1. `O + O = O`;
2. `(x, y) + O = O + (x, y) = (x, y)`;
3. `(x, y) + (x, -y) = O`;
4. for `x₁ ≠ x₂`, `(x₁, y₁) + (x₂, y₂) = (x₃, y₃)`, with
   `λ = (y₂ - y₁)/(x₂ - x₁)`, `x₃ = λ² - x₁ - x₂`, `y₃ = λ(x₁ - x₃) - y₁`;
5. for `y₁ ≠ 0`, `(x₁, y₁) + (x₁, y₁) = (x₃, y₃)`, with
   `λ = (3x₁² + a)/(2y₁)`, `x₃ = λ² - 2x₁`, `y₃ = λ(x₁ - x₃) - y₁`.

On the curve, `x₁ = x₂` means `y₂ = ±y₁`, so the last case is the
remaining one: `y₂ = y₁ ≠ 0`. -/
def add : Point C → Point C → Point C
  | .infinity, q => q
  | p, .infinity => p
  | .affine x₁ y₁, .affine x₂ y₂ =>
    if x₁ = x₂ ∧ y₂ = -y₁ then .infinity
    else if x₁ ≠ x₂ then
      let l := (y₂ - y₁) * inv (x₂ - x₁)
      let x₃ := l * l - x₁ - x₂
      .affine x₃ (l * (x₁ - x₃) - y₁)
    else
      let l := (3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)
      let x₃ := l * l - 2 * x₁
      .affine x₃ (l * (x₁ - x₃) - y₁)

/-- Scalar multiplication `kP = P + P + ⋯ + P` (`k` terms; `0P = O`) of
SEC 1 §2.2.1, by double-and-add from the most significant bit of `k`:
`(2m)P = mP + mP` and `(2m + 1)P = (mP + mP) + P`. (That this is the sum of
`k` copies of `P` uses the associativity of the group law.) -/
def mul (k : Nat) (P : Point C) : Point C :=
  if k = 0 then .infinity else
  let Q := mul (k / 2) P
  let Q := add Q Q
  if k % 2 = 0 then Q else add Q P
termination_by k
decreasing_by omega

/-! ## Octet strings (SEC 1 §2.3) -/

/-- Integer-to-Octet-String (§2.3.7): the `len` octets of `x < 256^len`, most
significant first. -/
def toBytes (len x : Nat) : List Byte :=
  (List.range len).reverse.map fun i => BitVec.ofNat 8 (x >>> (8 * i))

/-- Octet-String-to-Integer (§2.3.8): the octets read as an unsigned integer,
most significant first. -/
def ofBytes (bs : List Byte) : Nat :=
  bs.foldl (fun acc b => 256 * acc + b.toNat) 0

end VG.Spec.Weierstrass
