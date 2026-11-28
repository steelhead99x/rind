module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve P-224 (NIST SP 800-186)

**Trusted** (as every file in `Spec/`). The domain parameters of P-224
(also known as secp224r1), transcribed from NIST SP 800-186,
*Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve
Domain Parameters* (February 2023), §3.2.1.2, where they are given in
decimal (`p`, `n`) and hexadecimal (`b`, `G`). The coefficient `a` is
`-3`, that is `p - 3`. The cofactor is 1. Field elements and scalars have
224 bits, so their octet strings have 28 octets (SEC 1 §2.3.5, §2.3.7).
-/

@[expose] public section

namespace VG.Spec.P224

/-- `p = 2²²⁴ - 2⁹⁶ + 1`. -/
def p : Nat := 2 ^ 224 - 2 ^ 96 + 1

/-- The order of the base point. -/
def n : Nat := 26959946667150639794667015087019625940457807714424391721682722368061

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- P-224: `y² = x³ - 3x + b` over `GF(p)`, with 28-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := p - 3
  b := 0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4
  gx := 0xb70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21
  gy := 0xbd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34
  n := n
  len := 28

end VG.Spec.P224
