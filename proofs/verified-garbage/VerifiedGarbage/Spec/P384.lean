module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve P-384 (NIST SP 800-186)

**Trusted** (as every file in `Spec/`). The domain parameters of P-384
(also known as secp384r1), transcribed from NIST SP 800-186,
*Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve
Domain Parameters* (February 2023), §3.2.1.4, where they are given in
decimal (`p`, `n`) and hexadecimal (`b`, `G`). The coefficient `a` is
`-3`, that is `p - 3`. The cofactor is 1.
-/

@[expose] public section

namespace VG.Spec.P384

/-- `p = 2³⁸⁴ - 2¹²⁸ - 2⁹⁶ + 2³² - 1`. -/
def p : Nat := 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1

/-- The order of the base point. -/
def n : Nat :=
  39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- P-384: `y² = x³ - 3x + b` over `GF(p)`, with 48-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := p - 3
  b := 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
  gx := 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
  gy := 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
  n := n
  len := 48

end VG.Spec.P384
