module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve P-256 (NIST SP 800-186)

**Trusted** (as every file in `Spec/`). The domain parameters of P-256
(also known as secp256r1 and prime256v1), transcribed from NIST SP 800-186,
*Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve
Domain Parameters* (February 2023), §3.2.1.3, where they are given in
decimal (`p`, `n`) and hexadecimal (`b`, `G`). The coefficient `a` is
`-3`, that is `p - 3`. The cofactor is 1.
-/

@[expose] public section

namespace VG.Spec.P256

/-- `p = 2²⁵⁶ - 2²²⁴ + 2¹⁹² + 2⁹⁶ - 1`. -/
def p : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- The order of the base point. -/
def n : Nat := 115792089210356248762697446949407573529996955224135760342422259061068512044369

instance : NeZero p := ⟨by decide⟩
instance : NeZero n := ⟨by decide⟩

/-- P-256: `y² = x³ - 3x + b` over `GF(p)`, with 32-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := p - 3
  b := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  gx := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
  gy := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
  n := n
  len := 32

end VG.Spec.P256
