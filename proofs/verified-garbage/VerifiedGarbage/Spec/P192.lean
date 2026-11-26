module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve P-192 (NIST SP 800-186)

**Trusted** (as every file in `Spec/`). The domain parameters of P-192
(also known as secp192r1), transcribed from NIST SP 800-186,
*Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve
Domain Parameters* (February 2023), §3.2.1.1, where they are given in
decimal (`p`, `n`) and hexadecimal (`b`, `G`), and which allows the curve
for legacy use only. The coefficient `a` is `-3`, that is `p - 3`. The
cofactor is 1. Field elements and scalars have 192 bits, so their octet
strings have 24 octets (SEC 1 §2.3.5, §2.3.7).
-/

@[expose] public section

namespace VG.Spec.P192

/-- `p = 2¹⁹² - 2⁶⁴ - 1`. -/
def p : Nat := 2 ^ 192 - 2 ^ 64 - 1

/-- The order of the base point. -/
def n : Nat := 6277101735386680763835789423176059013767194773182842284081

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- P-192: `y² = x³ - 3x + b` over `GF(p)`, with 24-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := p - 3
  b := 0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1
  gx := 0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012
  gy := 0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811
  n := n
  len := 24

end VG.Spec.P192
