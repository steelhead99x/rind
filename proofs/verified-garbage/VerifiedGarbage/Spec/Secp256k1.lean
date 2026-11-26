module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve secp256k1 (SEC 2)

**Trusted** (as every file in `Spec/`). The domain parameters of secp256k1,
transcribed from SEC 2, *Recommended Elliptic Curve Domain Parameters*,
version 2.0 (Certicom Research, January 2010), §2.4.1, where they are given
in hexadecimal: `p`, `a`, `b`, the base point `G` (uncompressed: `04 ‖ x ‖
y`) and its order `n`. The coefficient `a` is `0`. The cofactor is 1. Field
elements and scalars have 256 bits, so their octet strings have 32 octets
(SEC 1 §2.3.5, §2.3.7).
-/

@[expose] public section

namespace VG.Spec.Secp256k1

/-- `p = 2²⁵⁶ - 2³² - 2⁹ - 2⁸ - 2⁷ - 2⁶ - 2⁴ - 1`. -/
def p : Nat :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

/-- The order of the base point. -/
def n : Nat :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- secp256k1: `y² = x³ + 7` over `GF(p)`, with 32-octet field elements and
scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := 0
  b := 7
  gx := 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
  gy := 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
  n := n
  len := 32

end VG.Spec.Secp256k1
