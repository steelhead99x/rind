module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve P-521 (NIST SP 800-186)

**Trusted** (as every file in `Spec/`). The domain parameters of P-521
(also known as secp521r1), transcribed from NIST SP 800-186,
*Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve
Domain Parameters* (February 2023), §3.2.1.5, where they are given in
decimal (`p`, `n`) and hexadecimal (`b`, `G`). The coefficient `a` is
`-3`, that is `p - 3`. The cofactor is 1. Field elements and scalars have
521 bits, so their octet strings have 66 octets (SEC 1 §2.3.5, §2.3.7), of
which the first is at most 1.
-/

@[expose] public section

namespace VG.Spec.P521

/-- `p = 2⁵²¹ - 1`. -/
def p : Nat := 2 ^ 521 - 1

/-- The order of the base point. -/
def n : Nat :=
  6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- P-521: `y² = x³ - 3x + b` over `GF(p)`, with 66-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := p - 3
  b := 0x051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00
  gx := 0xc6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66
  gy := 0x11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650
  n := n
  len := 66

end VG.Spec.P521
