module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve brainpoolP256r1 (RFC 5639)

**Trusted** (as every file in `Spec/`). The domain parameters of brainpoolP256r1,
transcribed from RFC 5639, *Elliptic Curve Cryptography (ECC) Brainpool
Standard Curves and Curve Generation* (March 2010), §3.4, where they are
given in hexadecimal: `p`, `A`, `B`, the base point's `x` and `y`, and its
order `q` (here `n`). The cofactor is 1. Field elements and scalars have
256 bits, so their octet strings have 32 octets (SEC 1 §2.3.5, §2.3.7).
-/

@[expose] public section

namespace VG.Spec.BrainpoolP256r1

/-- The prime `p`. -/
def p : Nat :=
  0xa9fb57dba1eea9bc3e660a909d838d726e3bf623d52620282013481d1f6e5377

/-- The order of the base point (RFC 5639's `q`). -/
def n : Nat :=
  0xa9fb57dba1eea9bc3e660a909d838d718c397aa3b561a6f7901e0e82974856a7

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- brainpoolP256r1: `y² = x³ + Ax + B` over `GF(p)`, with 32-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := 0x7d5a0975fc2c3057eef67530417affe7fb8055c126dc5c6ce94a4b44f330b5d9
  b := 0x26dc5c6ce94a4b44f330b5d9bbd77cbf958416295cf7e1ce6bccdc18ff8c07b6
  gx := 0x8bd2aeb9cb7e57cb2c4b482ffc81b7afb9de27e1e3bd23c23a4453bd9ace3262
  gy := 0x547ef835c3dac4fd97f8461a14611dc9c27745132ded8e545c1d54c72f046997
  n := n
  len := 32

end VG.Spec.BrainpoolP256r1
