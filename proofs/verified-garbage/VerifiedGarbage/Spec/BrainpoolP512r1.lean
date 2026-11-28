module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve brainpoolP512r1 (RFC 5639)

**Trusted** (as every file in `Spec/`). The domain parameters of brainpoolP512r1,
transcribed from RFC 5639, *Elliptic Curve Cryptography (ECC) Brainpool
Standard Curves and Curve Generation* (March 2010), §3.7, where they are
given in hexadecimal: `p`, `A`, `B`, the base point's `x` and `y`, and its
order `q` (here `n`). The cofactor is 1. Field elements and scalars have
512 bits, so their octet strings have 64 octets (SEC 1 §2.3.5, §2.3.7).
-/

@[expose] public section

namespace VG.Spec.BrainpoolP512r1

/-- The prime `p`. -/
def p : Nat :=
  0xaadd9db8dbe9c48b3fd4e6ae33c9fc07cb308db3b3c9d20ed6639cca703308717d4d9b009bc66842aecda12ae6a380e62881ff2f2d82c68528aa6056583a48f3

/-- The order of the base point (RFC 5639's `q`). -/
def n : Nat :=
  0xaadd9db8dbe9c48b3fd4e6ae33c9fc07cb308db3b3c9d20ed6639cca70330870553e5c414ca92619418661197fac10471db1d381085ddaddb58796829ca90069

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- brainpoolP512r1: `y² = x³ + Ax + B` over `GF(p)`, with 64-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := 0x7830a3318b603b89e2327145ac234cc594cbdd8d3df91610a83441caea9863bc2ded5d5aa8253aa10a2ef1c98b9ac8b57f1117a72bf2c7b9e7c1ac4d77fc94ca
  b := 0x3df91610a83441caea9863bc2ded5d5aa8253aa10a2ef1c98b9ac8b57f1117a72bf2c7b9e7c1ac4d77fc94cadc083e67984050b75ebae5dd2809bd638016f723
  gx := 0x81aee4bdd82ed9645a21322e9c4c6a9385ed9f70b5d916c1b43b62eef4d0098eff3b1f78e2d0d48d50d1687b93b97d5f7c6d5047406a5e688b352209bcb9f822
  gy := 0x7dde385d566332ecc0eabfa9cf7822fdf209f70024a57b1aa000c55b881f8111b2dcde494a5f485e5bca4bd88a2763aed1ca2b2fa8f0540678cd1e0f3ad80892
  n := n
  len := 64

end VG.Spec.BrainpoolP512r1
