module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve brainpoolP384r1 (RFC 5639)

**Trusted** (as every file in `Spec/`). The domain parameters of brainpoolP384r1,
transcribed from RFC 5639, *Elliptic Curve Cryptography (ECC) Brainpool
Standard Curves and Curve Generation* (March 2010), §3.6, where they are
given in hexadecimal: `p`, `A`, `B`, the base point's `x` and `y`, and its
order `q` (here `n`). The cofactor is 1. Field elements and scalars have
384 bits, so their octet strings have 48 octets (SEC 1 §2.3.5, §2.3.7).
-/

@[expose] public section

namespace VG.Spec.BrainpoolP384r1

/-- The prime `p`. -/
def p : Nat :=
  0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b412b1da197fb71123acd3a729901d1a71874700133107ec53

/-- The order of the base point (RFC 5639's `q`). -/
def n : Nat :=
  0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b31f166e6cac0425a7cf3ab6af6b7fc3103b883202e9046565

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- brainpoolP384r1: `y² = x³ + Ax + B` over `GF(p)`, with 48-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := 0x7bc382c63d8c150c3c72080ace05afa0c2bea28e4fb22787139165efba91f90f8aa5814a503ad4eb04a8c7dd22ce2826
  b := 0x04a8c7dd22ce28268b39b55416f0447c2fb77de107dcd2a62e880ea53eeb62d57cb4390295dbc9943ab78696fa504c11
  gx := 0x1d1c64f068cf45ffa2a63a81b7c13f6b8847a3e77ef14fe3db7fcafe0cbd10e8e826e03436d646aaef87b2e247d4af1e
  gy := 0x8abe1d7520f9c2a45cb1eb8e95cfd55262b70b29feec5864e19c054ff99129280e4646217791811142820341263c5315
  n := n
  len := 48

end VG.Spec.BrainpoolP384r1
