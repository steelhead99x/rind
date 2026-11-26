module

public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Point addition on a curve, in Montgomery form: its curves and working space

Not trusted: what the code of the curves' internal functions (`Rust.Internal`),
which only verified code calls, is generated from, and where it keeps its
numbers. The definitions their proofs share are in
`Proof/Weierstrass/PointContract.lean`, in these namespaces.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Point

/-- The bytes of a coordinate of `k` words. -/
def elemBytes (k : Nat) : Nat := 8 * k

/-- Where the functions' own working space starts: six coordinates and 64
bytes for saved registers below that of the functions of
`Proof/Weierstrass/MontContract.lean`, which ends at byte 4096. -/
def ownAt (k : Nat) : Nat := Mont.ownAt k - 6 * elemBytes k - 64

/-- Where `3b` is: just below the own working space. -/
def b3At (k : Nat) : Nat := ownAt k - elemBytes k

/-- Where `a` is: just below `3b`. -/
def aAt (k : Nat) : Nat := b3At k - elemBytes k

/-- Where `Q` is: just below `a`. -/
def qAt (k : Nat) : Nat := aAt k - 3 * elemBytes k

/-- Where `P` is: just below `Q`. -/
def pAt (k : Nat) : Nat := qAt k - 3 * elemBytes k

/-- Where the result `O` is: just below `P`. -/
def oAt (k : Nat) : Nat := pAt k - 3 * elemBytes k

/-- A curve whose point addition is a function: its name (the functions are
`vg_<curve>_point_add` and `vg_<curve>_point_double`, in the Rust module
`<curve>_point`), its prime `p`, the count `k` of 64-bit words of a
coordinate, with `p < 2^(64 k)`. -/
structure Curve where
  curve : String
  p : Nat
  k : Nat
  /-- How the documentation names the curve. -/
  desc : String
  [p_ne_zero : NeZero p]

attribute [instance] Curve.p_ne_zero

namespace Curve

variable (C : Curve)

/-- `R = 2^(64 k)`. -/
def R : Nat := 2 ^ (64 * C.k)

end Curve

/-! ## The curves -/

def p192 : Curve := { curve := "p192", p := Spec.P192.p, k := 3, desc := "P-192" }

def p224 : Curve := { curve := "p224", p := Spec.P224.p, k := 4, desc := "P-224" }

def p256 : Curve := { curve := "p256", p := Spec.P256.p, k := 4, desc := "P-256" }

def p384 : Curve := { curve := "p384", p := Spec.P384.p, k := 6, desc := "P-384" }

def brainpoolp256r1 : Curve :=
  { curve := "brainpoolp256r1", p := Spec.BrainpoolP256r1.p, k := 4, desc := "brainpoolP256r1" }

def brainpoolp384r1 : Curve :=
  { curve := "brainpoolp384r1", p := Spec.BrainpoolP384r1.p, k := 6, desc := "brainpoolP384r1" }

end VG.Impl.Weierstrass.Point
