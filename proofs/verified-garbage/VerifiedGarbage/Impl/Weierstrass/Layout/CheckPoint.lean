module

public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# The check of a public point: its curves and the slots of their working space

Not trusted: what the code of the curves' internal functions (`Rust.Internal`),
which only verified code calls, is generated from, and where it keeps its
numbers. Their contracts are in `Proof/Weierstrass/CheckPointContract.lean`, in these
namespaces.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.CheckPoint

/-- A curve whose check of a public point is a function: the curve `W` (its
prime `p` and coefficients `a` and `b`), its name (the function is
`vg_<curve>_check_point`, in the Rust module `<curve>_check_point`), the
count `k` of 64-bit words of a number, with `p < 2^(64 k)`, how the
documentation names it, and where the own working space of the functions of
`Proof/Weierstrass/MontContract.lean` that it calls starts and ends (by
default `Mont.ownAt k` and 4096; a target whose layout puts them elsewhere
gives its own). -/
structure Curve where
  W : Spec.Weierstrass.Curve
  curve : String
  k : Nat
  desc : String
  montOwn : Nat := Mont.ownAt k
  montOwnEnd : Nat := 4096

namespace Curve

variable (C : Curve)

/-- Byte offset of slot `i`: `64 + 8 k i`. -/
def slot (i : Nat) : Nat := 64 + 8 * C.k * i

/-- Where `p` is. -/
def pAt : Nat := C.slot 0

/-- Where `a R mod p` is. -/
def aAt : Nat := C.slot 6

/-- Where `G`'s coordinates, as the scalar multiplication takes them, are. -/
def gxAt : Nat := C.slot 8

def gyAt : Nat := C.slot 9

/-- Where the public point's `x` and `y` are. -/
def xAt : Nat := C.slot 33

def yAt : Nat := C.slot 36

/-- Where `x` and `y` in Montgomery's form go. -/
def xmAt : Nat := C.slot 34

def ymAt : Nat := C.slot 35

/-- Where the point the scalar multiplication takes goes. -/
def pxAt : Nat := C.slot 38

def pyAt : Nat := C.slot 43

/-- Where `R² mod p` is. -/
def r2At : Nat := C.slot 39

/-- Where `b R mod p` is. -/
def bAt : Nat := C.slot 40

/-- Where the flag is: its first 64-bit word. -/
def flagAt : Nat := C.slot 44

/-- `R = 2^(64 k)`. -/
def R : Nat := 2 ^ (64 * C.k)

end Curve

/-! ## The curves -/

def p192 : Curve := { W := Spec.P192.curve, curve := "p192", k := 4, desc := "P-192" }

def p224 : Curve := { W := Spec.P224.curve, curve := "p224", k := 4, desc := "P-224" }

def p256 : Curve := { W := Spec.P256.curve, curve := "p256", k := 4, desc := "P-256" }

def secp256k1 : Curve := { W := Spec.Secp256k1.curve, curve := "secp256k1", k := 4, desc := "secp256k1" }

def p384 : Curve := { W := Spec.P384.curve, curve := "p384", k := 6, desc := "P-384" }

def p521 : Curve := { W := Spec.P521.curve, curve := "p521", k := 9, desc := "P-521" }

def brainpoolp256r1 : Curve :=
  { W := Spec.BrainpoolP256r1.curve, curve := "brainpoolp256r1", k := 4, desc := "brainpoolP256r1" }

def brainpoolp384r1 : Curve :=
  { W := Spec.BrainpoolP384r1.curve, curve := "brainpoolp384r1", k := 6, desc := "brainpoolP384r1" }

def brainpoolp512r1 : Curve :=
  { W := Spec.BrainpoolP512r1.curve, curve := "brainpoolp512r1", k := 8, desc := "brainpoolP512r1" }

/-- Every curve. -/
def curves : List Curve := [p192, p224, p256, secp256k1, p384, p521, brainpoolp256r1,
  brainpoolp384r1, brainpoolp512r1]

end VG.Impl.Weierstrass.CheckPoint
