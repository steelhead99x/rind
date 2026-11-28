module

public import VerifiedGarbage.Impl.Weierstrass.Layout.Point

/-!
# Inverses modulo a curve's prime and order: its curves and the slots of their working space

Not trusted: what the code of the curves' internal functions (`Rust.Internal`),
which only verified code calls, is generated from, and where it keeps its
numbers. The definitions their proofs share are in
`Proof/Weierstrass/InverseContract.lean`, in these namespaces.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Inverse

/-- A curve whose inversions are functions: the curve `W` (its prime `p` and
order `n`), its name (the functions are `vg_<curve>_inv_mod_p` and
`vg_<curve>_inv_mod_n`, in the Rust module `<curve>_inverse`), the count `k`
of 64-bit words of a number, with `p, n < 2^(64 k)`, how the documentation
names it, the slot of its products' temporary area, and how many bytes its
working area has beyond `64 k + 64` (`workLen`). -/
structure Curve where
  W : Spec.Weierstrass.Curve
  curve : String
  k : Nat
  desc : String
  tmp : Nat
  workExtra : Nat := 0

namespace Curve

variable (C : Curve)

/-- Byte offset of slot `i`: `64 + 8 k i`. -/
def slot (i : Nat) : Nat := 64 + 8 * C.k * i

/-- Where `p` is. -/
def pAt : Nat := C.slot 0

/-- Where `n` is. -/
def nAt : Nat := C.slot 1

/-- Where `Z`, the number `inv_mod_p` inverts, is. -/
def zAt : Nat := C.slot 16

/-- Where `x`, the number `inv_mod_n` inverts, is. -/
def xAt : Nat := C.slot 37

/-- Where the result `A` is. -/
def outAt : Nat := C.slot 29

/-- Where the products' temporary area is. -/
def tmpAt : Nat := C.slot C.tmp

/-- Where the inversion's working area is: past three tables of `64 k + 8`
bytes from slot 45. -/
def workAt : Nat := C.slot 45 + 3 * (64 * C.k + 8)

/-- The bytes of the working area. -/
def workLen : Nat := 64 * C.k + 64 + C.workExtra

end Curve

/-! ## The curves -/

def p192 : Curve := { W := Spec.P192.curve, curve := "p192", k := 4, desc := "P-192", tmp := 2 }

def p224 : Curve := { W := Spec.P224.curve, curve := "p224", k := 4, desc := "P-224", tmp := 2 }

def p256 : Curve := { W := Spec.P256.curve, curve := "p256", k := 4, desc := "P-256", tmp := 2 }

def secp256k1 : Curve :=
  { W := Spec.Secp256k1.curve, curve := "secp256k1", k := 4, desc := "secp256k1", tmp := 2 }

def p384 : Curve := { W := Spec.P384.curve, curve := "p384", k := 6, desc := "P-384", tmp := 83 }

/-- P-521's working area has 72 more bytes (712 in all), for code whose
inversion keeps `9 k` words and the registers it saves there. -/
def p521 : Curve :=
  { W := Spec.P521.curve, curve := "p521", k := 9, desc := "P-521", tmp := 55, workExtra := 72 }

def brainpoolp256r1 : Curve :=
  { W := Spec.BrainpoolP256r1.curve, curve := "brainpoolp256r1", k := 4, desc := "brainpoolP256r1",
    tmp := 2 }

def brainpoolp384r1 : Curve :=
  { W := Spec.BrainpoolP384r1.curve, curve := "brainpoolp384r1", k := 6, desc := "brainpoolP384r1",
    tmp := 83 }

def brainpoolp512r1 : Curve :=
  { W := Spec.BrainpoolP512r1.curve, curve := "brainpoolp512r1", k := 8, desc := "brainpoolP512r1",
    tmp := 2, workExtra := 48 }

/-- Every curve. -/
def curves : List Curve := [p192, p224, p256, secp256k1, p384, p521, brainpoolp256r1, brainpoolp384r1,
  brainpoolp512r1]

end VG.Impl.Weierstrass.Inverse
