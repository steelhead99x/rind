module

public import VerifiedGarbage.Impl.Weierstrass.Layout.Point

/-!
# The multiplication of a curve's base point: its curves and the slots of their working space

Not trusted: what the code of the curves' internal functions (`Rust.Internal`),
which only verified code calls, is generated from, and where it keeps its
numbers. The definitions their proofs share are in
`Proof/Weierstrass/MulBaseContract.lean`, in these namespaces.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.MulBase

/-- A curve whose base point's multiplication is a function: the curve `W`
(its group, base point and prime `p`), its name (the function is
`vg_<curve>_mul_base`, in the Rust module `<curve>_mul_base`), the count `k`
of 64-bit words of a coordinate, with `p < 2^(64 k)`, how the documentation
names it, the slot of its products' temporary area, and whether every byte
from slot 45 on is the function's own working space too. -/
structure Curve where
  W : Spec.Weierstrass.Curve
  curve : String
  k : Nat
  desc : String
  tmp : Nat
  tail : Bool := false

namespace Curve

variable (C : Curve)

/-- Byte offset of slot `i`: `64 + 8 k i`. -/
def slot (i : Nat) : Nat := 64 + 8 * C.k * i

/-- Where the prime `p` is. -/
def modAt : Nat := C.slot 0

/-- Where zero is. -/
def zeroAt : Nat := C.slot 3

/-- Where the result `P` is. -/
def pAt : Nat := C.slot 14

/-- Where the scalar `k` is. -/
def kAt : Nat := C.slot 31

/-- Where the table of `k`'s bits is. -/
def bitsAt : Nat := C.slot 45

/-- Where the products' temporary area is. -/
def tmpAt : Nat := C.slot C.tmp

/-- The bytes of a point. -/
def ptBytes : Nat := 24 * C.k

end Curve

/-! ## The curves -/

def p224 : Curve := { W := Spec.P224.curve, curve := "p224", k := 4, desc := "P-224", tmp := 2 }

def p256 : Curve := { W := Spec.P256.curve, curve := "p256", k := 4, desc := "P-256", tmp := 2 }

def p384 : Curve := { W := Spec.P384.curve, curve := "p384", k := 6, desc := "P-384", tmp := 83 }

/-- P-521's temporary area is in slot 55's place, as x86-64's has it for nine
words (`Impl.Ecdsa.X86_64.Cfg.sl`, as `Proof/Weierstrass/InverseContract.lean`'s
`p521`); AArch64's products keep theirs in slot 54's (`Mont.moAt`), and
ARMv7's, PPC64LE's and x86's Montgomery functions their working space below
byte 4096: `tail` makes all of them the function's. -/
def p521 : Curve :=
  { W := Spec.P521.curve, curve := "p521", k := 9, desc := "P-521", tmp := 55, tail := true }

/-- Every curve. -/
def curves : List Curve := [p224, p256, p384, p521]

end VG.Impl.Weierstrass.MulBase
