module

public import VerifiedGarbage.Impl.Weierstrass.Layout.MulBase

/-!
# The multiplication of a point: its curves and the slots of their working space

Not trusted: what the code of the curves' internal functions (`Rust.Internal`),
which only verified code calls, is generated from, and where it keeps its
numbers. The definitions their proofs share are in
`Proof/Weierstrass/MulContract.lean`, in these namespaces.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Mul

/-- A curve whose points' multiplication is a function: the curve `W` (its
group and prime `p`), its name (the function is `vg_<curve>_mul`, in the
Rust module `<curve>_mul`), the count `k` of 64-bit words of a coordinate,
with `p < 2^(64 k)`, how the documentation names it, the slot of its
products' temporary area, the count of words past the table of bits
where the function may keep the callee-saved registers it changes, whether
slot 40 and every byte from slot 45 on are the function's own working space
too (`tail`), and whether the result is stated only for `k` in `[1, n - 1]`
(`inRange`). -/
structure Curve where
  W : Spec.Weierstrass.Curve
  curve : String
  k : Nat
  desc : String
  tmp : Nat
  saved : Nat := 1
  tail : Bool := false
  inRange : Bool := false

namespace Curve

variable (C : Curve)

/-- The curve's coordinates, as `Proof/Weierstrass/PointContract.lean` has them. -/
def toPoint : Point.Curve := { curve := C.curve, p := C.W.p, k := C.k, desc := C.desc }

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

/-- Where one (`R mod p`) is. -/
def oneAt : Nat := C.slot 5

/-- Where `a R mod p` is. -/
def aAt : Nat := C.slot 6

/-- Where `3 b R mod p` is. -/
def b3At : Nat := C.slot 7

/-- Where the point `Q` is: its affine coordinates, `x` then `y`, where the
result goes. -/
def qAt : Nat := C.pAt

/-- `x R mod p`: the Montgomery form of `x`. -/
def mont (x : Nat) : Nat := x * 2 ^ (64 * C.k) % C.W.p

end Curve

/-! ## The curves -/

def p192 : Curve := { W := Spec.P192.curve, curve := "p192", k := 4, desc := "P-192", tmp := 2 }

/-! P-224's, P-256's, P-384's and P-521's code multiplies by windows (`tail`,
`inRange`). Their temporary slot is slot 2 for every word count: ARMv7's,
PPC64LE's and x86's code names slot 2 as its products' temporary area (which
calls of the Montgomery functions leave), and the temporary areas that
x86-64's and AArch64's products write for six and nine words (slots 83 and
55, `Impl.Ecdsa.X86_64.Cfg.sl`; 82 and 54, `Mont.moAt`) are in the tail,
their slot 2's place unused. -/

def p224 : Curve :=
  { W := Spec.P224.curve, curve := "p224", k := 4, desc := "P-224", tmp := 2, tail := true,
    inRange := true }

def p256 : Curve :=
  { W := Spec.P256.curve, curve := "p256", k := 4, desc := "P-256", tmp := 2, tail := true,
    inRange := true }

def p384 : Curve :=
  { W := Spec.P384.curve, curve := "p384", k := 6, desc := "P-384", tmp := 2, tail := true,
    inRange := true }

def p521 : Curve :=
  { W := Spec.P521.curve, curve := "p521", k := 9, desc := "P-521", tmp := 2, tail := true,
    inRange := true }

def secp256k1 : Curve :=
  { W := Spec.Secp256k1.curve, curve := "secp256k1", k := 4, desc := "secp256k1", tmp := 2 }

def brainpoolp256r1 : Curve :=
  { W := Spec.BrainpoolP256r1.curve, curve := "brainpoolp256r1", k := 4, desc := "brainpoolP256r1",
    tmp := 2 }

/-- brainpoolP384r1's temporary area is in slot 83's place, as P-384's is for six
words (`Impl.Ecdsa.X86_64.Cfg.sl`). -/
def brainpoolp384r1 : Curve :=
  { W := Spec.BrainpoolP384r1.curve, curve := "brainpoolp384r1", k := 6, desc := "brainpoolP384r1",
    tmp := 83 }

def brainpoolp512r1 : Curve :=
  { W := Spec.BrainpoolP512r1.curve, curve := "brainpoolp512r1", k := 8, desc := "brainpoolP512r1",
    tmp := 2, saved := 6 }

/-- Every curve. -/
def curves : List Curve :=
  [p192, p224, p256, p384, p521, secp256k1, brainpoolp256r1, brainpoolp384r1, brainpoolp512r1]

end VG.Impl.Weierstrass.Mul
