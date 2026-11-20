module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# Elliptic curve key pairs and public keys

**Trusted** (as every file in `Spec/`). For any curve of
`Spec/Weierstrass.lean`:

* the public key `Q = dG` of a private key `d` in `[1, n-1]` (FIPS 186-5
  §A.2, NIST SP 800-56A Rev. 3 §5.6.1.2);
* the uncompressed octet-string form of a point, `04 ‖ x ‖ y` (SEC 1 v2
  §2.3.3, with point compression off), and of `O`, `00`;
* the conversion of an octet string to a public key (SEC 1 §2.3.4, for the
  uncompressed form only) with public-key validation (SP 800-56A §5.6.2.3.3):
  `Q ≠ O`, both coordinates in `[0, p-1]` and `Q` on the curve. The last
  check of §5.6.2.3.3, `nQ = O`, holds for every point on the curve when
  the cofactor is 1, as it is for every curve specified here.

The compressed form (`02`/`03 ‖ x`) is specified separately in
`EcKey/Compressed.lean`. This module's `decodePublicKey` continues to
accept only the uncompressed form.
-/

@[expose] public section

namespace VG.Spec.EcKey

open Weierstrass

variable (C : Curve)

/-- The public key `Q = dG`, for a private key `d` in `[1, n-1]`. -/
def publicKey (d : Nat) : Option (Point C) :=
  if 1 ≤ d ∧ d < C.n then some (mul d (G C)) else none

variable {C}

/-- Elliptic-Curve-Point-to-Octet-String (SEC 1 §2.3.3), uncompressed:
`00` for `O`, and `04 ‖ x ‖ y`, each coordinate in `len` octets, for an
affine point. -/
def encodePoint : Point C → List Byte
  | .infinity => [0]
  | .affine x y => 4 :: (toBytes C.len x.val ++ toBytes C.len y.val)

variable (C)

/-- The public key of an octet string `04 ‖ x ‖ y` of `2 len + 1` octets
(SEC 1 §2.3.4), validated (SP 800-56A §5.6.2.3.3): `x` and `y` in
`[0, p-1]`, and `(x, y)` on the curve. Every other string (`00`, which is
`O`, and compressed points included) is rejected. -/
def decodePublicKey (bs : List Byte) : Option (Point C) :=
  if bs.length = 2 * C.len + 1 ∧ bs.head? = some 4 then
    let x := ofBytes ((bs.drop 1).take C.len)
    let y := ofBytes (bs.drop (C.len + 1))
    if h : x < C.p ∧ y < C.p then
      let Q : Point C := .affine ⟨x, h.1⟩ ⟨y, h.2⟩
      if onCurve C Q then some Q else none
    else none
  else none

end VG.Spec.EcKey
