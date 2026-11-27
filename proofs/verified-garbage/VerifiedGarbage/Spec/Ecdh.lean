module

public import VerifiedGarbage.Spec.EcKey

/-!
# Elliptic curve Diffie-Hellman (NIST SP 800-56A)

**Trusted** (as every file in `Spec/`). The ECC CDH primitive of NIST
SP 800-56A Rev. 3, §5.7.1.2, for any curve of `Spec/Weierstrass.lean`:
the shared secret of the private key `d` and the peer's public key `Q` is
the x-coordinate of `P = h d Q` (the cofactor `h` is 1 here), as `len`
octets (the Field-Element-to-Byte-String conversion, SEC 1 §2.3.5), and an
error if `P = O`. The peer's public key is an octet string, validated as
`EcKey.decodePublicKey` does (§5.6.2.3.3), which §5.6.2.2.2 requires
before it is used.
-/

@[expose] public section

namespace VG.Spec.Ecdh

open Weierstrass

variable (C : Curve)

/-- The shared secret `Z` of the private key `d`, in `[1, n-1]`, and the
peer's public key `peer` (an octet string `04 ‖ x ‖ y`), or `none` if `d` is
out of range, `peer` is not a valid public key, or `dQ = O`. -/
def exchange (d : Nat) (peer : List Byte) : Option (List Byte) :=
  if 1 ≤ d ∧ d < C.n then
    match EcKey.decodePublicKey C peer with
    | some Q =>
      match mul d Q with
      | .affine x _ => some (toBytes C.len x.val)
      | .infinity => none
    | none => none
  else none

end VG.Spec.Ecdh
