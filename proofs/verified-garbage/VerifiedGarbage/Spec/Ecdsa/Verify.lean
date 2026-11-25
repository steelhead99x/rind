module

public import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Spec.Ecdsa

/-!
# ECDSA signature verification (FIPS 186-5)

**Trusted** (as every file in `Spec/`). ECDSA signature verification over
any curve of `Spec/Weierstrass.lean`, transcribed from FIPS 186-5, *Digital
Signature Standard (DSS)* (February 2023), §6.4.2, with the hash as the
integer `e` of `Spec/Ecdsa.lean` (`hashToInt`): hashing the message is the
caller's, as for signing.

`verifyWith` is §6.4.2's steps for a public key `Q` and a signature
`(r, s)`:

1. `r` and `s` must be in `[1, n-1]`;
2. (`e`, the hash's integer, is the input);
3. `w = s⁻¹ mod n`, which is `s^(n-2) mod n` (§B.1: `n` is prime);
4. `u = e w mod n` and `v = r w mod n`;
5. `R₁ = uG + vQ`, which must not be `O`;
6. `r₁ = x_{R₁} mod n`;
7. the signature is valid iff `r₁ = r`.

§6.4.2 requires assurance of the public key's validity before it is used:
`verify` takes the key as an octet string `04 ‖ x ‖ y` and validates it as
`EcKey.decodePublicKey` does (SP 800-56A §5.6.2.3.3), rejecting the
signature if it is not a valid public key; and the signature as `len`
octets of `r` then `len` octets of `s` (the encoding of `encode`).
-/

@[expose] public section

namespace VG.Spec.Ecdsa

open Weierstrass

variable (C : Curve)

/-- Whether `(r, s)` is a valid signature of the hash integer `e` with the
public key `Q` (§6.4.2). -/
def verifyWith (Q : Point C) (e r s : Nat) : Bool :=
  if 1 ≤ r ∧ r < C.n ∧ 1 ≤ s ∧ s < C.n then
    let w : Scalar C := pow (Fin.ofNat C.n s) (C.n - 2)
    let u : Scalar C := Fin.ofNat C.n e * w
    let v : Scalar C := Fin.ofNat C.n r * w
    match add (mul u.val (G C)) (mul v.val Q) with
    | .infinity => false
    | .affine x _ => x.val % C.n == r
  else false

/-- Whether the octet string `sig` (`r` then `s`, `len` octets each) is a
valid signature of the hash integer `e` with the public key whose octet
string is `pub` (`04 ‖ x ‖ y`): false if `pub` is not a valid public key. -/
def verify (pub : List Byte) (e : Nat) (sig : List Byte) : Bool :=
  match EcKey.decodePublicKey C pub with
  | some Q => verifyWith C Q e (ofBytes (sig.take C.len)) (ofBytes (sig.drop C.len))
  | none => false

end VG.Spec.Ecdsa
