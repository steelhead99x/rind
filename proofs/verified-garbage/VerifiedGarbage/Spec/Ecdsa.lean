module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# ECDSA signature generation (FIPS 186-5)

**Trusted** (as every file in `Spec/`). ECDSA over any curve of
`Spec/Weierstrass.lean`, transcribed from FIPS 186-5, *Digital Signature
Standard (DSS)* (February 2023), §6.4.1, with the private key `d` and the
per-message secret number `k` as inputs: how `k` is chosen (randomly, as in
§A.3, or deterministically, as in RFC 6979) is the caller's, and so is
hashing the message.

The hash `H` enters as the integer `e` of the leftmost `min(N, hashlen)`
bits of `H`, `N` being the bit length of `n` (`hashToInt`). The inverse
`k⁻¹ mod n` is `k^(n-2) mod n` (§B.1: `n` is prime). The signature is the
pair `(r, s)`; `encode` gives its usual fixed-length encoding, `r` then `s`,
each in `len` octets.
-/

@[expose] public section

namespace VG.Spec.Ecdsa

open Weierstrass

variable (C : Curve)

/-- `N`, the bit length of `n`. -/
def nBits : Nat := C.n.log2 + 1

/-- The integer `e` of the leftmost `min(N, hashlen)` bits of the hash `H`
(§6.4.1, with the Bit String to Integer conversion of §B.2.1). -/
def hashToInt (H : List Byte) : Nat :=
  if 8 * H.length ≤ nBits C then ofBytes H else ofBytes H >>> (8 * H.length - nBits C)

/-- The signature of the hash integer `e` with the private key `d` and the
per-message secret number `k` (§6.4.1): `R = kG`, `r = x_R mod n` and
`s = k⁻¹ (e + r d) mod n`. It is `none` if `d` or `k` is not in `[1, n-1]`
(§6.2.1, §A.3), or if `r = 0` or `s = 0`, for which §6.4.1 chooses another
`k`; `R = O` does not happen for `k` in `[1, n-1]`, and is `none` too. -/
def signWith (d e k : Nat) : Option (Nat × Nat) :=
  if 1 ≤ d ∧ d < C.n ∧ 1 ≤ k ∧ k < C.n then
    match mul k (G C) with
    | .infinity => none
    | .affine xR _ =>
      let r := xR.val % C.n
      let s : Scalar C := pow (Fin.ofNat C.n k) (C.n - 2) *
        (Fin.ofNat C.n e + Fin.ofNat C.n r * Fin.ofNat C.n d)
      if r = 0 ∨ s = 0 then none else some (r, s.val)
  else none

/-- The signature `(r, s)` as `len` octets of `r` followed by `len` octets
of `s` (the encoding of IEEE 1363 and of RFC 6979). -/
def encode (rs : Nat × Nat) : List Byte := toBytes C.len rs.1 ++ toBytes C.len rs.2

end VG.Spec.Ecdsa
