module

public import VerifiedGarbage.Spec.Hmac

/-!
# PBKDF2 (RFC 8018)

**Trusted** (as every file in `Spec/`). The password-based key derivation
function PBKDF2, over any pseudorandom function, transcribed from RFC 8018,
*PKCS #5: Password-Based Cryptography Specification Version 2.1* (January
2017), §5.2. Passwords, salts and derived keys are sequences of bytes.

The contracts of its iteration and of the whole of PBKDF2-HMAC, for any
streaming hash function, are in `Spec/Pbkdf2/Generic.lean`.
-/

@[expose] public section

namespace VG.Spec.Pbkdf2

/-- `INT (i)`: a four-octet encoding of the integer `i`, most significant
octet first (§5.2, step 3). -/
def int (i : Nat) : List Byte :=
  [BitVec.ofNat 8 (i / 2 ^ 24), BitVec.ofNat 8 (i / 2 ^ 16), BitVec.ofNat 8 (i / 2 ^ 8), BitVec.ofNat 8 i]

/-- The bytewise exclusive-or of two byte strings of the same length. -/
def xorBytes (a b : List Byte) : List Byte := List.zipWith (· ^^^ ·) a b

variable (prf : List Byte → List Byte)

/-- From `U = Uⱼ` and `T = U₁ ⊕ … ⊕ Uⱼ`, `n` more steps `Uⱼ₊₁ = PRF (P, Uⱼ)`
of step 3, each exclusive-or'ed into `T`; the result is the final `T`.
`prf` is `PRF (P, ·)`, the pseudorandom function keyed with the password. -/
def iterate : Nat → List Byte → List Byte → List Byte
  | 0, _, t => t
  | n + 1, u, t => let u' := prf u; iterate n u' (xorBytes t u')

/-- `F (P, S, c, i) = U₁ ⊕ U₂ ⊕ … ⊕ U_c` (step 3), with `U₁ = PRF (P, S ‖ INT (i))`. -/
def F (s : List Byte) (c i : Nat) : List Byte :=
  let u₁ := prf (s ++ int i)
  iterate prf (c - 1) u₁ u₁

/-- `PBKDF2 (P, S, c, dkLen)` (§5.2), for a pseudorandom function with
outputs of `hLen` bytes: `none` if the derived key is too long (step 1),
otherwise `T₁ ‖ T₂ ‖ … ‖ T_l<0..r-1>` (steps 2–5). -/
def pbkdf2 (hLen : Nat) (s : List Byte) (c dkLen : Nat) : Option (List Byte) :=
  if (2 ^ 32 - 1) * hLen < dkLen then none
  else
    let l := (dkLen + hLen - 1) / hLen
    some (((List.range l).flatMap fun k => F prf s c (k + 1)).take dkLen)

/-- PBKDF2 with HMAC-SHA-256 (RFC 2104, FIPS 198-1) as the pseudorandom
function, keyed with the password `p` (`hLen` = 32). -/
def pbkdf2HmacSha256 (p s : List Byte) (c dkLen : Nat) : Option (List Byte) :=
  pbkdf2 (Hmac.hmac Hmac.sha256 p) 32 s c dkLen

end VG.Spec.Pbkdf2
