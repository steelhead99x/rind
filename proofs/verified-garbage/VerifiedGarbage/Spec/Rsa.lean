module

public import VerifiedGarbage.TCB.Mem

/-!
# RSA primitives (RFC 8017 §§4–5, NIST SP 800-56B Rev. 2)

**Trusted** (as every file in `Spec/`). The RSA primitives of PKCS #1 v2.2
(RFC 8017), for a two-prime key, on octet strings:

* `publicOp`: RSAEP (§5.1.1), which is also RSAVP1 (§5.2.2):
  `c = m^e mod n`, an error if `m` is not in `[0, n-1]`.
* `privateCrt`: RSADP (§5.1.2), which is also RSASP1 (§5.2.1), with the
  private key in the second form of §3.2, `(p, q, dP, dQ, qInv)`: step 2.b,
  with `u = 2`.
* `crtKey`: a private key in SP 800-56B's prime-factor format `(p, q, d)`
  (§6.2.2) brought to the CRT format, for `privateCrt`: the CRT values
  `dP = d mod (p - 1)`, `dQ = d mod (q - 1)` and `qInv = q⁻¹ mod p`, as
  §6.2.2's CRT format defines them (`crtValues`), and an error if `q` has no
  inverse modulo `p`.

A private key in SP 800-56B's basic format `(n, e, d)` (§6.2.2) is brought to
the prime-factor format by Appendix C.2 (`primesKeyDet`, `Rsa/RecoverDet.lean`).

A private key in another format is brought to the CRT format once, when it
is loaded, rather than at every operation.

Beside these, what BoringSSL (`crypto/fipsmodule/rsa/`) checks, which the
operations will check instead of the above:

* `publicOpChecked`: `publicOp` with BoringSSL's limits on the public key
  (`rsa_check_public_key`): `exponentValid` (`e` odd, from 3 to 33 bits) as
  well as `modulusValid`.
* `privateChecked`: `privateCrt` given the public exponent `e` too, which
  releases the result `m` only if `m^e mod n` is the input, and is otherwise
  an internal error (`Outcome.fault`): BoringSSL's
  `rsa_default_private_transform`, which checks every result so that a
  fault in the computation (Boneh, DeMillo and Lipton, 1997) does not
  release a value that reveals the key.
* `checkKey`: BoringSSL's `RSA_check_key` of a private key
  `(n, e, d, p, q, dP, dQ, qInv)`.
* `checkCrtKey`: the checks of `checkKey` on the CRT form
  `(n, e, p, q, dP, dQ, qInv)` alone, without `d`, which the private-key
  operations do not use: for loading a key.

Integers are naturals, converted from and to octet strings by OS2IP and
I2OSP (§4), most significant octet first. The modulus `n` is given as its
`k` octets, and so are the input and the output of the operations;
`crtKey`'s values are as long as the factor
they are modulo.

Every primitive checks what it can afford to: the modulus is odd and from 512
to 8192 bits, its first octet is not zero (so `k` is its length in octets),
the input is below `n`, and the factors' product is `n`. Nothing checks that
`p` and `q` are prime or that the exponents match `e`. For a valid RSA key
(distinct primes, `e·d ≡ 1 (mod λ(n))`), `privateCrt` with the CRT values
`crtKey` gives computes
`c^d mod n`; for any other key they compute exactly what is written here.

Padding (EME-OAEP, EMSA-PSS, PKCS #1 v1.5) is a separate layer.
-/

@[expose] public section

namespace VG.Spec.Rsa

/-! ## Integers and octet strings (§4) -/

/-- OS2IP (§4.2): an octet string as an integer, most significant octet
first. -/
def os2ip (bs : List Byte) : Nat := bs.foldl (fun x b => 256 * x + b.toNat) 0

/-- I2OSP (§4.1): `x` as `xLen` octets, most significant first. §4.1 gives an
error if `x ≥ 256^xLen`; every integer converted here is below the modulus,
which is below `256^xLen`, so this keeps only the low `xLen` octets. -/
def i2osp (x xLen : Nat) : List Byte :=
  (List.range xLen).map fun i => BitVec.ofNat 8 (x / 256 ^ (xLen - 1 - i))

/-! ## Arithmetic -/

/-- `a^e mod m`, by square-and-multiply. -/
def powMod (a e m : Nat) : Nat :=
  if e = 0 then 1 % m else
    let t := powMod a (e / 2) m
    let u := t * t % m
    if e % 2 = 0 then u else u * a % m
termination_by e
decreasing_by omega

/-- Extended Euclid: from `r' = a s' + b t'` and `r = a s + b t`, the same for
`r' = gcd`. -/
def xgcd (r : Nat) (s : Int) (r' : Nat) (s' : Int) : Nat × Int :=
  if r = 0 then (r', s') else xgcd (r' % r) (s' - (r' / r : Nat) * s) r s
termination_by r
decreasing_by exact Nat.mod_lt _ (by omega)

/-- The inverse of `a` modulo `m > 1`: the `x < m` with `a x ≡ 1 (mod m)`,
which exists exactly when `gcd(a, m) = 1` and is then unique; `none` if there
is none. It is found by the extended Euclidean algorithm, and checked. -/
def inverse (a m : Nat) : Option Nat :=
  let x := ((xgcd (a % m) 1 m 0).2 % (m : Int)).toNat
  if a * x % m = 1 then some x else none

/-! ## The modulus -/

/-- A modulus the primitives take, given as `k` octets: odd, from 512 to
8192 bits, and `k` octets long (its first octet is not zero). -/
def modulusValid (n k : Nat) : Bool :=
  n % 2 == 1 && 2 ^ 511 ≤ n && n < 2 ^ 8192 && 256 ^ (k - 1) ≤ n

/-! ## Precomputed values of the modulus -/

/-- The 64-bit words of a `k`-octet modulus: `⌈k / 8⌉`. -/
def modulusWords (k : Nat) : Nat := (k + 7) / 8

/-- The low `w` words of 64 bits of `x`, least significant first. -/
def toWords (x w : Nat) : List (BitVec 64) :=
  (List.range w).map fun i => BitVec.ofNat 64 (x / 2 ^ (64 * i))

/-- What Montgomery multiplication modulo the `k`-octet modulus `nB` needs
of it, with `w = ⌈k / 8⌉` words and `R = 2^(64 w)`: `n` and then
`R² mod n`, as `w` words each, least significant first; or `none` if the
modulus is not valid. -/
def publicPrecompute (nB : List Byte) : Option (List (BitVec 64)) :=
  let n := os2ip nB
  let w := modulusWords nB.length
  if modulusValid n nB.length then some (toWords n w ++ toWords (2 ^ (128 * w) % n) w) else none

/-! ## The primitives on integers -/

/-- RSAEP (§5.1.1) and RSAVP1 (§5.2.2): `x^e mod n`, or `none` if `x` is not
in `[0, n-1]`. -/
def encrypt (n e x : Nat) : Option Nat :=
  if x < n then some (powMod x e n) else none

/-- RSADP (§5.1.2) and RSASP1 (§5.2.1) with the private key
`(p, q, dP, dQ, qInv)` (§3.2's second form, two primes), or `none` if `c` is
not in `[0, n-1]`, `p q ≠ n` or `qInv` is not in `[0, p-1]`. Step 2.b:
`m_1 = c^dP mod p`, `m_2 = c^dQ mod q`, `h = (m_1 - m_2) qInv mod p`, and
`m = m_2 + q h`. -/
def decryptCrt (n p q dP dQ qInv c : Nat) : Option Nat :=
  if c < n ∧ p * q = n ∧ qInv < p then
    let m₁ := powMod c dP p
    let m₂ := powMod c dQ q
    let h := (((m₁ : Int) - m₂) * qInv % (p : Int)).toNat
    some (m₂ + q * h)
  else none

/-- SP 800-56B Rev. 2 §6.2.2's CRT values of the private key `(p, q, d)`:
`(dP, dQ, qInv)` with `dP = d mod (p - 1)`, `dQ = d mod (q - 1)` and
`qInv = q⁻¹ mod p`, or `none` if `q` has no inverse modulo `p`. -/
def crtValues (p q d : Nat) : Option (Nat × Nat × Nat) :=
  (inverse q p).map fun qInv => (d % (p - 1), d % (q - 1), qInv)

/-- `m = 2^t r` with `r` odd, for `m > 0`: `(t, r)`. -/
def splitTwos (m : Nat) : Nat × Nat :=
  if m = 0 ∨ m % 2 = 1 then (0, m) else
    let (t, r) := splitTwos (m / 2)
    (t + 1, r)
termination_by m
decreasing_by omega

/-! ## The primitives on octet strings

The modulus `n` is `k` octets (OS2IP of `nB`, `k = nB.length`), and so are
the input and the result. -/

/-- RSAEP and RSAVP1 of the input `xB` with the public key `(nB, eB)`:
`some` result, or `none` if the modulus is not valid or the input is not
below it. -/
def publicOp (nB eB xB : List Byte) : Option (List Byte) :=
  let n := os2ip nB
  if modulusValid n nB.length then
    (encrypt n (os2ip eB) (os2ip xB)).map (i2osp · nB.length)
  else none

/-- RSADP and RSASP1 of the input `xB` with the private key
`(p, q, dP, dQ, qInv)` of the modulus `nB`: `some` result, or `none` if the
modulus is not valid, the input is not below it, `p q ≠ n`, or `qInv ≥ p`. -/
def privateCrt (nB xB pB qB dPB dQB qInvB : List Byte) : Option (List Byte) :=
  let n := os2ip nB
  if modulusValid n nB.length then
    (decryptCrt n (os2ip pB) (os2ip qB) (os2ip dPB) (os2ip dQB) (os2ip qInvB)
      (os2ip xB)).map (i2osp · nB.length)
  else none

/-- The CRT values of the private key `(p, q, d)` of the modulus `nB`
(`crtValues`): `some (dP, dQ, qInv)`, as `pB.length`, `qB.length` and
`pB.length` octets, or `none` if the modulus is not valid, `p q ≠ n`, or `q`
has no inverse modulo `p`. -/
def crtKey (nB pB qB dB : List Byte) : Option (List Byte × List Byte × List Byte) :=
  let n := os2ip nB
  let p := os2ip pB
  let q := os2ip qB
  if modulusValid n nB.length ∧ p * q = n then
    (crtValues p q (os2ip dB)).map fun (dP, dQ, qInv) =>
      (i2osp dP pB.length, i2osp dQ qB.length, i2osp qInv pB.length)
  else none

/-! ## BoringSSL's checks

What BoringSSL checks of RSA keys and results, in
`crypto/fipsmodule/rsa/rsa_impl.cc.inc` (`rsa_check_public_key`,
`rsa_default_private_transform`) and `crypto/fipsmodule/rsa/rsa.cc.inc`
(`RSA_check_key`). BoringSSL allows moduli of up to 16384 bits; the modulus
here is still `modulusValid`'s, up to 8192. -/

/-- A public exponent BoringSSL's `rsa_check_public_key` accepts: odd and of
2 to 33 bits (`kMaxExponentBits`), so from 3 to `2^33 - 1`. -/
def exponentValid (e : Nat) : Bool :=
  e % 2 == 1 && 3 ≤ e && e < 2 ^ 33

/-- RSAEP and RSAVP1 (`publicOp`) of the input `xB` with the public key
`(nB, eB)`, which BoringSSL's `rsa_check_public_key` must accept: `some`
result, or `none` if the modulus or the exponent is not valid
(`modulusValid`, `exponentValid`) or the input is not below the modulus. -/
def publicOpChecked (nB eB xB : List Byte) : Option (List Byte) :=
  if exponentValid (os2ip eB) then publicOp nB eB xB else none

/-- The outcome of `privateChecked`. -/
inductive Outcome where
  /-- The result, `k` octets. -/
  | ok (y : List Byte)
  /-- The key or the input is refused. -/
  | invalid
  /-- The internal error: the result `m` failed the check `m^e mod n = c`. -/
  | fault
  deriving DecidableEq

/-- RSADP and RSASP1 with the private key `(p, q, dP, dQ, qInv)` (step 2.b,
`decryptCrt`), checked against the public exponent `e`, as BoringSSL's
`rsa_default_private_transform` checks it: `some (some m)` if
`m^e mod n = c` for the result `m`, `some none` (an internal error) if not,
and `none` if `decryptCrt` refuses the key or the input. -/
def decryptChecked (n e p q dP dQ qInv c : Nat) : Option (Option Nat) :=
  (decryptCrt n p q dP dQ qInv c).map fun m => if powMod m e n = c then some m else none

/-- RSADP and RSASP1 of the input `xB` with the private key
`(p, q, dP, dQ, qInv)` of the modulus `nB` and the public exponent `eB`,
checked as BoringSSL's `rsa_default_private_transform` checks it:

* `invalid` if the modulus or the exponent is not valid (BoringSSL's
  `rsa_check_public_key`, which `freeze_private_key` runs), the input is not
  below the modulus, `p q ≠ n`, or `qInv ≥ p` (`decryptCrt`);
* otherwise, for the result `m` of step 2.b (`decryptCrt`), `ok` with `m`
  as `k` octets if `m^e mod n` is the input, and `fault` if not: the result
  is never released unless it passes the check. -/
def privateChecked (nB eB xB pB qB dPB dQB qInvB : List Byte) : Outcome :=
  let n := os2ip nB
  let e := os2ip eB
  if modulusValid n nB.length ∧ exponentValid e then
    match decryptChecked n e (os2ip pB) (os2ip qB) (os2ip dPB) (os2ip dQB) (os2ip qInvB)
      (os2ip xB) with
    | some (some m) => .ok (i2osp m nB.length)
    | some none => .fault
    | none => .invalid
  else .invalid

/-- BoringSSL's `RSA_check_key` of the private key
`(n, e, d, p, q, dP, dQ, qInv)` (with all of them given), for a modulus of
`k` octets:

* `rsa_check_public_key`: the modulus and the exponent are valid
  (`modulusValid`, `exponentValid`);
* `d < n`;
* `p < n`, `q < n` and `p q = n`;
* `d e ≡ 1 (mod p - 1)` and `d e ≡ 1 (mod q - 1)`;
* `check_mod_inverse` of `dP`, `dQ` and `qInv`: `dP < p - 1` and
  `e dP ≡ 1 (mod p - 1)`; `dQ < q - 1` and `e dQ ≡ 1 (mod q - 1)`;
  `qInv < p` and `q qInv ≡ 1 (mod p)`.

`RSA_check_key` does not check that `p` and `q` are prime, and neither does
this. -/
def keyValid (k n e d p q dP dQ qInv : Nat) : Bool :=
  modulusValid n k && exponentValid e &&
  d < n &&
  p < n && q < n && p * q == n &&
  d * e % (p - 1) == 1 && d * e % (q - 1) == 1 &&
  dP < p - 1 && e * dP % (p - 1) == 1 &&
  dQ < q - 1 && e * dQ % (q - 1) == 1 &&
  qInv < p && q * qInv % p == 1

/-- `keyValid` of the private key `(nB, eB, dB, pB, qB, dPB, dQB, qInvB)`,
the modulus of `k = nB.length` octets. The private exponent is checked as
given; the private-key operations do not use it. -/
def checkKey (nB eB dB pB qB dPB dQB qInvB : List Byte) : Bool :=
  keyValid nB.length (os2ip nB) (os2ip eB) (os2ip dB) (os2ip pB) (os2ip qB) (os2ip dPB)
    (os2ip dQB) (os2ip qInvB)

/-- `keyValid` without the checks of the private exponent `d`, which the
private-key operations do not use: the checks of the CRT form
`(n, e, p, q, dP, dQ, qInv)`, for a modulus of `k` octets.

* `rsa_check_public_key`: the modulus and the exponent are valid
  (`modulusValid`, `exponentValid`);
* `p q = n`;
* `dP < p - 1` and `e dP ≡ 1 (mod p - 1)`; `dQ < q - 1` and
  `e dQ ≡ 1 (mod q - 1)`; `qInv < p` and `q qInv ≡ 1 (mod p)`.

`keyValid`'s `p < n` and `q < n` are left out: they follow from `p q = n`
when neither is 0 (as the congruences modulo `p - 1` and `q - 1` require).
Like `keyValid`, this does not check that `p` and `q` are prime. -/
def crtKeyValid (k n e p q dP dQ qInv : Nat) : Bool :=
  modulusValid n k && exponentValid e &&
  p * q == n &&
  dP < p - 1 && e * dP % (p - 1) == 1 &&
  dQ < q - 1 && e * dQ % (q - 1) == 1 &&
  qInv < p && q * qInv % p == 1

/-- `crtKeyValid` of the private key `(nB, eB, pB, qB, dPB, dQB, qInvB)`,
the modulus of `k = nB.length` octets. -/
def checkCrtKey (nB eB pB qB dPB dQB qInvB : List Byte) : Bool :=
  crtKeyValid nB.length (os2ip nB) (os2ip eB) (os2ip pB) (os2ip qB) (os2ip dPB) (os2ip dQB)
    (os2ip qInvB)

end VG.Spec.Rsa
