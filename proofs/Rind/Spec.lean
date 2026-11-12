module
public import Aeneas
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.ZMod.Basic
open Aeneas Aeneas.Std
@[expose] public section

/-!
# What rind computes

The functional spec the proofs state rind's results against: how bytes and
limbs encode numbers, X25519 itself, and the NIST curves' group law with
P-256's, each as HOL Light defines it for s2n-bignum's theorems, and ChaCha20, QUIC header protection,
Poly1305, ChaCha20-Poly1305, and XChaCha20-Poly1305, transliterated from their
RFCs and draft-irtf-cfrg-xchacha-03.
-/

namespace rind.spec

/-- The number that little-endian bytes encode. -/
def leNat (bytes : List U8) : Nat :=
  Nat.ofDigits 256 (bytes.map (·.val))

/-- The number that big-endian bytes encode. -/
def beNat (bytes : List U8) : Nat :=
  leNat bytes.reverse

/-- The number that little-endian 64-bit limbs encode: HOL Light's
`bignum_from_memory`. -/
def wordsNat (words : List U64) : Nat :=
  Nat.ofDigits (2 ^ 64) (words.map (·.val))

/-- The two coordinates at `xy` as HOL Light's `bignum_pair_from_memory (xy,4)`
reads them. -/
def pairNat (xy : List U64) : Nat × Nat :=
  (wordsNat (xy.take 4), wordsNat ((xy.drop 4).take 4))

/-- RFC 7748's X25519 of a scalar and a u-coordinate, each read as a number,
including the scalar's clamping and the u-coordinate's top-bit mask: HOL
Light's `rfcx25519`, defined in `EC/x25519.ml` at
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/x25519.ml#L608
and proven there to be the u-coordinate of the scalar multiple on Curve25519.

It is opaque here: nothing is assumed of it beyond the routine contracts in
`Rind.<Arch>.S2nBignum`, which restate s2n-bignum's theorems about it. -/
opaque rfcx25519 : Nat → Nat → Nat

/-! ## The NIST curves' group law

HOL Light defines each NIST prime curve's group as `weierstrass_group
(integer_mod_ring p, ring_neg (integer_mod_ring p) (&3), &b)`: the points of
y² = x³ - 3x + b over the integers mod p. This transliterates that group law
once, over the prime `p` and constant `b`. -/

namespace nist

/-- A point as HOL Light writes one: `none` at infinity, otherwise its affine
coordinates, the field elements of `integer_mod_ring p`, which are numbers
below `p`. -/
abbrev Point := Option (Nat × Nat)

/-- Whether a point is in `weierstrass_curve (integer_mod_ring p, ring_neg
(integer_mod_ring p) (&3), &b)`, the group's carrier: infinity, or
coordinates in the field that satisfy y² = x³ - 3x + b, with
`integer_mod_ring`'s arithmetic mod `p`.

The proofs must decide this membership, so the composition rule lets it be
this defining equation rather than an opaque set. -/
def OnCurve (p b : Nat) : Point → Prop
  | none => True
  | some (x, y) => x < p ∧ y < p ∧ y ^ 2 % p = (x ^ 3 + (p - 3) * x + b) % p

instance (p b : Nat) : DecidablePred (OnCurve p b) := fun P =>
  match P with
  | none => isTrue trivial
  | some (x, y) => inferInstanceAs (Decidable (x < p ∧ y < p ∧ _))

/-! The group law, transliterated from HOL Light's definitions. The field's
operations are `integer_mod_ring`'s on numbers below `p`,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/Library/ringtheory.ml#L16887 -/

/-- `ring_sub (integer_mod_ring p)`: `(a - b) rem p`, which is never
negative. -/
def sub (p a b : Nat) : Nat := (a + (p - b % p)) % p

/-- `ring_inv (integer_mod_ring p)`: the number below `p` that `a` times is 1
mod `p`, if `a` is a field element with one, and otherwise 0,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/Library/ringtheory.ml#L1970 -/
noncomputable def inv (p a : Nat) : Nat :=
  haveI := Classical.propDecidable
  if h : a < p ∧ ∃ x, x < p ∧ a * x % p = 1 then Classical.choose h.2 else 0

/-- `weierstrass_add` on the curve, with `ring_div` as the product with
`inv`, `ring_of_num` 2 and 3 as themselves, and `a` as `p - 3`. It never reads
`b`,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/weierstrass.ml#L33 -/
noncomputable def add (p : Nat) : Point → Point → Point
  | none, q => q
  | P, none => P
  | some (x1, y1), some (x2, y2) =>
    if x1 = x2 then
      if y1 = y2 ∧ y1 ≠ 0 then
        let m := (3 * (x1 ^ 2 % p) % p + (p - 3)) % p * inv p (2 * y1 % p) % p
        let x3 := sub p (m ^ 2 % p) (2 * x1 % p)
        let y3 := sub p (m * sub p x1 x3 % p) y1
        some (x3, y3)
      else none
    else
      let m := sub p y2 y1 * inv p (sub p x2 x1) % p
      let x3 := sub p (m ^ 2 % p) ((x1 + x2) % p)
      let y3 := sub p (m * sub p x1 x3 % p) y1
      some (x3, y3)

/-- `group_pow` on the group, the point `P` multiplied by `n`: `group_pow`'s
definition, `P` times the multiple below,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/Library/grouptheory.ml#L376 -/
noncomputable def pow (p : Nat) (P : Point) : Nat → Point
  | 0 => none
  | n + 1 => add p P (pow p P n)

/-- `weierstrass_neg` on the curve, which `WEIERSTRASS_GROUP` shows is
`group_inv`: y negated mod p. -/
def neg (p : Nat) : Point → Point
  | none => none
  | some (x, y) => some (x, (p - y % p) % p)

/-- FIPS 186-5 section 6.4.1's ECDSA signature `(r, s)` on the curve over
`p` whose generator `G` has order `n`, under private key `d`, with
per-message secret `k`, of the hash's integer `e`: r is the x-coordinate of
kG mod n, and s is (e + rd)/k mod n. A rind signature is this for the first
`k` whose `r` and `s` are both nonzero. -/
noncomputable def ecdsaSign (p n : Nat) (G : Point) (d k e : Nat) : Option (Nat × Nat) :=
  match pow p G k with
  | some (x, _) => some (x % n, (((e + x % n * d : Nat) : ZMod n) * (k : ZMod n)⁻¹).val)
  | none => none

/-- FIPS 186-5 section 6.4.2's ECDSA verification of `(r, s)` over the hash's
integer `e` under the public key `Q`, on the curve over `p` whose generator
`G` has order `n`: r and s are in [1, n), and u₁G + u₂Q, for u₁ = e/s and
u₂ = r/s mod n, is a finite point whose x-coordinate mod n is r. -/
def ecdsaVerifies (p n : Nat) (G Q : Point) (e r s : Nat) : Prop :=
  0 < r ∧ r < n ∧ 0 < s ∧ s < n ∧
    match add p (pow p G (((e : ZMod n) * (s : ZMod n)⁻¹).val))
        (pow p Q (((r : ZMod n) * (s : ZMod n)⁻¹).val)) with
    | some (x, _) => x % n = r
    | none => False

end nist

/-! ## P-256, from HOL Light's `EC/nistp256.ml` at
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/nistp256.ml -/

/-- `p_256`, the field's prime. -/
def p256 : Nat := 115792089210356248762697446949407573530086143415290314195533631308867097853951

/-- `n_256`, the group's order. -/
def n256 : Nat := 115792089210356248762697446949407573529996955224135760342422259061068512044369

/-- `b_256`, the curve's constant term; its `a` is -3. -/
def b256 : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

/-- A point of `p256_group`. -/
abbrev P256Point := nist.Point

/-- Whether a point is in `group_carrier p256_group`, by `P256_GROUP`,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/nistp256.ml#L82 -/
abbrev p256OnCurve : P256Point → Prop := nist.OnCurve p256 b256

/-- `G_256`, the generator. -/
def p256G : P256Point :=
  some (0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
    0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)

/-- `ring_sub (integer_mod_ring p_256)`. -/
abbrev p256Sub : Nat → Nat → Nat := nist.sub p256

/-- `ring_inv (integer_mod_ring p_256)`. -/
noncomputable abbrev p256Inv : Nat → Nat := nist.inv p256

/-- `group_mul p256_group`, by `P256_GROUP`. -/
noncomputable abbrev p256Add : P256Point → P256Point → P256Point := nist.add p256

/-- `group_pow p256_group`. -/
noncomputable abbrev p256Pow : P256Point → Nat → P256Point := nist.pow p256

/-- `group_inv p256_group`, by `P256_GROUP`. -/
abbrev p256Neg : P256Point → P256Point := nist.neg p256

/-- FIPS 186-5 section 6.4.1's P-256 ECDSA signature. -/
noncomputable abbrev ecdsaP256Sign : Nat → Nat → Nat → Option (Nat × Nat) := nist.ecdsaSign p256 n256 p256G

/-- FIPS 186-5 section 6.4.2's P-256 ECDSA verification under the public key
`Q`. -/
abbrev ecdsaP256Verifies : P256Point → Nat → Nat → Nat → Prop := nist.ecdsaVerifies p256 n256 p256G

/-! ## ChaCha20 and QUIC header protection -/

namespace chacha20

/-- A 32-bit word of ChaCha20's state. -/
abbrev Word := BitVec 32

/-- RFC 8439 section 2.1's quarter round on four words. -/
def qr (a b c d : Word) : Word × Word × Word × Word :=
  let a := a + b
  let d := (d ^^^ a).rotateLeft 16
  let c := c + d
  let b := (b ^^^ c).rotateLeft 12
  let a := a + b
  let d := (d ^^^ a).rotateLeft 8
  let c := c + d
  let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- RFC 8439 section 2.2's quarter round on state words `x`, `y`, `z`, and `w`. -/
def quarterRound (s : List Word) (x y z w : Nat) : List Word :=
  let (a, b, c, d) := qr s[x]! s[y]! s[z]! s[w]!
  (((s.set x a).set y b).set z c).set w d

/-- RFC 8439 section 2.3.1's `inner_block`: the column rounds, then the
diagonal rounds. -/
def innerBlock (s : List Word) : List Word :=
  let s := quarterRound s 0 4 8 12
  let s := quarterRound s 1 5 9 13
  let s := quarterRound s 2 6 10 14
  let s := quarterRound s 3 7 11 15
  let s := quarterRound s 0 5 10 15
  let s := quarterRound s 1 6 11 12
  let s := quarterRound s 2 7 8 13
  quarterRound s 3 4 9 14

/-- The word whose little-endian bytes these are. -/
def le32 (b0 b1 b2 b3 : BitVec 8) : Word := BitVec.fromLEBytes [b0, b1, b2, b3]

/-- `bytes` as little-endian words, four bytes each. -/
def words (bytes : List (BitVec 8)) : List Word :=
  (List.range (bytes.length / 4)).map fun i =>
    le32 bytes[4 * i]! bytes[4 * i + 1]! bytes[4 * i + 2]! bytes[4 * i + 3]!

/-- RFC 8439 section 2.3's ChaCha20 block function: the 64-byte keystream
block for a 32-byte key, a block counter, and a 12-byte nonce. -/
def block (key : List (BitVec 8)) (counter : Word) (nonce : List (BitVec 8)) : List (BitVec 8) :=
  let state := [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++ words key ++ [counter] ++
    words nonce
  let working := innerBlock^[10] state
  (List.zipWith (· + ·) working state).flatMap BitVec.toLEBytes

/-- RFC 9001 section 5.4.4's ChaCha20 header-protection mask: ChaCha20 under
the header-protection key of five zero bytes, so the keystream's first five,
with the sample's first four bytes as the little-endian block counter and the
rest as the nonce. -/
def headerProtectionMask (key sample : List (BitVec 8)) : List (BitVec 8) :=
  (block key (le32 sample[0]! sample[1]! sample[2]! sample[3]!) (sample.drop 4)).take 5

/-- RFC 8439 section 2.4's ChaCha20 encryption: `msg` XOR the keystream from
block `counter` on, a block per 64 bytes, the last one cut to the message. -/
def encrypt (key : List (BitVec 8)) (counter : Word) (nonce msg : List (BitVec 8)) : List (BitVec 8) :=
  (List.range ((msg.length + 63) / 64)).flatMap fun j =>
    List.zipWith (· ^^^ ·) ((msg.drop (64 * j)).take 64) (block key (counter + BitVec.ofNat 32 j) nonce)

/-- draft-irtf-cfrg-xchacha-03 section 2.2's HChaCha20: ChaCha20's rounds
over the key and a 16-byte nonce in place of the counter and nonce, without
the block function's final addition, keeping words 0 to 3 and 12 to 15. -/
def hchacha20 (key nonce : List (BitVec 8)) : List (BitVec 8) :=
  let working := innerBlock^[10] ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++ words key ++
    words nonce)
  (working.take 4 ++ working.drop 12).flatMap BitVec.toLEBytes

end chacha20

/-! ## Poly1305 and ChaCha20-Poly1305 -/

namespace poly1305

/-- The number that little-endian bytes encode. -/
def leNum (bytes : List (BitVec 8)) : Nat :=
  Nat.ofDigits 256 (bytes.map (·.toNat))

/-- Poly1305's prime, 2^130 - 5. -/
def p : Nat := 2 ^ 130 - 5

/-- RFC 8439 section 2.5's `clamp`. -/
def clamp (r : Nat) : Nat := r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- RFC 8439 section 2.5.1's `poly1305_mac`: the accumulator over each 16-byte
block of `msg` with a one byte after it, the last one cut to the message, then
the low 128 bits of it plus `s`, little-endian. -/
def mac (key msg : List (BitVec 8)) : List (BitVec 8) :=
  let r := clamp (leNum (key.take 16))
  let s := leNum (key.drop 16)
  let a := (List.range ((msg.length + 15) / 16)).foldl (fun a i =>
    let block := (msg.drop (16 * i)).take 16
    (a + leNum block + 2 ^ (8 * block.length)) * r % p) 0
  (BitVec.ofNat 128 (a + s)).toLEBytes

end poly1305

namespace chacha20poly1305

/-- RFC 8439 section 2.8.1's `pad16`: the zeros that fill `x` to a multiple
of 16 bytes. -/
def pad16 (x : List (BitVec 8)) : List (BitVec 8) :=
  List.replicate ((16 - x.length % 16) % 16) 0

/-- RFC 8439 section 2.8.1's `mac_data`: the AAD, the ciphertext, each padded,
then their lengths as 64-bit little-endian numbers. -/
def macData (aad ct : List (BitVec 8)) : List (BitVec 8) :=
  aad ++ pad16 aad ++ ct ++ pad16 ct ++ (BitVec.ofNat 64 aad.length).toLEBytes ++
    (BitVec.ofNat 64 ct.length).toLEBytes

/-- RFC 8439 section 2.6's `poly1305_key_gen`: the first 32 bytes of the block
with counter zero. -/
def otk (key nonce : List (BitVec 8)) : List (BitVec 8) :=
  (chacha20.block key 0 nonce).take 32

/-- RFC 8439 section 2.8's AEAD_CHACHA20_POLY1305 encryption of `msg`: the
ciphertext, ChaCha20 from block 1, and the tag over the AAD and it. -/
def «seal» (key nonce aad msg : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  let ct := chacha20.encrypt key 1 nonce msg
  (ct, poly1305.mac (otk key nonce) (macData aad ct))

/-- RFC 8439 section 2.8's decryption of `ct`: the plaintext, and whether the
tag over the AAD and `ct` is `tag`. -/
def «open» (key nonce aad ct tag : List (BitVec 8)) : List (BitVec 8) × Bool :=
  (chacha20.encrypt key 1 nonce ct, poly1305.mac (otk key nonce) (macData aad ct) == tag)

/-- draft-irtf-cfrg-xchacha-03 section 2.3's XChaCha20-Poly1305 key and nonce
for a 24-byte nonce: HChaCha20 of the key and the nonce's first 16 bytes, and
four zero bytes then its last 8. -/
def xKeyNonce (key nonce : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  (chacha20.hchacha20 key (nonce.take 16), [0, 0, 0, 0] ++ nonce.drop 16)

/-- XChaCha20-Poly1305 encryption: ChaCha20-Poly1305's, under `xKeyNonce`. -/
def xseal (key nonce aad msg : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  «seal» (xKeyNonce key nonce).1 (xKeyNonce key nonce).2 aad msg

/-- XChaCha20-Poly1305 decryption: ChaCha20-Poly1305's, under `xKeyNonce`. -/
def xopen (key nonce aad ct tag : List (BitVec 8)) : List (BitVec 8) × Bool :=
  «open» (xKeyNonce key nonce).1 (xKeyNonce key nonce).2 aad ct tag

end chacha20poly1305

end rind.spec
