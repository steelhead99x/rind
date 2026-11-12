module
public import Aeneas
public import Mathlib.Data.Nat.Size
@[expose] public section

/-!
# RSA signature verification

RFC 8017's RSASSA-PKCS1-v1_5 and RSASSA-PSS verification over any hash,
transliterated from its sections 4, 5.2.2, 8, 9, and B.2.1. A hash is a
function of the message's octets, as `Rind.HashSpec` defines SHA-1 and
SHA-256, and the other proofs SHA-384 and SHA-512. The RFC bounds each
hash's input, which the theorems that use these state.
-/

namespace rind.spec.rsa

/-- OS2IP, section 4.2: the number big-endian octets encode. -/
def os2ip (X : List Byte) : Nat :=
  X.foldl (fun x b => 256 * x + b.toNat) 0

/-- I2OSP, section 4.1: `x` as `xLen` big-endian octets, or `none`
("integer too large") unless `x < 256^xLen`. -/
def i2osp (x xLen : Nat) : Option (List Byte) :=
  if x < 256 ^ xLen then
    some ((List.range xLen).reverse.map fun i => BitVec.ofNat 8 (x / 256 ^ i))
  else none

/-- RSAVP1, section 5.2.2: `s^e mod n`, or `none` ("signature
representative out of range") unless `s < n`. -/
def rsavp1 (n e s : Nat) : Option Nat :=
  if s < n then some (s ^ e % n) else none

/-- `k`, the modulus's length in octets. -/
def octetLen (n : Nat) : Nat :=
  (n.size + 7) / 8

/-- EMSA-PKCS1-v1_5-ENCODE, section 9.2, given `T`'s prefix: the DER of the
hash's `DigestInfo` up to the digest, as Note 1 lists it. -/
def emsaPkcs1v15Encode (H : List Byte → List Byte) (digestInfo M : List Byte)
    (emLen : Nat) : Option (List Byte) :=
  let T := digestInfo ++ H M
  if emLen < T.length + 11 then none
  else some ([0x00, 0x01] ++ List.replicate (emLen - T.length - 3) 0xff ++ [0x00] ++ T)

/-- RSASSA-PKCS1-V1_5-VERIFY, section 8.2.2: whether `S` is a valid
signature of `M` under `(n, e)`. -/
def rsassaPkcs1v15Verify (n e : Nat) (H : List Byte → List Byte) (digestInfo M S : List Byte) :
    Prop :=
  let k := octetLen n
  S.length = k ∧ ∃ m, rsavp1 n e (os2ip S) = some m ∧
    ∃ EM, i2osp m k = some EM ∧ emsaPkcs1v15Encode H digestInfo M k = some EM

/-- Note 1's `DigestInfo` prefix for SHA-1. -/
def digestInfoSha1 : List Byte :=
  [0x30, 0x21, 0x30, 0x09, 0x06, 0x05, 0x2b, 0x0e, 0x03, 0x02, 0x1a, 0x05, 0x00, 0x04, 0x14]

/-- Note 1's `DigestInfo` prefix for SHA-256. -/
def digestInfoSha256 : List Byte :=
  [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
    0x05, 0x00, 0x04, 0x20]

/-- Note 1's `DigestInfo` prefix for SHA-384. -/
def digestInfoSha384 : List Byte :=
  [0x30, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02,
    0x05, 0x00, 0x04, 0x30]

/-- Note 1's `DigestInfo` prefix for SHA-512. -/
def digestInfoSha512 : List Byte :=
  [0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03,
    0x05, 0x00, 0x04, 0x40]

/-- MGF1, section B.2.1, for `maskLen` up to `2^32 hLen`: the first `maskLen`
octets of the hashes of `mgfSeed` followed by each four-octet counter from
zero. -/
def mgf1 (H : List Byte → List Byte) (hLen : Nat) (mgfSeed : List Byte) (maskLen : Nat) :
    List Byte :=
  ((List.range ((maskLen + hLen - 1) / hLen)).flatMap fun counter =>
    H (mgfSeed ++ (BitVec.ofNat 32 counter).toBEBytes)).take maskLen

/-- EMSA-PSS-VERIFY, section 9.1.2, with MGF1 over the same hash: whether
`EM`, of `emLen = ceil(emBits / 8)` octets, encodes `M` with a salt of
`sLen` octets. -/
def emsaPssVerify (H : List Byte → List Byte) (hLen : Nat) (M EM : List Byte)
    (emBits sLen : Nat) : Prop :=
  let mHash := H M
  let emLen := EM.length
  -- The leftmost `8 emLen - emBits` bits of an octet.
  let top := 8 * emLen - emBits
  let maskedDB := EM.take (emLen - hLen - 1)
  let H' := (EM.drop (emLen - hLen - 1)).take hLen
  let dbMask := mgf1 H hLen H' (emLen - hLen - 1)
  let DB := (List.zipWith (· ^^^ ·) maskedDB dbMask).modifyHead
    fun b => b &&& BitVec.ofNat 8 (2 ^ (8 - top) - 1)
  let psLen := emLen - hLen - sLen - 2
  let salt := DB.drop (emLen - hLen - 1 - sLen)
  -- Step 3.
  hLen + sLen + 2 ≤ emLen ∧
  -- Step 4.
  EM.getLast? = some 0xbc ∧
  -- Step 6.
  (maskedDB.headD 0).toNat < 2 ^ (8 - top) ∧
  -- Step 10.
  (∀ b ∈ DB.take psLen, b = 0x00) ∧ DB[psLen]? = some 0x01 ∧
  -- Steps 12 to 14.
  H (List.replicate 8 0x00 ++ mHash ++ salt) = H'

/-- RSASSA-PSS-VERIFY, section 8.1.2: whether `S` is a valid signature of
`M` under `(n, e)` with a salt of `sLen` octets. -/
def rsassaPssVerify (n e : Nat) (H : List Byte → List Byte) (hLen : Nat) (M S : List Byte)
    (sLen : Nat) : Prop :=
  let modBits := n.size
  let emLen := (modBits - 1 + 7) / 8
  S.length = octetLen n ∧ ∃ m, rsavp1 n e (os2ip S) = some m ∧
    ∃ EM, i2osp m emLen = some EM ∧ emsaPssVerify H hLen M EM (modBits - 1) sLen

end rind.spec.rsa
