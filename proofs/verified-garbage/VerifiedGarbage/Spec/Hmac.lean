module

public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.Spec.Md5
public import VerifiedGarbage.Spec.Sha512

/-!
# HMAC (RFC 2104; FIPS 198-1)

**Trusted** (as every file in `Spec/`). The keyed-hash message
authentication code HMAC, over any hash function with an input block size,
transcribed from FIPS 198-1, *The Keyed-Hash Message Authentication Code*
(July 2008), §4 (the same construction as RFC 2104 §2). Keys, messages and
digests are sequences of bytes.

The hash functions it is used with are below; the contracts, for any hash
function with a streaming implementation, are in `Spec/Hmac/Generic.lean`.
-/

@[expose] public section

namespace VG.Spec.Hmac

/-- A hash function, as HMAC uses it: its input block size `B` in bytes, and
the digest of a message. -/
structure HashFunction where
  blockSize : Nat
  hash : List Byte → List Byte

/-- `ipad` and `opad` (FIPS 198-1 §3): the bytes `0x36` and `0x5c`, repeated `B` times. -/
def ipad : Byte := 0x36
def opad : Byte := 0x5c

/-- `k ⊕ (pad repeated)`. -/
def xorPad (k : List Byte) (pad : Byte) : List Byte := k.map (· ^^^ pad)

variable (H : HashFunction)

/-- Steps 1–3: the key `K₀`, of exactly `B` bytes. A key of `B` bytes is used
as is; a longer key is hashed first; either is then padded with zeros to
`B` bytes. -/
def blockKey (key : List Byte) : List Byte :=
  let k := if H.blockSize < key.length then H.hash key else key
  k ++ List.replicate (H.blockSize - k.length) 0

/-- Steps 4–9, from `K₀`: `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`. -/
def hmacBlockKey (k0 text : List Byte) : List Byte :=
  H.hash (xorPad k0 opad ++ H.hash (xorPad k0 ipad ++ text))

/-- `HMAC(K, text)`. -/
def hmac (key text : List Byte) : List Byte := hmacBlockKey H (blockKey H key) text

/-- SHA-256 (block size 64 bytes, FIPS 180-4 §1). -/
def sha256 : HashFunction := ⟨64, Sha256.hash⟩

/-- SHA-224 (block size 64 bytes, FIPS 180-4 §1). -/
def sha224 : HashFunction := ⟨64, Sha256.sha224⟩

/-- SHA-1 (block size 64 bytes, FIPS 180-4 §1). -/
def sha1 : HashFunction := ⟨64, Sha1.hash⟩

/-- MD5 (block size 64 bytes: RFC 1321 §3.4 processes the message in 16-word
blocks; RFC 2104 §2 uses `B = 64` for it). -/
def md5 : HashFunction := ⟨64, Md5.hash⟩

/-- SHA-384 (block size 128 bytes, FIPS 180-4 §1). -/
def sha384 : HashFunction := ⟨128, Sha512.sha384⟩

/-- SHA-512 (block size 128 bytes, FIPS 180-4 §1). -/
def sha512 : HashFunction := ⟨128, Sha512.sha512⟩

/-- SHA-512/224 (block size 128 bytes, FIPS 180-4 §1). -/
def sha512_224 : HashFunction := ⟨128, Sha512.sha512_224⟩

/-- SHA-512/256 (block size 128 bytes, FIPS 180-4 §1). -/
def sha512_256 : HashFunction := ⟨128, Sha512.sha512_256⟩

end VG.Spec.Hmac
