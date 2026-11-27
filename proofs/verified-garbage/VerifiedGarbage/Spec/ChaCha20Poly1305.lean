module

public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.Spec.Poly1305

/-!
# ChaCha20-Poly1305 (RFC 8439)

**Trusted** (as every file in `Spec/`). The AEAD construction
AEAD_CHACHA20_POLY1305, transcribed from RFC 8439, *ChaCha20 and Poly1305 for
IETF Protocols* (June 2018), §2.6 (the one-time key) and §2.8 (the AEAD); the
function names in backquotes are those of the pseudocode of §2.6.1 and
§2.8.1. The nonce is the 96-bit nonce of §2.3 (`constant | iv` in §2.8.1).

This file is independent of any architecture; the contracts of the
primitives on every target are in `Spec/ChaCha20Poly1305/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.ChaCha20Poly1305

open Poly1305 (mac leBytes)

/-- §2.8.1, `pad16(x)`: no bytes if the length of `x` is a multiple of 16,
otherwise enough zero bytes to make it one. -/
def pad16 (x : List Byte) : List Byte :=
  if x.length % 16 = 0 then [] else List.replicate (16 - x.length % 16) 0

/-- §2.6.1, `poly1305_key_gen(key, nonce)`: the first 32 bytes of the
ChaCha20 block with counter 0. -/
def polyKeyGen (key nonce : List Byte) : List Byte :=
  (ChaCha20.chacha20Block key 0 nonce).take 32

/-- §2.8.1: `mac_data`, the Poly1305 input for the additional data and the
ciphertext: `aad | pad16(aad) | ciphertext | pad16(ciphertext) |
num_to_8_le_bytes(aad.length) | num_to_8_le_bytes(ciphertext.length)`. -/
def macData (aad ct : List Byte) : List Byte :=
  aad ++ pad16 aad ++ ct ++ pad16 ct ++ leBytes 8 aad.length ++ leBytes 8 ct.length

/-- §2.8.1, `chacha20_aead_encrypt(aad, key, iv, constant, plaintext)`: the
ciphertext (the plaintext encrypted with ChaCha20 from block counter 1) and
the tag (the Poly1305 tag of `macData` under the one-time key). -/
def encrypt (key nonce aad pt : List Byte) : List Byte × List Byte :=
  let ct := ChaCha20.encrypt key 1 nonce pt
  (ct, mac (polyKeyGen key nonce) (macData aad ct))

/-- §2.8: decryption is as encryption, except that "the ChaCha20 encryption
function is applied to the ciphertext, producing the plaintext", "the
Poly1305 function is still run on the AAD and the ciphertext", and "the
calculated tag is bitwise compared to the received tag. The message is
authenticated if and only if the tags match." Only an authenticated message
has a plaintext. -/
def decrypt (key nonce aad ct tag : List Byte) : Option (List Byte) :=
  if mac (polyKeyGen key nonce) (macData aad ct) = tag then some (ChaCha20.encrypt key 1 nonce ct)
  else none

end VG.Spec.ChaCha20Poly1305
