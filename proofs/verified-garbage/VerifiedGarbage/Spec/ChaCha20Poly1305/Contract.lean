module

public import VerifiedGarbage.Spec.ChaCha20Poly1305
public import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20-Poly1305: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the one-shot AEAD
functions, in terms of `Spec/ChaCha20Poly1305.lean`, for any target: `A` is
the target's calling convention. The signatures fix where the arguments are,
the memory each function may access, disjointness, and that the pointers and
lengths are public (see `TCB/Sig.lean`); the contracts add the rest. The key,
the nonce, the additional data, the data and the tags are secret.

The functions are composed in assembly from the ChaCha20 and Poly1305
primitives, which they call. The key, the nonce and the tag are buffers of
their own: `seal` writes the tag to `tag`, and `open` reads the received tag
from it. Each function keeps its working space on the stack.

The data is encrypted or decrypted in place. Both functions may overwrite
their arguments passed in memory, where the calling convention allows it
(`writeArgs`), to pass arguments to the functions they call, and take the
number of bytes of stack below the stack pointer that their calls and frames
use (`stack`, see `Sig.contract`), which depends on the target.

The contracts do not limit the length of the data. Beyond RFC 8439's
`P_MAX`, 2³²-1 blocks, the ChaCha20 block counter wraps around (as in
`VG.Spec.ChaCha20.encrypt`) and the construction is no longer secure: the
caller must enforce `P_MAX`.
-/

@[expose] public section

namespace VG.Spec.ChaCha20Poly1305

open Poly1305 (bytesAt)

/-- `vg_chacha20_poly1305_seal(key: *const [u8; 32], nonce: *const [u8; 12], aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16])`. -/
def sealSig : Sig where
  params := [("key", .array false .u8 32), ("nonce", .array false .u8 12),
    ("aad", .slice false .u8 "aad_len"), ("data", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- With the key at `key` and the nonce at `nonce`: the `len` bytes at
`data` are encrypted, for the `aad_len` bytes of additional data at `aad`,
and the tag is at `tag`. -/
def sealPost (pb : Nat) : sealSig.Post pb :=
  fun key nonce aad aadLen data len tag m m' _ =>
    encrypt (bytesAt m key 32) (bytesAt m nonce 12) (bytesAt m aad aadLen.toNat)
        (bytesAt m data len.toNat) =
      (bytesAt m' data len.toNat, bytesAt m' tag 16)

/-- With the key at `key` and the nonce at `nonce`: encrypts the `len` bytes
at `data` in place, for the `aad_len` bytes of additional data at `aad`, and
writes the tag to `tag`. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (post := sealPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- `vg_chacha20_poly1305_open(key: *const [u8; 32], nonce: *const [u8; 12], aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const [u8; 16]) -> u32`. -/
def openSig : Sig where
  params := [("key", .array false .u8 32), ("nonce", .array false .u8 12),
    ("aad", .slice false .u8 "aad_len"), ("data", .slice true .u8 "len"),
    ("tag", .array false .u8 16)]
  ret := some .u32

/-! ## `open`, zeroing the data on a wrong tag

On a wrong tag the bytes at `data` are zeros, as in every other AEAD's
`open` here (`vg_aes_ccm_open`, `vg_aes_gcm_siv_open`, `vg_aes_ocb_open`),
so that the decryption of a forged ciphertext is never released, whatever
the caller does. In exchange, the function may leak whether it returns 1 (as
those functions do): it may branch on the result of the comparison of the
tags to zero the data only when they differ. The result is returned to the
caller, which branches on it anyway. -/

/-- With the key at `key`, the nonce at `nonce` and the received tag at
`tag`: if the message (the `len` bytes of ciphertext at `data`, with the
`aad_len` bytes of additional data at `aad`) is authenticated, the result is
1 and the plaintext is at `data`; otherwise the result is 0, and the `len`
bytes at `data` are zeros. -/
def openZeroPost (pb : Nat) : openSig.Post pb :=
  fun key nonce aad aadLen data len tag m m' r =>
    match decrypt (bytesAt m key 32) (bytesAt m nonce 12) (bytesAt m aad aadLen.toNat)
        (bytesAt m data len.toNat) (bytesAt m tag 16) with
    | some pt => r = 1 ∧ bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ bytesAt m' data len.toNat = List.replicate len.toNat 0

/-- What `vg_chacha20_poly1305_open` may leak (`openZeroContract`): whether
it returns 1 (`decrypt`'s outcome). -/
def openLeak (pb : Nat) : Curry (openSig.words pb) (Mem → List Nat) :=
  fun key nonce aad aadLen data len tag m =>
    [if (decrypt (bytesAt m key 32) (bytesAt m nonce 12) (bytesAt m aad aadLen.toNat)
        (bytesAt m data len.toNat) (bytesAt m tag 16)).isSome then 1 else 0]

/-- With the key at `key`, the nonce at `nonce` and the received tag at
`tag`: if the message (the `len` bytes of ciphertext at `data`, with the
`aad_len` bytes of additional data at `aad`) is authenticated, returns 1 and
leaves the plaintext at `data`; otherwise returns 0 and leaves zeros at
`data`. May leak which (`openLeak`). -/
def openZeroContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (post := openZeroPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openLeak A.ptrBits))

/-- `vg_chacha20_poly1305_seal` on every target. -/
def sealApi : Api where
  module := "chacha20poly1305"
  name := "vg_chacha20_poly1305_seal"
  sig := sealSig
  writeArgs := true
  contracts := some fun A stack => sealContract A stack
  summary := "ChaCha20-Poly1305 encryption (RFC 8439 §2.8): with the key `*key` and the nonce \
    `*nonce`, encrypts the `len` bytes at `data` in place and writes the tag of the ciphertext \
    and the `aad_len` bytes of additional data at `aad` to `*tag`.\n\n\
    Contract: `VG.Spec.ChaCha20Poly1305.sealContract`. Constant time: only the pointers and the \
    lengths may affect timing, not the key, the nonce or the data. The block counter wraps around \
    beyond 2³²-1 blocks of data (RFC 8439's `P_MAX`), which the caller must not exceed for the \
    construction to be secure."
  safety := []

/-- `vg_chacha20_poly1305_open` on every target, zeroing the data on a wrong
tag (`openZeroContract`). -/
def openZeroApi : Api where
  module := "chacha20poly1305"
  name := "vg_chacha20_poly1305_open"
  sig := openSig
  writeArgs := true
  contracts := some fun A stack => openZeroContract A stack
  summary := "ChaCha20-Poly1305 decryption (RFC 8439 §2.8): with the key `*key`, the nonce \
    `*nonce` and the received tag `*tag`, returns 1 if the tag is that of the `len` bytes of \
    ciphertext at `data` and the `aad_len` bytes of additional data at `aad`, having decrypted \
    the ciphertext in place; otherwise returns 0, and the `len` bytes at `data` are zeros. The \
    tags are compared without a branch.\n\n\
    Contract: `VG.Spec.ChaCha20Poly1305.openZeroContract`. Constant time but for the result: \
    only the pointers, the lengths and whether the function returns 1 or 0 may affect timing, \
    not the key, the nonce, the additional data, the tag or the data."
  safety := []

end VG.Spec.ChaCha20Poly1305
