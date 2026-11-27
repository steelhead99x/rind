module

public import VerifiedGarbage.Spec.Pbkdf2
public import VerifiedGarbage.Spec.Hmac.Generic

/-!
# PBKDF2-HMAC over any streaming hash function: the contracts, on every target

**Trusted** (as every file in `Spec/`). With the hash function a parameter
(`VG.Spec.Hmac.StreamingHash`), `vg_pbkdf2_hmac_<hash>` computes the whole of
PBKDF2-HMAC with that hash function (`VG.Spec.Pbkdf2.pbkdf2Hmac`): the key
(hashing a password longer than a block), `U₁` of each block, which absorbs
the salt, the iteration, and the truncation, composed from the verified
functions by calls. It keeps its working space on its own stack.

`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers, the lengths and the iteration counts are public (see
`TCB/Sig.lean`); the contracts add the rest. `stack` is the
number of bytes of stack below the stack pointer that an implementation's
calls use (see `Sig.contract`). The functions may overwrite their arguments
passed in memory, where the calling convention allows it (`writeArgs`), to
pass arguments to the functions it calls.

`VG.Spec.Hmac.Instance.pbkdf2Api` is the function of an `Instance` in the Rust
interface.
-/

@[expose] public section

namespace VG.Spec.Pbkdf2

open Sha256 (bytesAt)
open Hmac (StreamingHash xorPad ipad opad hmacBlockKey hmac)

variable (S : StreamingHash) (scratch : Nat)

/-- PBKDF2 with HMAC over the hash function of `S` (RFC 2104, FIPS 198-1) as
the pseudorandom function, keyed with the password `p` (`hLen` is the size of
the digest). -/
def pbkdf2Hmac (p s : List Byte) (c dkLen : Nat) : Option (List Byte) :=
  pbkdf2 (hmac S.H p) S.digestBytes s c dkLen

/-- `vg_pbkdf2_hmac_<hash>(password: *const u8, password_len: usize, salt: *const u8, salt_len: usize, c: u32, out: *mut u8, out_len: usize)`.
The iteration count `c` and the lengths are public. -/
def pbkdf2Sig : Sig where
  params := [("password", .slice false .u8 "password_len"), ("salt", .slice false .u8 "salt_len"),
    ("c", .int .u32 true), ("out", .slice true .u8 "out_len")]

/-- PBKDF2's precondition: `c` is positive and `out_len` at most
`(2³² − 1) · D`, with `D` the size of the digest (so that PBKDF2 accepts
it). -/
def pbkdf2Pre (pb : Nat) : Curry (pbkdf2Sig.words pb) (Mem → Prop) :=
  fun _password _passwordLen _salt _saltLen c _out outLen _m =>
    0 < c.toNat ∧ outLen.toNat ≤ (2 ^ 32 - 1) * S.digestBytes

/-- Writes `PBKDF2-HMAC (P, S, c, out_len)` of the `password_len` bytes `P`
at `password` and the `salt_len` bytes `S` at `salt` to the `out_len` bytes
at `out`. -/
def pbkdf2Post (pb : Nat) : pbkdf2Sig.Post pb :=
  fun password passwordLen salt saltLen c out outLen m m' _ =>
    pbkdf2Hmac S (bytesAt m password passwordLen.toNat) (bytesAt m salt saltLen.toNat)
      c.toNat outLen.toNat = some (bytesAt m' out outLen.toNat)

/-- If `c` is positive and `out_len` at most `(2³² − 1) · D` (`pbkdf2Pre`):
`pbkdf2Post`. The password, the salt and the derived key are secret. -/
def pbkdf2Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  pbkdf2Sig.contract A (pre := pbkdf2Pre S A.ptrBits) (post := pbkdf2Post S A.ptrBits)
    (writeArgs := true) (stack := stack)

end VG.Spec.Pbkdf2

namespace VG.Spec.Hmac.Instance

variable (I : Instance)

/-- The number of 64-bit words of working space of `vg_pbkdf2_hmac_<hash>`,
which an implementation keeps on its stack: that of the functions it calls (`scratch`), then a word for each byte of the
streaming state, for its own buffers (the HMAC key's two streaming states, a
third one for `U₁` and for hashing a long password, the digests `U` and `T`
and the hashed password, `INT (i)`) and spills. -/
def pbkdf2Scratch : Nat := I.scratch + I.S.stateBytes

/-- The contract of `vg_pbkdf2_hmac_<hash>`: `VG.Spec.Pbkdf2.pbkdf2Contract`. -/
def pbkdf2Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Pbkdf2.pbkdf2Contract I.S A stack

/-- `vg_pbkdf2_hmac_<hash>` on every target. -/
def pbkdf2Api : Api where
  module := s!"pbkdf2_{I.rust}"
  name := s!"vg_pbkdf2_hmac_{I.rust}"
  sig := Pbkdf2.pbkdf2Sig
  writeArgs := true
  contracts := some fun A stack => I.pbkdf2Contract A stack
  summary := s!"PBKDF2-HMAC-{I.alg} (RFC 8018 §5.2, with HMAC-{I.alg} as the pseudorandom \
    function): writes the `out_len`-byte key derived from the `password_len` bytes at `password` \
    and the `salt_len` bytes at `salt` with `c` iterations to `out`. Calls the verified {I.alg} \
    and HMAC-{I.alg} functions.\n\n\
    Contract: `VG.Spec.Hmac.Instance.pbkdf2Contract` of `VG.Spec.Hmac.{I.lean}`. Constant time: \
    only the pointers, the lengths and `c` may affect timing, not the password, the salt or the \
    key."
  safety := [s!"`c` must be positive, and `out_len` at most `(2^32 - 1) * {I.S.digestBytes}`."]

end VG.Spec.Hmac.Instance
