module

public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.TCB.Artifact

/-!
# Ed25519: contracts on every target

**Trusted** (as every file in `Spec/`). The signatures determine memory
validity, separation, and public pointers and lengths through `Sig.contract`.
Key derivation and signing keep all buffer contents secret. Verification
may leak its inputs; it returns exactly 0 or 1. There are no failure or
retry allowances for key derivation or signing.

The contracts also specify the hashing, so that an assembly caller can be
verified end to end, generic over SHA-512 backends.

All functions take 8 KiB of scratch space, whose contents are unspecified on
return and must be destroyed by callers handling secrets. `stack` describes
the space used below the stack pointer. `writeArgs` allows calls to reuse
the ABI's argument slots, including on 32-bit targets.
-/

@[expose] public section

namespace VG.Spec.Ed25519

/-- Bytes in a buffer, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- Working space in `u64`s, shared by all target signatures. -/
def scratchWords : Nat := 1024

def scratchSafety : String :=
  "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
    must destroy them after use."

/-! ## Verification -/

/-- `(pk: *const [u8; 32], message: *const u8, len: usize, signature: *const [u8; 64], scratch: *mut [u64; 1024]) -> u32`. -/
def verifySig : Sig where
  params := [("pk", .array false .u8 32), ("message", .slice false .u8 "len"),
    ("signature", .array false .u8 64), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Verify the signature, including the message hash. All inputs are public. -/
def verifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifySig.contract A
    (post := fun pk message len signature _scratch m _m' r =>
      r = if verify (bytesAt m pk 32) (bytesAt m message len.toNat)
        (bytesAt m signature 64) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk message len signature _scratch m =>
      (bytesAt m pk 32 ++ bytesAt m message len.toNat ++ bytesAt m signature 64).map (·.toNat))

/-! ## Emitted API documentation -/

def verifyApi : Api where
  module := "ed25519"
  name := "vg_ed25519_verify"
  sig := verifySig
  writeArgs := true
  contracts := some fun A stack => verifyContract A stack
  summary := "Ed25519 verification (RFC 8032 §5.1.7): returns 1 if the 64-byte signature at \
    `signature` verifies for the 32-byte public key at `pk` and the `len` bytes at \
    `message`, and 0 otherwise. Uses pure Ed25519, with no context or prehash. Checks \
    canonical point encodings, S < L, and `[S]B = R + [k]A` with the challenge \
    k = SHA-512(R || A || M) reduced modulo L, as in RFC 8032 §6. No additional subgroup or small-order check is imposed. \
    Contract: `VG.Spec.Ed25519.verifyContract`. Not constant time: timing may depend on \
    the public key, message and signature."
  safety := [scratchSafety]

end VG.Spec.Ed25519
