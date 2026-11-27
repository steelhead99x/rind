module

public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 key-pair derivation from the seed, with its SHA-512 digest

**Trusted** (as every file in `Spec/`). RFC 8032 §5.1.5 derives the public key
from the SHA-512 digest of the seed (step 1); §5.1.6, step 1 hashes the seed
again for every signature. A caller that keeps the digest for
`signExpandedContract` (`ExpandedSign.lean`) can have both written from the
seed by this one function: the digest, `Sha512.sha512 seed`, at `expanded`,
and the public key, `publicKey seed`, at `out`.

There is no precondition: the postcondition states both outputs in terms of
the seed at `seed`, so what this function writes is exactly what
`signExpandedContract`'s precondition requires, for that seed. No buffer
contents may affect timing.
-/

@[expose] public section

namespace VG.Spec.Ed25519

/-- `(out: *mut [u8; 32], expanded: *mut [u8; 64], seed: *const [u8; 32],
scratch: *mut [u64; 1024])`. -/
def keyPairSig : Sig where
  params := [("out", .array true .u8 32), ("expanded", .array true .u8 64),
    ("seed", .array false .u8 32), ("scratch", .array true .u64 scratchWords)]

/-- Derive the seed's SHA-512 digest and its public key, including pruning. -/
def keyPairContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keyPairSig.contract A
    (post := fun out expanded seed _scratch m m' _ =>
      bytesAt m' expanded 64 = Sha512.sha512 (bytesAt m seed 32) ∧
        bytesAt m' out 32 = publicKey (bytesAt m seed 32))
    (writeArgs := true) (stack := stack)

/-- Key-pair derivation from the seed, on every target. -/
def keyPairApi : Api where
  module := "ed25519"
  name := "vg_ed25519_key_pair"
  sig := keyPairSig
  writeArgs := true
  contracts := some fun A stack => keyPairContract A stack
  summary := "Ed25519 key-pair derivation (RFC 8032 §5.1.5): for the 32-byte private seed at \
    `seed`, writes its 64-byte SHA-512 digest (§5.1.5, step 1) to `*expanded` and its \
    32-byte public key to `*out`, including pruning: the digest and public key that \
    `vg_ed25519_sign_expanded` takes. \
    Contract: `VG.Spec.Ed25519.keyPairContract`. Constant time: only pointers may \
    affect timing."
  safety := [
    "The seed must originate from a cryptographically secure random generator.",
    "The 64 bytes written to `expanded` are secret: the caller must destroy them after use.",
    scratchSafety]

end VG.Spec.Ed25519
