module

public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 signing with a cached expanded secret and public key

**Trusted** (as every file in `Spec/`). RFC 8032 §5.1.6, step 1 hashes the
seed with SHA-512 for every signature; the digest depends on the seed alone.
A caller may retain that 64-byte digest (the input to `expandSecret`: the
secret scalar's bytes, then the nonce prefix) together with the public key
derived in §5.1.5, rather than computing them again for each signature.
This contract requires both correspondences explicitly: some seed
must have the digest at `expanded` and the public key at `pk`. It retains
the complete `sign seed message` postcondition for every such seed: the
signature is the one RFC 8032 specifies for the seed. It does not specify
a signature for an expanded secret or a public key chosen independently
of a seed.

The seed itself is not a parameter: a signature depends on the seed only
through its SHA-512 digest, which keeps the arguments in registers on
every target. No buffer contents may affect timing, including the cached
digest and public key.
-/

@[expose] public section

namespace VG.Spec.Ed25519

/-- `(out: *mut [u8; 64], expanded: *const [u8; 64], pk: *const [u8; 32],
message: *const u8, len: usize, scratch: *mut [u64; 1024])`. -/
def signExpandedSig : Sig where
  params := [("out", .array true .u8 64),
    ("expanded", .array false .u8 64), ("pk", .array false .u8 32),
    ("message", .slice false .u8 "len"), ("scratch", .array true .u64 scratchWords)]

/-- Sign with the SHA-512 digest of a seed and the public key
corresponding to that seed. The postcondition is the same complete signing
algorithm, `sign`, for every seed with that digest. -/
def signExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signExpandedSig.contract A
    (pre := fun _out expanded pk _message _len _scratch m =>
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Sha512.sha512 seed ∧
        bytesAt m pk 32 = publicKey seed)
    (post := fun out expanded _pk message len _scratch m m' _ =>
      ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Sha512.sha512 seed →
        bytesAt m' out 64 = sign seed (bytesAt m message len.toNat))
    (writeArgs := true) (stack := stack)

/-- Complete signing with a cached SHA-512 digest of the seed and a cached,
matching public key, on every target. -/
def signExpandedApi : Api where
  module := "ed25519"
  name := "vg_ed25519_sign_expanded"
  sig := signExpandedSig
  writeArgs := true
  contracts := some fun A stack => signExpandedContract A stack
  summary := "Deterministic Ed25519 signing (RFC 8032 §5.1.6): writes the 64-byte signature \
    to `*out`, for the `len` bytes at `message` and the 32-byte private seed whose \
    SHA-512 digest (§5.1.6, step 1) is cached at `expanded`, using its cached public key \
    at `pk`. Includes the remaining hashing, pruning and scalar/group \
    operations. Uses pure Ed25519, with no context or prehash. \
    Contract: `VG.Spec.Ed25519.signExpandedContract`. Constant time: only pointers and the \
    message length may affect timing, not any buffer contents."
  safety := [
    "The 64 bytes at `expanded` must equal the SHA-512 digest (`VG.Spec.Sha512.sha512`) \
      of a 32-byte seed, and the 32 bytes at `pk` the public key derived from that seed \
      by RFC 8032 §5.1.5 (`VG.Spec.Ed25519.publicKey`).",
    "The seed must originate from a cryptographically secure random generator.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the \
      caller must destroy them after use."]

end VG.Spec.Ed25519
