module

public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# ECDSA signature verification over any curve: the contracts, on every target

**Trusted** (as every file in `Spec/`). For a curve's `Ecdsa.Instance`,
`vg_ecdsa_<name>_verify`, in the module `ecdsa_<name>` (`verifyHashApi`):
whether a signature of a hash verifies with a public key (`Ecdsa.verify`),
with the validation of the public key.

It takes the public key as `2 len + 1` octets (`04 ‖ x ‖ y`), the hash as the
hash function's output itself, a slice of `digest_len` octets of any length,
as `vg_ecdsa_<name>_sign` takes it (`Spec/Ecdsa/Rfc6979/Table.lean`), and the
signature as `2 len` octets (`r` then `s`, as `sign` writes it). The function
converts the hash to the integer `e` itself (`hashToInt`, FIPS 186-5 §6.4.2
step 2, the leftmost `min(N, 8 digest_len)` bits), so that
`verifyHashContract` is `verify` of the hash as FIPS 186-5 §6.4.2 takes it.
The signature determines memory validity, separation and that the pointers
are public, through `Sig.contract`. Every input is public: the contents of
the three buffers may affect timing (`leak`), so an implementation may, for
instance, reject an invalid key or signature early, and use variable-time
arithmetic. The function returns 1 if the signature is valid and 0
otherwise. `scratch` is 8 KiB of working space, whose contents on return are
unspecified. `stack` is the number of bytes below the stack pointer that an
implementation's calls and frames use. The function may overwrite its
arguments passed in memory, where the calling convention allows it
(`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.Ecdsa

open Weierstrass

namespace Instance

variable (I : Instance)

/-- `(public: *const [u8; 2 len + 1], digest: *const u8, digest_len: usize,
sig: *const [u8; 2 len], scratch: *mut [u64; 1024]) -> u32`. -/
def verifyHashSig : Sig where
  params := [("public", .array false .u8 (2 * I.curve.len + 1)),
    ("digest", .slice false .u8 "digest_len"), ("sig", .array false .u8 (2 * I.curve.len)),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Whether the signature at `sig` of the hash `digest` (`digest_len`
octets, the hash function's output) verifies with the public key at
`public` (`verify` of its integer `e`, `hashToInt`): the function returns 1
if it does and 0 otherwise. Every input is public, and may affect timing. -/
def verifyHashContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.verifyHashSig.contract A
    (post := fun pk digest digestLen sig _scratch m _m' r =>
      r = if verify I.curve (bytesAt m pk (2 * I.curve.len + 1))
          (hashToInt I.curve (bytesAt m digest digestLen.toNat))
          (bytesAt m sig (2 * I.curve.len))
        then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk digest digestLen sig _scratch m =>
      (bytesAt m pk (2 * I.curve.len + 1) ++ bytesAt m digest digestLen.toNat ++
        bytesAt m sig (2 * I.curve.len)).map (·.toNat))

/-- `vg_ecdsa_<name>_verify` on every target, taking the hash function's
output. -/
def verifyHashApi : Api where
  module := s!"ecdsa_{I.name}"
  name := s!"vg_ecdsa_{I.name}_verify"
  sig := I.verifyHashSig
  writeArgs := true
  contracts := some fun A stack => I.verifyHashContract A stack
  summary := s!"ECDSA signature verification over {I.title} (FIPS 186-5 §6.4.2): whether \
    the signature at `sig` (`r` then `s`, {I.curve.len} bytes each, most significant first) \
    of the hash at `digest` (`digest_len` bytes, the hash function's output, of any length; \
    `e` is its leftmost {nBits I.curve} bits, or all of it if it is shorter) verifies with \
    the public key at `public`, which must be a valid public key in the uncompressed form of \
    SEC 1 §2.3.3 (`04`, then `x` and `y` in {I.curve.len} bytes each, most significant first, \
    both below `p`, on the curve; SP 800-56A §5.6.2.3.3). Returns 1 if it does, and 0 if \
    it does not or the public key is not valid.\n\n\
    Contract: `VG.Spec.Ecdsa.Instance.verifyHashContract`. Every input is public: timing may \
    depend on the pointers, `digest_len` and the contents of `public`, `digest` and `sig`."
  safety := ["The contents of `scratch` on return are unspecified; the caller may reuse or \
    destroy them."]

end Instance

end VG.Spec.Ecdsa
