module

public import VerifiedGarbage.Spec.Ecdh
public import VerifiedGarbage.Spec.EcKey.Generic

/-!
# ECDH over any curve: the contracts, on every target

**Trusted** (as every file in `Spec/`). For a curve's `EcKey.Instance`,
`vg_ecdh_<name>`, in the module `ecdh_<name>`: the ECC CDH primitive
(`Ecdh.exchange`), with the validation of the peer's public key.

The signature determines memory validity, separation and that the pointers
are public, through `Sig.contract`. The private key is secret; the peer's
public key is public, and may affect timing (`leak`): an implementation may,
for instance, reject an invalid one early. The function returns 1 and
writes the shared secret, or returns 0 and writes zeros, so the return value
depends on the private key too (whether it is in `[1, n-1]`). `scratch` is
8 KiB of working space, whose contents on return are unspecified. `stack` is
the number of bytes below the stack pointer that an implementation's calls
and frames use. The function may overwrite its arguments passed in memory,
where the calling convention allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.Ecdh

open Weierstrass EcKey

namespace Instance

variable (I : EcKey.Instance)

/-- `(out: *mut [u8; len], d: *const [u8; len], peer: *const [u8; 2 len + 1],
scratch: *mut [u64; 1024]) -> u32`. -/
def exchangeSig : Sig where
  params := [("out", .array true .u8 I.curve.len), ("d", .array false .u8 I.curve.len),
    ("peer", .array false .u8 (2 * I.curve.len + 1)), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- The shared secret of the private key at `d` and the peer's public key at
`peer`, if there is one (`exchange`): the function returns 1 and writes it
to `out`; otherwise it returns 0 and writes zeros. Constant time but for the
peer's public key, which may affect timing. -/
def exchangeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (exchangeSig I).contract A
    (post := fun out d peer _scratch m m' r =>
      match exchange I.curve (ofBytes (bytesAt m d I.curve.len))
          (bytesAt m peer (2 * I.curve.len + 1)) with
      | some z => r = 1 ∧ bytesAt m' out I.curve.len = z
      | none => r = 0 ∧ bytesAt m' out I.curve.len = List.replicate I.curve.len 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _d peer _scratch m =>
      (bytesAt m peer (2 * I.curve.len + 1)).map (·.toNat))

/-- `vg_ecdh_<name>` on every target. -/
def exchangeApi : Api where
  module := s!"ecdh_{I.name}"
  name := s!"vg_ecdh_{I.name}"
  sig := exchangeSig I
  writeArgs := true
  contracts := some fun A stack => exchangeContract I A stack
  summary := s!"ECDH over {I.title} (the ECC CDH primitive of SP 800-56A §5.7.1.2): \
    validates the peer's public key at `peer` (SP 800-56A §5.6.2.3.3: the uncompressed form \
    of SEC 1 §2.3.3, `04` then `x` and `y` in {I.curve.len} bytes each, most significant \
    first, both below `p`, on the curve), and writes the x-coordinate of `dQ` \
    ({I.curve.len} bytes, most significant first) for the private key `d` at `d` \
    ({I.curve.len} bytes, most significant first) to `*out`, and returns 1; or writes \
    zeros and returns 0 if `peer` is not a valid public key, `d` is not in `[1, n-1]`, or \
    `dQ` is the point at infinity.\n\n\
    Contract: `VG.Spec.Ecdh.Instance.exchangeContract`. Constant time but for the peer's \
    public key: timing may depend on the pointers and the contents of `peer`, not on the \
    private key."
  safety := [scratchSafety]

end Instance

end VG.Spec.Ecdh
