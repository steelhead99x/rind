module

public import VerifiedGarbage.Spec.EcKey
public import VerifiedGarbage.TCB.Artifact

/-!
# Elliptic curve keys over any curve: the contracts, on every target

**Trusted** (as every file in `Spec/`). An `Instance` is a curve as the Rust
interface has it: the curve, its name in the functions' names
(`vg_ec_<name>_public_key`, in the module `ec_<name>`; and the functions of
algorithms over the curve, such as `vg_ecdh_<name>`, `Spec/Ecdh/Generic.lean`),
and its name in their documentation. Each curve is an `Instance` in a file
of its own (`Spec/EcKey/P256.lean`, …).

The signature determines memory validity, separation and that the pointers
are public, through `Sig.contract`. `publicKey` keeps the private key
secret: only the pointers may affect timing. It returns 1 and writes the
public key, or returns 0 and writes zeros, so the return value depends on
the private key (whether it is in `[1, n-1]`). `scratch` is 8 KiB of
working space, whose contents on return are unspecified. `stack` is the
number of bytes below the stack pointer that an implementation's calls and
frames use. The functions may overwrite their arguments passed in memory,
where the calling convention allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.EcKey

open Weierstrass

/-- The bytes at `p`, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- Working space in `u64`s. -/
def scratchWords : Nat := 1024

/-- The `# Safety` item on the working space. -/
def scratchSafety : String :=
  "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
    must destroy them after use."

/-- A curve, and its names in the Rust interface. -/
structure Instance where
  curve : Curve
  /-- The name in function and module names, e.g. `p256`. -/
  name : String
  /-- The name in documentation, e.g. `P-256`. -/
  title : String

namespace Instance

variable (I : Instance)

/-- `(out: *mut [u8; 2 len + 1], d: *const [u8; len], scratch: *mut [u64; 1024]) -> u32`. -/
def publicKeySig : Sig where
  params := [("out", .array true .u8 (2 * I.curve.len + 1)), ("d", .array false .u8 I.curve.len),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- The public key `Q = dG` of the private key at `d`, if `d` is in
`[1, n-1]` (and `Q ≠ O`, which always holds then): the function returns 1
and writes `Q` (`04 ‖ x ‖ y`) to `out`; otherwise it returns 0 and writes
zeros. Constant time: the private key may not affect timing. -/
def publicKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.publicKeySig.contract A
    (post := fun out d _scratch m m' r =>
      match publicKey I.curve (ofBytes (bytesAt m d I.curve.len)) with
      | some (.affine x y) =>
        r = 1 ∧ bytesAt m' out (2 * I.curve.len + 1) = encodePoint (.affine x y)
      | _ => r = 0 ∧ bytesAt m' out (2 * I.curve.len + 1) = List.replicate (2 * I.curve.len + 1) 0)
    (writeArgs := true) (stack := stack)

/-- `vg_ec_<name>_public_key` on every target. -/
def publicKeyApi : Api where
  module := s!"ec_{I.name}"
  name := s!"vg_ec_{I.name}_public_key"
  sig := I.publicKeySig
  writeArgs := true
  contracts := some fun A stack => I.publicKeyContract A stack
  summary := s!"{I.title} public-key derivation (FIPS 186-5 §A.2, SP 800-56A §5.6.1.2): \
    writes the public key `Q = dG` of the private key `d` at `d` ({I.curve.len} bytes, most \
    significant first) to `*out`, in the uncompressed form of SEC 1 §2.3.3 (`04`, then `x` \
    and `y` in {I.curve.len} bytes each, most significant first), and returns 1; or, if \
    `d` is not in `[1, n-1]`, writes zeros and returns 0.\n\n\
    Contract: `VG.Spec.EcKey.Instance.publicKeyContract`. Constant time: only the pointers \
    may affect timing, not the private key."
  safety := [scratchSafety]

end Instance

end VG.Spec.EcKey
