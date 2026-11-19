module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.Artifact

/-!
# X25519: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_x25519_exchange` and `vg_x25519_base`, in terms of `Spec/X25519.lean`,
for any target: `A` is the target's calling
convention. The signature fixes where the arguments are, the memory the
function may access, disjointness, and that the pointers are public (see
`TCB/Sig.lean`); the contract adds the rest. The scalar and the
u-coordinate are secret (the u-coordinate is usually a public key, but the
function does not rely on it).

`vg_x25519_exchange` computes a shared secret, `X25519(k, u)` for a
peer's u-coordinate `u`, with the check RFC 7748 §6.1 allows of it: it
returns 0 if the result is all zero (which it is for a `u` of small order),
1 otherwise. The return value depends on the scalar and the u-coordinate,
but nothing else about them affects timing. It takes 4 KiB of working space
(`scratch`), which it leaves unspecified, since the ladder's variables do
not fit in the registers of any target.

`vg_x25519_base` computes a public key, `X25519(k, 9)` with the base point
(`basePoint`), so that an implementation can compute it otherwise than with
the ladder (e.g. as the u-coordinate `(1 + y) / (1 - y)` of a fixed-base
multiplication on edwards25519, RFC 7748 §4.1). It takes 8 KiB of working
space, as Ed25519's fixed-base multiplication does.

The contract takes the number of bytes of stack below the stack pointer that
an implementation's calls and frames use (`stack`, see `Sig.contract`), 0
for one that uses none.
-/

@[expose] public section

namespace VG.Spec.X25519

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- `vg_x25519_base(out: *mut [u8; 32], scalar: *const [u8; 32], scratch: *mut [u64; 1024])`.
`scratch` is working space. -/
def x25519BaseSig : Sig where
  params := [("out", .array true .u8 32), ("scalar", .array false .u8 32),
    ("scratch", .array true .u64 1024)]

/-- Writes `X25519(k, 9)` (the public key of `k`, RFC 7748 §6.1) to `out`, for
the 32-byte scalar `k` at `scalar`. -/
def x25519BaseContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  x25519BaseSig.contract A (post := fun out scalar _scratch m m' _ =>
    bytesAt m' out 32 = x25519 (bytesAt m scalar 32) basePoint)
    (stack := stack)

/-- `vg_x25519_base` on every target. -/
def x25519BaseApi : Api where
  module := "x25519"
  name := "vg_x25519_base"
  sig := x25519BaseSig
  contracts := some fun A stack => x25519BaseContract A stack
  summary := "Computes an X25519 public key (RFC 7748 §6.1): writes `X25519(k, 9)`, the X25519 \
    function of the 32-byte scalar `k` at `scalar` and the base point's u-coordinate 9, to \
    `*out`. The scalar is decoded (clamped).\n\n\
    Contract: `VG.Spec.X25519.x25519BaseContract`. Constant time: only the pointers may affect \
    timing, not the scalar."
  safety := ["The contents of `scratch` on return are unspecified and may contain secrets; \
    the caller must destroy them after use."]

/-- `vg_x25519_exchange(out: *mut [u8; 32], scalar: *const [u8; 32], point: *const [u8; 32], scratch: *mut [u64; 512]) -> u32`.
`scratch` is working space. -/
def exchangeSig : Sig where
  params := [("out", .array true .u8 32), ("scalar", .array false .u8 32),
    ("point", .array false .u8 32), ("scratch", .array true .u64 512)]
  ret := some .u32

/-- Writes `X25519(k, u)` to `out`, for the 32-byte scalar `k` at `scalar`
and the 32-byte u-coordinate `u` at `point`, and returns 0 if it is all zero,
1 otherwise (RFC 7748 §6.1). -/
def exchangeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  exchangeSig.contract A (post := fun out scalar point _scratch m m' r =>
    let z := x25519 (bytesAt m scalar 32) (bytesAt m point 32)
    bytesAt m' out 32 = z ∧ r = if z = List.replicate 32 0 then 0 else 1)
    (stack := stack)

/-- `vg_x25519_exchange` on every target. -/
def exchangeApi : Api where
  module := "x25519"
  name := "vg_x25519_exchange"
  sig := exchangeSig
  contracts := some fun A stack => exchangeContract A stack
  summary := "Computes an X25519 shared secret (RFC 7748 §6.1): writes `X25519(k, u)` to \
    `*out`, for the 32-byte scalar `k` at `scalar` and the 32-byte u-coordinate `u` at \
    `point`, and returns 0 if it is all zero (for a `u` of small order), 1 otherwise. The \
    scalar is decoded (clamped) and the most significant bit of `u` masked as RFC 7748 \
    specifies (§5).\n\n\
    Contract: `VG.Spec.X25519.exchangeContract`. Constant time: only the pointers may affect \
    timing, not the scalar or the u-coordinate; the return value depends on both."
  safety := ["The contents of `scratch` on return are unspecified and may contain secrets; \
    the caller must destroy them after use."]

end VG.Spec.X25519
