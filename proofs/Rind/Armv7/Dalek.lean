import Rind.Armv7.Funs
import Rind.Dalek
open Aeneas Aeneas.Std Result rind.spec

/-!
# Beneficial AI Foundation's curve25519-dalek X25519 on armv7

On armv7 rind runs curve25519-dalek's serial 32-bit backend, with its
precomputed tables, for X25519's public key on every CPU and for its shared
secret on a CPU without NEON (`Rind.Armv7.Curve25519`). Beneficial AI
Foundation (BAIF) proves that backend in Lean, through Aeneas, in its fork of
the crate. Each axiom here restates one of BAIF's theorems, at the revision
`admin/import-dalek` pins (f6351dfe), about a dalek function rind calls, which
the armv7 translation leaves opaque, in BAIF's spec of X25519,
`curve25519.X25519`, which `admin/import-dalek` vendors into
`proofs/curve25519-dalek` byte for byte with the modules it imports. An array
of bytes is the vector of them BAIF's `Array.toVector` reads, as in BAIF's
statement.

BAIF's theorems are about its translation of its fork's source, by the Aeneas
release its `AENEAS_VERSION.txt` names, with dalek's `alloc` and `zeroize`
features, which rind's build turns on too. `admin/prove dalek` translates the
crates.io release rind builds the same way and fails unless every definition
the two functions reach in the configuration armv7 builds, 32-bit with
precomputed tables, is BAIF's.

Trusted: each restatement, BAIF's proofs, which rest on Lean's axioms and
BAIF's own about the `alloc`, `subtle`, and `zeroize` functions dalek calls,
and Aeneas's translation of the Rust, as everywhere here.
-/

namespace rind.armv7

/-- `MontgomeryPoint::mul_clamped`: RFC 7748's `X25519(bytes, P)`,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Montgomery.lean#L71
(`Theorems.montgomery.MontgomeryPoint.mul_clamped`). -/
@[step]
axiom dalek_mul_clamped_spec (P : curve25519_dalek.montgomery.MontgomeryPoint)
    (bytes : Std.Array U8 32#usize) :
    curve25519_dalek.montgomery.MontgomeryPoint.mul_clamped P bytes ⦃ r =>
      r.toVector = curve25519.X25519 bytes.toVector P.toVector ⦄

/-- `MontgomeryPoint::mul_base_clamped`: RFC 7748's `X25519(bytes, 9)`,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Montgomery.lean#L78
(`Theorems.montgomery.MontgomeryPoint.mul_base_clamped`). -/
@[step]
axiom dalek_mul_base_clamped_spec (bytes : Std.Array U8 32#usize) :
    curve25519_dalek.montgomery.MontgomeryPoint.mul_base_clamped bytes ⦃ r =>
      r.toVector = curve25519.X25519 bytes.toVector (curve25519.encodeUCoordinate 9) ⦄

end rind.armv7
