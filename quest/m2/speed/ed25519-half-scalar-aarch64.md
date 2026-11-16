# [S] aarch64's Ed25519 verification uses half-size scalars, if it measures faster

## Goal

aarch64's Ed25519 verification runs x86_64's half-size check where it measures faster than s2n-bignum's proven `edwards25519_scalarmuldouble_alt`, which it keeps until then, and BENCHMARKS.md's `kixtop` row shows the result against aws-lc-rs.

## Plan

- [kixel-ai/rind#768](https://github.com/kixel-ai/rind/pull/768) took the half-size check on x86_64 only: no aarch64 host was reachable to measure it (`kixtop`, the report's only aarch64 host, was offline). On x86_64 it ran 15 to 20% faster than s2n-bignum's routine over the same point routines' `_alt` twins, which aarch64 runs, so expect a gain, but measure before taking it, as the quest rule says.
- Measure on `kixtop` (Apple M4), or a GitHub arm64 runner (Neoverse) with a same-run aws-lc-rs baseline: time `ed25519-verify` for rind and aws-lc-rs at `main` and with the switch, interleaved.
- The switch: `low::generic::edwards25519_msm` builds for `rind_backend = "aarch64"` too, `low/mod.rs` exports it there, and `mid::ed25519::VerifyingKey::verify` and `mid::half_size` drop their x86_64 cfg; `low::aarch64::edwards25519_scalarmuldouble` and its `admin/parse-asm` entry go.
- Taking it costs aarch64's `ed25519-verify` ✓: drop it from `benchmarks/verified.toml`, delete `proofs/Rind/Aarch64/Ed25519Verify.lean` and its import and `#print axioms` checks in `Rind/Aarch64/Axioms.lean`, remove the `edwards25519_scalarmuldouble_spec` axiom and `RunsDouble`, and declare the MSM and field product opaque in `Rind/Aarch64/FunsExternal.lean` as x86_64's are. [The proof quest](/quest/m4/verified/ed25519-half-scalar.md) then covers both targets.
- If it does not measure faster, record that in ALGORITHMS.md's Ed25519 note and delete this quest.

## Related

- [Ed25519 verification on x86_64 is proven again](/quest/m4/verified/ed25519-half-scalar.md) - the proof that would cover aarch64 too
