# rind runs pyca/verified-garbage's proven code wherever it is fastest

## Goal

On every tier where [pyca/verified-garbage](https://github.com/pyca/verified-garbage) (VG) measures at least as fast as what rind runs, at every size the speed bar sets, rind runs VG's routine under its own glue and behavior, and that cell earns the ✓ once the instructions its proof rests on are cosimulated.

## Plan

Decided with the maintainer on 2026-11-12, in `/quest-plan`:

- VG is an Apache-2.0-or-BSD-3-Clause library written by LLMs. Its assembly is written in Lean over Lean models of each ISA and proven correct and constant time (memory and branch traces) in Lean v4.35.0, the toolchain `proofs/` uses, then printed as Rust naked functions in its `crates/verified-garbage-asm-<target>/`. It proves its own code, not the aws-lc and BoringSSL code rind runs, so rind gets a VG proof only by running VG's code.
- ✅ Measure, then switch per primitive and tier where VG is fastest (rejected: measure only and decide later, or take only ideas and no VG code). This is `AGENTS.md`'s fastest-permissive-source rule. Each switch also replaces a HOL Light proof of the code it retires.
- The ✓: ✅ switch the code once it measures fastest; the ✓ waits until [the routine's instructions are cosimulated](/quest/m2/verified-garbage/cosim.md) (rejected: a ✓ at once with VG's models listed as trusted, which lowers the bar rind holds its own s2n-bignum additions to; or no switch before cosimulation, since speed and proof are separate claims). VG's ISA models are LLM-written and checked only against vendor manuals and golden values. Its encoder is checked only by golden tests, and no CI step decodes the bytes it emits.
- ✅ VG becomes a permanent library in rind-bench, the benchmark report, and the nightly tiers (rejected: a one-off harness, which goes stale at VG's pace). This extends the report's library list settled on 2026-11-03.
- ✅ The nine unstarted m4 proof quests whose code VG may replace wait on [the measurement](/quest/m2/verified-garbage/bench.md) (rejected: keep them ready). These are ChaCha20-Poly1305 (x86_64 cipher and AEAD, aarch64), P-521, RSA (signing, x86_64 Montgomery, x86_64 IFMA), and ML-KEM's AVX-512 sampler and portable arithmetic. In-flight PRs continue.
- ✅ m2 (rejected: m4 as a proof route, which delays the speed wins behind m3). m2 follows the release MoQ switches to, so hot paths don't change under it.

Settled by the agent, from `AGENTS.md`:

- Behavior: a switch takes VG's lowest routine that leaves rind's API and behavior intact, and keeps rind's glue. Rind follows aws-lc-rs where VG differs: rind signs ECDSA with hedged nonces where VG is deterministic (RFC 6979), refuses small-order Ed25519 keys where VG doesn't, and wipes as rind's `wipe` feature says, not VG's secret-residue rule.
- Code: the first switch adds `admin/import-vg`, which vendors VG's generated code byte for byte from a pinned VG commit, as `admin/import-aws-lc` does for aws-lc. It also updates `AGENTS.md`'s list of verified sources and [the m4 verified epic](/quest/m4/verified/README.md)'s routes.
- Proofs: each ✓ imports a VG routine's theorem as one axiom about rind's opaque wrapper, under [the m3 epic's composition rule](/quest/m3/verified/README.md). VG's proofs as a Lake dependency were ruled out: one routine's import closure is 155 to 650 modules (50k to 176k lines, against `proofs/Rind`'s 38k), and needs VG's 18 GB build cache.

Groundwork measured on 2026-11-12 on an AMD Ryzen 9 9950X (Zen 5, full-width AVX-512) at VG `c7f68f69`, one Criterion run, VG's time over rind's:

- VG was faster at every size for ChaCha20-Poly1305 (0.91 at 16 B to 0.60 at 16 KiB), X25519 (0.74), Ed25519 (0.63 to 0.67), P-256 (0.71 to 0.94), P-384 signing (0.71), RSA-2048 (0.60 to 0.91), and ML-KEM-768 key generation and encapsulation.
- It lost on AES-GCM below 1350 B (1.10 to 1.28), SHA-256, HMAC, ML-KEM decapsulation (1.09), and ML-DSA key generation and signing. SHA-384/512, P-384 verification, and ML-DSA verification were ties.
- VG's wins rest on AVX-512 kernels that none of the report's six hosts can run. VG's own CI saw it beat aws-lc-rs on Neoverse-N2 for RSA-2048 (1.7x), ML-DSA-65, and P-521, but import an RSA key 3.4x slower.
