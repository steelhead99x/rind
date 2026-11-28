# [L] Split charon/aeneas Funs.lean per algorithm family, parallelize, and cache

## Goal

Break `rind`'s monolithic per-architecture `proofs/Rind/<Arch>/Funs.lean` rebuild cascade by splitting `charon`/`aeneas` extractions into per-algorithm-family namespaces, running extractions in parallel, and caching extracted `{Types,Funs}.lean` artifacts by input hash, so editing one Rust algorithm only invalidates that algorithm's Lean proofs rather than every proof on the architecture.

Non-goals: changing any proven Rust semantics, weakening Aeneas translation checks or axioms, or altering proof coverage.

## Plan

Decided 2026-11-27 (maintainer, `/quest-plan`):
- ✅ Place in `m2`: per `quest/README.md`, `m2` holds proof groundwork that keeps `rind` correct and fast; this is a larger structural refactor (`[L]`) that complements `m0`'s cache work without blocking MoQ's `m1` switch.
- ✅ Split `charon`/`aeneas` extractions into per-algorithm-family namespaces (following `extract_kdf`'s existing pattern) AND parallelize and cache extractions, migrating incrementally family by family without breaking existing proofs (rejected: parallelizing and caching the monolithic `Funs.lean` files without splitting them per family, which still invalidates all proofs on an architecture on any 1-line Rust edit).

Baseline (2026-11-27):
- `admin/prove:1752-2023` runs 5+ `charon` + `aeneas` extractions serially (`X86_64`, `Aarch64`, `X86_64/Kdf`, `Aarch64/Kdf`, `Armv7`, plus `Portable` and `dalek`), and `to_lean` clobbers a single `$out/lean` scratch directory so extractions cannot overlap.
- Because `X86_64/Funs.lean` and `Aarch64/Funs.lean` each hold the entire translated Rust surface for that arch, editing a single Rust function (for example in `mlkem`) regenerates the whole `Funs.lean` and forces Lake to re-elaborate every downstream proof module for that architecture (AES-GCM, SHA-2, SHA-3, ChaCha20, P-256, P-384, RSA, Ed25519, ML-KEM).

Approach:
1. **Parallelize and content-address `charon`/`aeneas` extractions:**
   - Give each `to_lean` / `extract` / `extract_kdf` / `extract_armv7` invocation its own scratch directory under `$out/lean-<name>` (and per-target `CARGO_TARGET_DIR` isolation where needed) so all extractions run concurrently.
   - Cache extracted `{Types,Funs}.lean` artifacts locally (and optionally against the shared cache from [kixel-ai/rind#1138](https://github.com/kixel-ai/rind/pull/1138)), keying on every input that affects translation: `charon_path`, `rustc -vV`, `aeneas -version`, extraction flags, target triple and effective target/cfg configuration (including `RUSTFLAGS` / `CARGO_ENCODED_RUSTFLAGS`), `.cargo/config.toml`, root and crate `Cargo.toml` manifests, `Cargo.lock`, `rind/build.rs`, `rind/src/**` (and any local/vendored path crates Charon traverses), and `admin/prove`'s extraction/post-processing steps. Preserve file mtimes when generated outputs are byte-identical so Lake never sees spurious dirty timestamps.
2. **Split monolithic `X86_64` and `Aarch64` extractions by algorithm family:**
   - Following `extract_kdf`'s proven pattern (`proofs/Rind/<Arch>/Kdf/{Types,Funs}.lean` + `{Types,Funs}External.lean`), split independent algorithm families out of the monolith into their own namespaces (such as `MlKem`, `Rsa`, `P256`/`P384`/`Ecdsa`, `Ed25519`/`X25519`, `Aes`, `ChaCha`, `Sha`).
   - Keep shared foundational primitives (e.g., `Error`, `low::ct`, core hash contracts) in a small shared base extraction or opaque boundary so families do not duplicate heavy definitions, and preserve `admin/prove`'s global-name isolation invariant.
   - Migrate incrementally so every commit keeps full `admin/prove lean` green with identical theorem statements and zero new axioms.
3. **Measure impact:**
   - Measure before/after `admin/prove lean` wall time and CPU seconds for:
     - a clean/unchanged Rust run (testing extraction parallelization + caching), and
     - a 1-line edit inside a single algorithm (e.g., `rind/src/mid/mlkem.rs`), reporting how many of the 261 Lean modules re-elaborate before vs after.

## Related

- [Aeneas translation cache and SSH-shared Lake outputs](https://github.com/kixel-ai/rind/pull/1138) - shared cross-host cache work
- [Build spec-server once in prove.yml and add scoped admin/prove lean targets](/quest/m0/spec-server-single-build.md) - scoped `admin/prove lean <Module>` runs
- [Spike and benchmark Lean 4.35 speedup levers on rind's proof corpus](/quest/m2/lean-speed-spikes.md) - `module` system and tactic profiling
- [rind's HOL Light proofs are ported to Lean](/quest/m5/verified/hol-light-to-lean.md) - will add ~19.7k more lines of Lean proofs benefiting from split extractions
