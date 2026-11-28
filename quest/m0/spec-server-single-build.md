# [S] Build spec-server once in prove.yml and add scoped admin/prove lean targets

## Goal

Stop `.github/workflows/prove.yml` from compiling Mathlib to C and linking `spec-server` five separate times per nightly run (saving ~80 hosted runner-minutes per run), and add scoped module targeting (`admin/prove lean [Module...]`) so local agents and contributors can check individual Lean proof modules without rebuilding all 261 modules across 4 architectures.

Non-goals: dropping any `spec-tests` vector group or random case, changing what bare `admin/prove lean` verifies on full runs, or altering proof trust assumptions.

## Plan

Decided 2026-11-27 (maintainer, `/quest-plan`):
- ✅ Place in `m0`: eliminates ~80 minutes of duplicate hosted CI build time per nightly run against the org's 60-job concurrency cap and cuts local agent Lean iteration CPU on shared hosts immediately.
- ✅ Build `spec-server` once in a dedicated `spec-server-build` job in `.github/workflows/prove.yml` (with GitHub Actions caching for Mathlib `.c`/`.o` objects) and pass the compiled binary artifact to the 5 `spec-tests` matrix shards (rejected: keeping 5 separate builds and relying only on caching `.c`/`.o` files, since GitHub-hosted runners cannot reach `fedora`'s Tailscale cache).
- ✅ Add scoped `admin/prove lean [Module...]` targeting alongside the existing full `admin/prove lean` mode.

Baseline (2026-11-27):
- In `.github/workflows/prove.yml:348-386`, the `spec-tests` matrix runs 5 parallel `ubuntu-24.04` jobs (`mlkem.a`, `mlkem.b`, `mlkem.c`, `digests`, `rest`). Each job independently compiles every Mathlib module `spec-server` imports to C and links `proofs/.lake/build/bin/spec-server`, spending 17-27 minutes per runner (85-135 runner-minutes total) before running the vector driver.
- Locally, `admin/prove:2219` always runs bare `lake build` across all 261 `Rind` modules (`X86_64`, `Aarch64`, `Portable`, `Armv7`, `ForHumans`, `Proofs`) even when an agent only edited one proof file.

Approach:
1. **Single `spec-server` build job in `.github/workflows/prove.yml`:**
   - Add a `spec-server-build` job (`runs-on: ubuntu-24.04`) that runs the existing `lean_deps` Mathlib/Aeneas cache prefetch before `lake build spec-server` (optionally backed by `actions/cache` keyed on `proofs/lean-toolchain` + `proofs/lake-manifest.json` + spec inputs) and uploads `proofs/.lake/build/bin/spec-server` as a workflow artifact.
   - Have the 5 `spec-tests` matrix shards depend on `spec-server-build`, download the binary, and run only the `spec-tests` Rust driver against it (skipping both `lean_deps` and `lake build spec-server` in the shards when a prebuilt binary path is provided via env var or CLI flag to `admin/prove spec-tests`).
   - Verify `sh/select-jobs.sh` still handles `-f jobs=spec-tests` cleanly (including its `spec-server-build` dependency).
2. **Scoped `admin/prove lean [Module...]`:**
   - Extend `admin/prove` so passing module targets after `lean` (e.g., `admin/prove lean Rind.X86_64.AesGcm`) runs `lake build "$@"` instead of bare `lake build`, and skips unrelated architecture extractions when the requested modules only belong to one target directory (while refusing to emit or save a whole-`lean` cache key on a partial run).
   - Keep bare `admin/prove lean` unchanged (full verification across all architectures and `SimdVectors.lean`).
   - Document scoped `admin/prove lean <Module>` usage in `admin/prove`'s usage header and `proofs/README.md` / `CONTRIBUTING.md` where agents look for proof commands.
3. **Validation:**
   - Measure before/after wall time for a single-module `admin/prove lean Rind.X86_64.AesGcm` edit locally and verify `prove.yml` workflow lint (`actionlint` / `just check`).

## Related

- [Aeneas translation cache and SSH-shared Lake outputs](https://github.com/kixel-ai/rind/pull/1138) - shared cross-host proof cache and `nixos` `rind-ci` work
- [Split charon/aeneas Funs.lean per algorithm family, parallelize, and cache](/quest/m2/split-aeneas-extractions.md) - breaks monolithic `Funs.lean` invalidations
- [Spike and benchmark Lean 4.35 speedup levers on rind's proof corpus](/quest/m2/lean-speed-spikes.md) - measures `module` system, tactic profiling, `Elab.async`, and `leanc` flags
