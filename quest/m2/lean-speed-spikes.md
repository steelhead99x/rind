# [M] Spike and benchmark Lean 4.35 speedup levers on rind's proof corpus

## Goal

Measure and benchmark four general Lean 4.35 speedup levers on `rind`'s 261-module / 100k-LOC proof corpus, adopting clear low-risk wins directly in `rind` (`module` system on shared hubs and top profiled tactic hot spots) and producing a measured verdict on intra-file parallelism, `leanc` C-codegen speedups, and whether Lake's native remote cache suffices or a deeper standalone `mbx`-for-Lean tool is justified.

Non-goals: weakening proof rigor or trust assumptions, porting HOL Light proofs ([hol-light-to-lean](/quest/m5/verified/hol-light-to-lean.md)), or building a standalone `mbx`-for-Lean tool before the measurements here justify it.

## Plan

Decided 2026-11-27 (maintainer, `/quest-plan`):
- ✅ Place in `m2`: per `quest/README.md`, `m2` holds measurements and proof groundwork that keep `rind` correct and fast; findings also inform `kixel-ai/rust2`'s `quest/m2/lean-spike.md` and `kixel-ai/dotfiles`'s `quest/m0/lake-auto-cache.md`.
- ✅ Benchmark all 4 general Lean 4.35 levers on `rind`'s corpus (rejected: adopting `module` and tactic profiling only without measuring `Elab.async`, `leanc` C-codegen flags/`ccache`, and Lake native cache gaps).

Baseline (2026-11-27):
- `proofs/Rind/` contains 261 `.lean` files totaling ~100,124 LOC. Only 43 of 261 files currently use Lean 4.35's `module` header (`.olean` vs `.olean.private` split).
- Several single files sit on the critical path (`Portable/Mont.lean` 3,179 LOC, `X86_64/Sha3.lean` 2,370 LOC, `X86_64/P256Ecdsa.lean` 2,186 LOC, `X86_64/P384Ecdsa.lean` 1,906 LOC, `X86_64/Avx512Vectors.lean` 1,631 LOC, `X86_64/RsaKey.lean` 1,504 LOC).
- Linking `spec-server` compiles Mathlib + specs to C (~17-27 minutes in CI).

Approach:
1. **Lever 1 - Lean 4 `module` system (`module` + `public` + `.olean.private`):**
   - Identify the highest-fanout shared hub modules not yet using `module` (such as `Axioms.lean`, `Spec/*`, `FunsExternal.lean`, `TypesExternal.lean`, `S2nBignum.lean`, `AwsLc.lean`), convert the top hubs to `module`, and measure before/after (a) downstream modules rebuilt on a proof-body-only edit and (b) peak RSS during `lake build`.
2. **Lever 2 - Tactic profiler and mega-file splits:**
   - Enable `profiler = true` and `profiler.threshold = 500` in the `Rind` library's `leanOptions` in `proofs/lakefile.toml` (since Lake's CLI rejects `-D` flags) for the measurement run across `Rind`, ranking the top 20 slowest declarations and files (separating elaboration, tactic search like broad `simp`/`omega`/`bv_decide`/`ring`, and kernel typechecking).
   - Fix the highest-ROI tactic hot spots (e.g., replacing broad `simp` with `simp only [...]`) and measure splitting the single slowest mega-file (`Portable/Mont.lean` or whichever file leads the critical path).
3. **Lever 3 - Intra-file parallelism (`Elab.async` / `--threads`) and `leanc` C codegen:**
   - Benchmark `Elab.async` and thread counts on the slowest Lean files (wall time, CPU time, peak RSS).
   - Benchmark `leanc` options for `spec-server` and `rind-asm` (`ccache`, `clang` vs `gcc`, `-O0` vs default optimization for dev builds, and Lake `.o` artifact caching) to see how much of the 17-27 min `spec-server` compile can be eliminated locally and in CI.
4. **Lever 4 - Upstream Lake cache vs standalone `mbx`-for-Lean verdict:**
   - Exercise Lake 5.0's native artifact cache + `lake cache get|put` (and `kixel-ai/dotfiles`'s `quest/m0/lake-auto-cache.md` shim if landed) against real incremental edits and multi-host worktrees on `rind`.
   - Record concrete hit/miss/bypass rates and any Lake limitations (such as missing `.o` reuse, coarse invalidation, or slow serialization), ending with a clear verdict: keep the thin Lake shim + file upstream Lake issues, or open a follow-up quest for a deeper standalone `mbx`-for-Lean cache tool.

## Related

- [Aeneas translation cache and SSH-shared Lake outputs](https://github.com/kixel-ai/rind/pull/1138) - shared cross-host proof cache
- [Build spec-server once in prove.yml and add scoped admin/prove lean targets](/quest/m0/spec-server-single-build.md) - CI `spec-server` deduplication and scoped local targets
- [Split charon/aeneas Funs.lean per algorithm family, parallelize, and cache](/quest/m2/split-aeneas-extractions.md) - breaks monolithic `Funs.lean` invalidations
- [rind's HOL Light proofs are ported to Lean](/quest/m5/verified/hol-light-to-lean.md) - upcoming Lean proof growth
- `kixel-ai/dotfiles` `quest/m0/lake-auto-cache.md` - Tailscale Lake cache server and transparent `lake` PATH shim
- `kixel-ai/rust2` `quest/m2/lean-spike.md` - `rust2-lean` MIR extractor spike
