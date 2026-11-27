# [XS] rind runs in OSS-Fuzz

## Goal

rind's `fuzz` crate targets run continuously in OSS-Fuzz, with crashes reported to the maintainer, and its coverage shows on OSS-Fuzz's dashboard.

## Plan

- Promoted from m4 to `m2/confidence` on 2026-11-21 (maintainer, /quest-plan): ✅ promote to m2 (rejected: keep in m4). The upstream PR text is already approved and continuous OSS-Fuzz is an immediate assurance and public-trust signal.
- `fuzz/oss-fuzz/` holds `project.yaml`, `Dockerfile`, and `build.sh`, which [google/oss-fuzz#16607](https://github.com/google/oss-fuzz/pull/16607) copies to `projects/rind/` with that repo's required Google LLC license header added to `build.sh` and `Dockerfile`. Keep the two in sync: a change here is a PR there, or a push to the `rind` branch of kixelated/oss-fuzz while #16607 is open.
- [kixel-ai/rind#970](https://github.com/kixel-ai/rind/pull/970) rewrites `build.sh`'s body to skip the `python` target, which OSS-Fuzz's runners cannot run without CPython, and to ship the FIPS module the `fips` target loads. Once it lands, push its `build.sh`, with the header, to the upstream copy, which still builds every target, together with the `Dockerfile`, which after #16607 opened gained `rustup default` on the pinned nightly (OSS-Fuzz's `compile` copies the default toolchain's `rust-src` for coverage reports) and a reworded comment.
- On 2026-11-22 OSS-Fuzz's images had moved under the files: the 20.04 base's rustc (1.91) predates `fuzz/Cargo.toml`'s `rust-version` (1.94), and GitHub refuses its git 2.25's shallow protocol v0 clone with a 401, so the project moved to the Ubuntu 24.04 base, pinning `nightly-2026-01-20` (rustc 1.95, LLVM 21.1.8) and installing cargo-fuzz, which that base ships without. Locally the ASan `cargo fuzz build` then compiled every target; seeding failed on 24.04's `xxd` package, since fixed but not rebuilt, and the coverage build and `check_build` did not run (the maintainer paused local OSS-Fuzz builds for CPU), so google/oss-fuzz#16607's CI is their first full run.
- This was one of three children of an assurance epic (maintainer, 2026-11-07). On 2026-11-09 the maintainer chose ✅ ACVP to m2 and cryptofuzz deleted (rejected: retarget cryptofuzz at MozillaSecurity's fork, leave both in m4): ACVP is static vectors that need no outside approval, and cryptofuzz's upstream, guidovranken/cryptofuzz, is gone, with OSS-Fuzz's own cryptofuzz project disabled. Don't plan cryptofuzz again without a maintained upstream.
- Decided 2026-11-18 (maintainer, /quest-complete): ✅ approve the drafted google/oss-fuzz PR as written (rejected: hold, reject), with factual corrections keeping the approval. Opened 2026-11-22 as google/oss-fuzz#16607 with 25 targets (`cargo fuzz list`) and each group's oracle corrected.

## Waiting

- google/oss-fuzz: [#16607](https://github.com/google/oss-fuzz/pull/16607) passes its trial build, which OSS-Fuzz's maintainers start (its CLA, header, and PR helper checks passed by 2026-11-24), and merges; check with `gh pr view 16607 --repo google/oss-fuzz`. If its build fails, fix `fuzz/oss-fuzz/` here and push the same change to the `rind` branch of kixelated/oss-fuzz.
- Maintainer: once it merges, sign in to OSS-Fuzz's ClusterFuzz with kixelated@gmail.com (Google accounts only, so no agent can) and confirm crash reports and the coverage dashboard show rind. Delete this quest only once that is done, #970 has landed, and the upstream copy matches `fuzz/oss-fuzz/` plus the header, #970's `build.sh` included.
