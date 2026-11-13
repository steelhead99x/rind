# [S] rind 0.4 ships once

## Goal

rind 0.4.0 on crates.io carries every breaking change planned by 2026-11-12: the API epic's first three (the typed AES-CBC IV, agreement keys that keep their public key, and no runtime CPU check), ML-KEM's `kem` API, the removal of the `wipe` feature if the maintainer accepts it as kixel-ai/rind#609 proposes, the API shape the spike settles, and HKDF's `Prk`. No release before it carries only some of them, and each adapter moves its `rind` requirement from 0.3 to 0.4 once, in a patch release from the same release PR.

## Plan

Decided with the maintainer on 2026-11-09:

- Releases: one rind 0.4 that carries all three breaking changes, and a MoQ-side PR ready before the adapter fixes publish ✅ (rejected: the 0.4 quest alone, accepting that MoQ's build breaks until fixed; leaving both to release-plz). Three breaking releases would re-pin every adapter three times, and each would leave a consumer that pins rind 0.3 with two copies of rind until it follows.
- Two of the three merged the same day, while rind's version was hand-set to 0.3.3 and unpublished: the typed CBC IV ([kixel-ai/rind#530](https://github.com/kixel-ai/rind/pull/530)) and the agreement keys ([kixel-ai/rind#529](https://github.com/kixel-ai/rind/pull/529)). A version set by hand ahead of the published one is kept as is (`CONTRIBUTING.md`'s Releases section), so release PR [kixel-ai/rind#511](https://github.com/kixel-ai/rind/pull/511) proposed publishing both as rind 0.3.3. On 2026-11-10 the maintainer chose ✅ to return rind's manifest to the published 0.3.2, so release-plz proposes 0.4.0 itself from the `!` commits, and hold the release for the last change (rejected: hand-set 0.4.0; set 0.4.0 and ship it now, with the CPU-check removal as 0.5; revert both and release 0.3.3). [kixel-ai/rind#548](https://github.com/kixel-ai/rind/pull/548) sets it; any later `!` change to rind then lands inside the same 0.4.0.
- So the adapter fixes publish in the same release as rind 0.4, not before it, and MoQ's PR moves to both at once.
- Decided 2026-11-12 (maintainer, /quest-audit): 0.4 also waits for every breaking change planned by then ✅ (rejected: only ML-KEM and wiping, with the API fixes in 0.5; ship the first three as planned). The audit found four more breaks already written or planned, and a 0.5 weeks after 0.4 would re-pin every adapter a second time, which is what this quest exists to prevent. They are ML-KEM's `kem` API ([kixel-ai/rind#606](https://github.com/kixel-ai/rind/pull/606)), wiping without the `wipe` feature, which [kixel-ai/rind#609](https://github.com/kixel-ai/rind/pull/609) proposes and [its quest](/quest/m2/wipe-default.md) leaves the maintainer to accept or send back, [the API shape](/quest/m2/api/shape.md), and [HKDF's `Prk`](/quest/m2/api/hkdf-prk.md). The same day: 0.4 waits for the shape spike's verdict and whichever shape wins ✅ (rejected: fix names in today's modules for 0.4 and redesign in 0.5; only HKDF joins 0.4). `Required` below is the whole list, and the sentence after this list covers only the first three.

What remains is [rind needs no runtime CPU check](/quest/m2/api/cpu-check.md).

The hold uses only what the release tooling has. Publishing happens only when a release PR merges (`CONTRIBUTING.md`'s Releases section, `release_always = false` in `.release-plz.toml`), and one release PR covers every crate. So the hold is the maintainer leaving the release PR unmerged, and while it lasts no adapter fix and no pyrind release publishes either.

Before the release PR merges, check what it proposes:

- `rind` 0.4.0.
- Each adapter already on crates.io at its next patch version, requiring rind 0.4.0. rind-openmls is not one of them, and the last item covers it. A `!` commit or a removed item makes release-plz propose an adapter's next breaking version, which `sh/adapter-versions.sh` fails (`CONTRIBUTING.md`'s Releases section). [kixel-ai/rind#548](https://github.com/kixel-ai/rind/pull/548) set rind-rustls, rind-rcgen, rind-ring, and rind-str0m by hand for the changes merged by then; a later adapter PR with a `!` title sets its own patch version, as [kixel-ai/rind#522](https://github.com/kixel-ai/rind/pull/522) did.
- No breaking version for an adapter from the rind 0.4 requirement alone: its API did not change, so set its patch version by hand if release-plz proposes one.
- No first version of rind-openmls. It is new ([kixel-ai/rind#645](https://github.com/kixel-ai/rind/pull/645)) and uses `rind::hpke`, which 0.3.2 lacks, so it cannot be published by hand before rind 0.4.0, as `CONTRIBUTING.md`'s Releases section asks of a new crate, and trusted publishing cannot create it: in the release, it would fail after rind publishes. A dry run of `cargo publish -p rind-openmls` from `main` on 2026-11-12 failed on that import.

Decided 2026-11-12 (maintainer, rust2's /quest-unblock): keep rind-openmls out of the release ✅. Before the release PR merges, a PR sets `release = false` for it in `.release-plz.toml`. Once 0.4.0 is on crates.io, the maintainer publishes rind-openmls by hand from `main` with their own `cargo login`, adds its trusted publisher and turns on "require trusted publishing", and a PR removes the exclusion (rejected: merging the release and publishing rind-openmls by hand after its job fails, which leaves the release partial).

Each change documents its own migration in MIGRATING.md, so this quest adds none. Delete it once 0.4.0 is published.

The benchmark report is refreshed once before each minor release (maintainer, 2026-11-09), so this quest requires that run. Whoever plans the next minor release's quest creates the next run at the same path, from the last one in git history, and requires it.

## Waiting

- Maintainer: leave the release PR, [kixel-ai/rind#511](https://github.com/kixel-ai/rind/pull/511) or whichever replaces it, unmerged until every quest under `Required` is on `main` and MoQ's PR is ready, then merge it. An agent cannot: a release PR merges on the maintainer's approval (`CONTRIBUTING.md`'s Reviews section), and leaving rind alone out of the release (`release = false`) would not hold it, since every adapter's fix requires rind 0.4, which is why the hold is the unmerged PR. Check: `cargo search rind` shows 0.4.0.

## Required

- [ML-KEM-512 and ML-KEM-1024](/quest/m3/parity/ml-kem.md) - the `kem` API over all three parameter sets, a breaking change to `kem`
- [Measure what wiping costs, and decide whether it is on by default](/quest/m2/wipe-default.md) - the default decided; if it lands as its open PR, kixel-ai/rind#609, proposes, the `wipe` feature is removed, which is the breaking change, and if it lands as a default feature only, nothing breaks and this line goes
- [The API takes one shape](/quest/m2/api/shape.md) - the spike's verdict, and the renames and moves of whichever shape wins
- [HKDF PRKs load from bytes and fill a slice](/quest/m2/api/hkdf-prk.md) - `expand(info, usize)` replaced by `fill`
- [Benchmark report refresh, before rind 0.4](/quest/m2/bench/report-refresh.md) - the report and the README's claims, current for the release
- [rind needs no runtime CPU check](/quest/m2/api/cpu-check.md) - `cpu::check` and `MissingFeature` removed, the last of the three
- [Releases publish only after the full suite passes locally](/quest/m0/ci-speed/release-check.md) - the local full-suite run every release PR now passes before it merges
