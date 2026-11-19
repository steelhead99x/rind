# Handoff: AMD Zen 2 (no VAES) for the QUIC AES-GCM tier

Status: not started. Nothing is known about a Zen 2 machine in the owner's
reach. Fill in "Access" before starting.

Quest: [`quest/m3/quic-path.md`](/quest/m3/quic-path.md) (XS, unclaimed
upstream).

## Why this host

x86_64 CPUs with AVX and MOVBE but no VAES run the `HaveAvxMovbeForAesGcm`
tier: Vale's AES-GCM kernel at every length, except seals under 129 B
(`AVX_VALE_SEAL_FROM` in `rind/src/low/x86_64/aes_gcm.rs`), which run rind's
SSE `by8` loop (kixel-ai/rind#436, from a Coffee Lake measurement). Whether
Vale or `by8` is faster at QUIC packet sizes (64 B to 1452 B) on such a CPU
is decided from a measurement on one. The CPU must be Zen 2 or older AMD
(Ryzen 3000, EPYC 7002 such as the EPYC 7662 zshenker has, Threadripper 3000)
or Zen+ or Zen 1: **Zen 3 and later have VAES** and so take another tier. The
quest has Zen 3, 4, 5 and Arrow Lake numbers obtained by forcing the AVX tier
with `--cfg rind_cpu_disable`, and they show `by8` 3 to 8% ahead of Vale at
1200 to 1452 B on Zen 3, 4 and 5 but Vale 15 to 49% ahead on Arrow Lake, so a
forced tier on a newer core is not a stand-in for real Zen 2 silicon (cache,
and `pclmulqdq`/AES latency differ). Intel parts without VAES (Skylake to
Comet Lake, Coffee Lake) also run this tier, but the quest wants AMD, since
the existing 129 B threshold came from Coffee Lake.

The quest's own Waiting item is zshenker rerunning moq-dev/moq#7873's bench
on the Zen 2 EPYC 7662 with rind 0.1.13 or later; check for a reply there
(read-only; post nothing to other orgs). If it has arrived, an agent can act
on it without owning the hardware, and this handoff is only for running it
ourselves.

## Access (fill in)

| Item | Value |
| --- | --- |
| Host name or address (kept out of the repo) | |
| SSH user and key path (same) | |
| CPU model, family and stepping, cores, RAM | |
| `grep -c vaes /proc/cpuinfo` (must print 0) | |
| `grep -o -w -E 'avx|avx2|movbe|aes|pclmulqdq' /proc/cpuinfo \| sort -u` | |
| Governor and SMT state; can a core be pinned (`taskset`) | |
| Nix, or a Rust toolchain matching `rust-toolchain` | |

Confirm the CPU first and put the output in the first PR comment. If the
CPU lists `vaes`, stop: it is not the target.

## Commands

All timing runs: one pinned core, interleaved A/B, a separate
`CARGO_TARGET_DIR` per variant under `~/.cache`, at least 5 rounds, medians
with spread, and the aws-lc-rs control must stay within 1.02 between rounds.
Governor `performance` during runs, restored after.

1. Confirm which tier ran. The suite's own check:

       cargo test --release -p rind --lib -- detects_the_expected_cpu

   and the dispatch in `rind/src/low/x86_64/aes_gcm.rs` (`vale`, `by8`,
   `AVX_VALE_SEAL_FROM`, `VAES_AVX2_VALE_*_BELOW`).
2. Seal and open at 16, 64, 128, 129, 256, 512, 1200, 1452 B, rind against
   aws-lc-rs (and ring) for AES-128-GCM and AES-256-GCM:

       taskset -c 3 cargo bench -p rind-bench --bench aes_gcm -- --noplot \
         "(^|/)(rind|aws-lc-rs|ring)(/|\$)"

   (`rind-bench/benches/aes_gcm.rs`; `admin/bench-report collect` is the
   report's own harness and `sh/bench-select.sh` names bench targets.)
3. Force each candidate tier for the same lengths. `by8`-only: change the
   `AVX_VALE_SEAL_FROM` threshold locally (for example to a value above 1452)
   in one variant, and to 0 in the other, so one build runs `by8` at every
   seal length and the other Vale. Opens need the same for the open path
   (`vale::<false>` branch). Keep these variants out of the PR.
4. Decide: if `by8` is faster at some lengths on Zen 2 (seal, open or
   both), route AMD CPUs without VAES (`HaveAvxMovbeForAesGcm` and AMD vendor
   in `cpu.rs`) to the faster path at those lengths, with the threshold
   constant documented as the existing ones are, and a unit test for the
   routing. Otherwise the quest is deleted: say what the numbers were.
5. If code changes: `nix develop --command just ci upstream/main`, and
   `RIND_CPU_DISABLE_*` tier coverage in `build.yml`'s x86_64 matrix must
   still exercise both paths. Kernel changes are not proof-affected unless
   `proofs/` covers the touched routine; check `quest context`.

## What closes the quest

A Zen 2 (or older AMD) measurement table in the PR, and either a routing
change measured faster there (and no slower on Coffee Lake or the newer
AMD cores that also take this tier, shown by the same A/B) or the deletion of
the quest with the table as the reason. The quest file is deleted in the
finishing PR either way.

## Rules for every job

- Fork only. Always `gh --repo steelhead99x/rind`, never bare `gh`. Post
  nothing to kixel-ai or any other org, and publish nothing. Do not run
  `quest start` (it claims upstream); read-only `quest context` and
  `quest check` are fine.
- Read `AGENTS.md` and run `quest context` first. No em dashes. End GitHub
  posts and PR bodies with `(Written by <model>)`. PR bodies need
  `## Validation`, `## Models` (Size S first, Implementer last) and
  `## Waiting`.
- Fork PRs are draft, against a fork base branch at upstream `main`
  (fetch `kixel-ai/rind` main as `upstream/main`; the fork's `origin/main`
  has diverged and is not a base). No force-push, no rebase, never merge.
- Work in your own git worktree and CARGO_TARGET_DIR under `~/.cache`, never
  the shared clone and never `/tmp`. Commits are authored as the fork owner
  (`steelhead99x <224322244+steelhead99x@users.noreply.github.com>`) with a
  `Co-Authored-By: <model> <noreply@anthropic.com>` trailer. That is for fork
  PR commits only: anything bound for an upstream PR is restacked by the
  owner with no AI trailer, so do not open upstream PRs yourself.
- Report losses and failures as plainly as wins. Do not hide a failure with a
  retry or a looser check.

## Tracking

| Step | State | PR or link | Notes |
| --- | --- | --- | --- |
| zshenker's reply on moq-dev/moq#7873 checked | not started | | read-only |
| Zen 2 host found, no VAES confirmed | not started | | |
| Baseline table (seal and open, 8 lengths) | not started | | |
| `by8` against Vale at every length | not started | | |
| Decision and PR, or quest deleted | not started | | |

## Also unblocked by this host

- [`quest/m2/bench/fedora.md`](/quest/m2/bench/fedora.md) and
  [`quest/m2/bench/report-refresh.md`](/quest/m2/bench/report-refresh.md):
  a Zen 2 host is a row `BENCHMARKS.md` lacks (check each quest's own
  Waiting before assuming).
- The `vale`/`by8` thresholds themselves for Zen 1 and Zen+, if the owner has
  one.

## Report back

CPU and kernel, `vaes` absent confirmation, the table at each length for seal
and open (rind `by8`, rind Vale, aws-lc-rs, ring) with spread, the decision,
the PR, and what the owner must decide.
