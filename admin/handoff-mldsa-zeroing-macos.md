# Handoff: macOS/aarch64 host for the ML-DSA zeroing failure

Status: not started. Fill in "Access" before starting.

Quest: [`quest/m0/catch-on-pr/mldsa-zeroing-macos.md`](/quest/m0/catch-on-pr/mldsa-zeroing-macos.md)
(S, unclaimed upstream).

## Why this host

`rind/tests/zeroing.rs`'s `ml_dsa` test failed once in the nightly `coverage`
workflow's macOS job
([run 43997727786](https://github.com/kixel-ai/rind/actions/runs/43997727786),
2026-11-17): `byte 3968 (0x1) was not cleared after drop` for a 4016-byte
value, the ML-DSA-44 `KeyPair::from_seed` the test checks third. It passed in
the other macOS runs and on a local M-series Mac, so it is rare, and it only
shows on macOS/aarch64. The quest's Plan is to reproduce it first by looping
the test there, with and without `RIND_CPU_DISABLE_sha3=1` (the coverage job
runs both), print which field sits at that offset, and fix the wipe at its
root: a nonzero byte is either outside the value `mid::mldsa::KeyPair`'s drop
wipes (it wipes all `size_of::<Self>()` bytes, padding included) or a write
after the wipe, such as a field's drop glue or a lazily filled cache.

Hosted `macos-latest` can run it, but an agent cannot loop a test there
interactively, change the code and rerun in seconds, or read the memory around
the offset. A local Apple-silicon host can. Linux aarch64 (Pi 5, Jetson) is
the wrong host: the failure has not shown there, and macOS differs in the
allocator and in SHA-3 hardware (`sha3` is a CPU feature on M-series, which is
why the job also runs with it disabled).

## Access (fill in)

| Item | Value |
| --- | --- |
| Host name or address (kept out of the repo) | |
| SSH user and key path (same) | |
| macOS version and chip (M1 to M4; SHA-3 present?) | |
| Rust toolchain: the pinned one from `rust-toolchain` or `nix develop` | |
| Can the host loop a test for hours? | |

Confirm the host first and put the output in the first PR comment:

    uname -m; sw_vers; sysctl -n machdep.cpu.brand_string
    sysctl hw.optional.armv8_2_sha3                # 1 if SHA-3 instructions exist

## Commands

1. Reproduce. In your own worktree and `CARGO_TARGET_DIR` under `~/.cache`:

       cargo test --release -p rind --test zeroing ml_dsa            # once
       i=0; while cargo test --release -p rind --test zeroing ml_dsa -- --exact ml_dsa >/dev/null 2>&1; do i=$((i+1)); done; echo "failed after $i passes"
       RIND_CPU_DISABLE_sha3=1 RUSTFLAGS='--cfg rind_cpu_disable' \
         cargo test --release -p rind --test zeroing ml_dsa          # the job's second config

   The failure rate was low (one run in the nightlies), so run at least a few
   thousand iterations per config, and also under `taskpolicy`/load
   (`yes > /dev/null &` per core) because the allocator behaviour may matter.
   Compile once per config, then loop that config's test binary directly.
   `RUSTFLAGS` changes Cargo's target hash, so the two configs build two
   different binaries; find each path and loop it, so the default binary is
   not run twice:

       zbin() { cargo test --release -p rind --test zeroing --no-run --message-format=json 2>/dev/null | python3 -c 'import sys,json; [print(m["executable"]) for m in map(json.loads,sys.stdin) if m.get("executable") and m["target"]["name"]=="zeroing"]'; }
       bin1=$(zbin)
       bin2=$(RIND_CPU_DISABLE_sha3=1 RUSTFLAGS='--cfg rind_cpu_disable' zbin)
       for b in "$bin1" "$bin2"; do i=0; while "$b" --exact ml_dsa >/dev/null 2>&1; do i=$((i+1)); done; echo "$b failed after $i passes"; done
2. Locate it. Extend the test locally (do not commit the debugging) to print,
   on failure, the offset of each field of the 4016-byte value
   (`core::mem::offset_of!`, or `{:p}` differences from the base) and the
   failing byte's neighbours, for ML-DSA-44 `from_seed` (value size 4016).
3. Fix at the root in `rind/src/mid/mldsa*` (see `KeyPair`'s `Drop`). Not a
   retry and not a looser check; AGENTS.md requires the whole value wiped.
4. Prove it: the loop above runs clean for at least 10 times the iterations it
   took to fail before, in both configs, plus `cargo test -p rind --test
   zeroing` and the other Rust gates `nix develop --command just ci
   upstream/main` selects for the touched module. ML-DSA secret paths changing
   need ctgrind (`admin/ctgrind`, Linux x86_64 only), so run it on the
   x86_64 host or say it was not run.

## What closes the quest

`ml_dsa` passes on every run on macOS/aarch64 (hosted and local), the cause is
named in the PR with the field and offset, the fix is at the root, and the
quest file is deleted in the same PR. If no failure reproduces locally after
a very large loop, say so plainly, report the iteration count and the config,
and ask the owner whether to leave the quest open for a hosted-runner run with
extra instrumentation. Do not close it on "could not reproduce".

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
| Host reachable | not started | | |
| Reproduced (iterations, config) | not started | | |
| Offset and field identified | not started | | |
| Fix and clean loop in both configs | not started | | |
| Quest deleted in the finishing PR | not started | | |

## Also unblocked by this host

- [`quest/m0/mac-mini-runner.md`](/quest/m0/mac-mini-runner.md): same machine
  class (see `admin/handoff-mac-mini-runner.md`).
- [`quest/m2/confidence/apple-nightlies.md`](/quest/m2/confidence/apple-nightlies.md):
  any other macOS-only nightly failure can use the same loop.
- [`quest/m0/catch-on-pr/README.md`](/quest/m0/catch-on-pr/README.md): this
  failure turned main's nightly red without a cause on the PR; a macOS repro
  host helps each sibling quest there that reads a macOS red.
- [`quest/m2/confidence/uncovered-functions.md`](/quest/m2/confidence/uncovered-functions.md),
  which found this failure while reading the nightlies.

## Report back

Host and chip, how many iterations per config before a failure, the offset and
field, the fix and its PR, the clean loop counts, and what could not run
(ctgrind).
