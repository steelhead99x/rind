# Handoff: Raspberry Pi 4 (Cortex-A72) validation

Status: first round not started. The board is on the owner's local network and
has not been probed. Fill in the host details under "Access" before starting.

## Why this board

The Pi 4's Cortex-A72 is Armv8.0-A with NEON and **no crypto extension** (no
`aes`, `pmull`, `sha1`, `sha2`). Every other aarch64 board the owner has (Pi 5,
Jetson Orin Nano) has it. So the Pi 4 is the only host that runs rind's
fallback paths on real silicon:

- AES, GHASH, SHA-1 and SHA-256 run on aws-lc's NEON and scalar assembly
  (see [ALGORITHMS.md](/ALGORITHMS.md) and [PLATFORMS.md](/PLATFORMS.md)).
- `rind::cpu::has_aes_hardware()` is false, so rind-rustls and rind-dimpl
  prefer ChaCha20-Poly1305.
- SVE2 is absent, so ChaCha20-Poly1305 takes aws-lc's NEON assembly.
- Nothing in CI runs these paths natively; they only run under QEMU.

The same board is the target of the unclaimed quest
[`m5/verified/aarch64-no-crypto`](/quest/m5/verified/aarch64-no-crypto.md)
(L): proofs for vpaes, NEON GHASH and the scalar SHA routines. That quest needs
the Pi 4 for its speed check, not for the proofs.

## Access

Fill in before starting:

- Host / address:
- User and key:
- Cores / RAM / disk:
- Rust toolchain on the board (`cargo --version`), or cross-build from the
  laptop (`aarch64-unknown-linux-gnu`) and copy binaries:
- Valgrind and libclang present? (ctgrind needs both; the Pi 5 had Valgrind
  but no libclang, the Jetson had neither):
- Passwordless sudo? (needed for the CPU governor):

Confirm the CPU first and put the output in the first PR comment:

    uname -m; grep -m1 'CPU part' /proc/cpuinfo   # expect 0xd08 (Cortex-A72)
    grep -m1 Features /proc/cpuinfo                # expect no aes/pmull/sha1/sha2

## Rules for every job

- Fork only. Always `gh --repo steelhead99x/rind`, never bare `gh`. Post
  nothing to kixel-ai or any other org, and publish nothing.
- Read `AGENTS.md` and run `quest context` first. No em dashes. End GitHub
  posts with `(Written by <model>)`. PR bodies need `## Validation`,
  `## Models` and `## Waiting`.
- Work in your own git worktree and CARGO_TARGET_DIR under `~/.cache`, never
  the shared clone and never `/tmp`.
- Benchmarks: interleaved A/B, one pinned core, a separate target dir per
  variant, at least 5 rounds, medians with spread, and an aws-lc-rs control
  that stays within 1.02. Set the governor to `performance` for runs and put
  it back afterwards. Watch temperature: the Pi 4 throttles without a heatsink.
- Never reintroduce x86 VSHA512 use. New secret paths need ctgrind; if
  ctgrind cannot run on the board, say so and use `admin/ct-vartime`.
- Report losses as plainly as wins. Only keep changes that win reproducibly.

## Round 1 jobs

1. **Baseline table.** Build rind-bench or a small harness (the workspace
   bench may fail on openssl-sys on the board; the Pi 2B worker used a
   standalone A/B crate) and time rind against aws-lc-rs and ring at 64 B,
   1200 B and 16 KB for SHA-256, SHA-512, HMAC-SHA256, AES-128/256-GCM,
   ChaCha20-Poly1305, and at the usual sizes for X25519, Ed25519 sign and
   verify, P-256 ECDH and ECDSA, ML-KEM-768, and Argon2id. Put the table in
   `BENCHMARKS.md` or the platform notes via `admin/bench-report` if that tool
   accepts a new host, otherwise in the PR body.
2. **Largest gap.** Pick the largest reproducible gap above 1.05x that no open
   PR owns (check `gh pr list --repo steelhead99x/rind` and kixel-ai/rind) and
   fix it in pure Rust or the tree's existing asm style. Open a separate draft
   fork PR per fix.
3. **Fallback selection.** Check that rind picks the right kernel on a core
   without the crypto extension: AES-GCM thresholds, GHASH, whether
   ChaCha20-Poly1305 beats AES-GCM here (the rustls/dimpl preference depends on
   it), and Argon2's NEON versus scalar fill.
4. **Narrow versus wide multiplier schedules.** Fork PR #82 selects
   s2n-bignum's narrow-multiplier schedules on narrow cores. Check which
   schedule the A72 should use and whether the CPU-family check picks it.
5. **Native test lane.** Run the aarch64 tests natively (`cargo test -p rind
   --release`, plus rind-aws-lc-rs and rind-rustls if they build) and the
   no-crypto selection tests. Record pass counts and wall time; the Pi 5 and
   Jetson took about 39 minutes cold, so say whether the Pi 4 is viable.
6. **ctgrind.** If Valgrind and libclang can be installed on the board (ask
   the owner for sudo), run `admin/ctgrind` on the aarch64 secret paths
   (ChaCha20, Poly1305, AES fallback, GHASH). Otherwise list exactly what
   blocks it.

Do not start `m5/verified/aarch64-no-crypto` itself in round 1: it is an L
proof quest, and the claim needs the owner's go-ahead.

## Report back

Board and kernel versions, the CPU part and feature flags, the baseline
table, each PR link with its numbers, test pass counts, what could not run,
and any decision the owner must make.
