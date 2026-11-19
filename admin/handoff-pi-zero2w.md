# Handoff: Raspberry Pi Zero 2 W (Cortex-A53) benchmarks and tracking

Status: first round not started. The board has been described as connected to
the owner's network, but it was not found on 2026-11-19 (see "Access"). Fill in
the host details before starting, then keep the tracking table below current.

## Why this board

The Zero 2 W is a quad Cortex-A53 (BCM2710A1, up to 1 GHz), the smallest board
the owner has. It differs from every host measured so far:

- **No crypto extension.** [PLATFORMS.md](/PLATFORMS.md) lists the Zero 2 W with
  the Pi 4 and CM4: AES, GHASH, SHA-1 and SHA-256 run on aws-lc's NEON and
  scalar assembly, `rind::cpu::has_aes_hardware()` is false, and rind-rustls and
  rind-dimpl prefer ChaCha20-Poly1305.
- **In-order, dual-issue core.** The A53 is the narrow core that fork PR #82
  (`perf(aarch64): run s2n-bignum's narrow-multiplier schedules on narrow
  cores`) targets. The Pi 4's A72 and the Pi 5's A76 are out of order, so only
  this board and a Pi 3 exercise the narrow schedules on real silicon.
- **A multiplier that may not be constant-time.** PLATFORMS.md records that the
  A53's 64-bit multiply takes a cycle longer when both operands exceed 32 bits
  ([Gu and Shacham] 2.1, measured on a Pi 3), that Arm's manual documents no
  such variation, and that "the same likely holds for `umull` and `smull` on
  32-bit `arm` built for an A53, which no one has measured". This board can
  measure it.
- **512 MB of RAM and no fan.** Argon2 at its larger settings, big builds and
  long runs are limited, and the board throttles. Cross-build everything.
- **Both ISAs.** An A53 runs aarch64 and 32-bit armv7. Which one the board's OS
  runs decides the first target; a 64-bit kernel can usually run both. Record
  which you measured.

## Access

Fill in before starting:

- Host / address (it was not on 192.168.90.0/24 by Raspberry Pi MAC prefix, SSH
  scan or mDNS on 2026-11-19; `192.168.90.86` has a Raspberry Pi MAC but only
  ports 80 and 443 open, so it is something else; check the USB gadget
  interface and the serial console too):
- User and key:
- OS, bitness (`uname -m`, `getconf LONG_BIT`), kernel:
- CPU part (expect `0xd03`), `Features` line (expect no `aes`, `pmull`,
  `sha1`, `sha2`):
- RAM, swap, free disk, power supply:
- Toolchain on the board (`cargo --version`; unlikely) or cross-build only:
- `sudo` without a password? (needed for the CPU governor):

Confirm the CPU first and put the output in the first PR comment:

    uname -m; getconf LONG_BIT; grep -m1 'CPU part' /proc/cpuinfo
    grep -m1 Features /proc/cpuinfo; free -m; cat /sys/class/thermal/thermal_zone0/temp

## Rules for every job

- Fork only. Always `gh --repo steelhead99x/rind`, never bare `gh`. Post nothing
  to kixel-ai or any other org, and publish nothing.
- Read `AGENTS.md` and run `quest context` first. No em dashes. End GitHub
  posts with `(Written by <model>)`. PR bodies need `## Validation`,
  `## Models` and `## Waiting`.
- Work in your own git worktree and `CARGO_TARGET_DIR` under `~/.cache`, never
  the shared clone and never `/tmp`.
- Benchmarks: interleaved A/B, one pinned core, a separate target dir per
  variant, at least 5 rounds, medians with spread, and an aws-lc-rs or ring
  control that stays within 1.02. Record temperature and `vcgencmd
  get_throttled` before and after every round and discard throttled rounds.
  Set the governor to `performance` for runs and put it back afterwards.
- Never reintroduce x86 VSHA512 use. New secret paths need ctgrind; if ctgrind
  cannot run on the board, say so and use `admin/ct-vartime` and `admin/ct-qemu`.
- Report losses as plainly as wins. Only keep changes that win reproducibly.
- Raw logs go to the owner's `steelhead99x/rind-results` repo as a separate PR
  in the style of its #76 to #78, with paths, email addresses, hostnames, wifi
  names and tokens scrubbed. Do not merge it.

## Round 1 jobs

1. **Baseline table, every library.** Time rind against every library the tree
   benchmarks (aws-lc-rs, ring, RustCrypto crates, libcrux, dalek, and the
   others `rind-bench` lists) at 64 B, 1200 B and 16 KB for SHA-256, SHA-512,
   HMAC-SHA256, AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305; at the usual sizes
   for X25519, Ed25519 sign and verify, P-256 ECDH and ECDSA, ML-KEM-768 and
   Argon2id with a memory size the board can hold (state the size). `rind-bench`
   may fail to build for the board (openssl-sys); the Pi 2B and Jetson workers
   used a small standalone A/B crate: reuse it. Do it for the aarch64 build
   and, if the OS allows, the armv7 build.
2. **Narrow-schedule check for #82.** On the A53, compare s2n-bignum's narrow
   and wide multiplier schedules for Ed25519, X25519 and P-256 (forcing flags in
   `rind/src/low/aarch64/cpu.rs`: `cpu_forced`), and check that the CPU-part
   table classifies `0xd03` as narrow.
3. **Multiplier timing.** Measure whether the A53's multiply time depends on its
   operands, in the style of [Gu and Shacham] 2.1: 64-bit `mul` and `umulh` on
   aarch64, and `umull`, `smull` and `mla` on 32-bit arm, with operands whose
   high halves are all zero, all ones and random, over millions of iterations
   with the cycle counter (`PMCCNTR`, enabled through a tiny kernel module or
   `perf` if the board allows; else the 1 GHz counter on a pinned core with
   many repetitions). Report the cycle counts. This decides whether PLATFORMS.md
   should list 32-bit `arm` on an A53, and whether `admin/ct-vartime`'s
   no-exception rule is enough for it.
4. **Largest unowned gap.** Pick the largest reproducible gap above 1.05x that
   no open PR owns (`gh pr list --repo steelhead99x/rind`; #82, #128, #163,
   #187, #193 and #172 own areas) and fix it on a fork-only branch, one PR per
   fix. If none, open a docs PR with the table.
5. **Fallback selection.** Check AES-GCM, GHASH and SHA-2 fallback thresholds,
   whether ChaCha20-Poly1305 beats AES-GCM here, and Argon2's NEON fill against
   the portable one.
6. **Constant time.** `admin/ct-vartime` for the targets built; `admin/ct-qemu`
   with an A53 model (`-cpu cortex-a53`, `--deny aes,pmull,sha2` as the #187
   branch adds); ctgrind only if valgrind and libclang can be had.

Do not start `m5/verified/aarch64-no-crypto` itself: it is an L proof quest and
the claim needs the owner's go-ahead.

## Tracking table

Update this table in the tracking PR as results land (one row per job; link the
comment or the rind-results PR).

| Job | Status | Head tested | Result | Link |
| --- | --- | --- | --- | --- |
| 1 Baseline, aarch64 | not started | | | |
| 1 Baseline, armv7 | not started | | | |
| 2 Narrow schedules (#82) | not started | | | |
| 3 Multiplier timing | not started | | | |
| 4 Largest gap | not started | | | |
| 5 Fallback selection | not started | | | |
| 6 Constant time | not started | | | |

## Report back

Board, OS and kernel versions, the CPU part and feature flags, the baseline
table, each PR link with its numbers, throttling observed, what could not run,
and any decision the owner must make.

[Gu and Shacham]: https://arxiv.org/abs/2311.14246
