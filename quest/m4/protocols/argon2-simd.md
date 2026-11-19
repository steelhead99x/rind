# [S] Argon2id fills memory with the fastest kernel on aarch64 and AVX-512

## Goal

Argon2id's compression function runs the fastest kernel measured on aarch64, on x86_64 CPUs with AVX-512, and on x86_64 CPUs without AVX2, so a defender affords more memory per second than an attacker's GPU gains. Today aarch64 and x86_64 without AVX2 run rind's portable Rust, and x86_64 with AVX2 a port of the reference implementation's AVX2 rounds, which measured 18% faster than RustCrypto's `argon2` and 1.7x faster than OpenSSL's on an Intel Core Ultra 7 270K Plus (`rind-bench`'s `argon2`, RFC 9106's 64 MiB recommendation).

## Plan

- aarch64: write a NEON kernel on the reference's 128-bit (`blamka-round-opt.h` SSE) layout and keep it only if it beats the portable Rust, which LLVM may already vectorize, on an Apple core and a Neoverse core.
- AVX-512: measure libsodium's `argon2-fill-block-avx512f.c` (ISC) layout against the AVX2 port on Zen 4 or 5 and on Sapphire Rapids, keeping it only where it wins on both. `admin/ctgrind` cannot decode AVX-512, so its constant-time test runs under `admin/ct-sde`.
- x86_64 without AVX2: measure the reference's SSSE3 rounds against the portable Rust.
- No host the implementing agent could reach had AVX-512 or aarch64 when [moq-dev/rind#634](https://github.com/moq-dev/rind/pull/634) landed Argon2id; the Mac mini and the bench workflow's arm64 and AVX-512 runners can measure them.

### Status

aarch64 runs the NEON fill (`low::aarch64::argon2_neon`), ported from `perf/argon2-neon-scalar-rider` (`3025440d`): SHA3's `xar` / `umlal` fill on an Apple core that has SHA3, and plain NEON with the scalar rider on every other core. Plain NEON beats this tree's portable permutation on the Apple M1 Pro, Neoverse-N2 and Cortex-A76; on the Orin's Cortex-A78AE a controlled 64MiB-t3-p4 re-timing gives 0.983x to 0.989x, so no gain and about 1% to 2% slower; the SHA3 fill loses to it on the Neoverse-N2 (0.90x and 0.96x), so only Apple takes it. Tests compare both fills to the portable permutation (`low::aarch64::argon2_neon::neon_matches_scalar`), and `low::aarch64::argon2::tests::dispatch_matches_portable` checks the fill dispatch selects.

x86_64 runs the landed AVX2 fill, then the reference's SSSE3 fill on a CPU with SSSE3 and without AVX2, then the portable permutation. SSSE3 measured 1.12x to 1.22x the portable permutation with AVX2 denied (Xeon 6975P-C and Core Ultra 9 275HX). The reference's AVX-512F fill sits beside them, tested against the portable permutation, and runs only with `--cfg rind_argon2_avx512`: it is the one part still gated.

Published numbers from earlier work are in the owner's results repository, branches `results/argon2-a76-interleave` (`results/argon2-interleave/`) and the scalar-rider notes in that same branch (`results/argon2-scalar-rider/`). They compare fills to each other and to RustCrypto, at 1 MiB t=3, 16 MiB t=1, and 64 MiB t=1, which is not this bench.

### Still open against the keep rules

- AVX-512 stays only where it wins on Zen 4 or 5 and on Sapphire Rapids. Neither is measured. A 5th-gen Xeon is Emerald Rapids, and the Xeon 6975P-C GitHub runner (below) is Granite Rapids, so neither number closes the rule. Comparing the reference layout with libsodium's `argon2-fill-block-avx512f.c`, which the plan names, is also open.
- AVX-512 constant time is `admin/ct-sde argon2` (Sapphire Rapids model, test `ct_sde_argon2_avx512`), from `nix develop .#sde`. Not run on this branch.
- The NEON constant-time test: `crabgrind` needs libclang, which neither aarch64 board has, and the repo's `admin/ctgrind` needs the Nix shell, so valgrind was not run on aarch64 here. The fill is straight-line NEON arithmetic with no secret-dependent branch or index; the only data-dependent addressing is Argon2id's own, which AGENTS.md exempts.

### Measured

2026-11-19, on the owner's boards and laptop. `cargo bench -p rind-bench --bench argon2` with criterion's `--warm-up-time 1 --measurement-time 5`, each variant built once in its own target directory and run five times interleaved with the order rotated, pinned to one core (`taskset`), medians in ms; spread is (max - min) / median. Ratio is the portable `rind` time over this row's. Tree: this branch at `52e0ed73` for the portable rows; the NEON rows build the same tree with `--cfg rind_argon2_neon`, which this branch's change makes the default. rustc 1.98.1. The scratch build dropped the OpenSSL bench row, which is feature-gated off anyway.

Raspberry Pi 5 (Cortex-A76, governor `performance`, no `sha3`, so the plain NEON fill), and Jetson Orin Nano (Cortex-A78AE, governor `schedutil`, no `sha3`, so the plain NEON fill). RustCrypto's row comes from the same runs and does not use rind's fill.

| board | benchmark | portable | spread | NEON | spread | vs portable | RustCrypto |
|---|---|---|---|---|---|---|---|
| Pi 5 | 16MiB-t1-p1 | 27.57 | 0.2% | 19.83 | 0.6% | 1.391x | 26.40 |
| Pi 5 | 64MiB-t3-p4 | 340.92 | 0.2% | 243.49 | 0.6% | 1.400x | 335.20 |
| Orin | 16MiB-t1-p1 | 17.13 | 3.0% | 16.19 | 0.2% | 1.058x | 16.67 |
| Orin | 64MiB-t3-p4 | 270.85 | 1.7% | 263.95 | 1.9% | 1.026x | 280.49 |

Plain NEON beats the portable permutation on the Apple M1 Pro, Neoverse-N2 and Cortex-A76 (Pi 5 1.39x to 1.40x, Neoverse-N2 1.06x to 1.07x). On the Orin's Cortex-A78AE the rows above are an earlier run with 2% to 3% spreads, and the controlled 64MiB-t3-p4 re-timing is 0.983x to 0.989x: no gain, about 1% to 2% slower than portable. Whether plain NEON stays the default on the A78AE is the owner's decision; the dispatch is unchanged.

Intel Core Ultra 9 275HX (Arrow Lake-HX, a laptop, load average 3.4 to 5.7 from other work, pinned to a P-core), AVX2 denied with `--cfg rind_cpu_disable` and `RIND_CPU_DISABLE_avx2=1`; the SSSE3 build adds `--cfg rind_argon2_ssse3`, which this change also makes the default. Five rounds:

| benchmark | portable | spread | SSSE3 | spread | vs portable |
|---|---|---|---|---|---|
| 16MiB-t1-p1 | 5.652 | 1.5% | 4.646 | 10.8% | 1.217x |
| 64MiB-t3-p4 | 85.541 | 6.4% | 70.575 | 9.6% | 1.212x |

An earlier three-round run at load 5.7 gave 1.25x and 1.22x with spreads of 17% to 27%. RustCrypto is faster than both here (3.7 ms and 61 ms) because it is not subject to the AVX2 denial: the denial turns off rind's dispatch, not RustCrypto's compile-time vectorization.

2026-11-17, `cargo bench -p rind-bench --bench argon2` with criterion's defaults, each configuration built once and run three times, interleaved with the order rotated each round. The GitHub runners pin to one CPU. Each value is the median of the three runs' criterion medians, in ms; spread is (max - min) / median. Ratio is the portable `rind` time over this row's. Tree: this branch at `e3e4d0cd` plus a measuring workflow only (a fork PR branch), rustc 1.100.0.

Neoverse-N2 GitHub runner (`ubuntu-24.04-arm`, 4 CPUs, has `sha3`). `default` is the portable permutation, `neon` takes the SHA3 fill, and `neon-plain` is plain NEON with the scalar rider (`RIND_CPU_DISABLE_sha3=1`). `neon_matches_scalar` passes with and without the gate.

| rind fill | 16MiB-t1-p1 | spread | vs portable | 64MiB-t3-p4 | spread | vs portable |
|---|---|---|---|---|---|---|
| portable (`default`) | 7.16 | 2.3% | 1.000x | 129.60 | 1.5% | 1.000x |
| SHA3 (`rind_argon2_neon`) | 7.98 | 2.1% | 0.897x | 135.04 | 3.6% | 0.960x |
| plain NEON + rider | 6.72 | 2.4% | 1.066x | 122.84 | 1.7% | 1.055x |
| RustCrypto (in the `default` runs) | 7.12 | 6.2% | 1.005x | 136.10 | 2.4% | 0.952x |

Apple M1 Pro (macOS 14, has `sha3`), rustc 1.98.1, not pinned (macOS has no `taskset`), each round under the machine's bench lock while no other build or bench ran. Load rose during rounds 2 and 3 from work outside the lock, hence the wider 64 MiB spread. Every NEON run still beats every portable run. `neon_matches_scalar` passes with and without the gate.

| rind fill | 16MiB-t1-p1 | spread | vs portable | 64MiB-t3-p4 | spread | vs portable |
|---|---|---|---|---|---|---|
| portable (`default`) | 6.20 | 5.9% | 1.000x | 99.76 | 15.6% | 1.000x |
| SHA3 (`rind_argon2_neon`) | 3.52 | 2.9% | 1.760x | 60.58 | 17.8% | 1.647x |
| plain NEON + rider | 4.00 | 10.3% | 1.547x | 76.46 | 25.1% | 1.305x |
| RustCrypto (in the `default` runs) | 6.08 | 7.1% | 1.020x | 96.29 | 18.4% | 1.036x |

Intel Xeon 6975P-C GitHub runner (`ubuntu-24.04`, Granite Rapids, 4 vCPUs, has `avx512f`). `portable` and `ssse3` deny AVX2 with `RIND_CPU_DISABLE_avx2=1`. `matches_portable` passes for the AVX2, AVX-512, and SSSE3 fills, and `configured_dispatch_matches_portable` passes under `rind_argon2_avx512`.

| rind fill | 16MiB-t1-p1 | spread | vs portable | 64MiB-t3-p4 | spread | vs portable |
|---|---|---|---|---|---|---|
| portable | 7.85 | 0.4% | 1.000x | 106.89 | 0.6% | 1.000x |
| SSSE3 (`rind_argon2_ssse3`) | 7.01 | 0.5% | 1.120x | 94.31 | 3.3% | 1.133x |
| AVX2 (`default`) | 4.57 | 0.5% | 1.718x | 66.15 | 0.2% | 1.616x |
| AVX-512 (`rind_argon2_avx512`) | 3.53 | 0.5% | 2.224x | 54.13 | 4.2% | 1.975x |
| RustCrypto (in the `default` runs) | 6.04 | 0.0% | 1.300x | 94.19 | 0.4% | 1.135x |

On that Xeon, AVX-512 is 1.29x the AVX2 fill at 16 MiB and 1.22x at 64 MiB. Granite Rapids is neither of the plan's two CPUs, so AVX-512 stays gated.

### Bench

Record `lscpu` first. Each distinct `RUSTFLAGS` rebuilds. Compare the `rind` lines of `argon2id-16MiB-t1-p1` and `argon2id-64MiB-t3-p4`.

What dispatch runs today: the NEON fill on aarch64 (SHA3 on Apple, plain NEON elsewhere), AVX2 on an AVX2 CPU, SSSE3 on a CPU with SSSE3 and no AVX2:

```shell
cargo bench -p rind-bench --bench argon2 -- --noplot
```

Plain NEON on a CPU that has SHA3, to compare it with the SHA3 fill:

```shell
RUSTFLAGS='--cfg rind_cpu_disable' RIND_CPU_DISABLE_sha3=1 \
  cargo bench -p rind-bench --bench argon2 -- --noplot
```

The portable permutation, for a baseline: on x86_64, deny the vector tiers; on aarch64 build the commit before this change (`52e0ed73`), which ran it by default:

```shell
RUSTFLAGS='--cfg rind_cpu_disable' RIND_CPU_DISABLE_avx2=1 RIND_CPU_DISABLE_ssse3=1 \
  cargo bench -p rind-bench --bench argon2 -- --noplot
```

AVX-512 against the AVX2 fill, on a CPU that has both:

```shell
RUSTFLAGS='--cfg rind_argon2_avx512' cargo bench -p rind-bench --bench argon2 -- --noplot
```

The Pi 5, Jetson, and Pixel 9 Pro run the first command, which picks plain NEON on them. The M1 Pro runs the first two. The 5th-gen Xeon and a Zen 4 or 5 and a Sapphire Rapids host run the first and the AVX-512 command, which is still open. GitHub's `ubuntu-24.04-arm` runner is the Neoverse host. `ubuntu-24.04` runs the x86 commands; record `flags`, because the runner may not have AVX-512.
