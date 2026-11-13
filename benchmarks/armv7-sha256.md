# armv7 SHA-256 and SHA-1 source comparison

Without the crypto extension, armv7 runs aws-lc's SHA-256 and SHA-1
assembly: `sha256_block_data_order_neon` and `sha1_block_data_order_neon`
where the CPU has NEON, and their `_nohw` integer twins otherwise. Every
assembly row beat the Rust it replaced, Graviola's SHA-256 and rind's SHA-1.

## Assembly against Rust

Measured on 2026-11-11 on GitHub's `ubuntu-24.04-arm` Neoverse-N2 runner,
running `armv7-unknown-linux-gnueabihf` binaries natively with `setarch
linux32`, the crypto extension denied to rind with `RIND_CPU_DISABLE_sha2=1`,
and NEON with `RIND_CPU_DISABLE_neon=1` for the integer rows. The order was
Rust, NEON, integer, integer, NEON, Rust, on one runner. Each cell is the mean
of a variant's two Criterion central estimates, which agreed within 0.1%.

| Message | Rust | aws-lc NEON | aws-lc integer |
|---|---:|---:|---:|
| SHA-256, 64 B | 690.4 ns | 342.2 ns (2.02×) | 369.4 ns (1.87×) |
| SHA-256, 1350 B | 7.050 µs | 3.150 µs (2.24×) | 3.510 µs (2.01×) |
| SHA-1, 64 B | 322.1 ns | 215.1 ns (1.50×) | 268.0 ns (1.20×) |
| SHA-1, 1350 B | 2.971 µs | 1.772 µs (1.68×) | 2.406 µs (1.23×) |

aws-lc-rs ran its SHA instructions alongside, steady within 0.6% across the
run: 159–160 ns at 64 B for both hashes, 659 ns for SHA-1 and 756 ns for
SHA-256 at 1350 B.

This core is an ARMv9 one in 32-bit mode, not an ARMv7 core, and NEON's lead
over integer code varies by core: aws-lc's perlasm header gives its NEON
SHA-256 23% over its integer code on a Cortex-A8 and 50% on a Snapdragon S4.
Both assembly routines beat the Rust here by more than any of those spreads,
so the pick should hold on ARMv7 cores, though their ratios will differ.

The [run](https://github.com/kixel-ai/rind/actions/runs/43103564386) holds the
logs and the workflow, which builds the Rust variant by patching the dispatch
back to `low::generic`.

## Graviola against HACL*

Before the assembly, the 2026-11-08 run below picked Graviola's SHA-256 over
HACL*'s verified one on the same runner, with the same method. Graviola's
latency was 28.5% lower at 64 B and 30.2% lower at 1350 B. HACL*'s therefore
also loses to the assembly, by 2.8× and more.

| Message | Graviola, first | HACL*, first | HACL*, second | Graviola, second |
|---|---:|---:|---:|---:|
| 64 B | 689.01 ns | 964.21 ns | 964.33 ns | 689.23 ns |
| 1350 B | 7.0130 µs | 10.048 µs | 10.047 µs | 7.0205 µs |

The HACL* variant replaced the Rust fallback with
`libcrux_sha2::hacl::sha256_update_nblocks` from libcrux-sha2 0.0.9. The
[run](https://github.com/kixel-ai/rind/actions/runs/42496769936) and its
[workflow](https://github.com/kixel-ai/rind/blob/c2a9a1edb43d454d9a275fbb8d98a6274c23d91c/.github/workflows/bench.yml)
record the build and invocation.
