# SHA-512 at 16 KiB on an Android phone

A devbench quick run on a Samsung Galaxy A16 5G flagged rind's SHA-512 at
16 KiB as its one row behind ring. Paired, order-rotated runs show no gap
outside run-to-run noise: rind sits between aws-lc-rs and ring, all three
within 0.3%. A candidate that skips copying the final block on aligned
updates was 0.17% slower, so rind's SHA-512 is unchanged. Like
[pi4.md](pi4.md), this note records indicative numbers outside
`BENCHMARKS.md`, which times only `admin/bench-report`'s hosts.

The phone: SM-A166U1, Exynos 1330 (`s5e8535`, two Cortex-A78 at 2.4 GHz and
six Cortex-A55 at 2.0 GHz), Android 16 (SDK 36). Its CPU reports `aes`,
`pmull`, `sha1` and `sha2` but not `sha512`, so all three libraries run
scalar SHA-512 compression. Versions: rind 0.3.2, ring 0.17.14, aws-lc-rs
1.19.0 (aws-lc-sys 0.47.0).

## The quick runs

Two v15 quick runs ranked the pair in opposite orders: rind 33,399.27 ns
against ring's 33,397.40 ns, then 33,317.87 ns against 33,350.96 ns. The app
ranks by raw median, so a 0.006% difference shows as a loss. Three more runs
of just this pair, three rounds each, kept swapping the leader, with every
median difference under 0.2%:

| Run | rind | ring |
|---|---:|---:|
| 1 | 33,365.87 ns | 33,342.56 ns |
| 2 | 33,339.05 ns | 33,399.85 ns |
| 3 | 33,364.49 ns | 33,376.01 ns |

Those runs registered the libraries in the same order every round.

## Rotated order

A measurement-only APK built from the devbench app timed only the three
16 KiB rows. Each round took ten 100 ms samples per row after a 300 ms
warm-up, over six rounds, and rotated the libraries so each ran first,
second and third twice. All 18 rows completed without errors. Each cell is
the median of the six round medians:

| Library | Median | Per-round range |
|---|---:|---:|
| aws-lc-rs | 33.306 µs | 33.260–33.348 µs |
| rind | 33.348 µs | 33.343–33.405 µs |
| ring | 33.400 µs | 33.359–33.405 µs |

rind ran ahead of ring in five of the six rounds and by 0.16% on the
medians, and behind aws-lc-rs by 0.13%, with overlapping ranges.

## The candidate

The 16 KiB row hashes through the streaming context, `mid::sha2::Sha512Context`.
Its `update` hands whole blocks to compression through `Blockwise`, which
keeps the final whole block buffered, copied, so that `finish` can compress
it beside the padding. The candidate passed every block of an update
straight to `Sha512State::update_blocks` when nothing was buffered and the
update held two or more whole blocks. Its total compression work is the same,
less one 128-byte copy and one block moved from `finish` to `update`. All 23
of rind's SHA-512 unit tests passed with it, including a new one that checks
each prefix after mixed aligned and unaligned updates against the one-shot
path.

The A/B built two APKs with separate app IDs from one devbench app, which
differed only by the candidate, and ran them in the order baseline,
candidate, candidate, baseline. Each run was the six-round rotation above.
All 72 rows completed without errors. Each cell is a run's median, in µs:

| Run | rind | aws-lc-rs | ring |
|---|---:|---:|---:|
| baseline 1 | 33.362 | 33.362 | 33.399 |
| candidate 1 | 33.422 | 33.381 | 33.379 |
| candidate 2 | 33.420 | 33.376 | 33.386 |
| baseline 2 | 33.372 | 33.360 | 33.395 |

Pooled over twelve rounds each, rind took 33.367 µs at baseline and 33.422 µs
with the candidate, 0.17% slower. Every candidate round (33.400–33.473 µs)
was slower than every baseline round (33.329–33.388 µs), while aws-lc-rs and
ring, untouched, moved by under 0.1% between the variants. The candidate
also stepped outside `proofs/Rind/X86_64/Sha512.lean`'s `context_update_spec`,
which unfolds `update` straight into the `Blockwise` lemma, so adopting it
would have needed a regenerated translation and a proof of the new branch.
It was rejected, and the 64 B and 1350 B controls a change would need before
adoption were not timed.

These runs used the devbench app's branch at `d749a3c1`, whose rind differs
from main's. The candidate was applied to main as of `73b16de8` for the host
tests.

## What follows

Nothing in rind's SHA-512. The quick run's "behind ring" was the app ranking
sub-noise differences as strict wins and losses. Treating differences
inside repeated controls' spread as ties is a change to the app's scoring,
which should keep the raw timings.
