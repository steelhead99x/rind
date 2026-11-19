# P-256 on armv7: plan to import OpenSSL's `ecp_nistz256-armv4` field multiplication

Fork only: delete this directory before any upstream branch merges from this one.

Stage 1 of the "P-256 on armv7 (L)" follow-up from the Fire TV handoff
(`admin/handoff-firetv-armv7/README.md` on fork PR #217's branch `claude/firetv-armv7-handoff`, area 4):
measure, find the source, and plan. This branch changes no code and imports no assembly. Stage 2, the
import, is fork PR #222; its measured gain on the Pi 2 B is 8 to 13% (not the 15 to 18% estimated here),
and the table below is the stage 1 estimate.

Recommendation: **go**, narrowly. Import only the integer Montgomery multiplication and squaring
(`ecp_nistz256_mul_mont`, `ecp_nistz256_sqr_mont`, about 1.6 KB of code), behind the existing
`fe_mul` and `fe_sqr`. Do not import the point routines or the 150 KB generator table. Expected
gain on a Cortex-A7: 15 to 18% off ECDH, key generation and verification, about 10% off signing.

## Where the gap comes from, in one table

Measured on a Raspberry Pi 2 B Rev 1.1 (Cortex-A7, `CPU part 0xc07`, 900 MHz, 32-bit userland).
Time per call, microseconds, medians of 5 interleaved rounds (see [Method](#method)); the ratio is
rind's time over the other library's, so above 1.00 is slower.

| Operation | rind | OpenSSL 3.6.3 (vendored, `linux-armv4` asm) | aws-lc-rs 1.19 | ring 0.17 | rind / OpenSSL | rind / aws-lc-rs | rind / ring |
|---|---|---|---|---|---|---|---|
| ECDH keygen (key and public key) | 688.3 | 477.3 | 2070.2 | 2130.9 | **1.44** | 0.33 | 0.32 |
| ECDH, keygen plus agree (as `rind-bench`) | 3779.1 | 3378.7 | 8593.0 | 7783.1 | **1.12** | 0.44 | 0.49 |
| ECDSA keygen | 718.2 | 484.4 | 2075.3 | 2141.6 | **1.48** | 0.35 | 0.34 |
| ECDSA sign | 1105.5 | 1021.5 | 2476.4 | 2457.0 | **1.08** | 0.45 | 0.45 |
| ECDSA verify | 3813.1 | 3089.5 | 6095.7 | 7238.4 | **1.23** | 0.63 | 0.53 |

- rind is already 1.6 to 3 times faster than aws-lc-rs and ring on this core. Neither has P-256
  assembly for 32-bit ARM (see [Source](#source)), so both run generic C. The only library ahead
  of rind is OpenSSL, and only OpenSSL is the target of this plan.
- Spread (max minus min over the rounds, over the median) is under 7% for every row but OpenSSL's,
  which is 7 to 25% in a few rows because of its occasional slow rounds; its minimum is the better
  reading of its speed there (keygen 472.5, ECDH 3315.2, sign 1017.6, verify 3070.2).
- Control: rind against itself, the same binary under another name, interleaved the same way, 7
  rounds: keygen 0.999, ECDH 1.001, ECDSA keygen 1.001, sign 0.995, verify 0.998 (all within 1.02;
  `data/ab-run-control.log`). rind's own rows agree across the two runs within 1%.
- Temperature 40 to 45 C, `throttled=0x0` and 900 MHz in every round, in both runs
  (`data/ab-run-*.log`). Governor `performance` for the runs, restored to `ondemand` after.
- The OpenSSL column of the ECDH row pays for an `EC_KEY` public-key check (a full scalar
  multiplication) that rind's agreement does not, so 1.12 understates the gap. `openssl speed` on
  the Pi (Debian OpenSSL 3.5.9, derive alone) gives 1.79 ms per ECDH derive, against rind's about
  3.08 ms (rind's keygen plus agree, minus its keygen), which is 1.72. Key generation is the
  cleanest like-for-like row: one fixed-base multiplication and an inversion, 1.44.
- The Fire TV Stick's A53 gap (1.10, 1.17, 1.19 for ECDH, sign, verify) is smaller than the A7's.

## Why: the field multiplication is the gap

rind's armv7 P-256 runs the aarch64 algorithms in portable Rust over 32-bit limbs
(`low/generic/p256.rs`), with Montgomery multiplication and squaring in `p256_mul32.rs` (an
`umaal` schedule, 560 instructions, `quest/m5/verified-armv7/nist-curves.md`). OpenSSL's
`ecp_nistz256-armv4` runs the same Montgomery form (R = 2^256) with a reduction written for
p = 2^256 - 2^224 + 2^192 + 2^96 - 1 (word additions and subtractions, no multiplications).

Microbenchmark on the Pi (`mb/`): rind's `fe_mul` and `fe_sqr`, copied from `main`, against the
`ecp_nistz256_mul_mont` and `_sqr_mont` that OpenSSL's perlasm generates (cpp-processed, in
`global_asm!`), dependent chains pinned to core 3, three runs, each within 1% of the others:

| Routine | rind (Rust) | OpenSSL asm | asm over rind |
|---|---|---|---|
| mul | 701 to 708 ns (631 cycles) | 500 to 506 ns (450 cycles) | **0.71** |
| square | 594 to 600 ns (535 cycles) | 500 to 514 ns (450 cycles) | **0.84** |
| add (call, asm) vs fiat add | 146 ns (fiat) | 110 ns (asm, call included) | 0.76 |
| sub | 104 ns (fiat) | 102 ns | 0.98 |

The two multiplications agree on 20,000 random inputs below p, in every run (0 mismatches), so the
asm is a drop-in for `fe_mul` and `fe_sqr`: same Montgomery form, same word order, fully reduced
output for reduced input.

Counting the field operations in rind's formulas (`jdouble` 3M + 5S, `jadd` 12M + 4S, `jmixadd`
8M + 3S; Booth-5 variable-base: 263 doublings, 58 additions, one inversion of 255S + 12M; fixed-base:
43 mixed additions and an inversion):

| Operation | multiplications | squarings | time saved at 701/594 to 500 ns | of the rind row |
|---|---|---|---|---|
| variable-base multiplication (ECDH agree, verify's P part) | about 1500 | about 1800 | about 475 us | 15% of 3.08 ms |
| fixed-base multiplication (keygen, sign, verify's G part) | about 360 | about 385 | about 110 us | 16% of 0.69 ms |

So the estimate for the whole operation, with nothing else changed: keygen 688 to about 577 us
(-16%), ECDH 3779 to about 3190 (-16%), verify 3813 to about 3225 (-15%), sign 1105 to about 995
(-10%, the scalar-field work mod n stays in Rust), which would put rind at about 1.21 (keygen),
0.94 (ECDH), 0.97 (sign) and 1.04 (verify) of OpenSSL in the harness above. Adding the asm
`add`/`sub` is worth another 1 to 3%, but it is a call per operation where fiat's is inline, so it is
measured only after the multiplication lands (see [Plan](#stage-2-plan)). These are estimates from
operation counts times chain latency; the Cortex-A7 is in order, so there is little overlap to hide
in, but the number to hold the import to is the end-to-end one below.

What this does not close: OpenSSL's remaining lead on keygen (about 1.2 after the swap) and on
ECDH agree is the point routines in assembly, its 37-window fixed-base table (`w7`, 150 KB, against
rind's 43 windows) and the constant-time table lookups. Those are a much larger import for a
smaller return and are not proposed.

## Source

- **aws-lc does not have it.** The vendored `aws-lc-sys` (0.40 and 0.47 in this checkout's registry)
  builds `p256-nistz.c` only for `OPENSSL_X86_64` and `OPENSSL_AARCH64` (`#if !defined(OPENSSL_NO_ASM)
  && (defined(OPENSSL_X86_64) || defined(OPENSSL_AARCH64))`), and its generated 32-bit ARM sources
  (`generated-src/*-arm`) hold chacha, `armv4-mont`, `ghash-armv4`, SHA, and AES only. So
  `aws-lc-rs` on armv7 runs its generic C P-256, which is the 2 to 3 times slower row above.
  ring's 7.8 ms ECDH row shows it runs generic code there too.
- **OpenSSL has it:** `crypto/ec/asm/ecp_nistz256-armv4.pl`, 1856 lines of perlasm, by Andy
  Polyakov, "Copyright 2015-2025 The OpenSSL Project Authors", Apache-2.0 (also under the Cryptogams
  licence, which rind does not use). rind already imports OpenSSL's `keccak1600-armv4.pl` the same
  way, by `admin/import-openssl` at OpenSSL commit `2f4e3a5fec05394068cfa7379890ab552483a8a6`, under
  an existing "OpenSSL" section of `LICENSE`. No new licence class or upstream. (Stage 1 read the
  file from `openssl-src` 300.6.1 = OpenSSL 3.6.3; stage 2 must regenerate from the pinned commit and
  confirm the file is unchanged there.)
- What the file contains: field arithmetic (`to_mont`, `from_mont`, `mul_by_2`, `mul_by_3`,
  `div_by_2`, `add`, `sub`, `neg`, `sqr_mont`, `mul_mont`), table scatter and gather for w5 and w7,
  and the three point routines (`point_double`, `point_add`, `point_add_affine`) plus a 150 KB table
  of G's multiples. The generated `linux32` assembly is 4,429 lines, 820 KB with the table.
- **What to import:** `ecp_nistz256_mul_mont` and `ecp_nistz256_sqr_mont` (one shared body,
  `__ecp_nistz256_mul_mont`, 0x630 = 1,584 bytes of code, about 450 lines of generated assembly
  after cpp for ARM mode), and no data tables (the routine loads none). Second, optional:
  `add`, `sub`, `neg`, `mul_by_2`, `mul_by_3`, `div_by_2` (about 0.9 KB more). For size: rind's
  `fe_mul` is about 560 instructions (2.2 KB) today, so the code size is about neutral.
- The routines are integer ARM code (`umull`, `umlal`, `adds`, `adcs`, `sbcs`, `eor`, `orr`, `mov`,
  `ldr`, `str`, `ldm`, `stm`: no NEON, no predicated instruction, no branch but calls and the
  unconditional jump to the shared body), so the gate is the one the other
  32-bit ARM assembly uses: the `arm` backend builds them, and the portable 32-bit targets (wasm32,
  riscv32, thumbv7em) keep `p256_mul32.rs`.

## Method

Variants live in their own target directories (one variant here: `main` at `847a3e3c`, so one
directory; the harness takes a binary name per variant for stage 2), built on the laptop with
`nix develop .#armv7`, `cargo build --release --target armv7-unknown-linux-gnueabihf`, copied to the
Pi 2 B (`ssh $ARMV7_HOST`, Raspberry Pi OS 6.18 `armv7l`), run as `taskset -c 3 /lib/ld-linux-armhf.so.3
./ab-p256 <lib> <op>` with `performance` governor on all cores and nothing else running. `run.sh`
interleaves the libraries within each operation in each round, rotating the order between rounds;
each invocation warms up, sizes batches to 50 ms, takes 40 batches, and reports the median batch
mean per call; the table's value is the median of the rounds. `an.py` computes the table. Files:

- `ab-p256/`: the A/B binary (rind, aws-lc-rs, ring, vendored OpenSSL; `openssl` needs `perl` with
  `FindBin`, which the nix shell's host perl lacked, so build under `nix shell nixpkgs#perl`).
- `run.sh` (set `ARMV7_HOST` to the Pi's ssh host), `an.py`, `data/ab-run-control.log` (rind against itself, 7 rounds),
  `data/ab-run-openssl.log` (all four libraries, 5 rounds), `data/mul-microbench.txt`.
- `mb/`: the multiplication microbenchmark. It needs two generated files that are not committed
  (OpenSSL's assembly is the import this plan proposes, so it stays out of the tree until stage 2):
  `rind/src/low/generic/p256_mul32.rs` with its test module removed as `mb/src/p256_mul32.rs`, and
  `field.s`, made by running OpenSSL's `ecp_nistz256-armv4.pl linux32` (with `arm-xlate.pl` and
  `ecp_nistz256_table.c` beside it, under `nix shell nixpkgs#perl`), keeping the `.text` slice from
  `.LRR` to before `ecp_nistz256_scatter_w5`, through `cpp -P -x assembler-with-cpp` with
  `__ARM_ARCH__` defined as 7.

## What stage 2 needs (checklist the owner can hold the import to)

Per `AGENTS.md`: fastest permissive source per primitive per backend (this is it: 29% faster mul,
16% faster square than rind's best Rust, and no aws-lc or verified source exists for armv7), plan
its proof, constant-time checks, and doc rows.

Code and licence:
- `admin/import-openssl`: a third `IMPORTS_ARM` entry for `crypto/ec/asm/ecp_nistz256-armv4.pl`,
  spans cut to `ecp_nistz256_mul_mont`, `ecp_nistz256_sqr_mont` and the shared body, locals tagged.
  The perlasm needs `ecp_nistz256_table.c` only to emit the table, which the entry drops.
- `rind/src/low/arm/openssl/ecp_nistz256-armv4.s` and `rind/src/low/arm/ecp_nistz256.rs`
  (`global_asm!`, rind-version-qualified symbols, as `keccak1600_armv4.rs`), and a hook so that
  `low/generic/p256_mul32.rs`'s `fe_mul` and `fe_sqr` call it on the `arm` backend.
- `LICENSE`, OpenSSL section: add the file, "written by Andy Polyakov", and "Copyright 2015-2025 The
  OpenSSL Project Authors. All Rights Reserved." beside the existing 2005-2026 and 2017-2026 lines.
- `ALGORITHMS.md`: the Sources "OpenSSL" row (add P-256's armv7 field multiplication and its
  `ecp_nistz256-armv4` source), the P-256 row's armv7 cell ("fiat-crypto ✓ + rind ⚡ + Graviola ⚡"
  becomes "fiat-crypto ✓ + OpenSSL ⚡ + Graviola ⚡" for the multiplication), and the portable-notes
  paragraph that says armv7 P-256 runs `umaal` Rust (it then does only on the non-arm 32-bit targets).

Tests:
- A proptest of the asm against fiat-crypto's `mul` and `square` and against the Rust `fe_mul`
  and `fe_sqr`, over the same edge-weighted inputs `fiat_tests` uses (all-ones words, p - 1, p - 2,
  zero, one), in `low/arm/ecp_nistz256.rs`. The input contract to state and test: inputs below p,
  output below p (0 mismatches over 20,000 random inputs in stage 1, but not yet the edge set).
- Wycheproof and the aws-lc differential tests already cover P-256 ECDH and ECDSA on armv7 end to
  end; they must pass on `just armv7` with the asm on, and on the Pi 2 B natively.
- Constant time (`AGENTS.md`: new secret-handling asm needs ctgrind coverage): `admin/ctgrind`
  already runs `mid::p256::generate` and `from_bytes` on armv7 through the portable path, so those
  now run the asm; confirm valgrind reports nothing. The routines have no predicated instruction,
  no data-dependent branch, and no data-dependent address (the final reduction subtracts p, then adds it
  back under a mask taken from the borrow, `adds` and `adcs` of a synthesised p), which is the easy case for memcheck. Add `ct_qemu_ecdh_p256` on armv7 to
  `admin/ct-qemu` (instruction and memory-address trace under two seeds), and a BINSEC region if
  BINSEC's ARM32 front end handles the routine. `admin/ct-vartime` must stay clean: `umull` is not
  a division; confirm against the Cortex-A7 and A53 TRMs that their multiplier timing does not
  depend on the operands.
- `TESTING.md`: the ECDH P-256, ECDSA signing, and ECDSA verification rows gain
  `low::arm::ecp_nistz256::matches_fiat`, the qemu test, and (when it exists) the BINSEC test.
- `just armv7` natively on the Pi 2 B and on the Fire TV Stick (`adb`), and a repeat of the table
  above with the control, hold the result to: keygen at most 600 us, ECDH at most 3250 us, verify
  at most 3300 us, sign at most 1030 us on the Pi 2 B; on the Fire TV Stick rind at most 1.02 of
  OpenSSL on the area-4 rows (it is 1.10 to 1.19 today).

## Proofs and the Lean and `verified.toml` rows affected

- `benchmarks/verified.toml` has no armv7 P-256 row for rind today (its P-256 rows name x86_64 and
  aarch64 proofs, and the `libcrux` row names HACL*), so nothing there changes now. The armv7
  quest, [`quest/m5/verified-armv7/nist-curves.md`](../../quest/m5/verified-armv7/nist-curves.md),
  plans to prove rind's Rust `umaal` multiplication directly against the Montgomery spec and to
  give armv7 P-256 the ✓. With the import the multiplication that runs is OpenSSL's assembly, which
  no one has proved: the ✓ on armv7 P-256 would have to wait for a proof of this routine or keep
  the Rust one on the verified path. This is the real cost of the import and the owner's call.
- `AGENTS.md`: "take a formally verified one only where it measures as fast; otherwise run the
  fastest and plan its proof." The verified candidate (fiat-crypto's multiplication) is 2.4 times
  rind's `umaal` code in instructions (1,375 against 560) and was already rejected on speed; rind's
  `umaal` code is unverified but its 560 instructions are shorter than the routine's.
  So the plan is the one the rule gives: run the asm and plan its proof.
- Proof plan for the routine (stage 2b, not part of the import): it is straight-line (no loop, no
  data-dependent branch), about 450 instructions, over a small A32 subset (`umull`, `umlal`,
  `adds`, `adcs`, `subs`, `sbcs`, `rsbs`, `ldm`, `stm`, `ldr`, `str`, `mov`, `mvn`, `orr`, `and`,
  and conditional forms of them). Route A: an A32 subset model in Lean in the style of
  verified-garbage's models under `proofs/verified-garbage/` (which have x86_64 and aarch64 only,
  so the model is new work), cosimulated on the Pi 2 B and qemu, then a symbolic run against
  `fiat_p256_mul`'s spec (or `proofs/Rind/P256Booth.lean`'s Montgomery statement). Route B:
  bit-vector equivalence of the object code against the existing Rust `fe_mul` (which itself is
  tested against fiat-crypto) through an SMT bit-blast; no model code, but it proves equivalence
  to unproven Rust, so it needs the Rust proof the quest plans first. Route A is the one that earns
  a ✓ by itself. `proofs/Rind/Armv7/` has only Aeneas extern axioms today; the extern for this
  routine is one more of those until a proof lands.
- ALGORITHMS.md says rind's own proofs "do not cover its 32-bit ARM code" (assembly); the import
  does not change that statement.

## Risk

- **Constant time**: low. No branch, predicated instruction, or address depends on data; the
  only operand-dependent timing question is the cores' multiplier, which the existing 32-bit ARM
  imports (`armv4-mont`, the integer ChaCha20) already rely on.
- **Correctness**: low and checkable: the routine is 450 straight-line instructions, equal to
  fiat-crypto's multiplication on 20,000 random inputs already, and the whole ECDH and ECDSA suite
  (Wycheproof, aws-lc differential, CAVP, ACVP) runs on armv7 in CI and on the Pi.
- **Proof debt**: the main cost (above). It makes armv7 P-256's ✓ conditional on an A32 proof.
- **Win smaller than estimated**: the estimate is operation counts times chain latency, not an
  end-to-end run. The Cortex-A53 (Fire TV) has not had the multiplication microbenchmark run on it
  (the handoff's 10 to 19% gap suggests its mul gain is smaller; `umaal` and `umull` issue
  differently). A stage 2 first commit that only swaps `fe_mul` and `fe_sqr`, measured on both
  devices, decides before the rest of the work (tests, docs) is spent.
- **Thumb and interworking**: global_asm blocks are `.code 32`; Thumb-2 callers (Android armv7)
  reach them through the linker's interworking veneers, as `chacha-armv4` and `armv4-mont` already
  are. No new risk; the Fire TV run covers it.
- **Maintenance**: one more imported file, regenerated by `admin/import-openssl`; the symbol and
  header handling is the same as `keccak1600-armv4`.
- **License**: none new (OpenSSL, Apache-2.0, already in `LICENSE`).

## Stage 2 plan

1. One commit: the import, the wrapper, `fe_mul` and `fe_sqr` switched on the `arm` backend, the
   proptest. Re-run the A/B of this directory against the control on the Pi 2 B and the Fire TV;
   continue only if the expected win above reproduces (ECDH and verify within 5% of the estimates).
2. A second measured commit: asm `add` and `sub` (and `neg`, `mul_by_2`, `mul_by_3`, `div_by_2`
   where the formulas use them), kept only if it wins end to end.
3. Constant-time rows, doc rows, licence, `TESTING.md`; proof route A as its own quest.
4. Not proposed: the point routines, the w5 and w7 gather, and the 150 KB table.

## Stage 1 deliberately did not

Touch `rind/`, import any assembly, change any benchmark or proof, or run anything on the Fire TV
Stick (no device on hand for this task). The `mb` microbenchmark assembled OpenSSL's generated
assembly in a scratch crate on the laptop (`.tmp/`, never committed) and ran it on the Pi.
