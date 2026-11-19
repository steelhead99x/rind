# armv7 Android (Fire TV Stick) bench run: findings and fix handoff

Read this first, then pick an area from the checklist at the bottom. Each area states the
symptom, the measured root cause, where the code is, a suggested approach, and the number that
closes it. Everything here was measured on one physical device, with the commands in
[Reproduce](#reproduce).

All times are criterion medians on the device, pinned to one core, 1.69 GHz, rind `main` at
`847a3e3c0` unless a row says otherwise. Ratios are rind's time over the other library's time, so
above 1.00 is slower.

## Device

| | |
|---|---|
| Device | Amazon Fire TV Stick (3rd gen, 2021), model `AFTSSS`, Fire OS 7.7.0.4 (Android 9, API 28) |
| SoC | MediaTek MT8695, 4× Cortex-A53 r0p4 (`CPU part 0xd03`), `interactive` governor, 1.69 GHz and never seen to change |
| Kernel / userland | 4.4.162+ `armv7l`, 32-bit userland (a 64-bit kernel is not in play, so no AArch64 path is reachable) |
| ISA bits | `AT_HWCAP=0x3fb4d6`, `AT_HWCAP2=0x1f`: NEON, and AArch32 AES, PMULL, SHA-1, SHA-2, CRC32 |
| Memory | about 920 MB, 50–110 MB free with swap in use; every bench below fits (see area 5) |
| Shell | `adb shell`, uid `shell`: no root, `/data/local/tmp` is the only writable and executable place; toybox `taskset` takes a hex mask (`taskset 8`), not `-c` |
| Not readable | thermals (`/sys/class/thermal` is permission denied), `/proc/stat` counters are not monotonic, so no CPU-busy share |

The ISA bits are what `rind-cpuid` now prints on the device (area 1):

```
{ "cpuid": { "neon": 1, "aes": 1, "pmull": 1, "sha1": 1, "sha2": 1, "crc32": 1 }, "supports_crypto_ext": 1, "hwcap": 4174038, "hwcap2": 31 }
```

## What this PR changes

Only area 1 is code. Areas 2–6 are findings: no benchmark, backend, or proof changed.

- `rind-cpuid`: 32-bit ARM Linux and Android probe (it was `unsupported platform` there). The
  probe reads `getauxval(AT_HWCAP)` and `AT_HWCAP2` with `libc`, the same bits and the same
  mapping `rind/src/low/arm/cpu.rs` uses, and prints the feature set, `supports_crypto_ext`, and
  the raw words. Tests: five pure decode tests on every host, plus an armv7-only test that checks
  the auxv result against `/proc/cpuinfo`.
- `admin/bench-report`: the `armv7` feature list now names the real armv7 features
  (`neon, aes, pmull, sha1, sha2, crc32`) so a report from `rind-cpuid` is accepted; an x86 name
  is still refused. `admin/bench-report-test` covers both.
- This directory: findings, scripts, small data files (`data/`), and `armv7-probe.patch`, the
  throwaway component probe behind the area 2 and 3 numbers (see [Probe](#probe)).

## Baseline: rind main against the other libraries

Run on `main` twice, back to back; the second column of every pair agrees with the first within
0.5% (`data/bench-main-repeat.txt` holds both). The wider table from the first run, at
`ac0f2f936` (all ops, all sizes), is `data/firetv-vs-libs-at-ac0f2f936.md`.

| Row | rind | aws-lc-rs | OpenSSL 3.6.3 | ring | rind / best other |
|---|---|---|---|---|---|
| chacha20poly1305 32 B seal | 2.642 µs | 2.349 µs | 2.314 µs | 2.860 µs | 1.14 |
| chacha20poly1305 1350 B seal | 8.939 µs | 8.660 µs | 8.097 µs | 9.266 µs | 1.10 |
| chacha20poly1305 16 KB seal | 76.68 µs | 76.34 µs | 66.62 µs | 76.89 µs | 1.15 |
| aes128-gcm 16 KB seal | 24.83 µs | 25.13 µs | 25.82 µs | | 0.99 |
| aes128-gcm 16 KB open | 32.85 µs | 33.10 µs | 33.64 µs | | 0.99 |
| p256-ecdh | 1.560 ms | 6.141 ms | 1.423 ms | | 1.10 |
| p256-ecdsa-sign | 443.2 µs | 1.528 ms | 378.9 µs | | 1.17 |
| p256-ecdsa-verify | 1.497 ms | 4.739 ms | 1.257 ms | | 1.19 |

## Area 1: `rind-cpuid` had no 32-bit ARM path (done in this PR)

`rind-cpuid/src/main.rs` only knew x86 `cpuid` and AArch64 system registers, so on an armv7 device
it only printed `only for x86_64 and aarch64 architectures`, and the bench report could not say which tier ran. The new
`arm` module takes the two auxv words and maps the bits as `rind/src/low/arm/cpu.rs` does
(`HWCAP_NEON = 1<<12`; `HWCAP2_AES = 1<<0`, `PMULL = 1<<1`, `SHA1 = 1<<2`, `SHA2 = 1<<3`,
`CRC32 = 1<<4`). `supports_crypto_ext` is the same predicate rind uses (NEON, AES, PMULL, SHA-1, and SHA-2 all set, as in
`HaveCryptoExt`).

Verified on the host (`cargo test -p rind-cpuid`), cross-built for `armv7-linux-androideabi`, and
run on the device (output above). A follow-up could make the probe call into `rind` instead of
carrying its own constants, but `rind` is `no_std` with no public cpu API, so this stays
self-contained, as the other targets in this binary are.

## Area 2: ChaCha20-Poly1305 is 0.82–0.95× of the others on A53 32-bit NEON

Four separate causes. 2a explains the whole 16 KB gap to OpenSSL; 2b and 2c explain the small
messages; 2d is the QUIC header-protection row.

**2a. Poly1305 inner loop (16 KB, vs OpenSSL).** rind, aws-lc-rs, and ring all land at 76–77 µs
because they run the same two assembly files: `chacha-armv4.s` for the cipher and BoringSSL's
2-lane NEON Poly1305 (`poly1305_arm_asm.s`, called from `rind/src/low/arm/poly1305_arm.rs`). OpenSSL
runs Cryptogams' `chacha-armv4` (same cipher code) and Cryptogams' `poly1305-armv4` NEON. On this
core, by slope between sizes in the probe:

| Piece | rind | OpenSSL |
|---|---|---|
| ChaCha20 stream | 5.04 cpb | 5.05 cpb (same asm, so no gap) |
| Poly1305 | 2.63 cpb marginal, 2.75 cpb at 16 KB | 1.69 cpb |

The 0.94 cpb difference is 16384 × 0.94 / 1.69 GHz ≈ 9.1 µs of the 10.1 µs gap. The portable
HACL\* Poly1305 is 20.7 cpb, so it is nowhere near a fallback worth tuning.

Fix: import `poly1305-armv4` (the NEON path) the way `admin/import-openssl` already imports other
Cryptogams files, and call it from `poly1305_arm.rs` in place of `neon2`. It is Apache-2.0, like the
other imported files. Keep the existing `neon_matches_portable` style test, add the usual
constant-time checks, and plan a proof per `AGENTS.md` ("run the fastest and plan its proof").
Close it when chacha20poly1305 16 KB is at most 68 µs, which is OpenSSL's number.

**2b. Fixed cost per call (32 B and 1350 B).** At 32 B, rind is 0.29–0.33 µs behind aws-lc-rs and
OpenSSL (about 500–560 cycles). From the probe, each measured on its own:

| Step | Time |
|---|---|
| Poly key: `ChaCha20::new` + `cipher` over 32 B (integer `ChaCha20_ctr32_nohw`) | 532 ns |
| Same asm for a full 64 B block | 437 ns |
| Poly1305 NEON `new + add + finish` over 32 B | 1.09 µs (HACL: 1.20 µs) |
| `ChaCha20` init alone | 29 ns |

`low/generic/chacha20poly1305.rs` computes the poly key with a full `cipher` call on a 32 B buffer
(the tail path in `chacha_armv4.rs`, 95 ns slower than a whole block), then makes separate
`add_bytes` calls for the AAD, pad, data, pad, and the two length words, each through the buffering
logic in `poly1305_arm.rs`. Poly1305 setup runs two multiply-reduces for the r², r⁴ powers and
`finish` converts out of the two-lane form; all of that is paid at 32 B where there is no data to
amortise it.

Fix: (i) get the poly key from one 64 B call and use its first 32 B, or from a single-block asm
entry; (ii) build pad plus lengths as one 16 B block and absorb it in one call; (iii) give totals
under about 64–128 B a scalar Poly1305 (Cryptogams' integer path has no setup cost) and measure
where it crosses the NEON path. Close it when 32 B is at most 2.35 µs and 1350 B at most 8.7 µs
without regressing 16 KB.

**2c. The 192 B cliff in the cipher.** `ChaCha20_ctr32_neon` is entered from 192 B
(`NEON_MIN_LEN`, as in aws-lc); below it the integer path runs at 11–12 cpb on A53. The probe shows
the cliff directly: 191 B takes 1370 ns (12.1 cpb), 192 B takes 797 ns (7.0 cpb). 128–191 B inputs
(QUIC short packets, TLS records of small messages) pay for it. Measure a 2-block NEON entry or a
lower `NEON_MIN_LEN` on A53 in-order cores; Cryptogams' notes for this file suggest the integer path
can beat one NEON block on in-order cores, so measure rather than assume.

**2d. QUIC header protection (`quic-header-protection/chacha20`, 0.80–0.89×).** Header protection
makes one 64 B block through `low::chacha20_block`, which on armv7 runs HACL\*'s generic rounds:
606 ns in the probe against 437 ns for the same block through the assembly `nohw` entry, so 28%
faster. The comment in `rind/src/low/arm/chacha20.rs` that justifies the generic path measured it
on a 64-bit core, and it does not hold for 32-bit A53.

There is a proof constraint: `BENCHMARKS.md` lists the armv7 header-protection ChaCha20 as proven
(a Lean proof of HACL\*'s rounds, `proofs/Rind/X86_64/ChaCha20.lean`). Switching to the assembly
drops that proof coverage, and `AGENTS.md` says to run the fastest code and plan its proof, so this
needs a decision from the maintainers before it lands. Close it at 450 ns or less.

## Area 3: AES-128-GCM open looked 10% slower; it is not at `main`

The first run (`ac0f2f936`) showed rind open at 0.90× aws-lc-rs. It does not reproduce: on `main`,
twice, rind open 16 KB is 32.60–32.85 µs against aws-lc-rs 32.99–33.10 µs and OpenSSL 33.64 µs, and
seal is 24.83 µs against 25.13 µs and 25.82 µs. The first run's slow rows are most likely
the noise described in area 6; the cause was not proven.

The seal→open gap (about 7.9 µs for rind, 8.0 for aws-lc-rs, 7.9 for OpenSSL) is the bench itself:
`rind-bench/benches/aes_gcm.rs` copies the ciphertext into the plaintext buffer before each in-place
open (`pt.copy_from_slice(ct)`), and a 16 KB memcpy on this core is 7.48 µs (0.77 cpb). The
components agree: AES-CTR 14.2 µs + GHASH 9.8 µs = 24.0 µs against the 24.83 µs seal; open minus the
copy is 25.1 µs.

rind composes AES-GCM the way aws-lc does (`rind/src/mid/portable/aes_gcm.rs`: 3 KiB chunks, CTR and
GHASH as separate passes, GHASH first on open). A stitched CTR+GHASH loop could overlap the two, but
that is new assembly with an unproven ceiling on an in-order dual-issue core; no gap justifies it
here.

Action: none for the library. Optionally make the bench report the copy separately, or make open
out-of-place, so a future reader does not chase this again. Acceptance: open stays at or under
aws-lc-rs.

## Area 4: P-256 ECDH, ECDSA sign, and verify are 10–19% slower than OpenSSL

rind is 3.2–3.9× faster than aws-lc-rs here (it has no 32-bit P-256 assembly, so it runs generic code), but 1.10×, 1.17×,
and 1.19× behind OpenSSL (ECDH, sign, verify).

Cause: on armv7 rind runs Rust: fiat-crypto field and group operations with a 32-bit Montgomery
multiply (`rind/src/low/generic/p256_mul32.rs`, `umaal` rows) and Booth-5 windows
(`low/generic/p256.rs`). OpenSSL runs `ecp_nistz256-armv4` (Cryptogams): hand-scheduled 32-bit
multiplies, a reduction that uses the special form of the P-256 prime (word adds and subtracts, no
second multiply pass), and precomputed tables with wNAF. Field multiply dominates a scalar
multiply, so the gap is the multiply-and-reduce.

Options, by size of change:

1. Cheaper reduction in `p256_mul32`: reduce with the prime's special form instead of Montgomery
   reduction. That drops the reduce half of every `fe_mul`, but it changes the field domain, so the
   generator tables from `admin/p256-precomp` and the fiat bridging change with it.
2. Import `ecp_nistz256-armv4` through `admin/import-openssl` and add an armv7 `p256` mid-layer.
   Biggest gain and the least new Rust, with the usual constant-time, test, and proof-plan
   obligations.
3. For verify only, check that `u1·G + u2·Q` already runs as one interleaved double-scalar loop;
   at 1.50 ms, equal to ECDH, there may be a second doubling chain to share. A larger generator
   table is a smaller change with a smaller gain.

Close it when ECDH is at most 1.42 ms, sign at most 380 µs, and verify at most 1.26 ms, with the
`p256` correctness tests and the existing Wycheproof vectors unchanged.

## Area 5: benches skipped on the device

Memory was not the constraint. After the first run, every rind row that had been skipped ran on the
device, one binary at a time, with peak RSS (`VmHWM`) from 9.1 MB (md5) to 21.3 MB (Argon2 at 16
MiB) and 70.3 MB (Argon2id 64 MiB, t=3, p=4: 1.64 s). Per-binary time, RSS, and availability are in
`data/lowmem-run.txt`, medians in `data/lowmem-rind-rows.txt`:

md5, sha1, p521, hpke, oprf, vrf, spake2plus, rsa_pub, rsa_priv, blind_rsa, argon2.

What actually blocked them:

- **rustls handshakes** (`rind-bench/benches/rustls.rs`): the bench reads its test keys from the
  compile-time `CARGO_MANIFEST_DIR`, which is a host path on the device (it panics with `NotFound`).
  Not run on the device in this effort. Build with the manifest dir remapped (bubblewrap bind of the
  checkout at a fixed path, then push the key files to that path on the device), as the Galaxy A16
  run did, or change the bench to take a key dir from the environment at run time. Handshake rows
  start threads from `available_parallelism` (4 here), so cap them with the existing bench-CPU
  variable on a 920 MB box.
- **`rsa_gen`**: gated by the compile-time `NOISY_BENCHMARKS` (`option_env!`), so it lists no rows
  unless set when building. Set it at build time; expect it to be slow on an A53 and run it last.
- **md5, sha1**: not in `admin/bench-report`'s op list, so a report drops them even though they
  ran. Add them to the list if the report should show them.
- **The device itself**: one reboot (area 6) killed a long single on-device run. The scripts here make one
  `adb` call per bench and retry.

Low-memory profile (nothing in the repo implements it yet): `--sample-size 10 --warm-up-time 1
--measurement-time 2`, rows filtered to rind with the regex `/rind(/|$)`, one binary per call, pinned
to one core, Argon2 64 MiB and threaded rustls only when `MemAvailable` is at least about 150 MB. A
follow-up could add this as a named profile in `rind-bench` or a script in `admin/`.

## Area 6: bench methodology notes

- **Noise.** Repeat runs agree within 0.5% when the box is quiet. The first run had slow, uneven
  rows while a vendor service (`whad`) was busy and hopping between cores; pinning to one core
  helps but does not remove it. Check `top` for it before a long run, and take two repeats of any
  row before calling a regression.
- **Reboot.** The device rebooted mid-run once (uptime reset; cause not determined, no readable
  log as uid `shell`). Run each bench as its own `adb` call and retry.
- **Frequency.** `scaling_cur_freq` read 1.69 GHz at every check, so cycles per byte above use that
  clock. Thermals are unreadable (`/sys/class/thermal` is permission denied), so throttling can only
  be inferred from repeat-run drift, and none was seen.
- **No CPU-busy share.** `/proc/stat` counters were not monotonic, so do not report a utilisation
  figure from them.
- **Memory.** 50–110 MB free with swap in use; read `MemAvailable` before the run and keep one
  process at a time.
- **`taskset`.** Toybox wants a hex mask, `taskset 8` for CPU 3.
- **adb.** Fire OS leaves `adb` on TCP port 5555 once ADB debugging is on; use USB or a trusted LAN
  and turn it off afterwards. Nothing here installs anything outside `/data/local/tmp`, and the
  scripts remove their directory.
- **OpenSSL numbers in the probe** (`data/probe-components.txt`, last rows) include per-call EVP
  setup, so they are only good as the slope between sizes; the 5.05 cpb and 1.69 cpb figures above
  are that slope (`(63336.9 − 18424.8) ns / 15034 B`, and `(63044.3 − 48014.7) ns / 15034 B`).

## Reproduce

Needs: `rustup target add armv7-linux-androideabi`, an Android NDK (r28c used), perl and make for
the vendored OpenSSL, and `adb` with the device authorised. Build output goes to
`$CARGO_TARGET_DIR` (default `~/tmp/rind-armv7-target`, about 2–3 GB; delete it afterwards).

```sh
# 1. cross-build the benches and rind-cpuid into ./pkg (nothing here is committed)
docs/handoff/firetv-armv7/scripts/build.sh                       # all benches
docs/handoff/firetv-armv7/scripts/build.sh chacha20poly1305 p256 # or a few

# 2. push, run pinned to CPU 3, pull logs into ./out, remove the push
SERIAL=<adb serial> CPU_MASK=8 docs/handoff/firetv-armv7/scripts/run-on-tv.sh \
  'chacha20poly1305:^chacha20poly1305/(rind|aws-lc-rs|openssl)/(32B|1350B|16KB)$' \
  'aes_gcm:^aes128-gcm' \
  'p256:^p256-(ecdh|ecdsa-sign|ecdsa-verify)/'
```

By hand, the run line is
`taskset 8 ./chacha20poly1305 --bench --noplot --warm-up-time 1 --measurement-time 3 '<regex>'`.
The cross-build for tests only (no device) is
`cargo check -p rind-cpuid --target armv7-linux-androideabi` once the NDK variables from
`scripts/env-android.sh` are set.

### Probe

`armv7-probe.patch` adds, to a scratch checkout only, a `rind::__probe` module and
`rind-bench/examples/armv7_probe.rs`. It times the pieces named in areas 2 and 3 (the ChaCha20
entries by length, the HACL block, the poly-key call, both Poly1305 backends, AES-CTR, GHASH, a 16
KB memcpy) through the real backend dispatch. It widens `low::portable` visibility to `pub(crate)`
to reach the portable code, so do not merge it; apply it with `git apply`, build with
`cargo build --release -p rind-bench --example armv7_probe --target armv7-linux-androideabi`, push,
and run pinned. `data/probe-components.txt` is its output on the device.

## Checklist for the next agent

Each box closes with the number named, measured with the commands above and a repeat run.

- [ ] **2a** Cryptogams `poly1305-armv4` NEON in place of `neon2`: chacha20poly1305 16 KB ≤ 68 µs.
- [ ] **2b** Cheaper poly key and pad+lengths, scalar path for tiny inputs: 32 B ≤ 2.35 µs, 1350 B ≤ 8.7 µs.
- [ ] **2c** Re-measure `NEON_MIN_LEN` / a 2-block NEON path on A53: no cliff between 191 B and 192 B.
- [ ] **2d** Header protection through the assembly `nohw` block (maintainer decision on the proof first): ≤ 450 ns.
- [ ] **3** Optional: report the bench's copy separately; no library change.
- [ ] **4** P-256 on armv7: ECDH ≤ 1.42 ms, sign ≤ 380 µs, verify ≤ 1.26 ms.
- [ ] **5** Build and run rustls and `rsa_gen` on the device; add md5/sha1 to the report ops; add the low-memory profile.
- [ ] **6** Make a repeat run and a "device busy" check part of the bench script.
