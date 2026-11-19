# Handoff: open items that need other hardware or an owner decision

Status: written 2026-11-19 against upstream `main` at `29cdf710`. Every claim
below comes from a PR body, a posted review or a comment read with `gh` on that
day (fork `steelhead99x/rind` for the open fork PRs, `kixel-ai/rind` read-only
for the open claims of `steelhead99x`). Nothing here was run on hardware. Heads
are the first 8 characters of the PR head at read time; check the PR before
acting, since several heads move daily.

The Raspberry Pi 4 round has its own file, `admin/handoff-pi4.md` (fork PR
#171, base `base/pi4-handoff`). The board at 192.168.90.86 refused SSH on port
22 when #171 was written; this file does not repeat it.

Three sections:

- **A**: needs hardware that is not connected to the agent that wrote this.
- **B**: needs an owner or maintainer decision. Options and the recommendation
  recorded in the PR.
- **C**: an agent can proceed now.

Then an index of every open PR with what is outstanding. "#N" is a fork PR;
"kixel-ai #N" is an upstream PR.

## Rules for every job

Same as `admin/handoff-pi4.md`:

- Fork only. Always `gh --repo steelhead99x/rind`; `kixel-ai/rind` is read-only.
  Post nothing to another org and publish nothing.
- Read `AGENTS.md` and run `quest context` first. No em dashes. End GitHub
  posts with `(Written by <model>)`. PR bodies need `## Validation`,
  `## Models` and `## Waiting`.
- Own git worktree and `CARGO_TARGET_DIR` under `~/.cache`, never the shared
  clone and never `/tmp`.
- Benchmarks: interleaved A/B, one pinned core, a separate target dir per
  variant, at least 5 rounds, medians with spread, and an aws-lc-rs control
  that stays within 1.02. Report losses as plainly as wins.
- Squash merges: noreply author, clean `--body`, AI trailers stripped (B15).
- Never touch #141 (owner hold) or #94 (another agent has it).
- Never push to `quest/` claim branches or `up/drop-libcrux`; the owner or a
  maintainer does that.

## A. Needs hardware we do not have connected

Where results go, unless a row says otherwise: a comment on the PR it unblocks
(raw numbers, host CPU model, `uname -a`, rustc version, commit hash), the
`benchmarks/` report through `admin/bench-report` where a host row exists, and
raw logs and harness patches to
[steelhead99x/rind-results](https://github.com/steelhead99x/rind-results) as a
PR (the pattern #94 and #191 name).

### A1. Apple silicon Mac

Sources: kixel-ai #875, #149, #194, kixel-ai #824, #188, #128, kixel-ai #823,
#159, `quest/m2/confidence/apple-nightlies.md`. The bodies record earlier Apple
results from an M1 Pro (#149, #128, kixel-ai #823), so a Mac has been reachable
to some session; none is connected to this one. The Mac mini is not yet
reachable (#159).

| Job | Command or harness | Host needs | Unblocks | Results go |
| --- | --- | --- | --- | --- |
| Apple bytes in CI: make `admin/prove bytes` build the Apple targets and read Mach-O | `admin/prove bytes` on macOS with the `aarch64-apple-darwin` target; #194 adds the per-routine check (head `9d7d0dbf`) | macOS on Apple silicon, the repo's Rust pin, Nix | kixel-ai #875 (the quest's first step), #149, #194 | comment on #194 and #149; update `quest/m4/verified/apple-bytes.md` |
| Run an `x86_64-apple-darwin` build, which was only cross-built | `cargo test -p rind --lib --release --target x86_64-apple-darwin` | an Intel Mac or the hosted `macos-15-intel` runner | #149 (third row of its Waiting table), kixel-ai #875 | comment on #149 |
| Apple M4 (`kixtop`) Ed25519 verify row | `admin/bench-report collect --commit <head> --host kixtop` (host names come from the tool). BENCHMARKS.md's `kixtop` row still shows 18.81 us for aarch64 verify | the Apple M4 host `kixtop` | #188, #128, kixel-ai #824 | the `benchmarks/` report row; comment on #188 |
| ChaCha20 layout on a second Apple core | `rind-bench cipher`, filter `^chacha20/rind/`, 3 sessions of 5 interleaved rounds under the bench lock (the method kixel-ai #823 used on the M1 Pro, about 1.87x at 16 KB over `core_x4`) | Apple silicon, macOS | kixel-ai #823 | comment on kixel-ai #823's fork PR #169 |
| Native aarch64 queue runner | none until the machine is on the network; #159 holds the workflow and the label `rind-queue-arm64` | Mac mini reachable over SSH, with an account that can install Nix and register a runner | #159, `quest/m0/mac-mini-runner.md`, `apple-nightlies` | comment on #159 |
| Apple-silicon nightlies | survey the macOS and iOS rows in `build.yml` and the `dart` rows and move each that gains (the quest's plan) | the Mac mini | `quest/m2/confidence/apple-nightlies.md`, which Requires the runner quest | the quest's own PR |

### A2. Intel core that downclocks for 512-bit vectors

Sources: kixel-ai #788 (closed 2026-11-15, throughput not measured),
`quest/m2/speed/avoid-zmm.md`.

- Command: AES-GCM throughput on one core while another core runs scalar
  work, with and without the rule (the measurement the quest names). The rule
  is `slows_for_zmm` in `rind/src/low/x86_64/cpu.rs` in #788.
- Host needs: an Intel core in the list (family 6, models 0x55, 0x6a, 0x6c,
  0x7d, 0x7e, 0x9d, 0x8c, 0x8d: Skylake-SP, Cascade Lake, Cooper Lake, Ice
  Lake, Tiger Lake) with AVX-512 and VAES; Linux.
- Unblocks: nothing open. #788 was closed with the rule borrowed from
  BoringSSL and Linux and unmeasured; the quest says the same. This confirms
  or refutes it.
- Results go: a fork PR that touches PLATFORMS.md (the PR #788 cannot take a
  comment from this fork).

### A3. Zen 5 host

Sources: #152, #178, #174, kixel-ai #872, kixel-ai #830.

- The only Zen 5 named is `fedora` (kixel-ai #830); the Minisforum is Zen 4
  and #174 measured Zen 4 only.
- #152: macOS is still to do, and CI at `fdfdfad2`, including the
  `x86_64-sde` job, was queued behind the saturated hosted pool (run
  44477975923). Commands: `just check` and `just ci`; `admin/prove lean` to
  confirm High 1's fix (`seal` and `open` should translate exactly as on `main`).
- #174: measure whether the `is_intel()` gate can lift, on Zen 5 and on an
  Intel AVX-512 core. Command: the SLH-DSA bench, interleaved A/B with and
  without the eight-lane kernel; then the constant-time test for the new
  kernel.
- #178 lists a Zen 5 host among its outstanding items.
- Unblocks: #152, #174, #178.

### A4. AVX-512 hosts for Argon2id: Zen 4 or 5, and Sapphire Rapids

Sources: #163, kixel-ai #822, kixel-ai #830.

- Commands: AVX-512F fill against the AVX2 fill; `admin/ct-sde argon2` for
  the constant-time test (`nix develop .#sde`); the comparison with libsodium's
  `argon2-fill-block-avx512f.c` (#163).
- Evidence so far (kixel-ai #822): the closed fork #175 reports a Zen 4 gain
  of 18.0 and 13.6 percent for a separate kernel (AVX2 3.399 to 2.786 ms and
  54.043 to 46.669 ms), and this branch's own kernel ran only on a Granite
  Rapids runner, 1.29x at 16 MiB. The quest's rule is not closed by either.
- Unblocks: #163, kixel-ai #822, and the call on kixel-ai #830 (B20).

### A5. Zen 2 or Zen 3 host, and a CPU without ADX

Sources: #190, #79.

- #190: verified-garbage's routines take Intel and AMD with AVX-512 IFMA, so
  the s2n-bignum mixed-add swap only runs on AMD without IFMA (Zen 2 and 3)
  and on CPUs without ADX. Measured with that routing denied, on two hosts, it
  is 8 to 14 percent slower for keygen and signing. The path has therefore
  never run on the CPUs it is for.
- Command: the interleaved A/B in #190's `## Validation` (keygen and sign,
  aws-lc-rs control within 1.02, at least 5 rounds) on a real Zen 2 or Zen 3.
- Unblocks: closing #190 on evidence (B8) and the scope call on #79 (B10).
- Results go: comment on #190.

### A6. ESP32-S3 board (Xtensa)

Sources: #94 (another agent owns it: do not touch), #191, #87, #85, #181.

- #191: the Poly1305 26-bit-limb numbers on the ESP32-S3 and nRF52840 predate
  the restack onto #181; a re-run on head `d7bcb9a5` is not done and no new
  number is claimed. The harness is rind-hardware's `esp32` bench plus a local
  patch; the patch and raw logs are on the MSI only. Add them to rind-results
  as a PR next to `results/esp32s3/diag/poly1305-32`.
- #181 and #85: the CI-only Xtensa jobs in `.github/workflows/xtensa.yml` need
  the hosted pool; no board run is claimed for #181. Grok Bot's board run of
  #85 at `0fa33a92` is separate.
- Host needs: an ESP32-S3 board, the ESP Rust toolchain, a USB serial link.
- Unblocks: #191 and closing #87; #181 and closing #85 (B7).

### A7. Raspberry Pi 4 (Cortex-A72, no crypto extension)

Source: #171 and `admin/handoff-pi4.md`. The board at 192.168.90.86 refused
SSH on port 22; the owner enables SSH and fills the access section, and gives
sudo if ctgrind is wanted. Round 1 jobs are in that file; job 4 checks #82's
narrow schedule on an A72. Also asked of the A72 by #141 (held: do not touch).

### A8. aarch64 hosts with SHA3 or SVE2, and Neoverse

Sources: kixel-ai #823, #163, #187, #128. (kixel-ai #884, Neoverse N2 Keccak,
is upstream's and merged: not ours.)

- #128: one interleaved Neoverse N2 `bench` dispatch with `-f benches=ed25519`
  would meet the upstream quest to the letter; the N2 runs in #128 are
  separate runs, not interleaved.
- kixel-ai #823: a Neoverse and a Pi 5 timing once the Pi's load is free.
- #163: "plain NEON beats portable on every non-Apple aarch64 core" holds on
  the Pi 5 (1.39x and 1.40x), the Neoverse N2 runner (1.07x and 1.06x) and the
  Orin at 16 MiB (1.05x), and fails by 1 to 2 percent at the Orin's 64 MiB
  cost. A per-core gate for the A78AE needs another A78AE to measure.
- Host needs: aarch64 Linux with `sha3` (and `sve2` where the check is for
  it), Rust, root for the governor.

### A9. aarch64 host with Valgrind and libclang, for ctgrind

Sources: #187, kixel-ai #823.

- #187's ctgrind run was only done on the Pi 5, with a `__ctgrind` release
  unit-test binary cross-built on the laptop and copied with its glibc and
  `admin/ctgrind.supp` (valgrind 3.24, core 3): `low::aarch64::aes_gcm`
  (`kernels_match_composed`, `counter_wraps`), `mid::aes_gcm`, `aead`, 0
  memcheck errors. The vector-file tests did not run there (their paths are
  the laptop's), and ctgrind cannot run under qemu-user.
- kixel-ai #823 still needs a host with Valgrind and libclang on aarch64
  Linux, or a hosted `ctgrind` run that does not skip the draft; and a BINSEC
  run extending `ct_binsec_chacha20` over the eight-block, four-block and tail
  paths.
- Command: in `nix develop .#ctgrind`, `admin/ctgrind` (suites unit,
  wycheproof, adapters, fips; name one to run it alone).
- Unblocks: #187, kixel-ai #823.

### A10. RISC-V, s390x, POWER

Source: `quest/m2/confidence/ct-portable-targets.md` (i686, big-endian s390x,
riscv64gc; PowerPC appears in its motivation, libsodium's 32-bit PowerPC
fixes). The quest prefers `admin/ctgrind` where valgrind runs the target
(it names both s390x and riscv64 as supported) and otherwise extends
`admin/ct-qemu` with `qemu-s390x` and `qemu-riscv64`, which needs no native
host. No fork PR is open for it.

### A11. Windows on Arm

Sources: #164 (merged on the fork), kixel-ai #800. The Windows Dart jobs
(`windows-latest` and `windows-11-arm`) failed `native_asset_test.dart` by
splitting on `/`; #164's two-line fix is not yet on the claim branch. These are
hosted GitHub runners, so the need is the run, not owner hardware; a local run
needs the Dart SDK on Windows on Arm (none on the laptop, per #164).

### A12. A quiet laptop for timing

Sources: #178, #174, #82.

#178's numbers came from a shared host (load 10 to 48): only 1 round is clean
for X25519 and 3 for Ed25519 verification under the 1.02 control rule, fewer
than the 5 required. Command from #178: the same binary built with
`RUSTFLAGS='--cfg rind_cpu_disable'`; `RIND_CPU_DISABLE_avxifma=1` selects the
mulx path (A), its absence AVX-IFMA (B); `taskset -c <core>` (#178 used an
E-core, `-c 12`); criterion `--warm-up-time 1 --measurement-time 3`;
`rind-bench` `x25519-ecdh` and `ed25519-verify`; A and B interleaved, at least
5 clean rounds. #178's indicative B/A: X25519 0.73, Ed25519 verify 0.91. If
Ed25519 falls below 5 percent on an idle host, #178 says to close that half.
Host needs: a core with AVX-IFMA and no AVX-512, idle.

## B. Needs an owner or maintainer decision

| # | Item | Options | Recommendation (source) |
| --- | --- | --- | --- |
| B1 | #144 AES-GCM sealing under a caller's nonce (kixel-ai #873) | (a) the key stays in rind and is callable, opens included; (b) opens in the module, seals in rind; (c) refuse the seal, diverging from aws-lc-rs | (a): nothing refused, no approval claimed; `RandomizedNonceKey` and the TLS record keys are the approved path (#144) |
| B2 | #144 RSA refusals: private keys of an odd modulus bit count and PSS salts other than the hash's length | keep the refusal, or hold such a key in rind (approved and unapproved material in two places) | keep the refusal, listed in the README (#144) |
| B3 | #162 and #160: the `kem::Message` API (kixel-ai #896) | (a) the `kem::Message` newtype; (b) `encapsulate_with_message(&[u8; 32])`, the `foo_with_x` form `quest context` forbids; (c) break `encapsulate` to take a random-source handle (breaks `rind-rustls`, `rind-openmls`, `rind-aws-lc-rs`); (d) leave KEM traits out | (a) (#162, kixel-ai #896) |
| B4 | #162 route | this quest first, or with the traits work under its claim | this quest first (#162) |
| B5 | #187 AES-192 source size | accept the 4 imported files (about 3,000 lines of assembly) for AES-192-GCM, which has no TLS or QUIC suite, or not | none recorded; the body asks the maintainer to say (#187) |
| B6 | #102 close or re-cut | restore the x86_64 SHA512-instruction path or aws-lc-rs's AVX2 SHA-512, or accept the loss (6.5 to 7.3x slower than parent, 1.3x slower than aws-lc-rs); per-primitive keep or restore by measurement; the armv7 gaps | restore aws-lc-rs's AVX2 SHA-512 at least (#102). #102 is on hold and #172 stacks on it, "not for upstream" |
| B7 | #85 close in favour of #181 | close or keep | #181 is "restacked on main, supersedes #85" and #191 supersedes #87 ("to be closed once this is open"); close #85 once #181 is accepted (#181, #191) |
| B8 | #190 close | close, or a per-vendor dispatch | close: no faster than aws-lc's addition on either vendor, 8 to 14 percent slower; restricting to Intel is empty (#190) |
| B9 | #141 hold | owner hold; agents do not touch | the PR itself offers: close the handoff, or keep it for an `ecdsa-keygen` glue trial |
| B10 | #79 scope | close in favour of kixel-ai #790 once reviewed, or land | none recorded; #190 does not block it (#79) |
| B11 | armv7 gaps on a Cortex-A7 (kixel-ai #794) | accept SHA-512 2.14x, SHA-256 1.26x, ChaCha20-Poly1305 1.34x at 16 KB, or keep the assembly | keep the assembly for SHA-512 and for SHA-256 without the crypto extension; take ChaCha20-Poly1305 as is (kixel-ai #794) |
| B12 | `hacl-sha2-lean` quest (kixel-ai #794) | delete or keep the rewrite | delete if #794 merges, and make the new quest from kixel-ai #793 carry the Xtensa IRAM body and `generic::sha256` (kixel-ai #794) |
| B13 | kixel-ai #794: aarch64 SHA-2 in Rust (patch not pushed) and what "no libcrux" covers | swap and rewrite the Lean proofs, or keep HOL Light's routines; delete the HACL* ChaCha20 rounds and the bench comparators, or keep | not dropped; the owner says (kixel-ai #794) |
| B14 | landing #193's ChaCha20 into `up/drop-libcrux` | someone with write access merges #193 and #172's review fixes (`0f97f51b`) into the claim | #193 waits on a maintainer call on its `LICENSE` entry; the push to the claim is not an agent's (#193, kixel-ai #794) |
| B15 | squash-merge hygiene, and the history of `c3c56caa` (kixel-ai #874) and `70471fe1` (kixel-ai #868) | rule: noreply author, clean `--body`, no AI trailers. Both claim commits are squashes carrying many `Co-authored-by` trailers, including ones naming the owner under personal-style addresses (read from the commits). Either leave them or rewrite the claim branches | decide; no agent may force-push, and no PR records a recommendation |
| B16 | #822 and #163 landing | push `54dc751d` (merge of upstream `529ff5c0`, no rebase) to the claim branch; then squash #163 with the noreply `--author-email`; keep the SHA3 fill Apple-only; accept the 1 to 2 percent Orin loss at 64 MiB | push it; SHA3 Apple-only, plain NEON elsewhere (kixel-ai #822, #163) |
| B17 | #861 bench rows | run `admin/bench-report collect` on the report hosts | not run because other workers were benchmarking; land #179 into the claim as a merge commit, never a squash (kixel-ai #861) |
| B18 | #873 release hold and publish | the `rind-fips` release | HOLD, decided by the owner on 2026-11-19; nothing published (#144, kixel-ai #873). The first versions of `rind-digest`, `rind-aead`, `rind-signature` are published by hand by a maintainer (#160) |
| B19 | #897 outside reports approval (fork #161) | approve, edit or reject each draft; the maturity call | not yet: upstream's 2026-11-18 decision was to ask again after rind 0.4 ships and the benchmark report refresh lands; Tier 1 (seven issues) first, Tier 2 later, skip Tier 3 (kixel-ai #897) |
| B20 | kixel-ai #830 AVX-512 host | approve; approve for Argon2id only; decline and rely on `fedora` and the runners | approve for Argon2id first; merge fork #186 or the quest keeps three dangling links (kixel-ai #830) |
| B21 | #860 rustls 0.24 | an outside release, not part of the claim | kixel-ai #792 lands after #860 and must drop the ML-DSA filter in `verify_debug_names_the_type_and_ids_match_aws_lc`; #157 stacks on it (kixel-ai #860) |
| B22 | #874 dispatching `openssl-libraries` once | after landing, `gh workflow run openssl-libraries -R kixel-ai/rind` and check the aarch64 and macOS rows | do it once; keep the attach route from `release.yml` as built (kixel-ai #874). This dispatch is the maintainer's, not an agent's |
| B23 | #872 and #174 | accept the 1.03 to 1.18x AVX2 gap and amend the quest's Done-when, or profile the 54 ns (needs `perf_event_paranoid` 1 or lower on an AVX2 host) | profile first (kixel-ai #872, #183); keep #174 only if Zen 5 and Intel are no worse (#174) |
| B24 | #178 unproven tier | accept an unproven tier now, or wait for VG's VEX variants | none recorded; stay draft until 5 clean rounds (#178) |
| B25 | moving fork fixes onto claims (kixel-ai #820, #800, #799, #819) | merge fork #170, #164, #165, or apply #129's net diff, each as a normal commit | merge, as each body recommends; #164 is already merged on the fork |
| B26 | kixel-ai #824: how to move the fixes | A: merge upstream `main` into the claim, then apply four commits as new ones; B: push the fork branch as is (carries 151 commits of fork `main` history) | A, as fork #143 did for #872 (kixel-ai #824) |
| B27 | kixel-ai #823 | accept the 32 B loss (3.3 percent) against 21 to 26 percent from 1200 B up; merge fork #169; rewrite the quest Goal or close it if kixel-ai #882 wins | accept; yes; wait for the #882 comparison (kixel-ai #823) |
| B28 | #875 and #149 | `sha512_block_data_order_avx` rows keep the check or take `os = "linux"` | `os = "linux"`, as decided on 2026-11-17 for the other alignment-dependent rows (kixel-ai #875) |
| B29 | #94 IRAM and the `esp32s3-sha512-flash` opt-out | another agent owns it: do not touch | the body recommends IRAM on by default, the S3-only unroll, and an opt-out that selects main's rolled loop |
| B30 | #159 runner policy | Pi 5 and Jetson as queue runners, or not | not; the aarch64 Linux half stays a VM on the Mac mini (decided by the owner on 2026-11-19, #159) |

## C. An agent can proceed now

| # | Task | Who and how |
| --- | --- | --- |
| C1 | #182, #183, #184, #185, #186 quest syncs | a Claude worker; each is XS or S with only review waiting. Do not merge; get a second-model review |
| C2 | #192 | a different-model re-score of the High and both Mediums at `834be0a4` (#192) |
| C3 | #188 and #128 | a Gemini review at `38031a98`; the N2 interleaved `bench` dispatch on the fork if its runners are free (#128, #188) |
| C4 | #181 | run the CI-only Xtensa jobs when the hosted pool drains (#181) |
| C5 | #157 | a re-score by a model other than claude-sonnet-5-5 at the new head (#157) |
| C6 | #152 | cross-vendor re-review of `31f950bf`..`fdfdfad2`; `admin/prove lean` or CI's `prove` job (#152) |
| C7 | #163 | a re-score at the current head; `sh/dispatch.sh ci` once the laptop load drops (it was 20 to 45) (#163) |
| C8 | #172 and #193 | #193's unfiltered Pi crosschecks (more than 25 minutes); #172's fixes await a write-capable person (B14) |
| C9 | #64 | `rustup target add wasm32-wasip2 && just wasm`, and for `wasm32-unknown-unknown` the lib-only clippy check, on a host where rust-lang.org downloads work (#64) |
| C10 | kixel-ai #897 follow-ups | remove the armv7 `sanitizer: none`, remove the `blind-rsa-signatures` fork after a build check, fix stale `UPSTREAM.md` entries (#161, kixel-ai #897) |
| C11 | #171 | the Pi 4 round, once the owner enables SSH (A7) |
| C12 | #79 and #190 | confirm the `lean` and `prove` jobs and the full `admin/prove hol-light x86_64` on their heads (#79, #190) |

## Index: every open fork PR

| PR | Head | What is outstanding | Class |
| --- | --- | --- | --- |
| #194 | `9d7d0dbf` | `prove` job time with two extra builds; #149 first; different-model review | A1 |
| #193 | `9e4b0d1e` | `LICENSE` call; unfiltered Pi crosschecks; CI, ct-qemu, BINSEC, mutants on armv7 not run | B14, C8 |
| #192 | `834be0a4` | re-review | C2 |
| #191 | `d7bcb9a5` | board logs and ESP32-S3 re-run; waits on #181 | A6 |
| #190 | `ec158061` | close recommended; Zen 2 and 3 never measured | A5, B8 |
| #188 | `38031a98` | Gemini at head; M4 unmeasured; Lean and `sh/dispatch.sh ci` not run | A1, C3 |
| #187 | `f89d07fa` | CI ctgrind on the arm64 runner and `aarch64-qemu`; source size | A9, B5 |
| #186 | `af38f1f0` | owner merges it into the claim | C1, B20 |
| #185 | `4d6c0bef` | maintainer review | C1 |
| #184 | `dccf3546` | maintainer review | C1 |
| #183 | `a0851238` | profile the 54 ns or accept the gap | B23 |
| #182 | `f02d6c59` | maintainer review | C1 |
| #181 | `4efc7ce6` | hosted Xtensa CI; no board run | A6, C4 |
| #178 | `b472c64b` | 5 clean rounds, Zen 5, Windows CI, BINSEC, unproven tier | A12, A3, B24 |
| #174 | `79a47ba8` | Intel AVX-512 and Zen 5 measurements; kixel-ai #872 first | A3, B23 |
| #172 | `5bf2ae2c` | armv7 ChaCha20 unchanged; only the Pi 2B timed; stacked on held #102 | B6, C8 |
| #171 | `4b5e9199` | SSH on the Pi 4 | A7 |
| #163 | `fc4d7df0` | AVX-512 hosts; push `54dc751d`; Orin 64 MiB loss | A4, A8, B16 |
| #162 | `c82aeda0` | API go-ahead and route | B3, B4 |
| #161 | `3e82ddd7` | maturity call and draft approvals | B19 |
| #160 | `71765c1b` | first crate versions by hand; KEM crate waits on #162 | B3, B18 |
| #159 | `82dd91cf` | Mac mini validation | A1, B30 |
| #157 | `4b93e043` | QUIC out-of-order sealing, `fips()`, held release, re-score | B18, C5 |
| #152 | `fdfdfad2` | cross-vendor re-review, `prove lean`, CI incl. `x86_64-sde`, macOS | A3, C6 |
| #149 | `8f2272e4` | Mach-O in `admin/prove bytes`; Intel Mac run | A1 |
| #144 | `d5122a47` | nonce and RSA decisions (HKDF and release resolved by the owner) | B1, B2, B18 |
| #141 | `5dc1e735` | owner hold; do not touch | B9 |
| #128 | `bcaf6904` | M4 unmeasured; optional N2 dispatch | A1, A8 |
| #102 | `4a127155` | on hold; x86_64 SHA-512 decision; `lean` job | B6 |
| #94 | `3654a771` | another agent owns it; board logs on the MSI only | A6, B29 |
| #85 | `0fa33a92` | superseded by #181 | B7 |
| #82 | `51fd07cf` | merge fork `main`; run aarch64 tests and `rind-cpuid` on a narrow core (expect `"wide_mul": 0`); `admin/ct-qemu --target aarch64-unknown-linux-gnu` | A7, A8 |
| #79 | `0fa338a1` | `lean` and `prove` confirmation; scope against kixel-ai #790 | B10, C12 |
| #64 | `c552c582` | wasm check not run (downloads blocked) | C9 |

## Index: every open claim of steelhead99x on kixel-ai/rind (read-only)

| PR | Head | What is outstanding | Class |
| --- | --- | --- | --- |
| #897 | `67426f8e` | draft approvals, maturity call, rind-side follow-ups | B19, C10 |
| #896 | `1f9fa78a` | KEM message API; first crate versions; merge main; second-model review | B3, B18 |
| #875 | `44dd5989` | `os = "linux"` rows; Mach-O in CI; Intel Mac run | A1, B28 |
| #874 | `c3c56caa` | one dispatch of `openssl-libraries`; attach route; trailers on this commit | B22, B15 |
| #873 | `1f06a93e` | nonce, RSA, QUIC, held release, squash identity | B1, B2, B18 |
| #872 | `2addd479` | workflow approval; counters on an AVX2 host; Intel AVX-512 and Zen 5 | A3, B23 |
| #868 | `70471fe1` | review; re-measure P-256 ECDH after main is merged; trailers on this commit | B15 |
| #861 | `71f8af64` | land #179 as a merge; bench rows; second-model review | B17 |
| #860 | `8f4dbad5` | review; second-model review; ordering with #792; rustls 0.24 outside | B21 |
| #830 | `676e89ca` | approve the AVX-512 host | B20 |
| #824 | `891efb45` | M4 report; move fixes onto the claim; optional N2 dispatch | A1, A8, B26 |
| #823 | `d5d061b3` | Valgrind and libclang on aarch64; BINSEC; Neoverse and Pi 5 timing; 32 B loss | A8, A9, B27 |
| #822 | `cb5e26c7` | Zen 4 or 5 and Sapphire Rapids; push `54dc751d` | A4, B16 |
| #821 | `e8b72339` | approved; maintainer queue merge | none |
| #820 | `55f80fad` | merge fork #170; owner's link to the decision | B25 |
| #819 | `8ccd1bce` | apply #129's net diff after hosted CI | B25 |
| #800 | `14d49cbe` | #164's fix and a green Windows run | A11, B25 |
| #799 | `b1f0cd39` | maintainer review; merge #165 | B25 |
| #798 | `4af85052` | approved; two checks running | none |
| #794 | `9c4500bd` | armv7 gaps, quest deletion, aarch64 SHA-2, libcrux scope; `just ci` and ct-vartime on a quiet gate | B11, B12, B13 |
| #793 | `3263a332` | CI at `2c831a8a`; one open CodeRabbit finding; second-model re-score | none |
| #791 | `c2e9a13f` | approved; one job pending | none |

Not ours: kixel-ai #884 is merged and authored upstream; kixel-ai #788 is
closed (see A2).

Results from this file go back as PR comments on the fork; none is posted
upstream.
