# Handoff: open items by what they need

Refreshed 2026-11-19 (after 18:00 UTC) against upstream `main` at `29cdf710`
(the base of this branch). This file replaces both fork PR #195 (the short
version) and fork PR #196 (the long index); #196's content is folded in.

How to read it:

- Every fact is followed by the PR it was read from and the head the PR had
  when read: `[#N head]`. Fork PRs are `#N`; upstream is written `kixel-ai #N`
  (read-only). A body, a posted review or a comment was read with `gh` this
  session. Heads move, so check the PR before acting.
- `[owner]` marks a fact that comes from the owner's message to the agent that
  wrote this file and not from a PR. No PR records it, so confirm it.
- `Judgment:` marks the writer's own call. It is not from a PR.
- Nothing here was run on hardware by this file's author. "Done" always cites
  a PR comment that reports it.
- Addresses: only the LAN addresses already in repo docs are written
  (`192.168.90.42` and `192.168.90.86`, both in `admin/handoff-pi4.md` on
  #171). Other boards are named by hostname or ssh alias; the owner's ssh
  config has the rest.

Rules for every job (same as `admin/handoff-pi4.md`, #171 `a129c812`): fork
only, always `gh --repo steelhead99x/rind`; post nothing to kixel-ai or any
other org; publish nothing; no em dashes; end GitHub posts with
`(Written by <model>)`; PR bodies carry `## Validation`, `## Models` (Size
first, Implementer last) and `## Waiting`; own git worktree and
`CARGO_TARGET_DIR` under `~/.cache`, never the shared clone, never `/tmp`;
ordinary commits, no rebase, no force-push; never push to `quest/` claim
branches or `up/drop-libcrux`; never merge. Benchmarks: interleaved A/B, one
pinned core, a separate target dir per variant, at least 5 clean rounds,
aws-lc-rs control within 1.02, medians with spread, report losses as plainly as
wins. The laptop is shared: do not start a strict gate unless the gate worker
says it is free.

## 0. Not yours

| PR | Why | Source |
| --- | --- | --- |
| #94 (ESP32-S3 SHA-512 in IRAM) | another agent holds it. Its body recommends keeping the `esp32s3-sha512-flash` opt-out as the zero-IRAM choice and leaves the decision to the maintainer | [owner]; [#94 `6a0ea54d`] Waiting |
| #141 (P-256 aarch64 keygen) | on hold; it asks for a first review of `p256_vg.rs` and whether keygen, ECDH and sign stay on rind's routines on A72 and N1 (only the A76 was timed) | [owner] hold; [#141 `5dc1e735`] Waiting |
| #172 | marked DO NOT MERGE by the owner on 2026-11-19; stays open as a reference, based on #102 | [#172 `5bf2ae2c`] comment 17:35 |
| #190 | handed on; its body recommends closing it | [owner]; [#190 `ec158061`] Waiting |
| #79, #178, #174, #187 | handed on | [owner] |
| kixel-ai #823 and the aarch64 item kixel-ai #884 | handed on; #884 is upstream's and MERGED | [owner]; [kixel-ai #884 `37f18a2d`] state MERGED |

Hosts the other agent has: the MSI (Zen 3+, Ryzen 5 7535HS; a Zen 3+ A/B is
already in [#190 `ec158061`] Waiting), the Jetson over USB, and the Alienware
laptop [owner]. Coordinate with that agent before touching the handed items
below; do not start them from this file.

| Item | Host | What is left (from the PR) |
| --- | --- | --- |
| #190 | MSI, Zen 3+ | the Zen 3+ result is in: signing and keygen are 4.8 to 7.1 percent slower, 0 of 8 or 9 kept rounds faster; still no Zen 2 host. The PR recommends closing [#190 `ec158061`] Waiting |
| #79 | MSI | confirm `lean` and `prove` on `0fa338a1`; close in favour of kixel-ai #790 or keep [#79 `f84f3976`] Waiting |
| #178 | Alienware, quiet | 5 clean interleaved rounds (at the last measurement only 1 round was clean for X25519 and 3 for Ed25519 verify, load 10 to 48), a P-core and Zen 5, Windows CI of the frame handling, `admin/regenerate` in CI, BINSEC with the deny list; maintainer call on the unproven tier. Method from the body: the same binary built with `RUSTFLAGS='--cfg rind_cpu_disable'`, `RIND_CPU_DISABLE_avxifma=1` selects the mulx path (A) and its absence AVX-IFMA (B), `taskset -c <core>` (an E-core, `-c 12`, was used), criterion `--warm-up-time 1 --measurement-time 3`, `rind-bench` `x25519-ecdh` and `ed25519-verify`, A and B interleaved. If Ed25519 falls below 5 percent on an idle host the PR says to close that half [#178 `8bab6b67`] body and Waiting |
| #174 | Alienware | an Intel AVX-512 core and Zen 5 to decide whether the `is_intel()` gate lifts; only Zen 4 was measured [#174 `a9939936`] Waiting |
| #187 | Jetson | CI's ctgrind on the arm64 runner and the `aarch64-qemu` step do not run on pull requests; the Pi 5 and the laptop ran the same checks [#187 `3a920b05`] Waiting |
| kixel-ai #823 | Jetson | Valgrind plus libclang on aarch64 Linux, a BINSEC run extending `ct_binsec_chacha20`, Neoverse and Pi 5 timing [kixel-ai #823 `d5d061b3`] Waiting. The Jetson has neither Valgrind nor network [#169 `5514d0c0`] Waiting |

## A. Needs hardware this machine (the Arrow Lake laptop) does not have

This laptop is an Intel Core Ultra 9 275HX (Arrow Lake-HX, AVX2, no AVX-512)
[#170 `0e3e19d7`] comment 16:31. Results go as a PR comment on the PR named in
the row, signed `(Written by <model>)`; raw logs and harness patches go to
`steelhead99x/rind-results` as a PR (the pattern of #94 and #191); report
tables go through `admin/bench-report` where the host is a report host.

### A.1 Already on the network

| Host | What it is | Commands or harness | Unblocks | Source |
| --- | --- | --- | --- | --- |
| `pi2b` (ssh alias) | Raspberry Pi 2B, armv7, Cortex-A7, no crypto extension, 920 MB | cross-build in `nix develop .#armv7` through `quest gate`, copy the release test binaries (debug assertions on), run natively on cores 1 to 3 with the governor on `performance`, put it back to `ondemand`. Not yet run on armv7: the qemu tiers, `admin/ct-qemu`, BINSEC, mutants | #193 (ran at `9e4b0d1e`: lib 551 passed, 1 failed, 38 ignored in 1920 s; the one failure is the `finish_padded` ABI check that #202 fixes; unfiltered crosschecks 87 passed); kixel-ai #794 armv7 gaps (16 KB: SHA-512 2.14x, SHA-256 1.26x, ChaCha20-Poly1305 1.34x slower than aws-lc-rs) | [#193 `7f63bbed`] comment 17:36 and Waiting; [kixel-ai #794 `9c4500bd`] Waiting; [#163 `fc4d7df0`] body |
| `pi4b-bench`, `192.168.90.42` | Raspberry Pi 4 Model B Rev 1.5, Cortex-A72 (part `0xd08`), no crypto extension, Debian 13, glibc 2.41, `ondemand` governor, no Rust toolchain, no Valgrind or libclang, sudo asks for a password | first `uname -m; grep -m1 'CPU part' /proc/cpuinfo; grep -m1 Features /proc/cpuinfo`; then the six round-1 jobs in `admin/handoff-pi4.md` on #171 (baseline table, largest gap, fallback kernel selection, #82's narrow versus wide schedules on an A72, native `cargo test -p rind --release`, ctgrind if the owner gives sudo). Cross-build in `nix develop .#aarch64`, then `patchelf --set-interpreter /lib/ld-linux-aarch64.so.1` | #171, quest `m5/verified/aarch64-no-crypto`, #141's A72 and N1 question (held) | [#171 `a129c812`] doc and Gemini review 17:31. Claimed for a first round by Grok Bot at 17:32 ("results go in this PR's body"); no Pi 4 result was posted when this was read. The owner says the board came back and ran [owner]. Do not start a second round while that claim stands |
| Two Raspberry Pi 5 (Cortex-A76): the long-standing one and `pi5-bench` | one has been the bench board; `pi5-bench` is the second, 16 GB [owner] | ctgrind: cross-build `cargo test -p rind --lib --features __ctgrind --release --target aarch64-unknown-linux-gnu` in `nix develop .#aarch64` with `RUSTFLAGS=--cfg rind_cpu_disable`, copy it with its glibc, then `VALGRIND_BUG_494162=1 valgrind --error-exitcode=99 --unw-stack-scan-thresh=3 --suppressions=admin/ctgrind.supp BIN --test-threads=1 FILTERS` (valgrind 3.24 is on the Pi 5, libclang is not). Native tests: `cargo test -p rind --lib --locked -- low::aarch64::` and `cargo run -p rind-cpuid` (expect `"wide_mul": 0`). Timing: `taskset -c 3`, interleaved A/B | #163 (ctgrind at `fc4d7df0`: 10 passed, 0 valgrind errors), #187 (ctgrind run on the Pi 5), kixel-ai #823 Pi 5 timing, #200 Pi 5 numbers | [#163 `fc4d7df0`] comment 17:10; [#82 `f338bd06`] Waiting; [#200 `e8ce2ebf`] Validation (Pi 5 held at 1.5 GHz by the host); [#199 `0849a0ec`] body says two Pi 5s are on the LAN |
| `jetson` (ssh alias, or USB) | Jetson Orin Nano, Cortex-A78AE, 15 W mode, schedutil governor (no sudo), no Valgrind, no network | copy a cross-built binary (the host has no network); `taskset -c 3`; interleaved A/B | #163 (the Orin loses 1 to 2 percent at 64 MiB), #200, #128 and #188 (Jetson A/B), kixel-ai #823 (ChaCha20 +21 to 26 percent from 1200 B). Handed on for #187, kixel-ai #823 and kixel-ai #884 [owner] | [#200 `e8ce2ebf`] Validation; [#163 `fc4d7df0`] Waiting; [#169 `5514d0c0`] Waiting |
| `minisforum` (ssh alias) | Ryzen 7 255, Zen 4 (family 19h model 75h), AVX-512 including IFMA | `cargo test --release -p rind --lib --locked`; the ChaCha20-Poly1305 and ML-KEM A/B of #152; `admin/ct-sde argon2` for AVX-512 fills. It is Zen 4, not Zen 5: rind-results #78 fixes the "zen5" label and awaits the owner | #152 (Zen 4 measured), #163 and kixel-ai #822 (the Zen 4 side of the Argon2 AVX-512 fill), #174 (Zen 4 only) | [#192 `834be0a4`] comment 16:39; [#200 `e8ce2ebf`] Validation; [rind-results #78 `5c4deed2`] body |

### A.2 Not connected

For each: the command or harness, what the host needs, what it unblocks.

| Hardware | Command or harness | Host needs | Unblocks | Source |
| --- | --- | --- | --- | --- |
| Apple silicon (M1 Pro, M4 `kixtop`, Mac mini) | `admin/prove bytes` building the Apple targets and reading Mach-O (#194 adds the per-routine check); `rind-bench cipher` with filter `^chacha20/rind/`, 3 sessions of 5 interleaved rounds under the bench lock; `admin/bench-report collect --commit <head> --host kixtop`. The M4 iPad (iPad16,6) was tried from the M1 Pro Mac on 2026-11-19 and blocked: no registered device in the Apple Development team, and Xcode 15.4 (the newest macOS 14.0 runs) has no iPadOS destination newer than its iOS 17.5 SDK; it needs a newer Xcode on a newer macOS, or the iPad's UDID registered plus a signed build installed by hand | macOS on Apple silicon, the repo's Rust pin, Nix | kixel-ai #875, #149, #194 (Mach-O in `admin/prove bytes`); #128, #188, kixel-ai #824 (the `kixtop` Ed25519 row still shows 18.81 us; the M1 Pro result stands in as evidence only); kixel-ai #823 | [#128 `b14b1ed7`] and [#188 `38031a98`] Waiting; [#149 `8f2272e4`] Waiting; [#194 `a50dc187`] Waiting |
| Intel Mac or the hosted `macos-15-intel` runner | `cargo test -p rind --lib --release --target x86_64-apple-darwin` (that build was only cross-built) | an Intel Mac or the hosted runner | #149, kixel-ai #875 | [#149 `8f2272e4`] Waiting table |
| Mac mini as CI runner | register a self-hosted runner labelled `rind-queue-arm64` and validate a queue group with the draft `queue-build.yml` | the Mac mini on the network, an SSH account that can install Nix and register a runner; the host name and account from the owner | #159 (last item), quests `m0/mac-mini-runner` and `m2/confidence/apple-nightlies` | [#159 `82dd91cf`] Waiting |
| Zen 5 | `rind-bench` ChaCha20-Poly1305 and ML-KEM-768 A/B on one pinned core; the SLH-DSA bench with and without the eight-lane kernel; `admin/ct-sde` for AVX-512 kernels; `just check`, `just ci` and `admin/prove lean` for #152. The only Zen 5 a PR names is `fedora` (kixel-ai #830) | `avx512f avx512vl avx512ifma`, Zen 5 | #152 (macOS and CI at the head also open), #174 and #178 remainders, kixel-ai #830 | [#152 `c2f98061`] Waiting; [#174 `a9939936`] Waiting; [kixel-ai #830 `676e89ca`] Waiting |
| Intel AVX-512 server that downclocks (Skylake-SP through Tiger Lake: family 6 models 0x55, 0x6a, 0x6c, 0x7d, 0x7e, 0x9d, 0x8c, 0x8d); also Sapphire Rapids or Granite Rapids for Argon2 | AES-GCM throughput on one core while another core runs scalar work, with and without the `slows_for_zmm` rule (branch `quest/m2/speed/avoid-zmm` keeps it); `admin/ct-sde argon2` and the AVX-512 fill against AVX2. Evidence so far: the closed fork #175 (a separate AVX-512 kernel) reports a Zen 4 gain of 18.0 and 13.6 percent (AVX2 3.399 to 2.786 ms and 54.043 to 46.669 ms), and kixel-ai #822's own kernel ran only on a Granite Rapids runner, 1.29x at 16 MiB; neither closes the quest's rule | Intel with `avx512f vaes vpclmulqdq`, Linux | kixel-ai #788 (closed; parked by the maintainer because no host could measure it), #174's `is_intel()` gate, #163 and kixel-ai #822 | [kixel-ai #788 `100cdf28`] comment 2026-11-15; [kixel-ai #822 `cb5e26c7`] Waiting (cites #175); [#163 `fc4d7df0`] Waiting |
| Zen 2 (the MSI is Zen 3+ and with another agent) and CPUs without ADX | the interleaved A/B in #190's Validation (keygen and sign, control within 1.02, at least 5 rounds) | a real Zen 2, or any CPU without `adx` | the close decision on #190, the scope of #79 | [#190 `ec158061`] body ("No Zen 2 host is available") |
| Windows x86_64 and Windows on Arm | kixel-ai #800's hosted Dart jobs `windows-latest` and `windows-11-arm` (`native_asset_test.dart`; fork #164's two-line fix is MERGED into the claim base); a local run needs the Dart SDK on Windows; #178's Windows CI run of the new frame handling | Windows 11 on x86_64 or Arm, Dart SDK | kixel-ai #800, #178 | [kixel-ai #800 `14d49cbe`] Waiting; [#164 `70ac6965`] MERGED; [#178 `8bab6b67`] Waiting |
| RISC-V, s390x, POWER | `admin/ctgrind` where Valgrind runs the target, else extend `admin/ct-qemu` with `qemu-s390x` and `qemu-riscv64`; the quest names i686, big-endian s390x and riscv64gc, with 32-bit PowerPC in its motivation | native `riscv64gc`, big-endian `s390x`, or a 32-bit PowerPC host (the qemu route needs none) | quest `m2/confidence/ct-portable-targets` (no fork PR is open for it) | [#196 `ed0bfcb1`] doc A10; the quest file itself was not re-read |
| ESP32-S3 (Grok has a board [owner]) | rind-hardware's `esp32` bench plus the local known-answer patch; the Xtensa lint and `xtensa.yml` jobs are CI-only | ESP32-S3, the ESP Rust toolchain, a serial link | #191 (board re-run on `d7bcb9a5` not done, no new number claimed; waits on #181), #181 (no board run claimed), #94 (another agent's; its 2026-11-19 opt-out rerun logs are on the MSI only) | [#191 `d7bcb9a5`] Waiting; [#181 `a850e606`] Waiting; [#94 `6a0ea54d`] Waiting |
| Pi Zero 2 W (Cortex-A53), not found | find it: on 2026-11-19 it was not on 192.168.90.0/24 by Raspberry Pi MAC prefix, SSH scan or mDNS (`192.168.90.86` has a Raspberry Pi MAC but only ports 80 and 443 open); then the six round-1 jobs in `admin/handoff-pi-zero2w.md` on #199 (baseline, #82's narrow schedules on real silicon, whether `umull` and `smull` are operand-dependent on an A53) | an address or a USB gadget interface, and a key, from the owner | fork #199 tracks it | [#199 `0849a0ec`] body and Waiting |
| Graviton or Neoverse (N1, N2) | `cargo test -p rind --lib --locked -- low::aarch64::` and `cargo run -p rind-cpuid`; one Neoverse N2 `bench` dispatch with `-f benches=ed25519` to meet the upstream quest to the letter (the workflow name was not checked here); SHA3 against plain NEON for Argon2 and Keccak | aarch64 Linux; SHA3 or SVE2 for the SHA3 questions | #128 and #188 (optional interleaved N2 run), kixel-ai #823 (Neoverse timing), kixel-ai #822 and #163 (SHA3 versus plain NEON; a per-core gate on the A78AE needs a second A78AE) | [#128 `b14b1ed7`] Waiting; [#163 `fc4d7df0`] Waiting; [kixel-ai #823 `d5d061b3`] Waiting |

#82 is MERGED (847a3e3c, head `f338bd06`), so its Pi 5 check no longer waits;
its A72 side is round job 4 on the Pi 4 [#171 `a129c812`].

## B. Needs an owner or maintainer decision

One row per decision. The recommendation is the one the PR records unless the
row says `Judgment:`. "Owner" is the fork owner; "maintainer" is kixel-ai's.

| # | Item | Options | Recommendation | Source |
| --- | --- | --- | --- | --- |
| B1 | AES-GCM sealing under a caller's nonce (#144, kixel-ai #873) | (a) the key stays in rind and is callable, opens included; (b) opens in the module, seals in rind (approved key material in two places); (c) refuse the seal (diverges from aws-lc-rs) | (a): nothing refused, no approval claimed; `RandomizedNonceKey` and the TLS record keys are the approved path | [#144 `d5122a47`], [kixel-ai #873 `1f06a93e`] Waiting |
| B2 | RSA refusals (#144): odd modulus bit count and PSS salts other than the hash length | keep the refusal, or hold such a key in rind | keep the refusal, listed in the README | [#144 `d5122a47`] Waiting |
| B3 | KEM message API (#162, #160, kixel-ai #896) | (a) the `kem::Message` newtype; (b) `encapsulate_with_message(&[u8; 32])` (the `foo_with_x` form `quest context` forbids); (c) break `encapsulate` to take a random-source handle (breaks `rind-rustls`, `rind-openmls`, `rind-aws-lc-rs`); (d) leave KEM traits out | (a). #162 awaits this go-ahead; Gemini scored it 9/10 at `bf0eda6f` | [#162 `bf0eda6f`] Waiting, comments 17:36 and 17:54; [kixel-ai #896 `1f9fa78a`] Waiting |
| B4 | Route for B3 | its own quest first, or with the traits claim | its own quest first | [#162 `bf0eda6f`] Waiting |
| B5 | AES-192 source size (#187, handed on) | accept 4 imported files (about 3,000 lines of asm) for a cipher with no TLS or QUIC suite, or drop | none recorded; the PR asks the maintainer | [#187 `3a920b05`] Waiting |
| B6 | #102 (on hold) and the x86_64 SHA-512 loss | close or re-cut; restore the SHA512-instruction path or aws-lc-rs's AVX2 SHA-512, or accept 6.5 to 7.3x slower than parent and 1.3x slower than aws-lc-rs; armv7 keep-or-restore per primitive | restore aws-lc-rs's AVX2 SHA-512 at least | [#102 `4a127155`] Waiting. #172 is stacked on #102 and marked DO NOT MERGE |
| B7 | #190 (handed on) | close, or a per-vendor dispatch | close: no faster than aws-lc's addition on either vendor, 8 to 14 percent slower where it is reached, 4.8 to 7.1 percent slower on Zen 3+ | [#190 `ec158061`] Waiting |
| B8 | #79 against kixel-ai #790 (handed on) | close in favour of kixel-ai #790 once reviewed, or land | none recorded; #190 does not block it | [#79 `f84f3976`] Waiting |
| B9 | armv7 gaps on a Cortex-A7 (kixel-ai #794) | accept SHA-512 2.14x, SHA-256 1.26x, ChaCha20-Poly1305 1.34x at 16 KB, or keep the assembly | keep asm for SHA-512 and for SHA-256 without the crypto extension; take ChaCha20-Poly1305 as is | [kixel-ai #794 `9c4500bd`] Waiting |
| B10 | `hacl-sha2-lean` quest (kixel-ai #794) | delete or keep the rewrite | delete if #794 merges, and make the new quest from kixel-ai #793 (now MERGED) carry the Xtensa IRAM body and `generic::sha256` | [kixel-ai #794 `9c4500bd`] Waiting; [kixel-ai #793 `3263a332`] state MERGED |
| B11 | aarch64 SHA-2 in Rust and the scope of "no libcrux" (kixel-ai #794) | swap and rewrite the Lean proofs, or keep HOL Light's routines; delete the HACL* ChaCha20 rounds and bench comparators, or keep | not dropped; the owner says | [kixel-ai #794 `9c4500bd`] Waiting |
| B12 | Landing fixes into `up/drop-libcrux` (#202, #193) | someone with write access lands #202 (the `finish_padded` ABI exemption, generic SHA-1 not built for armv7, the `TESTING.md` rows), then kixel-ai #794, then #193 picks it up; #172's review fixes (`0f97f51b`) also wait on a writer | order: #202, kixel-ai #794, #193. The push is not an agent's. #193 also waits on a maintainer call on its `LICENSE` entry | [#202 `be8f26f3`] body, Waiting, comments 17:24, 17:25; [#193 `7f63bbed`] Waiting |
| B13 | kixel-ai #822 and #163 | push `54dc751d` to the claim, then squash #163 with the noreply author; keep the SHA3 fill Apple-only; accept the 1 to 2 percent loss at the Orin's 64 MiB | keep SHA3 Apple-only. Judgment: #163's Waiting says the claim now holds `cb5e26c7` (a merge of upstream main) and #163 merges it at `fc4d7df0`, so the push of `54dc751d` named in the older text looks done; confirm on the claim | [#163 `fc4d7df0`] Waiting ("Resolved (2026-11-19)") |
| B14 | kixel-ai #861 (X-Wing) | land #179 into the claim as a fast-forward or merge, never a squash; accept `fips::acvp::MlKemSet` as written, or re-export `Params`, or split ACVP | accept `MlKemSet`. Fork #197 merges main (`6efcb465`) into the claim head for the conflicts in `TESTING.md` and `benchmarks/report.json`; land it as a merge commit | [kixel-ai #861 `71f8af64`] Waiting; [#197 `c30dbba2`] body |
| B15 | X-Wing bench rows and the `admin/bench-report` `HOSTS` list (#200) | add the Pi 5, Jetson, Pi 2B and Ryzen 7 255 to `HOSTS` (the maintainer's settled list), or keep `benchmarks/xwing.md` as the only record | keep the note (the precedent is `benchmarks/armv7-sha256.md`); the report rows still need `admin/bench-report collect` on `nixos`, `desktop`, `kixtop`, `ovh-iad`, `ovh-sea`. Raw logs are rind-results #80, a draft for the owner | [#200 `e8ce2ebf`] body and Waiting; [rind-results #80 `72e6ab9a`] body |
| B16 | rustls parity (kixel-ai #860, #157) | land fork #198 (merge of main `6efcb465`; ML-DSA loaders onto `rind::KeyPair::from_pkcs8`; the ML-DSA filter in `verify.rs` is gone) into the claim | merge #198 as a merge commit; rustls 0.24 is an outside wait | [#198 `2c66c22a`] body; [kixel-ai #860 `8f4dbad5`] Waiting |
| B17 | `rind-fips` release hold and `try_fips_mode()` | hold or publish | HOLD, decided by the owner on 2026-11-19; `try_fips_mode()` fails until the routing completes; the first versions of `rind-digest`, `rind-aead` and `rind-signature` are published by hand by a maintainer | [#144 `d5122a47`] Waiting; [#160 `71765c1b`] Waiting; [#157 `4b93e043`] Waiting |
| B18 | QUIC out-of-order sealing and `fips()` on the TLS 1.2 suites (#157) | a module service for QUIC nonce construction in rind-fips, held with the release; whether TLS 1.2 AES-GCM reports `fips()` once the module seals TLS 1.2 records | none recorded beyond the hold | [#157 `4b93e043`] Waiting |
| B19 | kixel-ai #897 outside reports (#161) | approve, edit or reject each draft; the maturity call | not yet: upstream decided on 2026-11-18 to ask again after rind 0.4 ships and the benchmark report refresh lands; Tier 1 (seven issues) first, Tier 2 later, skip Tier 3. #185 (the quest file taking main's decision) is MERGED | [kixel-ai #897 `454285b1`] Waiting; [#161 `3618a8a6`] Waiting; [#185 `4d6c0bef`] MERGED |
| B20 | kixel-ai #830 AVX-512 host | approve; approve for Argon2id only; decline and rely on `fedora` and the runners | approve for Argon2id first; merge fork #186 or the quest keeps three dangling links (the claim branch is also 62 commits behind main) | [kixel-ai #830 `676e89ca`] Waiting; [#186 `af38f1f0`] Waiting |
| B21 | kixel-ai #872, #174 and #201 | accept the 1.03 to 1.18x AVX2 gap and amend the quest's Done-when, or profile the 54 ns (needs `perf_event_paranoid` 1 or lower on an AVX2 host); the workflow approval | profile first; keep #174 only if Zen 5 and Intel are no worse. Fork #201 merges main (`e74437d9`) into the claim so kixel-ai #872 stops conflicting; it must land as a fast-forward or merge, never a squash | [kixel-ai #872 `68e5a0b1`] Waiting; [#174 `a9939936`] Waiting; [#201 `fb387109`] body |
| B22 | kixel-ai #874: dispatch `openssl-libraries` once | after landing, `gh workflow run openssl-libraries -R kixel-ai/rind` and check the aarch64 and macOS rows; the attach route from `release.yml` as built | do it once and keep the attach route. It is the maintainer's to run | [kixel-ai #874 `c3c56caa`] Waiting |
| B23 | History of the claim commits `c3c56caa` (kixel-ai #874) and `70471fe1` (kixel-ai #868) | both are squash commits whose messages carry `Co-authored-by` trailers. Most are noreply forms, but 1 on `c3c56caa` and 7 on `70471fe1` are not noreply addresses (counted from the commits API; the addresses are not written here). Leave them, or rewrite the claim branch history | owner decision. Judgment: leave them unless the owner objects; a rewrite needs a force-push, which no agent does | commits API read this session; [kixel-ai #868 `70471fe1`] Waiting |
| B24 | Squash-merge hygiene | noreply author (`--author-email 224322244+steelhead99x@users.noreply.github.com`), clean `--body`, AI trailers stripped; a merge commit onto an upstream claim branch carries no trailer | adopt as the rule (#190, #79, #163, #152, #181, #172, #171 state it) | the PRs' merge-time lines in `## Waiting` |
| B25 | kixel-ai #868: P-256 ECDH figures | the branch lacks upstream main's P-256 ECDH, which a scratch merge measured 9 to 16 percent faster through the provider; re-measure the README figures after main is merged | re-measure after the merge | [kixel-ai #868 `70471fe1`] Waiting |
| B26 | Moving fork fixes onto claims (kixel-ai #820, #800, #799, #819) | #170, #164 and #165 are MERGED into their claim bases; #129 is MERGED on fork main (`1ae175e2`), but kixel-ai #819 still needs its net diff (histories diverged: 5 commits only on the claim, 211 only on the fork branch) | apply #129's net diff as a normal commit after hosted CI on `4d3dc38f`. Judgment: the Waiting text of kixel-ai #820, #800 and #799 still says "merge #170, #164, #165", which is stale. The owner still owes kixel-ai #820 a link to where option (c) was decided | [#170 `0e3e19d7`], [#164 `70ac6965`], [#165 `c6ae53ad`] MERGED; [kixel-ai #819 `8ccd1bce`], [kixel-ai #820 `55f80fad`] Waiting |
| B27 | kixel-ai #824: how to move the fork's fixes | A: merge upstream main into the claim, then apply four commits as new ones; B: push the fork branch as is (carries 151 commits of fork main history) | A, as fork #143 did for #872 | [kixel-ai #824 `891efb45`] Waiting |
| B28 | kixel-ai #823 | accept the 32 B loss (3.3 percent, about 7.5 ns) against 21 to 26 percent from 1200 B up; #169 (MERGED) put the Jetson numbers in the quest file | accept; the quest Goal is rewritten or closed if kixel-ai #882 (open, `251c77f3`, aarch64 ChaCha20 on verified-garbage's code) wins the comparison | [kixel-ai #823 `d5d061b3`] Waiting; [#169 `5514d0c0`] MERGED; kixel-ai #882 state OPEN |
| B29 | kixel-ai #875 and #149 | `sha512_block_data_order_avx` rows: keep the check or take `os = "linux"` | `os = "linux"`; #149 already did it at `8f2272e4`, as the owner decided on 2026-11-17 | [kixel-ai #875 `44dd5989`] Waiting; [#149 `8f2272e4`] Waiting |
| B30 | #194 (Mach-O check) | maintainer: CI `prove` job time with two more builds (the aarch64 job already runs about 100 of its 150 minutes), the first hosted run of the flake change, #149 first | land #149 first; Gemini scored it 9/10 at `a50dc187` | [#194 `a50dc187`] Waiting and comment 17:30 |
| B31 | #159 runner policy | Pi 5 and Jetson as queue runners, or not | not; the aarch64 Linux half stays a VM on the Mac mini (owner, 2026-11-19) | [#159 `82dd91cf`] Waiting |
| B32 | #181 landing | keep in draft until the `xtensa.yml` jobs and other hosted CI finish green; squash with the AI trailers stripped | the hosted pool is saturated; a strict local gate passed (exit 0, 1331 s) at `4efc7ce6` and Gemini scored 9/10 at `a850e606` | [#181 `a850e606`] Waiting, comments 17:50 and 17:54 |
| B33 | #182, #184 and #186 quest-sync PRs | maintainer review and merge into the claim | merge; each has only review waiting (Gemini 9/10: #182 at `f02d6c59`, #184 at `4146a381`, #186 at `af38f1f0`) | their `## Waiting` and comments |
| B34 | rind-results #78 (Zen 4 label fix) and #80 (X-Wing raw logs) | owner merges or rejects; #78 goes into `bench/minisforum-zen5-avx512` first, which is not on `main` yet | merge #78 into that branch first | [rind-results #78 `5c4deed2`], [rind-results #80 `72e6ab9a`] bodies |
| B35 | #195 and #196 (this file) | #195 carries this refreshed file; #196 is superseded | merge #195 once reviewed; close #196 | this PR |

## C. Can proceed now

No hardware and no decision needed. "Done" means a PR comment reports it.

| # | Task | State and what remains | Source |
| --- | --- | --- | --- |
| C1 | #152: re-review, `admin/prove lean` (or CI's `prove` job), hand-dispatch the `x86_64-sde` ctgrind on `c2f98061`, strict gate | the PR is a draft again until `prove` and `x86_64-sde` are green; the re-review must come from a model other than claude-opus-5-5; the strict gate is another worker's | [#152 `c2f98061`] Waiting, comment 18:02 |
| C2 | #157: re-score by a model other than claude-sonnet-5-5 | a strict local gate passed at `4b93e043` (exit 0, 1539 s); the trailer strip is merge-time | [#157 `4b93e043`] comments 16:06 and 17:57 |
| C3 | #163: re-score and `sh/dispatch.sh ci` | Gemini 9/10 at `5352a51f`; a 10 minute fuzz run (nothing found) and a Pi 5 ctgrind run (0 errors) at `fc4d7df0` are posted; `sh/dispatch.sh ci` was not run (laptop load 20 to 45) | [#163 `fc4d7df0`] comments 17:06 and 17:10, Waiting |
| C4 | #181: the hosted Xtensa jobs | dispatch the CI-only jobs in `.github/workflows/xtensa.yml` when the hosted pool drains | [#181 `a850e606`] Waiting |
| C5 | #193: the armv7 gates not yet run | CI, `admin/ct-qemu`, BINSEC, mutants on armv7 and the qemu tiers (the laptop load was above 30) | [#193 `7f63bbed`] Waiting, comment 17:36 |
| C6 | Gemini reviews waiting on a head | #202 `be8f26f3` (requested 17:24), #201 `fb387109` (17:08), #200 `e8ce2ebf` (17:01), #188 `38031a98` (review at the new head) | each PR's comments and Waiting |
| C7 | #188: `sh/dispatch.sh ci` and the Lean build | not run | [#188 `38031a98`] Waiting |
| C8 | #201: strict gate on the merge | "The full strict gate has not been run on the merge"; only the cheap checks and `cargo test -p rind --lib -- sha3 slhdsa keccak` (22 passed) ran. Needs the gate worker | [#201 `fb387109`] body |
| C9 | #197 and #198: gates | #197 ran no cargo gate; #198 ran `cargo test -p rind-rustls` (46 lib plus all integration tests), clippy and fmt on the minisforum, and not the rest of the workspace | [#197 `c30dbba2`], [#198 `2c66c22a`] bodies |
| C10 | The wasm check of #64 | #64 is MERGED. Its note said `rustup target add` was blocked. Judgment: that looks stale, since the strict gate of #181 reports the wasm module passed in 290 s; confirm before relying on it | [#64 `c552c582`] Waiting; [#181 `a850e606`] comment 17:50 |
| C11 | kixel-ai #897 rind-side follow-ups | remove the armv7 `sanitizer: none`, remove the `blind-rsa-signatures` fork after a build check, fix stale `UPSTREAM.md` entries; not before the maturity call (B19) | [#161 `3618a8a6`] Waiting |
| C12 | A different model's review of this file | the owner confirms the `[owner]` rows | this PR |

## Index: open fork PRs

Class points to a row above. Heads are as read at refresh time.

| PR | Head | Outstanding | Class |
| --- | --- | --- | --- |
| #202 | `be8f26f3` | Gemini review; order #202, kixel-ai #794, #193 | B12, C6 |
| #201 | `fb387109` | Gemini review; strict gate; land as a merge | B21, C8 |
| #200 | `e8ce2ebf` | Gemini review; `HOSTS` and report-host rows | B15, C6 |
| #199 | `0849a0ec` | the board's address and a key | A.2 |
| #198 | `2c66c22a` | owner merges into the rustls claim | B16, C9 |
| #197 | `c30dbba2` | owner merges into the X-Wing claim | B14, C9 |
| #196 | `ed0bfcb1` | superseded by #195 | B35 |
| #195 | this branch | review | B35, C12 |
| #194 | `a50dc187` | maintainer: `prove` job time, #149 first | B30 |
| #193 | `7f63bbed` | `LICENSE` call; armv7 qemu, ct-qemu, BINSEC, mutants; after #202 | B12, C5 |
| #191 | `d7bcb9a5` | board logs and ESP32-S3 re-run; waits on #181 | A.2 |
| #190 | `ec158061` | handed on; close recommended | B7 |
| #188 | `38031a98` | Gemini review at head; M4 unmeasured; `sh/dispatch.sh ci` | A.2, C6, C7 |
| #187 | `3a920b05` | handed on; CI ctgrind; source size | B5 |
| #186 | `af38f1f0` | owner merges into the claim | B20, B33 |
| #184 | `4146a381` | maintainer review | B33 |
| #182 | `f02d6c59` | maintainer review | B33 |
| #181 | `a850e606` | hosted Xtensa jobs; no board run | B32, C4 |
| #178 | `8bab6b67` | handed on | section 0 |
| #174 | `a9939936` | handed on; Zen 5 and Intel | section 0 |
| #172 | `5bf2ae2c` | DO NOT MERGE | section 0 |
| #171 | `a129c812` | Pi 4 first round claimed by Grok Bot; sudo for ctgrind | A.1 |
| #163 | `fc4d7df0` | AVX-512 hosts; Orin 64 MiB loss | B13, C3 |
| #162 | `bf0eda6f` | `kem::Message` go-ahead | B3, B4 |
| #161 | `3618a8a6` | maturity call and draft approvals | B19 |
| #160 | `71765c1b` | first crate versions by hand; KEM crate waits on #162 | B17 |
| #159 | `82dd91cf` | Mac mini | A.2, B31 |
| #157 | `4b93e043` | re-score; QUIC sealing; held release | B17, B18, C2 |
| #152 | `c2f98061` | re-review, `prove`, `x86_64-sde`, Zen 5 | C1 |
| #149 | `8f2272e4` | Mach-O in `admin/prove bytes`; Intel Mac run | A.2 |
| #144 | `d5122a47` | nonce and RSA decisions | B1, B2 |
| #141 | `5dc1e735` | owner hold | section 0 |
| #128 | `b14b1ed7` | M4 unmeasured; optional N2 dispatch | A.2 |
| #102 | `4a127155` | on hold; SHA-512 decision | B6 |
| #94 | `6a0ea54d` | another agent | section 0 |
| #79 | `f84f3976` | handed on | B8 |

## Index: open claims of steelhead99x on kixel-ai/rind (read-only)

| PR | Head | Outstanding | Class |
| --- | --- | --- | --- |
| kixel-ai #897 | `454285b1` | draft approvals, maturity call | B19, C11 |
| kixel-ai #896 | `1f9fa78a` | KEM message API; first crate versions | B3, B17 |
| kixel-ai #875 | `44dd5989` | Mach-O in CI; Intel Mac run; `os = "linux"` rows | A.2, B29 |
| kixel-ai #874 | `c3c56caa` | one dispatch of `openssl-libraries`; history | B22, B23 |
| kixel-ai #873 | `1f06a93e` | nonce, RSA, QUIC, held release | B1, B2, B17 |
| kixel-ai #872 | `68e5a0b1` | workflow approval; counters; #201 | B21 |
| kixel-ai #868 | `70471fe1` | review; re-measure P-256 ECDH; history | B23, B25 |
| kixel-ai #861 | `71f8af64` | land #179 and #197 as merges; bench rows | B14, B15 |
| kixel-ai #860 | `8f4dbad5` | review; #198; rustls 0.24 outside | B16 |
| kixel-ai #830 | `676e89ca` | approve the AVX-512 host | B20 |
| kixel-ai #824 | `891efb45` | M4 report; moving fixes | A.2, B27 |
| kixel-ai #823 | `d5d061b3` | handed on (aarch64); Valgrind, BINSEC, timing | section 0, B28 |
| kixel-ai #822 | `cb5e26c7` | Zen 4 or 5 and Sapphire Rapids | A.2, B13 |
| kixel-ai #821 | `e8b72339` | approved; maintainer queue merge | none |
| kixel-ai #820 | `55f80fad` | owner's link to decision (c); review | B26 |
| kixel-ai #819 | `8ccd1bce` | apply #129's net diff | B26 |
| kixel-ai #800 | `14d49cbe` | green Windows Dart run; review | A.2, B26 |
| kixel-ai #799 | `b1f0cd39` | maintainer review | B26 |
| kixel-ai #794 | `9c4500bd` | armv7 gaps, quest deletion, scope; #202 first | B9 to B12 |

Gone since the earlier lists: kixel-ai #884 (not ours), #793, #791, #798 and
#792 (all MERGED upstream, state read this session).

## What changed since the two earlier files

- MERGED on the fork: #82 (847a3e3c), #64, #23, #129, #131, #173, #177, #185,
  #164, #165, #169, #170, #176, #192 [each PR's state].
- CLOSED: #183, #85, #87, #166, #168, #132, #136, #155, #158, #175 [each PR's
  state]. #85 and #87 are superseded by #181 and #191.
- New open: #197, #198, #199, #200, #201, #202.
- The Pi 4 was probed (#171 `a129c812`); a second Pi 5 is on the LAN and the
  Pi Zero 2 W has not been found [#199 `0849a0ec`].
- rind-results #78 awaits the owner [rind-results #78 `5c4deed2`].

## Where results go

A PR comment on the named fork PR, signed `(Written by <model>)`; raw board
logs and harness patches to `steelhead99x/rind-results` as a PR; tables
through `admin/bench-report`. Delete this file before any upstream branch
merges from this one. Report losses as plainly as wins.
