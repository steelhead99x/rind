# Handoff: open items by what they need

Written 2026-11-19 against upstream `29cdf710`. Every claim below comes from a
PR body, a posted review or a comment, read with `gh`. Fork is
`steelhead99x/rind`; `kixel-ai/rind` is read-only. Heads are the short SHAs
read at the time and will move. Style follows
[handoff-pi4.md](/admin/handoff-pi4.md) (fork PR #171).

Rules for every job: fork only, always `gh --repo steelhead99x/rind`; post
nothing to kixel-ai or any other org; publish nothing; no em dashes; end
GitHub posts with `(Written by <model>)`; own worktree and `CARGO_TARGET_DIR`
under `~/.cache`, never the shared clone and never `/tmp`; ordinary commits,
no rebase, no force-push; never push to `quest/` claim branches or
`up/drop-libcrux`. Benchmarks: interleaved A/B, one pinned core, at least 5
clean rounds, an aws-lc-rs control within 1.02, medians with spread. Owner
holds #141 and another agent has #94: do not touch either.

## Handed to another agent (hosts: MSI Zen 3+, Jetson over USB, Alienware laptop)

The owner reports another agent now holds #79, #190, #178, #174, #187 and the
aarch64 items #823 and #884, with these hosts reachable to it. Do not start
them from this file; coordinate with that agent.

| Item | Host | What it needs (from the PR) |
| --- | --- | --- |
| #79, #190 (P-256 mixed add) | MSI, Zen 3+ | #190's swap runs only on AMD without IFMA (Zen 2 and 3) and CPUs without ADX; #190 recommends closing it. #79 waits on `lean` and `prove` on `0fa338a1`. |
| #178 (AVX-IFMA X25519/Ed25519) | Alienware laptop, quiet | 5 clean interleaved rounds on an idle host; Ed25519 (0.91) is the smaller win and closes if under 5 percent. Zen 5 and a P-core are still not covered (see below). |
| #174 (eight-lane Keccak) | Alienware laptop | Only Zen 4 was measured; Intel AVX-512 and Zen 5 remain uncovered (see below). |
| #187 (AES-192-GCM, aarch64) | Jetson | Ran ctgrind on the Pi 5 only; Jetson ctgrind not run; CI's ctgrind and `aarch64-qemu` steps do not run on pull requests. |
| #823, #884 (aarch64 ChaCha20, Keccak hybrid) | Jetson (SHA3, valgrind to be checked) | #823 waits on Valgrind plus libclang on aarch64 Linux for ctgrind, a BINSEC run, and Neoverse and Pi 5 timing. #884 is upstream's (kixelated) merged four-way Keccak PR, not a steelhead99x claim. |

## A. Needs hardware not connected

For each: command or harness, host needs, PRs unblocked, where results go.
Results go as a PR comment on the named PR unless a row says otherwise; raw
logs go to `steelhead99x/rind-results` as a PR; benchmark tables go through
`admin/bench-report` into `benchmarks/` where the host is a report host.

| Hardware | Command or harness | Host needs | Unblocks | Results |
| --- | --- | --- | --- | --- |
| Mac, Apple silicon (M1 Pro, M4 `kixtop`, Mac mini) | `admin/prove bytes` building the Apple targets and reading Mach-O; `rind-bench` `cipher` with `^chacha20/rind/` for M1 numbers; `admin/bench-report collect --host kixtop` | macOS, Rust 1.98.x, Nix | upstream #875 and fork #149, #194 (Apple-bytes check; Mach-O alignment); #824 and fork #188 (the `kixtop` Apple M4 Ed25519 row is unmeasured; an M1 Pro result stands in for it); #823 M1 numbers | PR comment; `kixtop` row via `admin/bench-report` |
| Mac mini as CI runner | Register a self-hosted runner labelled `rind-queue-arm64`; validate a queue group; nightlies per `quest/m2/confidence/apple-nightlies.md` | Mac mini on the network, SSH account that can install Nix and register a runner | fork #159 (draft, "waiting on the machine"), apple-nightlies quest. Owner decided 2026-11-19 that aarch64 Linux stays a VM on the Mac mini | PR comment on #159 |
| Intel core that downclocks for 512-bit vectors (family 6 models 0x55, 0x6a, 0x6c, 0x7d, 0x7e, 0x9d, 0x8c, 0x8d) | AES-GCM throughput on one core while another runs scalar work, with and without the avoid-zmm rule (the measurement `quest/m2/speed/avoid-zmm.md` names) | Skylake-SP through Tiger Lake, `avx512f vaes vpclmulqdq` | #788 (closed upstream; the rule shipped unmeasured, no host could time it) | PR comment on a fork PR opened for it |
| Zen 5 host (the minisforum is Zen 4) | `rind-bench` ChaCha20-Poly1305 and ML-KEM-768 A/B on one pinned core; `admin/ct-sde` for AVX-512 kernels | `avx512f avx512vl avx512ifma`, Zen 5 | #152 (a re-review and `admin/prove lean` also outstanding, not hardware); #178 and #174 remainders | PR comments |
| Intel AVX-512 core, Sapphire Rapids or Granite Rapids | `admin/ct-sde argon2`; eight-lane Keccak and Argon2 AVX-512 against AVX2 | `avx512f`, Intel | #174 (`is_intel()` gate), #163/#822 (Argon2 AVX-512 on Zen 4 or 5 and Sapphire Rapids) | PR comments |
| Zen 2 or 3 or a non-ADX CPU | covered for Zen 3+ by the MSI, see the handed-off table; Zen 2 and non-ADX remain | AMD Zen 2, or any CPU without `adx` | #79, #190 | PR comment |
| ESP32-S3 board | rind-hardware's `esp32` bench plus the local known-answer patch; Xtensa lint is CI-only | ESP32-S3, ESP toolchain, serial access | #181 (CI-only Xtensa jobs; no board run claimed), #191 (Poly1305 26-bit limbs; board re-run on this head not done), #87 and #85 (superseded). #94's board logs: another agent has #94, do not touch | raw logs to `rind-results` next to `results/esp32s3/diag/poly1305-32`, then a PR comment |
| Raspberry Pi 4 (Cortex-A72, no crypto extension) | the six round-1 jobs in [handoff-pi4.md](/admin/handoff-pi4.md) | the owner must enable SSH (192.168.90.86 refused port 22) and fill in its Access section | fork #171, quest `m5/verified/aarch64-no-crypto`, #82 narrow versus wide schedules on A72, #141's open question on A72 and N1 (hold: do not touch) | PR comments on #171 |
| aarch64 with SHA3 or SVE2, or Neoverse (Graviton, N2) | `cargo test -p rind --lib --locked -- low::aarch64::` and `cargo run -p rind-cpuid` (expect `"wide_mul": 0` on narrow cores); Neoverse N2 `bench` dispatch with `-f benches=ed25519` | aarch64 Linux | #82 (narrow core run on the Pi 5), #188 and #128 (interleaved Neoverse N2 dispatch), #822/#163 (SHA3 versus plain NEON). #823 and #884 are handed off above | PR comments |
| aarch64 host with Valgrind and libclang (ctgrind) | `nix develop .#ctgrind` then `admin/ctgrind` | aarch64 Linux, Valgrind, libclang. Done only on the Pi 5 (cross-built binary) so far | #823, #187 (handed off); #82 via `admin/ct-qemu --target aarch64-unknown-linux-gnu` | PR comments |
| RISC-V, s390x, POWER | `admin/ctgrind` where Valgrind runs the target, else extend `admin/ct-qemu` with `qemu-s390x` and `qemu-riscv64` | native `riscv64gc`, big-endian `s390x`, or 32-bit PowerPC host | `quest/m2/confidence/ct-portable-targets.md` (unclaimed) | quest PR |
| Windows on Arm | `windows-11-arm` Dart job | Windows 11 Arm, Dart SDK | upstream #800 and fork #164 (merged; the Windows run on #800 is the only verification) | upstream's CI |
| Wasm toolchains (not hardware, blocked downloads) | `rustup target add wasm32-wasip2 && just wasm` | network to rust-lang.org | #64 | PR comment |

## B. Needs an owner or maintainer decision

Recommendations are the ones recorded in the PR bodies.

| Item | Options | Recommendation |
| --- | --- | --- |
| #144 (also upstream #873): AES-GCM under a caller's nonce | (a) key stays in rind, callable, nothing approved claimed; (b) opens in module, seals in rind; (c) refuse the seal | (a) |
| #144: RSA keys of odd modulus bits and PSS salts | keep refusal, or hold such a private key in rind | keep the refusal |
| #162 and #160 (upstream #896): `kem::Message` API and route | (a) `kem::Message` newtype; (b) `encapsulate_with_message(&[u8; 32])`; (c) break `encapsulate`; (d) no KEM traits. Route: its own quest first, or with the traits claim | (a), own quest first |
| #187: AES-192 source size | accept 4 imported files (about 3,000 lines of asm) for a cipher with no TLS or QUIC suite, or drop | owner call; PR asks |
| #102 | close, or re-cut; x86_64 SHA-512 restore (SHA512 instructions, or aws-lc's AVX2) or accept the loss; armv7 per-primitive keep-or-restore | restore aws-lc's AVX2 SHA-512 at least; #172 is stacked on it, on hold |
| #85 | close in favour of #181 | close |
| #190 | close | close (swap is 8 to 14 percent slower, empty on Intel) |
| #141 | owner has it on hold | none; do not touch |
| #79 | close in favour of upstream #790, or keep | decide once the maintainer reviews #790; #190 does not block it |
| #794 | armv7 gaps (16 KB: SHA-512 2.14x, SHA-256 1.26x, ChaCha20-Poly1305 1.34x on a Pi 2B); the `hacl-sha2-lean` quest; HACL* ChaCha20 rounds; aarch64 SHA in Rust; landing #193's ChaCha20 and #172's fixes into `up/drop-libcrux` (another writer, not this agent) | keep asm for SHA-512 and non-crypto-extension SHA-256, take ChaCha20-Poly1305 as is; delete the quest if #794 merges, carry its work into #793's new quest |
| #822 and #163 | push `54dc751d` to the claim branch, then squash #163 (noreply author, no AI trailers); keep SHA3 fill Apple-only; accept the 1 to 2 percent plain-NEON loss at the Orin's 64 MiB | push it; keep SHA3 Apple-only |
| #861 | X-Wing bench rows need `admin/bench-report collect` on report hosts; `MlKemSet` marker; land #179 as FF or merge, never squash | accept `MlKemSet` as written |
| #873 | release hold on `rind-fips` (decided 2026-11-19: held); publish later; order #860, #157, then #873 | keep the hold |
| #897 | outside reports: upstream decided "not yet" on 2026-11-18; approve each draft | Tier 1 first after the maturity item clears, skip Tier 3 |
| #860 | rustls 0.24 release is an outside wait; #792 must drop the ML-DSA filter | wait |
| #874 | dispatch `openssl-libraries` once after landing (`gh workflow run openssl-libraries -R kixel-ai/rind`; maintainer's to run); trigger from `release.yml` or a tag-push | keep as built |
| History rewrite on upstream claim branches #874 and #868 | commits `c3c56caa` and `70471fe1` are squash commits whose messages carry personal-address `Co-authored-by` trailers beside AI trailers. Options: leave, or rewrite the claim branch history | owner decision; this agent never force-pushes and does not do it |
| Squash-merge hygiene | noreply author (`--author-email 224322244+steelhead99x@users.noreply.github.com`), clean `--body`, AI trailers stripped | adopt as the rule (#190, #79, #163, #822, #861, #873 all state it) |

## C. Can proceed now by an agent

- #194: a different model's review, and Linux CI `prove` job time; stacks on #149.
- #192, #183, #186, #185, #184, #182: quest-sync and review follow-ups; need a re-review by a different model or maintainer merges. No hardware.
- #181, #191: CI-only Xtensa jobs and stack order (#191 waits on #181); a reviewer can retarget after #181 lands.
- #152: cross-vendor re-review of `31f950bf`..`fdfdfad2` by a model other than claude-opus-5-5; `admin/prove lean`.
- #157: re-score by a model other than claude-sonnet-5-5.
- #161 and #897: nothing outside the maturity call.
- #188: Gemini review at `38031a98` and `sh/dispatch.sh ci`.
- #64: ready; wasm check needs the toolchain download only.
- #82: merge fork `main` (redo on `22e65e53`, run `admin/prove lean`).
- #172: stacked on #102 (hold).

## Where results go

PR comment on the named fork PR, signed `(Written by <model>)`; raw board logs
and harnesses to `steelhead99x/rind-results` as a PR; tables through
`admin/bench-report`. Report losses as plainly as wins.
