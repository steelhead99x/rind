# Handoff: Apple bytes for the proofs' ✓

Fork-side notes for `quest/m4/verified/apple-bytes`. The upstream claim stays an empty commit. Nothing here is the implementation.

> **Delete this file before anything merges onto `quest/m4/verified/apple-bytes`.** The only change on this branch is `notes/apple-bytes-handoff.md`. Merging it would put the note on the claim. Implement on this branch, delete the note, then merge into `quest/m4/verified/apple-bytes` with a merge commit so that branch keeps the claim commit and moves forward. Do not squash this PR onto the quest branch, and do not force-push the claim. Pushing `quest/m4/verified/apple-bytes` updates the upstream draft. This session does not merge.

## Claim

Upstream claim: https://github.com/kixel-ai/rind/pull/875 (draft). Head is `steelhead99x:quest/m4/verified/apple-bytes`, base is kixel-ai/rind `main`.

Branch `quest/m4/verified/apple-bytes` on this fork is empty commit `44dd59898c35c33a40c5c7370a0cbbca4ba2d04d` (`chore(quest): claim quest/m4/verified/apple-bytes.md`, `Quest-Claim: 937a036d908eb012`). Its tree matches its parent, kixel-ai/rind `main` at `863ad5a8f2be2ad333e42bc0279c19ca0cf6a5c4`.

Parents: [`quest/m4/verified/README.md`](../quest/m4/verified/README.md) (every hot path proven; this child is about what a ✓ claims), [`quest/m4/README.md`](../quest/m4/README.md), [`quest/README.md`](../quest/README.md). Maintainer, 2026-11-16: the quest is m4, in the verified epic. Skipping it was rejected.

## Goal

Every `benchmarks/verified.toml` row whose proof `admin/prove bytes` checks only against the Linux build either is checked against the Apple build too and passes, or carries `os = "linux"`. A ✓ in `README.md` or `BENCHMARKS.md` then covers only bytes something checks.

`admin/bench-report` `proof_for` treats a missing `os` as the host's OS, so the row matches Linux and macOS. `os = "linux"` drops the ✓ on a macOS host. The only macOS bench host today is `kixtop` (Apple M4, aarch64) in `admin/bench-report`'s `HOSTS`. An x86_64 row with no `os` would mark a future x86_64 macOS host the same way; [kixel-ai/rind#778](https://github.com/kixel-ai/rind/pull/778) already did that for P-256.

## Done when

`admin/prove bytes` builds each proven routine for `x86_64-apple-darwin` and `aarch64-apple-darwin` and compares it as it compares the Linux build, and the run lists which `benchmarks/verified.toml` rows match. A row that matches keeps its ✓ for macOS. A row that does not match carries `os = "linux"`, and its proof text says the proof is of the Linux build, as the two x86_64 P-256 rows already do.

The quest prefers a match. For a row that differs only by alignment, align the Apple entry so the bytes match, where that changes no instruction the proof checks and does not slow the routine. Benchmark that change on the macOS host. Where the bytes still differ, or the bench is slower, set `os = "linux"`.

"The bytes match" means the Apple object's instructions are the bytes the proof lists. `admin/prove-bytes` `compare` already drops a naked function's alignment padding and accepts a longer branch when it still lands on the same instruction. That exception is a weaker check than the byte list in a HOL Light `define_assert_from_elf` / `define_assert_relocs_from_elf`. [kixel-ai/rind#778](https://github.com/kixel-ai/rind/pull/778) treated a changed `call` displacement as uncovered: with the Apple entry 16 bytes off, P-256's first call targets entry+0x7b0, and with the entry 32-byte aligned it targets entry+0x7a0, the Linux object's target.

## What is already marked

`benchmarks/verified.toml` has `os = "linux"` on two rows, both x86_64, from #778:

- `p256-ecdh`
- `p256-ecdsa-sign`, `p256-ecdsa-verify`

Their proof text says "the object code rind's Linux build emits". `rind/src/low/x86_64/ecp_nistz256.rs` and `proofs/hol-light/x86_64/ecp_nistz256_point_add_affine.ml` say the same. Leave those rows in place unless an Apple build is shown to match the listed bytes. #778's maintainer choice was `os = "linux"`.

## Rows the quest names

Naked functions pick `.linux.s` or `.apple.s` with `#[cfg(target_vendor = "apple")]`. `admin/prove` `triple` is `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` only, and `bytes` assembles the Linux upstream text with `x86_64-linux-gnu-as` / `aarch64-linux-gnu-as`.

| Row | Arch / CPU | Routine the proof checks | Apple text |
|---|---|---|---|
| `sha512/*` | x86_64, `intel`, `avx`, `ssse3`, `!avx2` | `sha512_block_data_order_avx`, in `admin/prove-bytes` `NAKED` | `rind/src/low/x86_64/aws_lc/sha512_block_data_order_avx.apple.s` (`.p2align 4` inside; Linux has `.align 64` at the entry) |
| `sha512/*` | x86_64, `avx`, `avx2`, `bmi1`, `bmi2`, `popcnt`, `ssse3`, `!sha512` | OpenSSL `sha512_block_data_order_avx2`, HOL Light of the Linux object (`proofs/hol-light/x86_64/sha512_block_data_order_avx2.ml`). Not in `NAKED` | `rind/src/low/x86_64/openssl/sha512_block_data_order_avx2.apple.s` (`.p2align` inside; Linux `.align 64` at the entry) |
| `ed25519-sign` | the same two x86_64 CPU sets | those SHA-512 routines, plus s2n-bignum Edwards code rind transliterates | the SHA-512 `.apple.s` files |
| AES-GCM seal and open | x86_64, `aes`, `pclmulqdq`, `ssse3`, `sse4.1`, `avx`, `movbe`, `!vaes` | Vale `compute_iv_stdcall`, `gcm128_encrypt_opt`, `gcm256_encrypt_opt`, `gcm128_decrypt_opt`, `gcm256_decrypt_opt`, in `NAKED`. `bytes` assembles `dist/vale/aesgcm-x86_64-linux.S` | `rind/src/low/x86_64/hacl/<name>.apple.s`, included from `rind/src/low/x86_64/aes_gcm_avx.rs` |
| `sha256/*`, `hmac-sha256/*`, `hkdf-sha256/*` | aarch64, `aes`, `pmull`, `sha2` | `sha256_block_data_order_hw`, HOL Light of the Linux object (`proofs/hol-light/aarch64/sha256_block_data_order_hw.ml`) | `rind/src/low/aarch64/aws_lc/sha256_block_data_order_hw.apple.s` (no entry `.align`; Linux has `.align 6`). This ✓ shows on `kixtop` |
| `sha512/*` | aarch64 | `sha512_block_data_order_hw` (HOL Light, `proofs/hol-light/aarch64/sha512_block_data_order_hw.ml`) and `sha512_block_data_order_nohw` (`NAKED`) | `rind/src/low/aarch64/aws_lc/sha512_block_data_order_hw.apple.s` (Linux `.align 6` at the entry, `.align 4` on the loop; Apple keeps the loop align only) and `sha512_block_data_order_nohw.apple.s` (Linux `.align 6`, Apple has no `.align`). This ✓ shows on `kixtop` |

`ed25519-sign` and `ed25519-verify` on aarch64 compose those same SHA-512 routines (`benchmarks/verified.toml`, the aarch64 Ed25519 row). The quest text names SHA-256 and SHA-512. List the Ed25519 row with them: its ✓ shows on `kixtop` too.

s2n-bignum routines in `rind/src/low/{x86_64,aarch64}` are one `asm!` on every OS. `admin/prove-bytes` `routines()` collects them and `bytes` compares the Linux build to the proof's byte list. Build them for the Apple triples as well and list which rows match. X25519, aarch64 P-256, P-384, and SHA-3 are in that set. Their sources have no `.apple.s`.

The AES-GCM row with `!avx` is rind's by-8 kernel, not the Vale naked functions. It is outside the rows named above. Include it only if the Apple build of a routine `bytes` checks actually feeds that row.

## Files

- `quest/m4/verified/apple-bytes.md` — the quest. Delete it when the quest is done, per the other finished quests.
- `admin/prove` — `triple`, `build_asm`, `asm_block`, `asm_function`, `relocations`, `bytes`. `bytes` is the subcommand (`admin/prove bytes`). `hol_light_proofs` is the list of objects HOL Light reads, all from the Linux build.
- `admin/prove-bytes` — `list`, `check`, `NAKED`, `compare`. The module docstring is the allowed differences.
- `benchmarks/verified.toml` — the rows and the header comment that already says x86_64 P-256 is Linux-only.
- `admin/bench-report` — `proof_for`, `host_os`, `load_verified` (`os` is `linux` or `macos`). `render` rewrites `BENCHMARKS.md`, `README.md`'s comparison, and the SVGs. `just ci` runs `render --check`.
- `.github/workflows/prove.yml` — `nix develop .#hol-light --command admin/prove bytes` on `ubuntu-24.04`, in `hol-light-aarch64`. Path filter includes `admin/prove` and `admin/prove-bytes`. It does not include `benchmarks/verified.toml`. The workflow is not part of `just ci`.
- `flake.nix` — `devShells.hol-light` rustc targets are the three Linux triples. `devShells.vg` has `llvmPackages_21`, whose `llvm-mc` is the assembler #778 used (21.1.8).
- `admin/import-aws-lc` — writes the `.linux.s` / `.apple.s` pairs. Apple is `mac-x86_64` / `ios-aarch64` with `-D__APPLE__`. `alignment()` keeps a leading `.align` / `.p2align`. Headers say do not edit the `.s` by hand.
- `admin/import-hacl` — Vale's `linux` and `darwin` flavors, landed as `.linux.s` / `.apple.s`.
- `rind/src/low/tests.rs` `apple_routines_open_one_cfi_frame` — each `.apple.s` has at most one `.cfi_startproc`, because ld64 splits atoms on CFI frames.
- Call sites: `rind/src/low/x86_64/sha512.rs`, `rind/src/low/x86_64/aes_gcm_avx.rs`, `rind/src/low/aarch64/sha256.rs`, `rind/src/low/aarch64/sha512.rs`, `rind/src/low/x86_64/ecp_nistz256.rs`.

## Preferred plan: check the Apple build

1. On Linux, list the routines and the rows. `admin/prove-bytes list` needs no build. Map each `NAKED` symbol and each `hol_light_proofs` object onto the table above, and map each s2n-bignum routine onto the `verified.toml` row whose proof names it.
2. On Linux, assemble each proven `.linux.s` and `.apple.s` with `llvm-mc` from `nix develop .#vg` (`-triple x86_64-apple-macosx` / `aarch64-apple-macosx` for the Apple text, the Linux triple for the other). Compare instruction bytes and each branch target relative to the entry, which is what #778 did for P-256. Repeat with the Apple entry aligned to the alignment its helpers use (32 bytes / `.p2align 5` for the P-256 shape, 64 bytes where the Linux entry is `.align 64` or `.align 6`). Record which routines match only after that alignment, and which differ by something other than alignment (opcode bytes, not just a displacement or `nop`).
3. Teach `admin/prove bytes` to build `x86_64-apple-darwin` and `aarch64-apple-darwin` and to compare those objects the way it compares the Linux ones. Print a line per `verified.toml` row: match, or the first routine that differs.
   The Linux `bytes` path is ELF-shaped. `relocations` parses `RELOCATION RECORDS FOR`, and `asm_function` requires the symbol to be the whole of `.text.$sym` and its relocs to name one `.rodata` section. Mach-O objdump and section names differ, and Apple relocation kinds (`ARM64_RELOC_*`, `X86_64_RELOC_*`) are not the `R_AARCH64_*` / `R_X86_64_*` strings `prove-bytes` matches. Normalize those before compare. A cargo object is the artifact the quest asks for; the `llvm-mc` diff in step 2 is the scout.
   `devShells.hol-light` does not install the Apple rustc targets, and this flake has no macOS SDK or ld64. `cargo rustc -p rind --lib --release --target aarch64-apple-darwin --emit=obj` from this Linux shell is the thing to try, and it is expected to stop at the linker. `--emit=asm` can still show which `.s` the `cfg` selected.
4. Where step 2 says the only difference is entry alignment, put that alignment on the Apple path. Prefer a directive in the `#[cfg(target_vendor = "apple")]` `naked_asm!`, or a change in `admin/import-aws-lc` / `admin/import-hacl` that the next import keeps. A hand edit of a generated `.s` is wiped by the next import. The Linux object, which the HOL Light byte list names, stays as it is. Re-run the compare. The instructions the proof names stay the same; only the Apple entry's alignment changes.
5. Benchmark that alignment on the macOS host before keeping it. `kixtop` is the aarch64 host in `HOSTS` (Apple M4). Benches: `rind-bench/benches/sha2.rs`, `hmac.rs`, `hkdf.rs`, `ed25519.rs`. There is no x86_64 macOS host in `HOSTS`. An x86_64 alignment (SHA-512 AVX, SHA-512 AVX2, Vale AES-GCM) has nowhere in the report to be timed. See open questions.
6. For each row: keep it unrestricted when the Apple bytes match and the bench is not slower; otherwise set `os = "linux"`, say "Linux build" in that row's `proof`, and update the header comment in `benchmarks/verified.toml`. Follow #778 for the docs it touched (`ALGORITHMS.md` only where a cell's wording claims the macOS object, the module doc, the HOL Light banner).
7. `admin/bench-report render` so `README.md` and `BENCHMARKS.md` pick up the `os` restriction. `just ci` fails when `render --check` is stale.

## Fallback: mark the uncovered rows

The quest allows this per row, and it is the whole change when an Apple build cannot be checked.

1. Set `os = "linux"` on every row in the table above whose Apple bytes were not shown to match, including the aarch64 Ed25519 row if its SHA-512 routines did not match.
2. Update those rows' `proof` strings and the `verified.toml` header the way the P-256 rows are written.
3. `admin/bench-report render`.
4. Leave `admin/prove bytes` as it is only when every such row carries `os = "linux"`. A checker that still builds Linux alone, beside a row with no `os`, misses the done-when bar.

Do this for the rows whose bytes differ by more than alignment even if the preferred plan lands. P-256 x86_64 is already done.

## What a Mac is for

No Mac is on hand for this session. Split the work on that fact.

On Linux, this VM:

- Read and diff the `.apple.s` / `.linux.s` pairs, and run `admin/prove-bytes list`.
- Assemble both flavors with `llvm-mc` and compare object bytes and branch targets, including the aligned-entry experiment. That is the #778 measurement, and it needs no Apple SDK.
- Edit `admin/prove`, `admin/prove-bytes`, `benchmarks/verified.toml`, and the `naked_asm!` / import path. `admin/prove bytes` against the Linux triples still runs here (`nix develop .#hol-light`).
- Regenerate the report. `render` reads `benchmarks/data`; it does not need a Mac.
- `just ci` and `quest check`.

Needs a macOS machine:

- `cargo` for `aarch64-apple-darwin` and `x86_64-apple-darwin` when the Linux link fails, which is the expected case. GitHub's `build.yml` already builds on `macos-latest` (arm64) and `macos-15-intel` (x86_64). Those runners can dump the objects. `prove.yml` cannot: it is `ubuntu-24.04` only.
- The speed check the quest asks for, on the macOS bench host. For aarch64 that host is `kixtop`. Nothing in `HOSTS` is x86_64 macOS. `quest/m0/mac-mini-runner.md` is still waiting on the maintainer's Mac mini, so do not plan on it.
- A confirmation that ld64's linked image matches the `llvm-mc` object. `rind/src/low/tests.rs` exists because ld64 splits atoms on CFI frames; an object compare can miss a link-time split.

An aarch64-only Mac answers the `kixtop` benches and the `aarch64-apple-darwin` objects. The x86_64 Apple objects still need an Intel Mac or `macos-15-intel`.

## Tests

From the Nix dev shell. Pass the claim's parent. The fork's `origin/main` is a different history.

```sh
nix develop --command just ci 863ad5a8f2be2ad333e42bc0279c19ca0cf6a5c4
```

`just ci` runs `quest check` and `admin/bench-report render --check`. It does not run `admin/prove bytes`.

```sh
nix develop .#hol-light --command admin/prove bytes
quest check
quest check --base 863ad5a8f2be2ad333e42bc0279c19ca0cf6a5c4
```

After an `os` or proof-text edit:

```sh
nix develop --command admin/bench-report render
```

`prove.yml` runs `admin/prove bytes` on a pull request that changes `admin/prove` or `admin/prove-bytes`. A `verified.toml`-only change does not start that workflow; run `bytes` locally anyway. The workflow stays on Linux until someone adds a macOS job. Adding one is optional and is not what makes the quest done.

A benchmark of an alignment change, on `kixtop`:

```sh
cargo bench -p rind-bench --bench sha2
cargo bench -p rind-bench --bench hmac
cargo bench -p rind-bench --bench hkdf
cargo bench -p rind-bench --bench ed25519
```

Time AES-GCM only if its Apple entry alignment changes: `--bench aes_gcm`. Compare against the same host's current numbers. The quest's bar is that the routine is not slower.

## Risks and open questions

- aarch64 Ed25519 is not in the quest's sentence and its proof uses the SHA-512 objects. Confirm with the maintainer that it is in scope. The done-when bar covers it once `bytes` checks those objects.
- #778 fixed P-256 by `os = "linux"` rather than by aligning the entry. This quest prefers alignment when the bytes then match and the bench holds. Ask before removing `os = "linux"` from those two rows.
- x86_64 has no macOS bench host. Ask whether an alignment-only x86_64 fix may land on the `llvm-mc` compare alone, or whether those rows stay `os = "linux"` until an Intel Mac can time them.
- `define_assert_relocs_from_elf` reads ELF. The HOL Light scripts keep checking the Linux object. The Apple side is a byte compare against that list, not a second HOL Light run on Mach-O.
- Apple `.s` uses `@PAGE` / `@PAGEOFF` where Linux uses `:lo12:`, and `.long` where Linux uses `.inst`. Those assemble to the same instruction or they do not; the object compare decides. Do not diff the text and stop.
- `asm_function` and `relocations` assume ELF. Budget a Mach-O reader before expecting `admin/prove bytes` to pass on an Apple object.
- Generated `.s` files say not to edit them by hand. An alignment that lives only in the `.s` disappears on the next `admin/import-aws-lc` or `admin/import-hacl`.
- `kixtop`'s published numbers are from `9e7f6a5a` (2026-11-07). A bench there is a new measurement, not a comparison against that commit's table unless the same machine reruns both.

## Upstream claim

https://github.com/kixel-ai/rind/pull/875
