# Upstream workarounds

Every place rind works around a bug or gap in a tool or dependency it doesn't own.
Each entry says what breaks, how to see it, the workaround and where it lives, whether it is reported upstream, and what lets the workaround go.
Each workaround's comment names its entry by heading, as [CONTRIBUTING.md](CONTRIBUTING.md#upstream) asks.

rind's own bugs, deliberate choices, and plain version pins are not listed.
"Reported" names an upstream issue rind filed or found; "no" means none is linked yet.

## Compilers and linkers

### rust-lld cannot link ELFv1

- **Breaks:** Rust links `powerpc64-unknown-linux-gnu` with its bundled rust-lld, which supports only ELFv2, so every link fails with `ABI version 1 is not supported` on glibc's `Scrt1.o`.
- **Reproduce:** `cargo build --target powerpc64-unknown-linux-gnu` of any binary with Rust 1.98 in `nix develop .#powerpc64`, without the flag below.
- **Workaround:** the `powerpc64` shell in `flake.nix` passes `-C link-arg=-fuse-ld=bfd`, which gcc obeys over rustc's own `-fuse-ld`, so GNU ld links. Found in [kixel-ai/rind#554](https://github.com/kixel-ai/rind/pull/554).
- **Reported:** no (rust-lang/rust, for the target's default linker).
- **Goes when:** Rust's powerpc64 target links with the system linker by default, or lld supports ELFv1.

### lld links BSS-PLT objects into a crashing ppc32 binary

- **Breaks:** nixpkgs' `pkgsCross.ppc32` gcc is built without `--enable-secureplt`, so its objects, its `crtbeginS.o` included, use the BSS PLT. lld supports only the Secure PLT, yet links those objects without error into a binary that crashes. GNU ld detects them and copes.
- **Reproduce:** `int main(void) { return 0; }` built with that gcc and `-fuse-ld=lld` crashes at exit under qemu-ppc, and runs with GNU ld.
- **Workaround:** the `powerpc` shell in `flake.nix` passes `-C link-arg=-fuse-ld=bfd`, as for powerpc64. Diagnosed in [kixel-ai/rind#580](https://github.com/kixel-ai/rind/pull/580).
- **Reported:** no (llvm/llvm-project, for lld to refuse BSS-PLT objects; NixOS/nixpkgs, for a Secure PLT gcc).
- **Goes when:** lld refuses or handles BSS-PLT objects and nixpkgs' ppc32 gcc emits the Secure PLT, or Rust links powerpc with the system linker.

### Build scripts cannot see ARM's `v7` target feature

- **Breaks:** stable Rust leaves the unstable `v7` feature out of `CARGO_CFG_TARGET_FEATURE`, so a build script cannot tell an ARMv7 target from an earlier one by feature.
- **Reproduce:** `rustc --print cfg --target armv7-unknown-linux-gnueabihf` on stable names no `v7`, which is what a build script sees.
- **Workaround:** `rind/build.rs` reads the version from the target triple.
- **Reported:** no.
- **Goes when:** the `v7` target feature is stable.

### No AddressSanitizer for 32-bit ARM Linux

- **Breaks:** rustc has no AddressSanitizer for `armv7-unknown-linux-gnueabihf`.
- **Workaround:** `fuzz.yml`'s armv7 replay row runs with `sanitizer: none`.
- **Reported:** no.
- **Goes when:** rustc supports `-Zsanitizer=address` there.

## Constant-time analysis

### Valgrind hides ADX from `cpuid`

- **Breaks:** valgrind runs ADX instructions but clears ADX from the `cpuid` it reports, so `admin/ctgrind` would check only s2n-bignum's `_alt` routines.
- **Reproduce:** `is_x86_feature_detected!("adx")` prints `true` natively and `false` under valgrind on a CPU with ADX.
- **Workaround:** `admin/ctgrind` sets `VALGRIND_BUG_494162`, which `rind/src/low/x86_64/cpu.rs` reads to take the ADX routines anyway.
- **Reported:** [KDE bug 494162](https://bugs.kde.org/show_bug.cgi?id=494162).
- **Goes when:** the flake's valgrind reports ADX.

### Valgrind cannot run x86_64's newest extensions

- **Breaks:** valgrind (through 3.27) decodes no AVX-512, VAES, VPCLMULQDQ, or SHA instruction and hides them from `cpuid`, so ctgrind never reaches the code that uses them.
- **Workaround:** `admin/ct-sde` compares Intel SDE traces of those paths for two secrets, through the `ct_sde` tests (`rind/src/low/x86_64/ct_sde.rs`), in `ctgrind.yml`'s `x86_64-sde` job, all but AVX-512 ML-KEM, which samples only the public matrix. Unlike ctgrind it sees only addresses, not variable-time instructions.
- **Reported:** no.
- **Goes when:** valgrind decodes them and reports them in `cpuid`, and ctgrind runs on a host that has them; `admin/ct-sde` then duplicates ctgrind.

### Valgrind hides the ARM crypto extension and SHA3

- **Breaks:** valgrind passes `AT_HWCAP2` only to ppc64 programs (3.22 through 3.28), so the armv7 build never sees its ARMv8 crypto extension; on aarch64 it hides SHA3 and the SHA-512 instructions. ctgrind never reaches the code that uses them.
- **Reproduce:** `getauxval(AT_HWCAP2)` is nonzero natively and zero under an armhf valgrind on an arm64 host.
- **Workaround:** `admin/ct-qemu` and `admin/ct-qemu-plugin.c` compare qemu traces of those paths for two secrets, through the `ct_qemu` tests (`rind/src/low/arm/ct_qemu.rs`), in `ctgrind.yml`'s `armv7-qemu` and `aarch64-qemu` jobs.
- **Reported:** no.
- **Goes when:** valgrind passes `AT_HWCAP2` on ARM and runs SHA3 on aarch64.

### Memcheck blames a public flag on a secret carry

- **Breaks:** on armv7 without NEON, memcheck flags the `beq` at `sha512_block_data_order_nohw+460` in aws-lc's integer SHA-512, which reads only the Z flag of a `tst` on the public round-constant pointer. The `tst` keeps the carry of the secret `adds` before it, and memcheck counts that carry against the branch when a superblock boundary falls between them, which the caller's code layout decides.
- **Reproduce:** the `no-neon` armv7 ctgrind row with `--vex-guest-max-insns=1` flags it, along with every branch on a `tst` of a public value.
- **Workaround:** the `aws-lc-sha512-armv4-nohw-flags` suppression in `admin/ctgrind.supp`.
- **Reported:** no.
- **Goes when:** memcheck tracks the Z flag apart from the carry.

### Valgrind on ARM does not fault guard pages

- **Breaks:** under valgrind on ARM, reading a `PROT_NONE` guard page does not fault, so `low::guard_pages`'s `planted_over_read_faults` fails.
- **Workaround:** `rind/src/low/mod.rs` leaves the `low::guard_pages` tests out of `__ctgrind` builds; plain `cargo test` still runs them. Added in [kixel-ai/rind#607](https://github.com/kixel-ai/rind/pull/607).
- **Reported:** no.
- **Goes when:** valgrind faults the read on ARM, if the bounds tests are ever wanted under ctgrind.

### BINSEC cannot decode much of what rind runs

- **Breaks:** BINSEC 0.11.3 stops at instructions it cannot decode: on x86_64, AES-NI, VAES, the SHA512 instructions, and every EVEX encoding; on aarch64, the crypto extension's AES, PMULL, and SHA instructions, SHA3's, and the `msr` that sets DIT; on armv7, the NEON table lookups and the crypto extension.
- **Workaround:** `admin/ct-binsec`'s `UNDECODED` denies those features, leaving their paths to `admin/ctgrind`, `admin/ct-sde`, and `admin/ct-qemu`, and armv7 has no `binsec` row in `ctgrind.yml`.
- **Reported:** no.
- **Goes when:** a BINSEC release decodes each, feature by feature.

### BINSEC cannot decode instructions `admin/ct-binsec` stubs

- **Breaks:** BINSEC 0.11.3 stops with `uninterpreted` at these instructions rind's code or glibc runs: on x86_64, `stc` (`f9`), `clc` (`f8`), `movmskps` and VEX `vmovmskps`, `vinsertf128` (VEX.256 0F3A 18), `vpermpd` (VEX.256.W1 0F3A 01), `vmovshdup` (VEX F3 0F 16), and the `syscall` in glibc's `mprotect`; on aarch64, `mrs xN, tpidr_el0` (glibc's `malloc`), `tbl` with one to four table registers (8B and 16B), and `cnt` (8B and 16B).
- **Reproduce:** `admin/ct-binsec` with `STUBS` emptied stops at the first one its harnesses reach, such as `stc` in `ct_binsec_ecdh_p521` on x86_64 or `tbl` in `ct_binsec_aes` on aarch64.
- **Workaround:** `admin/ct-binsec`'s `STUBS` gives each its effect in BINSEC's script language, generated per encoding from objdump's disassembly of the test binary and glibc, since `replace opcode` matches exact bytes; `tbl`, a constant-time table lookup, becomes a shift of the whole table, which needs no branch. Its script makes `mprotect` succeed without its system call.
- **Reported:** no.
- **Goes when:** a BINSEC release decodes them, or `replace opcode` matches an encoding by mask, so one stub covers every encoding of an instruction.

### BINSEC cannot decode glibc's string functions

- **Breaks:** glibc picks `memcpy` and friends for the CPU, and BINSEC 0.11.3 cannot decode the `xtest` in its TSX `_rtm` variants, the EVEX encodings of its AVX-512 ones, or aarch64's SVE `memcpy`.
- **Workaround:** `admin/ct-binsec`'s `LIBC` replaces whichever `memcpy`, `memmove`, `memset`, `memcmp`, and `bcmp` glibc picked with byte loops, as valgrind replaces them. Added in [kixel-ai/rind#604](https://github.com/kixel-ai/rind/pull/604).
- **Reported:** no.
- **Goes when:** BINSEC decodes them; the byte loops then only shorten the search.

### gdb dumps a guarded thread stack empty

- **Breaks:** glibc marks a thread stack's guard pages with `MADV_GUARD_INSTALL`, inside the stack's own mapping, so gdb fails to read the mapping and its core dump holds the stack empty.
- **Reproduce:** `generate-core-file` in a thread of any Rust test on a kernel and glibc that install guard regions; BINSEC then finds the stack unmapped.
- **Workaround:** `admin/ct-binsec` calls `madvise(MADV_GUARD_REMOVE)` on the stack's mapping before dumping.
- **Reported:** no.
- **Goes when:** gdb's core dumps skip or read through guard regions.

## Proofs

### Aeneas cannot translate several kinds of Rust

- **Breaks:** Aeneas cannot translate function pointers, `&dyn` calls, `'static` and nested borrows, raw-pointer loads, atomics, and some standard-library impls, so the Rust that uses them stays untranslated.
- **Workaround:** `proofs/` models that Rust by hand, quote-checked against the source by `admin/prove`. [Its quest](/quest/m4/verified/aeneas-fn-pointers.md) lists each model, with the Aeneas issue that blocks it where one exists.
- **Reported:** per limitation, in that quest.
- **Goes when:** each limitation lifts, model by model.

### Aeneas emits a duplicate `markerCopyInst` field

- **Breaks:** Aeneas names both of `ZeroablePrimitive`'s `Copy` clauses, which `NonZeroU32::get` brings in, `markerCopyInst`, and Lean refuses the duplicate field.
- **Reproduce:** `admin/prove lean`'s KDF translation without the rename fails in `Kdf/Types.lean`.
- **Workaround:** `admin/prove` renames the second to `markerCopyInst1` with `sed`.
- **Reported:** no.
- **Goes when:** Aeneas names the clauses apart.

### Lean cannot compile P-384's comb as one literal

- **Breaks:** Lean cannot compile the Aeneas translation of P-384's precomputed comb when it is one array literal.
- **Workaround:** `admin/p384-precomp` emits each table as its own constant, which Aeneas translates to its own Lean definition.
- **Reported:** no.
- **Goes when:** Lean compiles the whole comb as one literal.

### s2n-bignum lacks instructions and specs rind's proofs use

- **Breaks:** s2n-bignum's HOL Light x86_64 model cannot decode some instructions of aws-lc's ChaCha20-Poly1305 and ChaCha20 routines, or the SHA extensions rind's SHA-256 blocks run, and its SHA-256 and SHA-512 specs are in pull requests not yet merged, so those routines cannot be proven on it.
- **Workaround:** rind forks s2n-bignum in `thirdparty/s2n-bignum` (maintainer, 2026-11-13, on [kixel-ai/rind#701](https://github.com/kixel-ai/rind/pull/701)). Each change, with its upstream pull request, is in [its `RIND.md`](/thirdparty/s2n-bignum/RIND.md), which `admin/regenerate` checks lists every file that differs from upstream's: the model additions of [awslabs/s2n-bignum#450](https://github.com/awslabs/s2n-bignum/pull/450), the SHA extensions among them, rind's own additions, both cosimulated against the CPU, and the specs of [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415) and [#420](https://github.com/awslabs/s2n-bignum/pull/420).
- **Reported:** found #415, #420, and #450, all open; rind's own additions are not offered, which needs the maintainer's approval ([kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- **Goes when:** s2n-bignum merges each change and the fork's base moves past it.

### dmtcp_command fails a checkpoint that succeeds

- **Breaks:** `dmtcp_command --kcheckpoint` sends a blocking checkpoint and then a checkpoint, which the coordinator refuses once the first has killed the computation, so DMTCP 4.1.1's command prints `Computation was checkpointed and killed.` and exits 2. It prints the same when the computation dies during the checkpoint, having written nothing.
- **Reproduce:** `dmtcp_launch --new-coordinator --port-file port sleep 100 &`, then `dmtcp_command --coord-port "$(<port)" --kcheckpoint; echo $?` prints 2 beside the checkpoint it wrote.
- **Workaround:** `admin/prove`'s `session_image` ignores the exit status and requires the checkpoint file once the computation has exited.
- **Reported:** no.
- **Goes when:** `dmtcp_command --kcheckpoint` exits 0 once it has checkpointed and killed the computation.

### Mathlib's cache unpacks a copy into each checkout

- **Breaks:** `lake exe cache get` decompresses all of Mathlib, about 6.7 GB, into each checkout's `proofs/.lake/packages`, and Lake unpacks Aeneas's release archive the same way, neither into Lake's artifact cache, so worktrees share none of it. Reservoir serves no Lake cache outputs for Mathlib's releases that `lake cache get` could fetch instead.
- **Reproduce:** `lake cache get --package=mathlib --repo=leanprover-community/mathlib4` in `proofs/` finds no outputs in 100 revisions.
- **Workaround:** `admin/prove` restores Mathlib and Aeneas from Lake's artifact cache with `lake build --no-build --no-cache` and falls back to Mathlib's cache and Aeneas's archive only when that misses, then puts both in Lake's cache for the next checkout.
- **Reported:** no.
- **Goes when:** Mathlib's cache and Lake's release archives unpack through Lake's artifact cache, or Reservoir serves Mathlib's outputs.

## Mutation testing

### cargo-mutants cannot see into `cfg_if!`

- **Breaks:** cargo-mutants finds no module declared inside a `cfg_if!` invocation, so it mutates none of that module's code.
- **Workaround:** `rind/src/low/mod.rs` declares the backend modules outside `cfg_if!`, and `rind/src/mid/mod.rs` swaps its portable modules with a `#[cfg]` pair and a plain `#[path]`, since cargo-mutants also ignores a `path` inside `cfg_attr`.
- **Reported:** no.
- **Goes when:** cargo-mutants expands `cfg_if!` and `cfg_attr`, or rind stops using them.

### cargo-mutants misses compound `cfg(test)`s

- **Breaks:** cargo-mutants skips code under a bare `#[cfg(test)]`, but not under one that also names an architecture, such as `cfg(all(test, rind_backend = "x86_64"))`, so it mutates test helpers.
- **Workaround:** `.cargo/mutants.toml` excludes `rind/src/low/tests.rs` by glob and `\btests::` by regex.
- **Reported:** no.
- **Goes when:** cargo-mutants treats any `cfg` that requires `test` as test-only.

## Emulators

### cross's i686 Android image cannot run its binaries natively

- **Breaks:** run natively in cross's `i686-linux-android` container, rind's test binaries die of `SIGSYS` before the first test.
- **Workaround:** `Cross.toml` leaves that target on cross's qemu runner, whose Atom N270 model serves the portable backend.
- **Reported:** no.
- **Goes when:** the image runs i686 binaries natively, as its x86_64 one does.

### Flutter's debug JIT crashes under the Android emulator's ARM translation

- **Breaks:** the x86_64 Android emulator runs armv7 apps through its ARM translation, in which Flutter's debug JIT crashes.
- **Workaround:** `rind-dart/integration/android-arm.sh` runs the armv7 integration test as a release build and reads its result from the test reporter's log, since release builds leave out `integration_test`'s plugin.
- **Reported:** no.
- **Goes when:** the debug JIT runs under the translation.

## Dependencies

### libcrux-platform calls `__cpuid` outside `unsafe`

- **Breaks:** libcrux-platform 0.0.4, which libcrux-aes pulled in, calls `__cpuid` outside `unsafe`, which compiles only since `__cpuid` became safe in Rust 1.94. rind dropped libcrux-aes with [kixel-ai/rind#613](https://github.com/kixel-ai/rind/pull/613), but README.md and PLATFORMS.md still state a 1.94 exception on 32-bit x86.
- **Workaround:** README.md and PLATFORMS.md state the exception, and CI checks i686 only on stable.
- **Reported:** [celabshq/libcrux#1646](https://github.com/celabshq/libcrux/issues/1646).
- **Goes when:** [the x86 quest](/quest/m2/adoption/targets/x86.md) checks i686 on the MSRV and drops the exception.

### aws-lc cannot deny 32-bit ARM features at run time

- **Breaks:** aws-lc reads `OPENSSL_armcap` to deny CPU features on aarch64, but its 32-bit ARM detection has no such variable.
- **Workaround:** `bench.yml`'s armv7 `no-crypto` row builds aws-lc with `-DOPENSSL_STATIC_ARMCAP -DOPENSSL_STATIC_ARMCAP_NEON`, fixing its capabilities to NEON alone.
- **Reported:** no.
- **Goes when:** aws-lc reads `OPENSSL_armcap` on 32-bit ARM.

### aws-lc-sys targets the SDK's iOS version

- **Breaks:** aws-lc-sys builds its C for the iOS SDK's own deployment target unless told otherwise, and that code then needs symbols missing at rustc's default iOS version, so the device tests fail to link.
- **Workaround:** `build.yml`'s iOS job exports `rustc --print deployment-target` before building.
- **Reported:** no.
- **Goes when:** aws-lc-sys builds for the deployment target rustc uses.

### nixpkgs' Rust crashes cargo-llvm-cov's tests

- **Breaks:** cargo-llvm-cov's tests build with nixpkgs' rustc, whose instrumented binaries crash on exit, so cache.nixos.org has no build of it.
- **Workaround:** `flake.nix`'s `coverage` shell overrides cargo-llvm-cov with `doCheck = false`; rind's coverage builds with the pinned toolchain, not nixpkgs'.
- **Reported:** no.
- **Goes when:** nixpkgs builds cargo-llvm-cov.

### nixpkgs' Lean cannot read Mathlib's cache

- **Breaks:** Mathlib's prebuilt cache is read by the `leantar` bundled with the Lean toolchain, which nixpkgs' Lean lacks.
- **Workaround:** `flake.nix`'s `prove` shell takes `elan`, which fetches the toolchain `proofs/lean-toolchain` names.
- **Reported:** no.
- **Goes when:** nixpkgs' Lean reads Mathlib's cache.

### nixpkgs marks release-plz broken on Darwin

- **Breaks:** nixpkgs marks release-plz broken on Darwin, so the default shell cannot evaluate with it there.
- **Workaround:** `flake.nix`'s default shell adds release-plz only off Darwin.
- **Reported:** no.
- **Goes when:** nixpkgs builds release-plz on Darwin.

## CI tools

### actionlint rejects `concurrency.queue`

- **Breaks:** actionlint 1.7.12 errors on `queue: max`, which GitHub's concurrency groups accept since May 2026, as `unexpected key "queue" for "concurrency" section`.
- **Reproduce:** `actionlint .github/workflows/mutants.yml` without the ignore below.
- **Workaround:** `.github/actionlint.yaml` ignores that error in `mutants.yml`.
- **Reported:** [rhysd/actionlint#657](https://github.com/rhysd/actionlint/issues/657), with a fix in [rhysd/actionlint#654](https://github.com/rhysd/actionlint/pull/654).
- **Goes when:** an actionlint release in nixpkgs accepts `queue`.

## CI runner images

### Ubuntu's AppArmor denies Intel SDE's sandbox

- **Breaks:** the flake's `sde` runs Intel's unmodified binaries in a bubblewrap sandbox, which needs the unprivileged user namespaces Ubuntu's AppArmor denies a program it has no profile for.
- **Workaround:** each job that runs `sde` (`coverage.yml`, `ctgrind.yml`, `fuzz.yml`, `x86-cpu.yml`) first sets `kernel.apparmor_restrict_unprivileged_userns=0`.
- **Reported:** no.
- **Goes when:** the runner image allows the Nix store's bubblewrap a user namespace.
