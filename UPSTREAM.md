# Upstream workarounds

Every upstream rind forks, and every place it works around a bug or gap in a tool or dependency it doesn't own.
Each entry says what breaks, how to see it, the workaround and where it lives, whether it is reported upstream, and what lets the workaround go.
Each workaround's comment names its entry by heading, as [CONTRIBUTING.md](CONTRIBUTING.md#upstream) asks.

rind's own bugs, deliberate choices, and plain version pins are not listed.
"Reported" names an upstream issue rind filed or found; "no" means none is linked yet.

## Forks

Each upstream rind changes, with where its fork is vendored and where the list of rind's changes to it lives, as [CONTRIBUTING.md](CONTRIBUTING.md#upstream) asks.

### s2n-bignum

- **Breaks:** s2n-bignum's HOL Light x86_64 model cannot decode some instructions of aws-lc's ChaCha20-Poly1305 and ChaCha20 routines, or the SHA extensions rind's SHA-256 blocks run, its SHA-256 and SHA-512 specs are in pull requests not yet merged, and it has no AArch32 model, so those routines and armv7's assembly cannot be proven on it.
- **Fork:** `thirdparty/s2n-bignum`, upstream's whole tree at the base its `RIND.md` names (maintainer, 2026-11-13, on [kixel-ai/rind#701](https://github.com/kixel-ai/rind/pull/701)).
- **Changes:** listed in [its `RIND.md`](/thirdparty/s2n-bignum/RIND.md), which `admin/regenerate` checks lists every file that differs from upstream's: the model additions of [awslabs/s2n-bignum#450](https://github.com/awslabs/s2n-bignum/pull/450), the SHA extensions among them, rind's own additions, both cosimulated against the CPU, rind's AArch32 model in `aarch32/`, cosimulated against qemu-arm, rind's ChaCha20-Poly1305 spec, and the specs of [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415) and [#420](https://github.com/awslabs/s2n-bignum/pull/420).
- **Offered:** no. #415, #420, and #450 are upstream's own open pull requests; rind's own changes need the maintainer's approval to post ([kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)), which [upstream-reports](/quest/m2/upstream-reports.md) asks for.
- **Goes when:** s2n-bignum merges each change and the fork's base moves past it.

## Compilers and linkers

### Clippy flags const thread-local initializers

- **Breaks:** Espressif Rust 1.98.1.0's `missing_const_for_thread_local` flags `DIT_GUARDS` in `rind/src/low/cpu.rs` and `HELD` in `rind/src/low/entry.rs` on `xtensa-esp32s3-espidf`, although both initializers are already `const` blocks.
- **Reproduce:** with that version installed as `esp`, run `cargo +esp clippy -Zbuild-std=std,panic_abort -p rind --lib --locked --target xtensa-esp32s3-espidf -- --deny warnings`.
- **Workaround:** `sh/bare-metal.sh` compiles the ESP-IDF library with `cargo check` in debug and release. Its bare-metal targets still run Clippy.
- **Reported:** [rust-lang/rust-clippy#17566](https://github.com/rust-lang/rust-clippy/issues/17566), the same false positive on targets without native thread-local support.
- **Goes when:** the pinned Espressif toolchain's Clippy accepts those const initializers, so the ESP-IDF row can run Clippy too.

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

### Clearing soft-float with -C target-feature will become an error

- **Breaks:** `x86_64-unknown-none` is soft-float and does not enable SSE2. The x86_64 backend's `xmm` operands need SSE2, and leaving `soft-float` set beside `+sse2` makes LLVM abort with `Do not know how to split the result of this operator!`. Passing `-C target-feature=-soft-float` is how the lint clears it, and rustc warns that clearing a feature this way will become a hard error.
- **Reproduce:** `cargo build -p rind --lib --target x86_64-unknown-none` with `RUSTFLAGS='--cfg getrandom_backend="custom" -C target-feature=+sse,+sse2'` on rustc 1.98.1 aborts in LLVM. Adding `-soft-float` builds, and prints the future-compat warning.
- **Workaround:** `sh/bare-metal.sh` passes `-C target-feature=+sse,+sse2,-soft-float` for that target. `--deny warnings` does not fail the warning.
- **Reported:** [rust-lang/rust#116344](https://github.com/rust-lang/rust/issues/116344).
- **Goes when:** `x86_64-unknown-none` enables SSE2 without soft-float, or rustc provides another way to clear soft-float that is not this warning.

### Build scripts cannot see ARM's `v7` target feature

- **Breaks:** stable Rust leaves the unstable `v7` feature out of `CARGO_CFG_TARGET_FEATURE`, so a build script cannot tell an ARMv7 target from an earlier one by feature.
- **Reproduce:** `rustc --print cfg --target armv7-unknown-linux-gnueabihf` on stable names no `v7`, which is what a build script sees.
- **Workaround:** `rind/build.rs` reads the version from the target triple. The manifest cannot, so it links the arm backend's libcrux crates when the target has 64-bit atomics, which every standard ARMv7-A and ARMv7-R triple has and no ARMv5TE or M-profile triple does. ARMv6 has them too and stays portable, so it builds those crates and does not call them. A custom ARMv7 target without 64-bit atomics stays portable and loses the NEON assembly.
- **Reported:** no.
- **Goes when:** the `v7` target feature is stable.

### Build scripts cannot see Zmmul or ARMv4T and ARMv5TE

- **Breaks:** Rust 1.98.1 does not put `zmmul` in `cfg(target_feature)`. It is not a Rust target feature: `-C target-feature=+zmmul` warns and still passes the name to LLVM, and `--print cfg` does not list it. `v5te` is unstable, so stable `--print cfg` omits it for `armv5te-unknown-linux-gnueabi` and for `-C target-feature=+v5te`. `v4t` is not a target feature; an `armv4t` target's cfg lists `soft-float` and not `v4t`. A build script that reads only `CARGO_CFG_TARGET_FEATURE` treats Zmmul as no multiplier and a custom ARMv5TE target as a later core.
- **Reproduce:** `rustc +1.98.1 --print cfg --target riscv32i-unknown-none-elf -C target-feature=+zmmul` warns and lists no `zmmul`. `rustc +1.98.1 --print cfg --target armv5te-unknown-linux-gnueabi` lists no `v5te`. With `RUSTC_BOOTSTRAP=1`, `rustc +1.98.1 -Z unstable-options --print cfg --target` a JSON whose `features` is `+v5te` and whose `llvm-target` is `arm-none-eabi` lists `target_feature="v5te"`. The same for an `armv4t-none-eabi` `llvm-target` lists no `v4t`.
- **Workaround:** `rind/build.rs` reads the triple. For the names stable cfg hides, it also reads `-C target-feature` from `CARGO_ENCODED_RUSTFLAGS` and a custom target JSON's `features` and `llvm-target`. Builtin `armv4t`, `armv5te`, and `arm-linux-androideabi` still come from the triple. Rust's unversioned `arm-unknown-linux-*` triples stay ARMv6.
- **Reported:** no.
- **Goes when:** `zmmul` and `v5te` are stable `target_feature` cfgs, and a custom target's architecture is visible the same way. `v4t` needs a cfg or the `llvm-target` string keeps naming it.

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

### Valgrind models only MXCSR's rounding mode

- **Breaks:** valgrind's x86_64 guest keeps only MXCSR's rounding mode, so `stmxcsr` reads `0x1F80` after `ldmxcsr 0x1FBF`, and the `low::mcdt` tests that read back Intel's MXCSR mitigation fail. The guard itself still loads and restores MXCSR there.
- **Reproduce:** `admin/ctgrind unit low::mcdt` fails `holds_and_restores` with `left: 8064, right: 8127`.
- **Workaround:** `rind/src/low/mcdt.rs` ignores those two tests in `__ctgrind` builds; plain `cargo test` and x86-cpu.yml's SDE rows still run them.
- **Reported:** no.
- **Goes when:** valgrind keeps MXCSR's other bits.

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

- **Breaks:** BINSEC 0.11.3 stops with `uninterpreted` at these instructions rind's code or glibc runs: on x86_64, `stc` (`f9`), `clc` (`f8`), `movmskps` and VEX `vmovmskps`, `vinsertf128` (VEX.256 0F3A 18), `vpermpd` (VEX.256.W1 0F3A 01), `vmovshdup` (VEX F3 0F 16), `stmxcsr` and `ldmxcsr` (0F AE /3 and /2, which Intel's MXCSR mitigation runs on a CPU that needs it), and the `syscall` in glibc's `mprotect`; on aarch64, `mrs xN, tpidr_el0` (glibc's `malloc`), `tbl` with one to four table registers (8B and 16B), and `cnt` (8B and 16B).
- **Reproduce:** `admin/ct-binsec` with `STUBS` emptied stops at the first one its harnesses reach, such as `stc` in `ct_binsec_ecdh_p521` on x86_64 or `tbl` in `ct_binsec_aes` on aarch64.
- **Workaround:** `admin/ct-binsec`'s `STUBS` gives each its effect in BINSEC's script language, generated per encoding from objdump's disassembly of the test binary and glibc, since `replace opcode` matches exact bytes; `tbl`, a constant-time table lookup, becomes a shift of the whole table, which needs no branch; `stmxcsr` stores MXCSR's default, and `ldmxcsr` does nothing, since BINSEC models no floating-point state. Its script makes `mprotect` succeed without its system call.
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

### Charon panics on HACL*'s unrolled SHA-2

- **Breaks:** libcrux-macros' `unroll_for!` unrolls the 64 or 80 rounds of libcrux-sha2's `sha256_update_nblocks` and `sha512_update_nblocks` into one body whose blocks nest past Charon's fixed `MAX_STACK_DEPTH` of 1024, and Charon panics rebuilding its control flow.
- **Reproduce:** add `--include 'libcrux_sha2::hacl::sha256_update_nblocks' --extract-opaque-bodies` to `admin/prove`'s portable pass and run `admin/prove lean`: Charon panics with "stack depth limit exceeded" in `transform/control_flow/ullbc_to_llbc.rs` translating `sha256_update`.
- **Workaround:** the portable pass leaves both functions opaque, as Charon leaves other crates' bodies, and `proofs/Rind/Portable/Hacl.lean` states each as an axiom restating HACL*'s F* theorem about it. Found in [kixel-ai/rind#649](https://github.com/kixel-ai/rind/pull/649).
- **Reported:** not yet; filing is approved, and [its quest](/quest/m4/verified/hacl-sha2-lean.md) holds the draft issue awaiting the maintainer's approval of its text.
- **Goes when:** Charon translates both, and that quest proves them in Lean.

### Lean cannot compile P-384's comb as one literal

- **Breaks:** Lean cannot compile the Aeneas translation of P-384's precomputed comb when it is one array literal.
- **Workaround:** `admin/p384-precomp` emits each table as its own constant, which Aeneas translates to its own Lean definition.
- **Reported:** no.
- **Goes when:** Lean compiles the whole comb as one literal.

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

### cargo-mutants matches `#[path]` with `..` literally

- **Breaks:** cargo-mutants 27.1.0, the version nixpkgs pins in `flake.lock`, records a module included by `#[path = "../generic/aes_nohw.rs"]` as `rind/src/low/portable/../generic/aes_nohw.rs` (and the `x86_64` twin). `--in-diff` compares that string to the Git path, which has no `..`. Nothing matches, and a diff that selects no mutants exits 0, so the portable campaign reports success without testing the change. The same gap hits every campaign, because `x86_64` includes that file through the same kind of path.
- **Reproduce:** `cargo mutants --list -p rind | grep /\.\./` prints the names, and `cargo mutants --list -p rind --in-diff` over a diff of `rind/src/low/generic/aes_nohw.rs` lists none of them; `admin/mutants --expand-diff-self-test` checks the rewrite. `SourceFile::load` in cargo-mutants 27.1.0 `src/source.rs` keeps a path whose `..` never climbs out of the tree, and `diff_filter` in `src/in_diff.rs` matches it with no normalization; `NoMutants` uses the success exit code.
- **Workaround:** `admin/mutants` copies each diff section onto those un-normalized names before passing `--in-diff`. Survivor aggregation still strips one `/<dir>/../` when it joins outcomes.
- **Reported:** no.
- **Goes when:** cargo-mutants normalizes `..` before matching a diff.

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

### LeakSanitizer deadlocks under Intel SDE

- **Breaks:** at exit, LeakSanitizer clones a thread that ptrace-stops the program's threads to scan them. Under SDE that tracer sometimes waits forever on a futex with the main thread stopped, so a replay that printed libFuzzer's `Done` never exits, and `fuzz.yml`'s SDE replays ran into their 60-minute timeout.
- **Reproduce:** replay any ASan fuzz target's corpus with `sde -dmr -- TARGET -runs=0 CORPUS` in `nix develop .#sde` a few dozen times; about one run in eight hangs, its main thread in `ptrace_stop` and traced by its own clone.
- **Workaround:** `sh/fuzz-replay.sh` sets `ASAN_OPTIONS=detect_leaks=0` for the `x86_64-sde` tiers; the native x86_64 fuzzing and replay still check leaks. Diagnosed in [kixel-ai/rind#743](https://github.com/kixel-ai/rind/pull/743).
- **Reported:** no (Intel SDE has no public tracker; LLVM documents that LeakSanitizer does not work under ptrace).
- **Goes when:** an SDE release runs LeakSanitizer's stop-the-world without hanging.

### Intel SDE aborts Go's `acvptool`

- **Breaks:** with `x86-cpu.yml`'s Diamond Rapids job running the offline ACVP test under `sde -dmr --` as its cargo runner, SDE followed the test into `acvptool`, a Go binary, and Pin's instrumentation of it aborted it with SIGABRT and no message, twice on GitHub's AMD runners, so the job failed before any set was answered.
- **Reproduce:** on an AMD x86_64 host in `nix develop .#sde`, run `CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER="sde -dmr --" cargo test -p rind-acvp --features module --release --test offline`. It has not reproduced on an Intel host (Core Ultra 7 270K), where all three CPU masks pass.
- **Workaround:** the job sets `RIND_ACVP_WRAPPER_RUNNER` instead, and `rind-acvp/tests/offline.rs`'s `wrapper` runs only `rind-acvp`, the module, under SDE; the test and `acvptool` run natively. Found in [kixel-ai/rind#789](https://github.com/kixel-ai/rind/pull/789).
- **Reported:** no (Intel SDE has no public tracker).
- **Goes when:** an SDE release after 9.53.0 runs Go binaries on AMD hosts. Keeping it costs no coverage, since only the module needs the emulated CPU.

## Dependencies

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

### blind-rsa-signatures 0.18 does not build on rsa 0.10.0

- **Breaks:** blind-rsa-signatures 0.18.0, the latest release, accepts `rsa` `^0.10.0-rc.18` but implements the release candidates' `PrivateKeyParts`, so it fails to compile against 0.10.0, the first release patched for RUSTSEC-2023-0071. A workspace holds one `rsa` 0.10, so rind-bench's 0.10.0 breaks rind's tests, which check blind RSA against it.
- **Reproduce:** `cargo check -p rind --tests` without the workspace's `[patch.crates-io]` entry for it.
- **Workaround:** rind forks it in `thirdparty/blind-rsa-signatures`, ported to `rsa` 0.10.0, each change listed in [its `RIND.md`](/thirdparty/blind-rsa-signatures/RIND.md).
- **Reported:** no; offering it needs the maintainer's approval, which [upstream-reports](/quest/m2/upstream-reports.md) asks for.
- **Goes when:** a blind-rsa-signatures release builds on `rsa` 0.10.0.

### nixpkgs' Lean cannot read Mathlib's cache

- **Breaks:** Mathlib's prebuilt cache is read by the `leantar` bundled with the Lean toolchain, which nixpkgs' Lean lacks.
- **Workaround:** `flake.nix`'s `prove` shell takes `elan`, which fetches the toolchain `proofs/lean-toolchain` names.
- **Reported:** no.
- **Goes when:** nixpkgs' Lean reads Mathlib's cache.

## CI tools

### actionlint rejects `concurrency.queue`

- **Breaks:** actionlint 1.7.12 errors on `queue: max`, which GitHub's concurrency groups accept since May 2026, as `unexpected key "queue" for "concurrency" section`.
- **Reproduce:** `actionlint .github/workflows/mutants.yml` without the ignore below.
- **Workaround:** `.github/actionlint.yaml` ignores that error in `mutants.yml` and `release.yml`.
- **Reported:** [rhysd/actionlint#657](https://github.com/rhysd/actionlint/issues/657), with a fix in [rhysd/actionlint#654](https://github.com/rhysd/actionlint/pull/654).
- **Goes when:** an actionlint release in nixpkgs accepts `queue`.

### acvptool sends ML-DSA's externalMu for the external interface

- **Breaks:** NIST's ML-DSA sigGen and sigVer sets give external-interface groups `externalMu: false`, and aws-lc's `acvptool` (through v5.11 and its `main`) forwards it to the module wrapper whatever the group's `signatureInterface`. A wrapper, aws-lc's own included, reads a present flag as the internal interface, so it signs and verifies the external interface's tests without their context and domain separation, and answers them wrongly.
- **Reproduce:** run an unpatched `acvptool -json` on `thirdparty/acvp/ML-DSA-sigGen-FIPS204.json` through `rind-acvp`: the external groups' signatures differ from the expected ones.
- **Workaround:** `flake.nix`'s `acvptool` forwards `externalMu` only for `signatureInterface: internal`, the convention aws-lc's module wrapper states. Found in [kixel-ai/rind#789](https://github.com/kixel-ai/rind/pull/789).
- **Reported:** no (aws/aws-lc).
- **Goes when:** an aws-lc release in nixpkgs forwards `externalMu` only for the internal interface.

### Dependabot's Cargo lockfile updates skip its cooldown

- **Breaks:** Dependabot pins the crate it bumps to a release older than its cooldown, but not the crates that release newly needs, which `cargo update` resolves to their newest compatible releases, however young. It does not pin a crate declared in `[workspace.dependencies]` either, so one would take its newest release too; rind declares none.
- **Workaround:** REVIEW.md has a Dependabot PR's reviewer run `sh/cooldown.sh`, which lists each release its `Cargo.lock` gains that is younger than the cooldown.
- **Reported:** [dependabot/dependabot-core#16428](https://github.com/dependabot/dependabot-core/issues/16428), for `[workspace.dependencies]`; no, for the crates a release newly needs.
- **Goes when:** Dependabot holds its whole lockfile update to the cooldown.

## CI runner images

### Ubuntu's AppArmor denies Intel SDE's sandbox

- **Breaks:** the flake's `sde` runs Intel's unmodified binaries in a bubblewrap sandbox, which needs the unprivileged user namespaces Ubuntu's AppArmor denies a program it has no profile for.
- **Workaround:** each job that runs `sde` (`coverage.yml`, `ctgrind.yml`, `fuzz.yml`, `x86-cpu.yml`) first sets `kernel.apparmor_restrict_unprivileged_userns=0`.
- **Reported:** no.
- **Goes when:** the runner image allows the Nix store's bubblewrap a user namespace.
