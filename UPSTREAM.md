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

### Rust 1.90's assembler cannot read verified-garbage's `.base64`

- **Breaks:** pyca/verified-garbage prints its x86_64 machine code as `.base64` directives, which LLVM's assembler reads only from LLVM 22 (Rust 1.95); Rust 1.94 (LLVM 21.1) and rind's 1.90 MSRV stop at the first one.
- **Reproduce:** a `naked_asm!` holding `.base64 "uAEAAADD"` builds on Rust 1.95 and fails at the directive on 1.94, as `nix shell --inputs-from . 'rust-overlay#rust_1_94_0'` runs it.
- **Workaround:** `admin/import-vg` writes each `.base64` line as `.byte` lines of the same bytes, so rind's copy assembles to verified-garbage's machine code. Found in [kixel-ai/rind#811](https://github.com/kixel-ai/rind/pull/811).
- **Reported:** no; verified-garbage requires Rust 1.95, so this is rind's MSRV, not its bug.
- **Goes when:** rind's MSRV reaches Rust 1.95.

### No AddressSanitizer for 32-bit ARM Linux

- **Breaks:** rustc has no AddressSanitizer for `armv7-unknown-linux-gnueabihf`.
- **Workaround:** `fuzz.yml`'s armv7 replay row runs with `sanitizer: none`.
- **Reported:** no.
- **Goes when:** rustc supports `-Zsanitizer=address` there.

### Cargo runs $CARGO_HOME/bin's subcommands before PATH's

- **Breaks:** Cargo looks up an external subcommand such as `cargo-fmt` or `cargo-clippy` in `$CARGO_HOME/bin` before `PATH`, unless that directory is itself on `PATH` ([the Cargo book](https://doc.rust-lang.org/cargo/reference/external-tools.html#custom-subcommands)). On a host with rustup there, `cargo fmt` and `cargo clippy` inside the dev shell run rustup's default toolchain, not the flake's, while `which cargo-fmt` names the flake's. A newer rustfmt then reformats files CI's accepts, and a toolchain without a cross target's standard library fails `check cross` with `can't find crate for core`.
- **Reproduce:** `nix develop --command cargo fmt --version` on a host whose `$CARGO_HOME/bin/cargo-fmt` is rustup's, with `$CARGO_HOME/bin` not on `PATH`, reports rustup's rustfmt; found on [#140](https://github.com/steelhead99x/rind/pull/140).
- **Workaround:** `sh/toolchain.sh`, which `sh/dispatch.sh` runs inside the dev shell before any check, stops unless `cargo fmt --version` and `cargo clippy --version` name the build `rustc --version` does.
- **Reported:** no.
- **Goes when:** Cargo prefers `PATH`'s subcommands, or the flake's shells put an empty `$CARGO_HOME/bin` ahead of a host's.

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

- **Breaks:** on armv7, memcheck flags a branch or predicated instruction that reads only the Z flag of a logical op on public values, such as a `tst` or `ands`, when that op keeps the carry of a secret `adds` before it and a superblock boundary falls between them, which code layout decides. It flags the `beq` at `sha512_block_data_order_nohw+460` in aws-lc's integer SHA-512 without NEON, which tests the public round-constant pointer. It flagged the portable P-384 scalar inverse's `step_by(4).rev()` loop, whose `ands r0, r0, #3` follows the inlined reduction of the secret, and whose `movweq` then poisons the loop counter and the table index. On x86_64, VEX builds `stc`'s flags from the previous op's, so s2n-bignum's `bignum_add_p521`, which begins `stc` then `adc`, returned an undefined sum of two defined inputs right after the generic backend's secret arithmetic in `low::generic::limb64::p521::tests::field_ops`.
- **Reproduce:** the `no-neon` armv7 ctgrind row with `--vex-guest-max-insns=1` flags the SHA-512 branch, along with every branch on a `tst` of a public value. At main's d0e8e97f1, `admin/ctgrind unit --target armv7-unknown-linux-gnueabihf --release -- high::ecdsa::tests::digest_signing_matches_message_signing` flags `fs_pow` at the default 50 instructions per superblock and at 30, and passes at 100. At 0470f9956 (kixel-ai/rind#817's first head), x86_64's `admin/ctgrind unit --release -- low::generic::limb64::p521::tests::field_ops` reports 2313 errors, and main passes it.
- **Workaround:** the `aws-lc-sha512-armv4-nohw-flags` suppression in `admin/ctgrind.supp`; the portable P-256 and P-384 scalar inverses count nibbles with a plain range, whose loop armv7 tests with `cmp`, which sets every flag. The generic backend's tests mark their reference results public before comparing.
- **Reported:** no.
- **Goes when:** memcheck tracks the Z flag apart from the carry.

### Valgrind cannot unwind std's frame-pointer entries on armv7

- **Breaks:** valgrind unwinds armv7 code through its `.ARM.exidx` entries, and can rebuild the stack pointer from `r7`, Thumb's frame pointer, but not from `r11`, ARM's (`readexidx.c`, 3.22 through 3.27). Rust's prebuilt std keeps frame pointers, so its entries begin `vsp = r11`. A debug build calls std's shared `<[u8]>::starts_with` rather than inlining it, so a memcheck stack in it stops there, and a suppression that names the caller never matches: rind-dimpl's `pem_signing` reported rustls-pki-types' PEM boundary test, which `rustls-pki-types-pem-line-compare` covers.
- **Reproduce:** at main's d0e8e97f1, on an arm64 host, `cargo test -p rind-dimpl --test ctgrind --features rind/__ctgrind --target armv7-unknown-linux-gnueabihf -- pem_signing` under `admin/ctgrind --run` reports `bcmp` called by `<[u8]>::starts_with` with no frame above it.
- **Workaround:** `admin/ctgrind` passes `--unw-stack-scan-thresh=3`, which recovers `rustls_pki_types::pem::read` from the stack when an unwind stops within three frames. Scanned frames below the first can be stale return addresses.
- **Reported:** no.
- **Goes when:** valgrind's EXIDX reader takes `vsp = r11`.

### Memcheck flags OpenSSL's name map on aarch64

- **Breaks:** nixpkgs' OpenSSL 3.5.9 on aarch64 branches on the bytes past a NUL in its own uninitialised stack buffers while it sets up a library context: `OPENSSL_strlcpy` under `provider_conf_params_internal` when `OSSL_LIB_CTX_load_config` loads the config, and under `OBJ_obj2txt` when `get_legacy_*_names` fills the name map. Those bytes hash into the map's buckets, so `ossl_namemap_name2num` and `namemap_add_name` report on every later lookup. x86_64's build of the same OpenSSL reports nothing. None of it touches a key.
- **Reproduce:** at main's 561555b3f, on an arm64 host, `admin/ctgrind adapters --release` reports 2945 errors from 32 contexts in `rind-openssl`'s `ctgrind` test, all in `libcrypto.so.3`'s setup.
- **Workaround:** the `openssl-*` suppressions in `admin/ctgrind.supp`, each naming libcrypto's setup frames, never the provider's.
- **Reported:** no.
- **Goes when:** nixpkgs' OpenSSL no longer reads those bytes on aarch64, or memcheck tracks them apart.

### Valgrind on ARM does not fault guard pages

- **Breaks:** under valgrind on ARM, reading a `PROT_NONE` guard page does not fault, so `low::guard_pages`'s `planted_over_read_faults` fails.
- **Workaround:** `rind/src/low/mod.rs` leaves the `low::guard_pages` tests out of `__ctgrind` builds; plain `cargo test` still runs them. Added in [kixel-ai/rind#607](https://github.com/kixel-ai/rind/pull/607).
- **Reported:** no.
- **Goes when:** valgrind faults the read on ARM, if the bounds tests are ever wanted under ctgrind.

### BINSEC cannot decode much of what rind runs

- **Breaks:** BINSEC 0.11.3 stops at instructions it cannot decode: on x86_64, AES-NI, VAES, the SHA512 instructions, and every EVEX encoding; on aarch64, the crypto extension's AES, PMULL, and SHA instructions, SHA3's, every SVE encoding, such as SVE2's `xar`, and the `msr` that sets DIT; on armv7, the NEON table lookups and the crypto extension.
- **Workaround:** `admin/ct-binsec`'s `UNDECODED` denies those features, leaving their paths to `admin/ctgrind`, `admin/ct-sde`, and `admin/ct-qemu`, and armv7 has no `binsec` row in `ctgrind.yml`.
- **Reported:** no.
- **Goes when:** a BINSEC release decodes each, feature by feature.

### BINSEC cannot decode instructions `admin/ct-binsec` stubs

- **Breaks:** BINSEC 0.11.3 stops with `uninterpreted` at these instructions rind's code or glibc runs: on x86_64, `stc` (`f9`), `clc` (`f8`), `movmskps` and VEX `vmovmskps`, `vinsertf128` (VEX.256 0F3A 18), `vpermpd` (VEX.256.W1 0F3A 01), `vmovshdup` (VEX F3 0F 16), `stmxcsr` and `ldmxcsr` (0F AE /3 and /2, which Intel's MXCSR mitigation runs on a CPU that needs it), and the `syscall` in glibc's `mprotect`; on aarch64, `mrs xN, tpidr_el0` (glibc's `malloc`), `tbl` with one to four table registers (8B and 16B), `cnt` (8B and 16B), and `fcsel` (s2n-bignum's narrow X25519).
- **Reproduce:** `admin/ct-binsec` with `STUBS` emptied stops at the first one its harnesses reach, such as `stc` in `ct_binsec_ecdh_p521` on x86_64 or `tbl` in `ct_binsec_aes` on aarch64.
- **Workaround:** `admin/ct-binsec`'s `STUBS` gives each its effect in BINSEC's script language, generated per encoding from objdump's disassembly of the test binary and glibc, since `replace opcode` matches exact bytes; `tbl`, a constant-time table lookup, becomes a shift of the whole table, which needs no branch, and `fcsel` becomes a flag mux into the scalar lane with the rest of the Q register zero; `stmxcsr` stores MXCSR's default, and `ldmxcsr` does nothing, since BINSEC models no floating-point state. Its script makes `mprotect` succeed without its system call.
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

### BINSEC stalls on some ML-KEM ciphertexts

- **Breaks:** `ct_binsec_mlkem*` decapsulates a ciphertext, and for about one in a hundred of them BINSEC 0.11.3 stops making progress inside `kpke_encrypt`'s re-encryption: it sends the solver no query and visits no more than a few hundred thousand instructions in 480 s, where the others finish in under ten seconds. `gdb` shows it inside `Term.sizeof`, building a term. A given ciphertext always stalls, so it is the input, not the runner, and swapping one half of a stalling ciphertext for another's makes it finish.
- **Reproduce:** run `admin/ct-binsec --timeout 60 ct_binsec_mlkem512` on the portable backend a few hundred times with a random `encaps()` message, as the check did before it pinned one.
- **Workaround:** the harness encapsulates a fixed message, so every run explores a ciphertext that finishes on every backend. Which ciphertexts stall moves with the compiled code: [kixel-ai/rind#870](https://github.com/kixel-ai/rind/pull/870)'s counted loops made the pinned `0x5a` message stall ML-KEM-768 on the portable backend, and `0x00` stall ML-KEM-1024, so the harness now pins `0x01`, which finishes every parameter set on x86_64 and portable in under ten seconds. A change that stalls the pinned message picks another, rather than raising the timeout.
- **Reported:** no.
- **Goes when:** BINSEC builds that term without the stall; the harness may then draw random messages again.

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

### Flutter's iOS simulator test run hangs when its log stream attaches late

- **Breaks:** `flutter test integration_test -d <simulator>` reads the app's Dart VM service URL from a `log stream` process it starts as it launches the app, and `log stream` drops what was logged before it attached, about two seconds after the launch. When the app logs the URL first, as it did in roughly one `dart-ios` run in four on stable 3.50.0, the tool waits for it forever: silent after `Xcode build done` until the job's timeout.
- **Reproduce:** run `flutter test integration_test -d <simulator> -v` on `rind-dart/integration` on a hosted `macos-latest` runner a few dozen times, with `xcrun simctl spawn <udid> log stream` running beside it. A hung run's verbose log ends at `Waiting for VM Service port to be available...`, and the simulator's log has the app's `The Dart VM service is listening on` line a fraction of a second before the `log` process's `Sending stream request to diagnosticd`; a passing run has them the other way round.
- **Workaround:** `build.yml`'s `dart-ios` job runs Flutter's beta channel, whose 3.51.0-0.1.pre has the fix. Diagnosed in [kixel-ai/rind#810](https://github.com/kixel-ai/rind/pull/810).
- **Reported:** [flutter/flutter#181771](https://github.com/flutter/flutter/issues/181771), fixed by [flutter/flutter#193142](https://github.com/flutter/flutter/pull/193142), which makes the tool wait for `log stream`'s first line before launching the app.
- **Goes when:** a stable Flutter release has that fix, and the job returns to `channel: stable`.

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

### curve25519-dalek cannot compile without SSE

- **Breaks:** curve25519-dalek compiles its AVX2 backend on every x86_64 target, choosing it or the serial one at run time, and LLVM fails to compile it where SSE is off, as on `x86_64-unknown-none` and `x86_64-unknown-uefi`.
- **Reproduce:** `cargo build -p rind --lib --target x86_64-unknown-none` with `RUSTFLAGS='--cfg getrandom_backend="custom"'`.
- **Workaround:** `sh/dispatch.sh`'s `no_std` builds pass `--cfg curve25519_dalek_backend="serial"` for `x86_64-unknown-none`, and [PLATFORMS.md](PLATFORMS.md) tells callers to do the same.
- **Reported:** [curve25519-dalek#601](https://github.com/dalek-cryptography/curve25519-dalek/issues/601).
- **Goes when:** curve25519-dalek falls back to its serial backend where the target lacks SSE.

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
