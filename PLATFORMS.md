# Platforms

rind has assembly for `aarch64`, `x86_64`, and 32-bit `arm` from ARMv7 on, and
a portable Rust backend for every other architecture. CI tests Linux (glibc and musl), macOS, and Windows on `x86_64` and `aarch64`, Linux and Windows on
32-bit `x86`, iOS in the simulator on `aarch64`, Android on `aarch64`,
`armv7`, ARMv5TE, `x86_64`, and 32-bit `x86`, all but `x86_64` under qemu, and
Linux on `armv7`, ARMv6, big-endian `s390x`, `riscv64gc` (glibc and musl),
`loongarch64`, `powerpc64le`, and big-endian `powerpc64` and `powerpc` under
qemu. iOS devices' code is only built.

- The `aarch64` assembly backend requires NEON, which every aarch64 target
  with `std` enables at compile time; a build without it uses the portable
  backend. Where the CPU has the crypto
  extension (`aes`, `pmull`, and `sha2`), as the Raspberry Pi 5 and most
  aarch64 servers and phones do, AES, GHASH, SHA1, and SHA256 run on its
  instructions. Without it, as on the Raspberry Pi 4, CM4, and Zero 2 W, they
  run [aws-lc]'s NEON and scalar assembly instead (see
  [ALGORITHMS.md](ALGORITHMS.md)), `rind::cpu::has_aes_hardware()` is false, and
  rind-rustls and rind-dimpl prefer ChaCha20-Poly1305. Where the CPU has
  SVE2, as Armv9 cores from Neoverse N2 and Cortex-A710 on do,
  ChaCha20-Poly1305 runs [verified-garbage]'s SVE2 assembly, and aws-lc's
  NEON assembly otherwise. On Apple's platforms,
  secret-dependent code runs with data-independent timing (DIT), set and
  cleared in each call unless `rind::cpu::Dit::hold()` holds it across a batch
  of calls. rind sets no DIT on other aarch64 platforms, where Arm says it
  changes nothing on current cores.
- `x86_64` runs on every x86_64 CPU. It needs a target that enables SSE2,
  as every one with an OS does; `x86_64-unknown-none` and
  `x86_64-unknown-uefi` disable it and run the portable backend. Without `aes` and `pclmulqdq`, as on
  Core 2 and Nehalem, AES and GHASH run [aws-lc]'s SSSE3 assembly instead
  (see [ALGORITHMS.md](ALGORITHMS.md)), `rind::cpu::has_aes_hardware()` is false,
  and rind-rustls and rind-dimpl prefer ChaCha20-Poly1305. Without `avx2`, as
  on Sandy Bridge, Ivy Bridge, and AMD's Bulldozer and Jaguar cores,
  ChaCha20-Poly1305 runs [aws-lc]'s SSE4.1 assembly, ChaCha20, SHA1, and
  SHA256 its SSSE3 assembly, or for SHA its AVX assembly on Intel's cores,
  SHA-512 its scalar assembly on other vendors' cores,
  ML-KEM's and ML-DSA's arithmetic runs Rust ports of [mlkem-native]'s and
  [mldsa-native]'s portable C, but for ML-KEM-768's encapsulation, which runs
  [verified-garbage]'s assembly, and
  table lookups use SSE2 (see [ALGORITHMS.md](ALGORITHMS.md)). Without `sse4.1`,
  as on the first Core 2s and Atoms and AMD's Bobcat, ChaCha20 and Poly1305
  run in separate passes.
  Without `ssse3` either, as on Intel's CPUs before Core 2, AMD's before
  Bobcat and Bulldozer, and QEMU's default `qemu64` model, AES and GHASH run
  Rust ports of [aws-lc]'s constant-time SSE2 and integer C, SHA1 and SHA256
  its integer assembly, and ChaCha20 [HACL\*]'s verified rounds.
  Without `adx`, as on Haswell, AMD's cores before Zen, and virtual CPUs
  that hide it, [s2n-bignum]'s `_alt` routines replace those that use it,
  and [aws-lc]'s Montgomery multiplication replaces its Karatsuba routines
  for RSA; with `avx2` there, as on Haswell, RSA-2048 signing runs aws-lc's
  RSAZ exponentiation, and Ed25519 verification's multiplication a port of
  [curve25519-dalek]'s AVX2 backend. With `avx2` but without `sha`, as on
  Intel's cores before Ice Lake and AMD's before Zen, SLH-DSA's SHA-2
  parameter sets hash eight SHA-256 inputs at once with a port of the
  SPHINCS+ team's AVX2 code. With `avx512ifma`, as on Ice Lake,
  Sapphire Rapids, and AMD's Zen 4 and 5, RSA-2048 and 4096 signing and
  the public operation of 2048-, 3072-, and 4096-bit moduli with
  e = 65537 run [verified-garbage]'s routines, and RSA-3072 signing too with `avx512fp16`, as on Intel's
  since Sapphire Rapids, and aws-lc's dual AVX-512 RSAZ without it, as
  for the 3969- to 4032-bit keys VG's CRT does not take.
- 32-bit `arm` from ARMv7 on (tested on `armv7-unknown-linux-gnueabihf` and
  `armv7-linux-androideabi`) runs portable Rust instead, mostly from
  [libcrux] (see [ALGORITHMS.md](ALGORITHMS.md)), and needs no CPU features. RSA's
  Montgomery multiplication runs [aws-lc]'s assembly, with NEON where the CPU
  has it. Where
  the CPU has the ARMv8 crypto extension, as most 32-bit Android devices do,
  AES, GHASH, SHA1, and SHA256 run [aws-lc]'s assembly for it instead.
  Without it, `rind::cpu::has_aes_hardware()` is false, and rind-rustls and
  rind-dimpl prefer ChaCha20-Poly1305, which is faster there: ChaCha20 runs
  aws-lc's assembly, and so does Poly1305 where the CPU has NEON. SHA-384,
  SHA-512, and SHA-512/256 always run aws-lc's assembly, with NEON where the
  CPU has it, as do SHA-1 and SHA-256 without the crypto extension, and with
  NEON, X25519's shared secret runs [BoringSSL]'s assembly. SHA-3's, ML-KEM's,
  and ML-DSA's Keccak-f runs [OpenSSL]'s assembly, on NEON where the CPU has it.
  That assembly is A32 on every target, but `armv7-linux-androideabi` and
  the `thumbv7` targets build Rust as Thumb-2, the inline assembly of the
  constant-time compares included, so the compares' proofs (see
  [proofs/README.md](proofs/README.md)) cover only targets that build A32,
  such as `armv7-unknown-linux-gnueabihf`.

- Thumb-only M-profile targets (`thumbv6m-none-eabi`, `thumbv7em-none-eabihf`)
  and `riscv32imc-unknown-none-elf` build the portable backend; M-profile has
  no A32 and no NEON for the arm assembly. Where the target has no
  compare-and-swap (`thumbv6m`, `riscv32imc`), the reuse cache keeps nothing, so
  each use builds its value again; that is correct on any number of cores and
  interrupt handlers and needs no critical section.

- Builds with `-Z cf-protection=branch` or `-Z branch-protection=bti`, both
  unstable, are unsupported: rind calls aws-lc's x86_64 and aarch64 routines
  through function pointers, and their text, as rind imports it, holds no
  `endbr64` or `bti` landing pad. `admin/import-aws-lc` should keep aws-lc's
  markers once either flag stabilizes.

- Every other architecture, big-endian `aarch64` and `arm`, whose assembly
  assumes little-endian, and `arm` before ARMv7, which rind's ARMv7 assembly
  does not run on, run the portable backend: what 32-bit `arm` runs without
  NEON and the crypto extension, with portable Rust in place of the assembly
  `arm` always runs (see [ALGORITHMS.md](ALGORITHMS.md)). It needs no CPU
  features, `rind::cpu::has_aes_hardware()` is false, and rind-rustls and
  rind-dimpl prefer ChaCha20-Poly1305. Stable Rust shows a build script an
  ARM target's version only in its triple, so `arm-unknown-linux-gnueabihf`
  runs the portable backend even when built for a newer core. CI tests it on
  32-bit `x86` (`i686`), and under qemu on big-endian `s390x`, on `riscv64gc`
  (scalar only: rind uses neither the vector nor the scalar crypto
  extensions), on `loongarch64`, on `arm-unknown-linux-gnueabi` and
  `arm-unknown-linux-gnueabihf` on qemu's ARMv6 core (the ARM1176 of the
  Raspberry Pi 1 and Zero), on `arm-linux-androideabi`, which Rust builds for
  ARMv5TE, on `powerpc64le` and big-endian `powerpc64` and `powerpc` Linux,
  and on `x86_64`,
  where `--cfg rind_portable` forces it. `just ci` also compiles the library
  for `wasm32-wasip2` and `wasm32-unknown-unknown`
  when a change touches rind, the workspace manifest or lockfile, or the
  flake, and `just gate` always does. It compiles every published adapter
  for both, and rind-rustls's and rind-ring's tests for `wasm32-wasip2`, when
  a change touches an adapter, rind's manifest, the workspace manifest or
  lockfile, or the flake. `wasm32-unknown-unknown` enables `getrandom/wasm_js`
  for JavaScript randomness, as rind-ring's `wasm32_unknown_unknown_js` does
  for a ring caller; the WASI target uses its system random source. There the
  adapters' upstreams need what they need with any backend, which
  [admin/wasm-fixture](admin/wasm-fixture/Cargo.toml) adds: rustls's clock
  (`rustls-pki-types/web`) and the random sources of jsonwebtoken and str0m.
  The nightly `build.yml` runs rind's vector tests and rind-rustls's and
  rind-ring's tests on `wasm32-wasip2` under wasmtime (`just wasm`), without
  the differential tests, since aws-lc does not build for wasm; Ed25519's CCTV
  vectors and the expanded ML-DSA wipe check run against data recorded from
  aws-lc instead, and the adapters' handshakes run rind against itself. `wasm32-unknown-unknown` stays
  compile-only: its tests need a JavaScript host. Constant time is unchecked on
  wasm: ctgrind and the trace checks inspect native code, and a wasm engine
  compiles rind again, so its JIT may turn a select into a branch.
  Bare-metal targets (`target_os = "none"`) build the library without std, on
  `alloc`: the program supplies a global allocator and a getrandom backend.
  `just check` lints them in debug and release (`just bare-metal`) whenever a
  change reaches the portable or x86_64 backend: `thumbv6m-none-eabi` and
  `riscv32imc-unknown-none-elf`, which lack compare-and-swap and so keep no
  reuse cache, `thumbv7em-none-eabihf`, `armv7a-none-eabi`,
  `armv7r-none-eabihf`, `aarch64-unknown-none`,
  `aarch64-unknown-none-softfloat`, and `x86_64-unknown-none`. Every one but
  `x86_64-unknown-none` runs the portable backend: the aarch64 and 32-bit ARM
  assembly loads and stores unaligned words, which these strict-align targets
  fault on when the MMU is off or alignment checking is on.
  `x86_64-unknown-none` is soft-float and does not enable SSE2, so it stays on
  the portable backend, which leaves out `stmxcsr` (that raises `#UD` when
  `CR4.OSFXSR` is clear), and needs `--cfg curve25519_dalek_backend="serial"`
  or `"fiat"`, since dalek's default `simd` backend does not compile there.
  Built with `-C target-feature=+sse,+sse2,-soft-float`, it runs the x86_64
  backend, which reads CPUID; the lint builds that too, so its `global_asm`
  is assembled. SSE2 alone leaves soft-float set, and LLVM then aborts while
  splitting vector results; rustc warns that clearing soft-float this way
  will become an error
  ([rust-lang/rust#116344](https://github.com/rust-lang/rust/issues/116344)).
  AVX, AVX2, SHA512, VAES, VPCLMULQDQ, and AVX-512 run only when the build
  enables those target features, since XCR0 does not show that an interrupt
  saves YMM or ZMM. curve25519-dalek follows the same opt-in: its default on
  x86_64 is the simd backend, or avx512 when `avx512ifma` and `avx512vl` are
  enabled, and cpufeatures reports AVX2 and AVX-512 on this os only when they
  are target features. An explicit `simd` or `avx512` cfg selects the same
  code. `Dit::hold` does nothing on these targets: there is no thread-local
  count, and these backends set no CPU state there.
  The ESP32's Xtensa targets are tier 3, on Espressif's toolchain, so they
  are not part of that Nix lint. They use Espressif's 1.98.1.0, the release of
  the dev shell's rustc, since 1.97's Clippy does not know every lint rind
  names. `just xtensa` and `.github/workflows/xtensa.yml`
  clippy `xtensa-esp32-none-elf`, `xtensa-esp32s2-none-elf` (no compare-and-swap),
  and `xtensa-esp32s3-none-elf` the same four ways, check the ESP-IDF library
  (`xtensa-esp32s3-espidf`, which has std and getrandom's own backend) the
  same four ways, and check `rind-bench`'s bench targets there. Those
  benches are empty programs on Xtensa: criterion does not build against
  ESP-IDF's libc, and ring and OpenSSL have no Xtensa port, so those paths
  are `cfg`'d out. The check compiles the empty programs. A name inside that
  `cfg` is not typechecked. None of these targets runs a test or a
  constant-time check.
  RSA and the NIST curves run on 64-bit limbs on 64-bit targets and on
  `wasm32` built with `-C target-feature=+wide-arithmetic` (stable from Rust
  1.101), whose 128-bit products take one or two multiply instructions, and
  on 32-bit limbs elsewhere, where a 128-bit product would be a library call.

A backend requires only what its target enables at compile time, so rind runs
on every CPU its target does; every other feature only picks a faster path.

rind is `no_std` with `alloc`, so a target without `std` builds it, given a
global allocator. CI builds it for `x86_64-unknown-none`,
`aarch64-unknown-none`, and `armv7a-none-eabi`. Without an OS:

- rind draws random bytes from [getrandom], which has no source there until
  the caller supplies one: pass `--cfg getrandom_backend="custom"` to every
  crate, through `RUSTFLAGS` or the target's `rustflags` in
  `.cargo/config.toml` rather than `cargo rustc`, and define
  `__getrandom_v03_custom` in the application, as getrandom's documentation
  says.
- The x86_64 backend, which a target needs SSE2 for (`x86_64-unknown-none`
  runs the portable one), reads `cpuid` and XCR0 itself, as `std` does, so it
  takes a vector path only where the CPU has it and XCR0 says its registers
  are saved. It detects once, at its first call, for every core and every
  later call. So without a kernel, before that call the firmware must enable
  every vector state the target enables at compile time, and the state XCR0
  then enables must stay enabled; every core that runs rind must report the
  same features and XCR0; and the code that switches contexts must save
  every state XCR0 enables (or, where the target leaves AVX off, XCR0's AVX
  bit can stay clear throughout).
- aarch64 cannot ask without an OS, so it runs what the target enables at
  compile time: `-C target-feature=+aes,+sha2` turns on its crypto extension
  paths, `+sha3` those that use the SHA3 extension, such as SHA-512's
  (Keccak-f1600 runs on it only on Apple's cores, so not here), and `+sve2`
  the SVE2 ChaCha20-Poly1305. 32-bit `arm` asks only Linux and Android, so
  elsewhere it runs the code for a core with neither NEON nor the crypto
  extension, whatever the target enables.
- curve25519-dalek, which the portable backend runs X25519 and Ed25519 on,
  compiles its AVX2 backend on every x86_64 target, which LLVM fails to do
  where SSE is off, as on `x86_64-unknown-none` and `x86_64-unknown-uefi`
  ([curve25519-dalek#601]): build with
  `--cfg curve25519_dalek_backend="serial"` there, as UPSTREAM.md's
  "curve25519-dalek cannot compile without SSE" says.
- The aarch64 and `arm` assembly makes unaligned loads and stores and runs
  vector instructions, so it needs what an OS sets up for its code: the MMU
  on, buffers in Normal memory, alignment checking off (SCTLR.A clear), and
  Advanced SIMD, and SVE in a `+sve2` build, untrapped at every exception
  level that runs rind. The `*-none` targets
  build Rust with `strict-align` for code that runs before that.
- `RIND_CPU_DISABLE_*` does nothing, and `rind::cpu::Dit::hold()` holds
  nothing, since rind sets DIT only on Apple's platforms.

[rind-fips](rind-fips/README.md)'s FIPS 140-3 module builds only for glibc
Linux on `x86_64` and `aarch64`, and runs only the fastest paths there: on
`x86_64` it requires `aes`, `pclmulqdq`, `ssse3`, `sse4.1`, `popcnt`,
`movbe`, `avx`, `avx2`, `bmi1`, `bmi2`, and `adx`, as on Broadwell, Zen, and
later cores, and on `aarch64` the crypto extension. It refuses to load on a
CPU without them, naming the first missing, so each path it can take gets its
own ACVP run ([rind-acvp](rind-acvp/README.md)) and no other path is in it.

rind's secret-dependent code divides no secret and does no floating-point
arithmetic on any architecture, as `admin/ct-vartime` checks, but it multiplies
secrets, so it runs in constant time only where the integer multiplier does.
Poly1305 is the exception a bullet names. rind has no masked multiply for the
other secret products on the cores whose multiplier finishes early for some
operands, so it is not constant-time on them:

- `aarch64`: Arm's Cortex-A53 (Raspberry Pi 3 and Zero 2 W), whose 64-bit
  multiply takes a cycle longer when both operands exceed 32 bits, as measured
  on a Raspberry Pi 3 ([Gu and Shacham] 2.1). Arm's A53 manual documents no
  such variation. The same likely holds for `umull` and `smull` on 32-bit
  `arm` built for an A53, which no one has measured.
- 32-bit `powerpc`: the 603e, 604e, 750 (G3), 7400 and 7410 (G4), 7441
  through 7457 (G4), and e300c1, each of whose `mullw`, `mulhw`, and `mulhwu`
  take fewer cycles when the top bits of an operand are all zeros or all ones
  ([MPC603EUM] Table 6-4, [MPC604EUM] 6.7, [MPC750UM] Table 6-6,
  [MPC7410UM] Table 6-6, [MPC7450UM] Table 6-5, [e300coreRM] Table 7-4). The
  e300c2 through c4, e500v1 and v2, and e500mc multiply in fixed time
  ([e300coreRM] Table 7-4, [E500CORERM] Table 4-6, [E500MCRM] Table 10-2).
  Poly1305 on 32-bit `powerpc` uses that widening multiply. On
  `powerpc-unknown-linux-gnu` it lowers to `mulhwu` and `mullw`, and a
  16-bit half lowers to `mullw` after the top half is cleared. `rind_mul16`
  is not set: BearSSL records both that 32-bit product and the 64-bit
  product as not constant time on the 603e and the 7xx ([BearSSL ctmul]),
  and this tree has not checked a multiply that holds the early exit off.
- 32-bit `mips`: the MIPS32 4Km's multiplier is 32-by-16 bits and finishes
  early, so a 32x32 product varies by one cycle ([eprint 2009/538]).
  Poly1305 uses the plain widening multiply. `rind_mul16` is not set. Rust
  1.98.1 ships no prebuilt MIPS standard library, so the code a `mips`
  target generates was not checked, and a 16-bit half was not assumed to
  be one fixed-time digit on every core that implements `multu`.
- 64-bit `powerpc64`: NXP's e6500, whose 64-bit `mulld` and `mulhd` take 4 to
  7 cycles by the width of their operands ([E6500RM] Table 10-2). Its
  predecessor the e5500 likely does too, but its manual is not public.
  POWER8 and POWER9, the only cores `powerpc64le` runs on that rind has
  documents for, list one multiply latency ([POWER8 UM] Table 10-16, [POWER9 UM]
  Table A-1). Neither the PowerPC 970 (G5) nor POWER10 has a public multiply
  timing rind could check.
- `riscv64gc`: T-Head's C906 (Allwinner D1, Sophgo CV1800B), whose open RTL
  iterates a 64-bit `mul` or `mulh` when an operand's high half is significant
  ([openc906] `aq_iu_mul.v`), and Rocket cores built with `mulEarlyOut`, as
  rocket-chip's big and huge core configurations are ([rocket-chip]). A core
  with the Zkt extension, which the RVA22 and RVA23 profiles require, such as
  SpacemiT's X60, guarantees its multiplies' timing ([Zkt]), and SiFive's U54
  and U74 and T-Head's C910 and C920 document a fixed latency.
- `riscv32` without a multiply instruction, such as
  `riscv32i-unknown-none-elf` and `riscv32e-unknown-none-elf`: there is no
  `mul`, so the compiler lowers a 32-bit `wrapping_mul` to `__mulsi3` and a
  32x32->64 product to `__muldi3`, and those routines' iterations follow the
  bits of an operand. Poly1305 builds each 16-bit half with sixteen masked
  shifts and adds. Zmmul (`mul` and `mulhu`, no divide) is a multiplier:
  Poly1305 keeps the widening multiply, and the shift-and-add does not run.
  The rest of rind's secret arithmetic on a target with no multiply
  instruction still calls `__mulsi3` or `__muldi3`.
- `riscv64` without the M extension and without Zmmul: there is no `mul`.
  Poly1305 stays on 64-bit limbs, so each 64x64->128 product is a call to
  `__multi3` on the secret limbs. `rind_mul16` does not apply to that width.
  The build warns. Zmmul is a multiplier, and then those products are `mul`
  and `mulhu`. The rest of rind's secret arithmetic on a target with no
  multiply instruction still calls `__multi3`.
- `s390x`: IBM publishes no instruction timing for IBM Z, so rind cannot say.
- 32-bit `arm` before ARMv7: Intel's XScale (ARMv5TE), whose `mul`, `umull`,
  and `smull` terminate early by the top bits of their second operand
  ([XScale] Table 10-6), and ARMv4T's ARM7TDMI and ARM9TDMI ([BearSSL ctmul]).
  ARMv6's ARM1176 does not terminate early ([ARM1176 TRM] Table 3-46), nor does
  the ARM926EJ-S. On the ARMv4T and ARMv5TE triples, and on a custom target
  whose triple, `llvm-target`, or features name `v4t` or `v5te`, Poly1305
  sets bit 31 of each 16-bit half before multiplying, which misses every early-out row in
  that table, so the long path is taken whatever the secret is and whichever
  operand the compiler picks. The ARM926EJ-S shares those triples and does
  not end early, so it pays that long path; its speed was not measured. The
  rest of rind's secret arithmetic on 32-bit limbs still takes whole products.
- 32-bit `arm` M-profile: Arm's Cortex-M3, whose `umull`, `smull`, `umlal`,
  and `smlal` end early "depending on the size of the source values" ([Cortex-M3
  TRM] Table 3-1), as when an operand fits in 16 bits, is
  zero, or is a power of two ([BearSSL ctmul]). On its target,
  `thumbv7m-none-eabi`, and on `thumbv6m-none-eabi` and
  `thumbv8m.base-none-eabi`, whose cores have no `umull`, Poly1305 builds
  each product from 32x32->32-bit multiplies of 16-bit halves, which those
  cores do in one fixed time, so ChaCha20-Poly1305's MAC is constant time
  there. The rest of rind's secret arithmetic on 32-bit limbs still takes
  whole 32x32->64-bit products. The Cortex-M4's `umull` takes one cycle
  ([Cortex-M4 TRM] Table 3-1).
- `x86_64` and 32-bit `x86`: VIA's Nano 2000 series ([BearSSL ctmul]). Intel
  lists `mul` and `imul` as data-independent-time ([Intel DOIT]).

Intel guarantees the timing of the instructions it lists as data-independent
([Intel DOIT]) only on two conditions:

- On processors that enumerate DOITM, those from Ice Lake and Gracemont on
  with current microcode, only while the operating system sets it in
  `IA32_UARCH_MISC_CTL`, which user code cannot. A processor that does not
  enumerate it with current microcode behaves as if it were set, and an SGX
  enclave on one that does runs with it set whatever the OS does
  ([Intel DOITM]). Linux does not set it, as of 7.4, nor does KVM pass it to
  guests, and rind knows of no other kernel that does. Intel's list leaves out
  the `VSHA512` instructions, which SHA-384 and SHA-512 run where the CPU has
  them, as from Arrow Lake and Lunar Lake on.
- On Intel processors that do not report `MCDT_NO`, such as its Core processors
  from Skylake to Alder Lake, only while MXCSR holds `0x1FBF`: otherwise some
  vector integer multiplies, such as `vpmuludq` and `vpmullw`, may take a cycle
  longer for some values ([Intel MCDT]), and SGX enclaves are no exception.
  rind loads `0x1FBF` around its x86_64 ML-KEM, ML-DSA, RSA exponentiation
  with AVX2 or AVX-512, and Ed25519 verification with AVX2 but without ADX,
  and around every call on 32-bit `x86`, whose compiled arithmetic may use
  them anywhere, then
  restores the caller's MXCSR. On the x86_64 backend, `admin/ct-vartime`
  checks that nothing rind exports reaches one except through a function that
  enters the mitigation. It counts all of such a function as covered, so each
  enters first, holds it to its end, and never inlines into its caller. On
  32-bit `x86` and the portable backend, coverage rests on every call's
  `Entry`, which the scan does not check. aws-lc and BoringSSL do not
  mitigate this.

[COMPATIBILITY.md](COMPATIBILITY.md) lists the features of each Intel CPU
family since 2004, and of some AMD cores.

[s2n-bignum]: https://github.com/awslabs/s2n-bignum
[getrandom]: https://docs.rs/getrandom
[curve25519-dalek#601]: https://github.com/dalek-cryptography/curve25519-dalek/issues/601
[curve25519-dalek]: https://github.com/dalek-cryptography/curve25519-dalek
[HACL\*]: https://github.com/hacl-star/hacl-star
[mlkem-native]: https://github.com/pq-code-package/mlkem-native
[verified-garbage]: https://github.com/pyca/verified-garbage
[mldsa-native]: https://github.com/pq-code-package/mldsa-native
[libcrux]: https://github.com/cryspen/libcrux
[aws-lc]: https://github.com/aws/aws-lc
[BoringSSL]: https://boringssl.googlesource.com/boringssl
[OpenSSL]: https://github.com/openssl/openssl
[MPC603EUM]: https://www.nxp.com/docs/en/reference-manual/MPC603EUM.pdf
[MPC604EUM]: https://www.nxp.com/docs/en/reference-manual/MPC604EUM.pdf
[MPC750UM]: https://www.nxp.com/docs/en/reference-manual/MPC750UM.pdf
[MPC7410UM]: https://www.nxp.com/docs/en/reference-manual/MPC7410UM.pdf
[MPC7450UM]: https://www.nxp.com/docs/en/reference-manual/MPC7450UM.pdf
[e300coreRM]: https://www.nxp.com/docs/en/reference-manual/e300coreRM.pdf
[E500CORERM]: https://www.nxp.com/docs/en/reference-manual/E500CORERM.pdf
[E500MCRM]: https://www.nxp.com/docs/en/reference-manual/E500MCRM.pdf
[E6500RM]: https://www.nxp.com/docs/en/reference-manual/E6500RM.pdf
[POWER8 UM]: https://www.setphaserstostun.org/power8/POWER8_UM_v1.3_16MAR2016_pub.pdf
[POWER9 UM]: https://wiki.raptorcs.com/w/images/c/ce/POWER9_um_OpenPOWER_v21_10OCT2019_pub.pdf
[openc906]: https://github.com/T-head-Semi/openc906/blob/main/C906_RTL_FACTORY/gen_rtl/iu/rtl/aq_iu_mul.v
[rocket-chip]: https://github.com/chipsalliance/rocket-chip/blob/master/src/main/scala/rocket/Configs.scala
[Zkt]: https://docs.riscv.org/reference/isa/v20240411/unpriv/scalar-crypto.html
[XScale]: https://download.intel.com/design/intelxscale/27347302.pdf
[ARM1176 TRM]: https://developer.arm.com/documentation/ddi0301/h
[BearSSL ctmul]: https://www.bearssl.org/ctmul.html
[eprint 2009/538]: https://eprint.iacr.org/2009/538
[Cortex-M3 TRM]: https://developer.arm.com/documentation/ddi0337/h
[Cortex-M4 TRM]: https://developer.arm.com/documentation/ddi0439/b
[Gu and Shacham]: https://arxiv.org/abs/2311.14246
[Intel DOIT]: https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/resources/data-operand-independent-timing-instructions.html
[Intel DOITM]: https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/best-practices/data-operand-independent-timing-isa-guidance.html
[Intel MCDT]: https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/best-practices/mxcsr-configuration-dependent-timing.html
