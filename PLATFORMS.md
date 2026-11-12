# Platforms

rind has assembly for `aarch64`, `x86_64`, and 32-bit `arm` from ARMv7 on, and
a portable Rust backend for every other architecture. CI tests Linux (glibc and
musl), macOS, and Windows on `x86_64` and `aarch64`, Linux and Windows on
`i686`, iOS in the simulator on `aarch64`, Android on `aarch64`,
`armv7`, ARMv5TE, `x86_64`, and `i686`, all but `x86_64` under qemu, and
Linux on `armv7`, ARMv6, big-endian `s390x`, `riscv64gc` (glibc and musl),
`loongarch64`, `powerpc64le`, and big-endian `powerpc64` and `powerpc` under
qemu. Those runs test `rind` and `rind-rustls`. The wasm runs below do
not: they build, and on `wasm32-wasip2` test, the `rind` library only.
iOS devices' code is only built, which is not a test, so a device target
is not covered. CI neither compiles nor tests big-endian `aarch64`,
big-endian `arm`, `i586`, `riscv32`, `sparc64`, or MIPS.
`rind/build.rs` would select the portable backend for each of them.
Stable Rust ships no MIPS standard library.

## Targets by triple

Each target triple CI builds, and what it checks there. "Tests" runs the
tests of `rind` and every adapter, `rind-rustls` included; "built" compiles
them without running; "compiled" builds the `rind` library alone. Constant
time is checked natively on `x86_64` and `aarch64` Linux and on `armv7`, as
[TESTING.md](TESTING.md) details; the other native-code rows run the same
Rust or assembly as one of those.

| Triple | CI | Crates | Constant time |
|---|---|---|---|
| `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu` | tests | all | ctgrind |
| `armv7-unknown-linux-gnueabihf` | tests, under qemu | all | ctgrind |
| `x86_64-unknown-linux-musl`, `aarch64-unknown-linux-musl` | tests | all | as the same architecture's Linux row |
| `x86_64-apple-darwin`, `aarch64-apple-darwin` | tests | all | as the same architecture's Linux row |
| `x86_64-pc-windows-msvc`, `aarch64-pc-windows-msvc`, `i686-pc-windows-msvc` | tests | all | as the same architecture's Linux row |
| `i686-unknown-linux-gnu` | tests | all | as the portable backend's |
| `aarch64-apple-ios-sim` | tests, in the simulator | all | as the same architecture's Linux row |
| `aarch64-apple-ios` | built | all | as the same architecture's Linux row |
| `aarch64-linux-android`, `armv7-linux-androideabi`, `x86_64-linux-android`, `i686-linux-android`, `arm-linux-androideabi` | tests, under qemu but `x86_64` | all | as the same architecture's Linux row |
| `arm-unknown-linux-gnueabi`, `arm-unknown-linux-gnueabihf` | tests, under qemu's ARM1176 | all | as the portable backend's |
| `s390x-unknown-linux-gnu`, `riscv64gc-unknown-linux-gnu`, `riscv64gc-unknown-linux-musl`, `loongarch64-unknown-linux-gnu`, `powerpc64le-unknown-linux-gnu`, `powerpc64-unknown-linux-gnu`, `powerpc-unknown-linux-gnu` | tests, under qemu | all | as the portable backend's |
| `wasm32-wasip2` | tests: the vector tests, nightly, under wasmtime | `rind` only | unchecked |
| `wasm32-unknown-unknown` | compiled | `rind` only | unchecked |

"As the portable backend's" means ctgrind's forced portable run on x86_64,
which checks the same Rust built for another architecture, not its machine
code. A triple not in this table is untested, even when a row differs from it
only in vendor, OS, or environment, such as `x86_64-pc-windows-gnu`,
`aarch64-pc-windows-gnullvm`, `x86_64-unknown-freebsd`, or
`armv7-unknown-linux-musleabihf`.

- `aarch64` requires the `neon` CPU feature. Where the CPU has the crypto
  extension (`aes`, `pmull`, and `sha2`), as the Raspberry Pi 5 and most
  aarch64 servers and phones do, AES, GHASH, SHA1, and SHA256 run on its
  instructions. Without it, as on the Raspberry Pi 4, CM4, and Zero 2 W, they
  run [aws-lc]'s NEON and scalar assembly instead (see
  [ALGORITHMS.md](ALGORITHMS.md)), `rind::cpu::has_aes_hardware()` is false, and
  rind-rustls and rind-dimpl prefer ChaCha20-Poly1305. On Apple's platforms,
  secret-dependent code runs with data-independent timing (DIT), set and
  cleared in each call unless `rind::cpu::Dit::hold()` holds it across a batch
  of calls. rind sets no DIT on other aarch64 platforms, where Arm says it
  changes nothing on current cores.
- `x86_64` runs on every x86_64 CPU. Without `aes` and `pclmulqdq`, as on
  Core 2 and Nehalem, AES and GHASH run [aws-lc]'s SSSE3 assembly instead
  (see [ALGORITHMS.md](ALGORITHMS.md)), `rind::cpu::has_aes_hardware()` is false,
  and rind-rustls and rind-dimpl prefer ChaCha20-Poly1305. Without `avx2`, as
  on Sandy Bridge, Ivy Bridge, and AMD's Bulldozer and Jaguar cores,
  ChaCha20-Poly1305 runs [aws-lc]'s SSE4.1 assembly, ChaCha20, SHA1, and
  SHA256 its SSSE3 assembly, or for SHA its AVX assembly on Intel's cores,
  SHA-512 its scalar assembly on other vendors' cores,
  ML-KEM's and ML-DSA's arithmetic runs Rust ports of [mlkem-native]'s and
  [mldsa-native]'s portable C, and
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
  RSAZ exponentiation, and Ed25519 verification a port of
  [curve25519-dalek]'s AVX2 backend. With `avx512ifma`, as on Ice Lake,
  Sapphire Rapids, and AMD's Zen 4 and 5, RSA-2048, 3072, and 4096 signing
  runs aws-lc's dual AVX-512 RSAZ.
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
  CPU has it, and with NEON, X25519's shared secret runs [BoringSSL]'s
  assembly. SHA-3's, ML-KEM's, and ML-DSA's Keccak-f runs [OpenSSL]'s assembly, on
  NEON where the CPU has it.

- Builds with `-Z cf-protection=branch` or `-Z branch-protection=bti`, both
  unstable, are unsupported: rind calls aws-lc's x86_64 and aarch64 routines
  through function pointers, and their text, as rind imports it, holds no
  `endbr64` or `bti` landing pad. `admin/import-aws-lc` should keep aws-lc's
  markers once either flag stabilizes.

- Every other architecture, big-endian `aarch64` and `arm`, whose assembly
  assumes little-endian, and `arm` before ARMv7, which rind's ARMv7 assembly
  does not run on, select the portable backend: what 32-bit `arm` runs without
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
  where `--cfg rind_portable` forces it. The merge gate's `cross` module
  compiles the `rind` library, and not the adapters, for `wasm32-wasip2`
  and `wasm32-unknown-unknown`, with and without `wipe`
  (`sh/dispatch.sh:257-263`), when the diff matches that module's path
  (`sh/dispatch.sh:65`: `rind`'s `src`, `tests`, `build.rs`, or manifest,
  the workspace manifest or lockfile, or the flake) or the gate's own
  orchestration (`justfile`, `sh/dispatch.sh`, `sh/changed.sh`, or
  `sh/select.sh`), which runs every check. A push to `main` runs
  `just ci --all`, which compiles both every time. The latter enables
  `getrandom/wasm_js` for JavaScript randomness; the WASI target uses its
  system random source. The nightly `build.yml` runs the vector tests on
  `wasm32-wasip2` under wasmtime (`just wasm`), without the differential
  tests, since aws-lc does not build for wasm.
  `wasm32-unknown-unknown` stays compile-only: its tests need a JavaScript
  host. Constant time is unchecked on wasm, `wasm32-wasip2` included,
  though its tests run: ctgrind and the trace checks inspect native code,
  and a wasm engine compiles rind again, so its JIT may turn a select into
  a branch. The portable rows' own machine code is not checked either:
  ctgrind of that backend is the x86_64 build forced with
  `--cfg rind_portable`.

`missing_cpu_feature` returns `None` on x86_64, 32-bit arm, and the portable
backend. On little-endian aarch64 it names `neon` only when runtime detection
does not see it, and every aarch64 target with `std` enables `neon` at compile
time (`rustc --print cfg --target aarch64-unknown-linux-gnu` lists
`target_feature="neon"`). `rind::cpu::check()` therefore cannot fail on a
target rind builds for, and rind 0.4 removes it: do not add that call. A debug
build can still deny `neon` with `RIND_CPU_DISABLE_neon`, which is a test
toggle, not a target.

rind's secret-dependent code divides no secret and does no floating-point
arithmetic on any architecture, as `admin/ct-vartime` checks, but it multiplies
secrets, so it runs in constant time only where the integer multiplier does.
rind has no masked multiply for the cores whose multiplier finishes early for
some operands, so it is not constant-time on them:

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
- `s390x`: IBM publishes no instruction timing for IBM Z, so rind cannot say.
- 32-bit `arm` before ARMv7: Intel's XScale (ARMv5TE), whose `mul`, `umull`,
  and `smull` terminate early by the top bits of their second operand
  ([XScale] Table 10-6), and ARMv4T's ARM7TDMI and ARM9TDMI ([BearSSL ctmul]).
  ARMv6's ARM1176 does not terminate early ([ARM1176 TRM] Table 3-46), nor does
  the ARM926EJ-S.
- `x86_64` and 32-bit `x86`: VIA's Nano 2000 series ([BearSSL ctmul]). Intel
  lists `mul` and `imul` as data-independent-time ([Intel DOIT]).

[COMPATIBILITY.md](COMPATIBILITY.md) lists the features of each Intel CPU
family since 2004, and of some AMD cores.

[s2n-bignum]: https://github.com/awslabs/s2n-bignum
[curve25519-dalek]: https://github.com/dalek-cryptography/curve25519-dalek
[HACL\*]: https://github.com/hacl-star/hacl-star
[mlkem-native]: https://github.com/pq-code-package/mlkem-native
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
[Gu and Shacham]: https://arxiv.org/abs/2311.14246
[Intel DOIT]: https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/resources/data-operand-independent-timing-instructions.html
