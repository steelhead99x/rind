# Security review guide

Where an outside security reviewer, or an adopter's security team, starts on
rind: what is in scope, the threat model, where the code came from and at
which pin, what each automated check does and does not establish, and where
the checks are thinnest. Each section is a map: it says what holds and
links the document with the detail.

Report a vulnerability as [SECURITY.md](SECURITY.md) says, never in an issue
or pull request.

## Scope

[SECURITY.md](SECURITY.md#what-counts) says which packages are in scope and
what counts as a vulnerability. The code under review:

- The `rind` crate, whose public modules wrap three private layers:
  `low`, the only one that may hold `unsafe`, with one backend per target
  (`x86_64`, `aarch64`, `arm`, or `portable`), then `mid` and `high`, which
  deny `unsafe_code`. [ARCHITECTURE.md](ARCHITECTURE.md) describes them, and
  `admin/structure` fails on a reference from a lower layer to a higher one.
- The `rind-<consumer>` adapter crates, each offering exactly the API of the
  provider its upstream ships. Each README lists what rind cannot back, and
  `admin/adapter-api` fails on a public item that differs from upstream's.
- The language bindings: `rind-dart`, a C ABI for Dart's FFI, and
  `rind-python` (pyrind), on PyO3.
- `rind-openssl`, an OpenSSL 3 provider: a C ABI that OpenSSL loads, backing
  X25519 and Ed25519.

[ALGORITHMS.md](ALGORITHMS.md) says whose code runs each algorithm on each
CPU tier, and [PLATFORMS.md](PLATFORMS.md) which CPU features each tier
needs. A backend requires only what its target enables at compile time, so
rind runs on every CPU its target does, and each other feature only picks a
faster path.

## Threat model

rind assumes an attacker who:

- chooses every input rind parses or computes on: keys, signatures,
  ciphertexts, encodings, peer shares, nonces, and lengths, malformed and
  maximal ones included;
- measures how long rind's operations take, remotely over a network and
  locally from another process or virtual machine on the same host, through
  shared caches, branch predictors, and other microarchitectural state that
  a secret-dependent branch, memory index, or variable-time instruction
  reaches.

rind's defenses are the rules [AGENTS.md](AGENTS.md#required) sets: hostile
input returns an error, never a panic, and its cost is bounded by design;
secret-dependent code runs in constant time; and a key type wipes its whole
value on drop, with keyed state and heap scratch derived from a private key
([Wiping keys](README.md#wiping-keys)). Wiping is a
second layer against an attacker who later reads freed memory, as in a heap
dump; it does not wipe digest contexts, decrypted messages, or stack
temporaries.

Outside the model:

- Fault injection, such as voltage glitches or Rowhammer. The one
  countermeasure is RSA's: a private-key operation checks its result before
  returning it, as aws-lc does.
- Power, electromagnetic, and acoustic analysis, and physical access.
- Speculative execution beyond what the constant-time rule gives: only
  secret-independent control flow and addresses stand against it. The one
  speculation barrier rind adds follows setting DIT on Apple's platforms, as
  Apple asks, so no instruction after it runs speculatively without DIT.
- A compromised toolchain, build machine, or dependency. `cargo deny`
  checks crates against RustSec's advisories, licenses, and sources; nothing
  checks a release's build is reproducible.
- A compiler or flags other than CI's: constant time is checked on the
  builds CI makes for Linux, so a user's own toolchain, a non-Linux target,
  or a wasm engine may emit code no check has seen.
- A CPU whose multiplier takes time by its operands, and an Intel CPU whose
  operating system leaves DOITM unset, as Linux does, both of which
  [PLATFORMS.md](PLATFORMS.md) describes. Intel's data-independent list also
  omits the `VSHA512` instructions, which SHA-384 and SHA-512 run where the
  CPU has them, until [their quest](/quest/m2/confidence/intel-vsha512.md)
  drops them. Intel's MXCSR-dependent timing is in the model: rind loads
  `0x1FBF` around the x86_64 code that reaches an affected multiply, and
  around every call on 32-bit x86.
- The operating system's random source, which rind trusts through
  `getrandom`, and an attacker who reads the process's memory while it runs.
- A caller's misuse the API permits, such as repeating a nonce it passes.

## Provenance

rind began as a copy of [Graviola](https://github.com/ctz/graviola) and no
longer tracks it. [ALGORITHMS.md's Sources table](ALGORITHMS.md#sources)
names every source of rind's code, Graviola and rind itself among them, and
says what rind takes from each, under which license, and what of it is
formally verified. Each file under `rind/src` names its license in an SPDX
comment, which `admin/scan-license` checks, and [LICENSE](LICENSE) holds
every copied source's text.

The pins, as `admin/audit` renders them from the files that hold them, so
`just check` fails when this table and a pin disagree:

<!-- admin/audit pins: begin -->
| Upstream | Pin | Pinned in | What rind takes at it |
|---|---|---|---|
| aws-lc | `5ed12cce0fd4` | `admin/import-aws-lc` | copied and ported code |
| BoringSSL | `8f2554dc344d` | `admin/import-boringssl` | copied code |
| OpenSSL | `2f4e3a5fec05` | `admin/import-openssl` | copied code |
| HACL\* | `f557259007db` | `admin/import-hacl` | Vale's x86_64 AES-GCM |
| pyca/verified-garbage | `e7b0fe8a82b7` | `admin/import-vg` | copied code and the Lean ISA models its proofs rest on |
| s2n-bignum | `3f01260ff1bd` | `thirdparty/s2n-bignum/RIND.md` | assembly and the HOL Light proofs of it |
| aws-lc | `c21d40da4bbe` | `admin/prove-bytes` | the routines aws-lc-verification's SHA-384/512 proofs are about |
| ACVP-Server | `975de31eb83d` | `admin/sync-acvp` | test vectors |
| aws-lc | `5ed12cce0fd4` | `admin/sync-vectors` | test vectors |
| BoringSSL | `8f2554dc344d` | `admin/sync-vectors` | test vectors |
| Wycheproof | `65ca494727a5` | `admin/sync-vectors` | test vectors |
| CAVP | `0220357e399b` | `admin/sync-vectors` | test vectors |
| CCTV | `b88c4b206254` | `admin/sync-vectors` | test vectors |
| RFC 9180 | `b1f7cb0cdeab` | `admin/sync-vectors` | HPKE test vectors |
| RFC 9380 | `664b13592116` | `admin/sync-vectors` | hash-to-curve test vectors |
| blind-rsa-signatures | `45d0abfa829c` | `admin/sync-vectors` | RFC 9474 test vectors |
| RFC 9497 | `5d7d94c8dc75` | `admin/sync-vectors` | OPRF test vectors |
| RFC 9591 | `127452b93acb` | `admin/sync-vectors` | FROST test vectors |
| cfg-if | 1.0.5 | `Cargo.lock` | a macro for `cfg` blocks |
| curve25519-dalek | 5.0.0 | `Cargo.lock` | X25519, Ed25519, and ristretto255 on armv7 and the portable backend |
| fiat-crypto | 0.3.0 | `Cargo.lock` | the NIST curves' field arithmetic on armv7 and the portable backend |
| getrandom | 0.4.3 | `Cargo.lock` | the operating system's random source |
| libc | 0.2.191 | `Cargo.lock` | `getauxval`, for armv7's crypto extension bits |
| libcrux-hacl-rs | 0.0.6 | `Cargo.lock` | the runtime of the HACL\* ChaCha20 rounds rind copied |
| libcrux-macros | 0.0.4 | `Cargo.lock` | the same |
| libcrux-poly1305 | 0.0.7 | `Cargo.lock` | HACL\*'s Poly1305, on 32-bit portable targets |
| libcrux-sha2 | 0.0.9 | `Cargo.lock` | HACL\*'s SHA-2 block functions, on the portable backend |
<!-- admin/audit pins: end -->

Code taken once, with no importer to rerun, carries no machine-readable pin:
Graviola, whose aarch64 ChaCha20 and Poly1305 began as cifra's; aws-lc's
C, which rind ported to Rust by hand; mlkem-native at `d1b2fe78` and mldsa-native at v2.0.0 (`834a90d5`), whose C
rind ported to Rust; libcrux 0.0.10's bitsliced AES and HACL\*'s ChaCha20
rounds; and curve25519-dalek 5.0.0's AVX2 backend, ported to intrinsics.
The recurring [upstream-updates quest](/quest/m2/upstream-updates.md)
reviews every source for changes since its pin every two weeks, since `cargo deny` sees advisories
only for crates.

How copied code is regenerated and checked:

- `admin/import-aws-lc`, `admin/import-boringssl`, `admin/import-openssl`,
  `admin/import-hacl`, and `admin/import-vg` fetch their upstream at its
  `REV` and write its assembly under `rind/src/low` as Rust naked functions
  or `global_asm!`.
- `admin/parse-asm` transliterates s2n-bignum's assembly, from rind's fork
  in `thirdparty/s2n-bignum`, into Rust `asm!`. The fork's
  [RIND.md](thirdparty/s2n-bignum/RIND.md) lists every file that differs
  from upstream at its base.
- `admin/regenerate`, nightly in the `regenerate` workflow, reruns every
  importer and generator at its pin and fails if the result differs from the
  committed code, a committed file is one nothing generates, or the fork
  differs from upstream beyond what RIND.md lists.
- `admin/prove bytes`, in the `prove` workflow, checks that rind's release
  build of each proven routine holds the instructions its proof is about,
  with only the differences `admin/prove-bytes` lists.
- [UPSTREAM.md](UPSTREAM.md) lists every workaround for a bug in a tool or
  dependency rind does not own.

## Checks and their limits

[TESTING.md](TESTING.md) says which checks reach each primitive on each CPU
tier, and `admin/testing`, in `just ci`, fails when an export, test, fuzz
target, or vector file is missing from its tables. What each check
establishes, and what it does not:

- **Vectors**: Wycheproof, NIST's CAVP and ACVP samples, CCTV, the RFCs,
  and aws-lc's and BoringSSL's files, run by `cargo test` on each tier
  [TESTING.md's tier table](TESTING.md#tiers) names. They check only the
  cases published, and each tier only where CI runs it, natively, under
  Intel SDE, or under qemu.
- **Differential tests** against aws-lc-rs, or a Rust crate where aws-lc-rs
  lacks the primitive, on the same tiers. Where rind runs aws-lc's own
  routine, as for ChaCha20-Poly1305 on x86_64 and aarch64 or RSA's RSAZ
  exponentiation, the test compares that routine with itself, so it
  checks rind's glue around it, and only vectors check the routine. wasm runs
  none, since aws-lc does not build for it.
- **Fuzz targets**, weekly for twenty minutes each against aws-lc-rs,
  replayed on every tier and against the portable backend. The ECVRF, OPRF,
  and blind RSA targets compare rind with itself, so they find panics and
  hangs, not wrong answers. Coverage does not measure what fuzzing reaches.
  [OSS-Fuzz](/quest/m4/oss-fuzz.md) is not running yet.
- **ctgrind** (`admin/ctgrind`, weekly, in release and debug builds, armv7's
  included) runs the unit tests under valgrind, failing on a branch or address
  that depends on a marked secret. It sees only the paths the tests take,
  with the secrets they mark; it cannot run AVX-512, VAES, the SHA
  extensions, or ARM's crypto extension and SHA3; and it sees no
  variable-time instruction.
- **`admin/ct-sde` and `admin/ct-qemu`** compare execution traces of the
  code valgrind cannot run under two secrets, so they see only a difference
  between those two.
- **`admin/ct-binsec`** has BINSEC check each `ct_binsec_...` region for
  every value of its secrets at once, on x86_64, aarch64, and the portable
  backend. Its public inputs are fixed, it cannot decode AES-NI, VAES, the
  SHA512 instructions, AVX-512, or aarch64's crypto extension and SHA3, it
  does not run on armv7, and its lifter misses a secret branch whose two
  sides are empty.
- **`admin/ct-vartime`**, in `just ci`, scans the release builds of every
  Linux target rind builds for divisions and floating point, against an
  allowlist of public operands. On the x86_64 backend it also fails on a
  multiply whose timing depends on MXCSR that an export reaches outside
  `rind::low::Mcdt`, the mitigation; on 32-bit x86 and the portable backend,
  that every call enters it is unchecked. It takes the integer multiplier to
  run in constant time, and does not refuse `VSHA512`.
- **s2n-bignum's `_SAFE` theorems** prove the routines
  [ALGORITHMS.md](ALGORITHMS.md#s2n-bignums-constant-time-theorems) lists
  constant time for every input, variable-time instructions included, but
  not the Rust that calls them.
- **Timing tests** (`admin/timing`, weekly on GitHub's runners) run dudect
  over each secret the API lets them set, and the Marvin toolkit against
  RSA-OAEP decryption. They are statistical, on shared hardware, and cannot
  time key generation or encapsulation.
- **Proofs**: s2n-bignum's, HACL\*'s, Vale's, fiat-crypto's, and
  aws-lc-verification's published proofs, and rind's own HOL Light and Lean
  proofs in [`proofs/`](proofs/README.md), checked nightly by `admin/prove`.
  [BENCHMARKS.md's verified code](BENCHMARKS.md#verified-code), from
  `benchmarks/verified.toml`, marks the operations whose whole computation a
  proof covers. Lean's proofs are about Charon and Aeneas's translation of
  the Rust and rest on hand models of what the Rust quotes and on
  restatements of the imported proofs as axioms, which
  [the trust base](proofs/README.md#trust-base) lists; libcrux's Rust is
  compiled from HACL\*'s verified C by an unverified step.
- **Zeroing**: `rind/tests/zeroing.rs` drops each value holding a secret and
  fails on any byte left nonzero, and `rind/tests/heap_scratch.rs` fails on a
  freed heap block that differs between two keys. Both see only the value
  itself and the heap blocks it frees.
- **Bounds**: `low::guard_pages` runs each kernel that takes a caller's
  slice against `PROT_NONE` pages, at lengths up to 1100 bytes and, for the
  AEADs, 2000 to 2600, on Unix. It is the only bounds check on the assembly
  valgrind cannot run, since AddressSanitizer, nightly in `asan`, does not
  instrument assembly.
- **Calling convention**: `low::abi` calls every assembly routine through a
  trampoline that fails when a register its ABI preserves, the stack
  pointer, or x86_64's direction flag comes back changed, and
  `admin/prove-bytes clobbers` checks each s2n-bignum block declares what
  its proof says it may change.
- **Miri**, weekly, runs the portable backend's unit tests on x86_64 and
  big-endian s390x, failing on undefined behavior. It runs no assembly, and
  skips the slow tests `sh/miri.sh` lists.
- **Mutation testing** (`admin/mutants`) fails on a mutant of rind's Rust
  that no test catches. Weekly, on native x86_64 and aarch64 Linux runners
  and the portable backend, it mutates only the Rust that changed in the
  last week; a campaign over the whole workspace runs only when dispatched.
  It skips generated assembly, which proofs and differential tests own.
- **Coverage** (`admin/coverage`, nightly on Linux and macOS) reports the
  published functions no test runs, under `cargo test`, `dart test`, and
  pyrind's tests, on each runner's tiers, but not under fuzzing.
- **Adapter fuzz targets**, for rind-rustls, rind-dimpl, and rind-str0m,
  feed a hostile peer's bytes and whole handshakes edited in flight, against
  upstream's aws-lc-rs provider, and rind-openssl's calls its C ABI as
  OpenSSL does, with parameters and buffers of any shape, against rind's own
  API. The other adapters have none.

## Where the checks are thinnest

Built from TESTING.md's tables, ALGORITHMS.md's ✓ marks,
`benchmarks/verified.toml`, and the nightly coverage run of 2026-11-13 at
`67a476ff`. Every primitive has a differential test and vectors, but for
random bytes, which have neither, and the constant-time compare, which has
no published vectors. These are the places where a check is weak, and what
still reaches each.

Hand-written arithmetic no proof covers, by where it came from:

- **aws-lc's, BoringSSL's, and OpenSSL's assembly** that rind runs without a
  ✓, such as ChaCha20-Poly1305 on x86_64 and aarch64, RSAZ, Montgomery
  multiplication off ADX, the AVX2 and SHA512-instruction SHA-2, VAES
  AES-GCM, and all of armv7's. Vectors and fuzzing reach each on its tier;
  the differential test, which runs aws-lc's code too, checks only the glue.
- **Graviola's** code under AES, GHASH, SHA-256, HMAC, P-256, P-384,
  ML-KEM, and RSA, wherever ALGORITHMS.md names it. Vectors, differential
  tests independent of it, and fuzzing reach each.
- **rind's own**, which ALGORITHMS.md marks ⚡, such as its parts of P-384 and
  P-521, x86_64 SHA-256, the portable RSA multiplication, and armv7
  Ed25519. Vectors, independent differential tests, and fuzzing reach each,
  and each Montgomery routine's unit tests compare it with proven or
  portable arithmetic on edge-case limbs, as
  [TESTING.md](TESTING.md#vector-suites) describes.
- **Ports to Rust**: mlkem-native's and mldsa-native's C, outside their CBMC
  proofs; curve25519-dalek's AVX2 backend, for Ed25519 verification on
  x86_64 without ADX; and aws-lc's constant-time SSE2 AES and integer GHASH.
  `low::generic::mldsa_poly::backend_matches_port` checks the ML-DSA port
  against the AVX2 and Neon routines.
- **curve25519-dalek's serial backend**, X25519, Ed25519, and ristretto255
  on armv7 and the portable backend. There ristretto255's differential test
  compares dalek with itself, so only RFC 9496's and RFC 9497's vectors
  check it.
- **x86_64 P-256's mixed addition on macOS**, aws-lc's: rind's HOL Light
  proofs check the Linux build's object, and Apple's text can place the
  routines' helpers at other offsets.

Primitives whose reference is weak: ECVRF, OPRF, VOPRF, blind RSA, SPAKE2+,
FROST, and HPKE have no aws-lc-rs counterpart, so their differential tests
compare with other Rust crates, and their fuzz targets with rind itself,
except HPKE's, against rustls's aws-lc-rs provider. SPAKE2+ and FROST have no
fuzz target.

Constant time is checked by no tool on:

- wasm, whose engine compiles rind again;
- builds for macOS, iOS, Windows, and Android, and any toolchain but CI's:
  every constant-time check runs on CI's Linux builds, so what carries over
  is the assembly those builds share and the proofs about its instructions;
- AES-GCM and ML-DSA on aarch64 under BINSEC, which cannot finish them in a
  scheduled run's time, and the paths whose instructions BINSEC cannot decode,
  which ctgrind, `admin/ct-sde`, and `admin/ct-qemu` cover for one or two
  secrets.

Functions no test runs, from the nightly coverage report: in the `rind`
crate, 80 of 2,889 on Linux and 76 of 2,589 on macOS, most in `high/`
(`hpke.rs`, `spake2plus.rs`, `blind_rsa.rs`, `oprf.rs`, `vrf.rs`, and
`signature.rs`); and in the adapters and bindings, 127 in rind-aws-lc-rs, 33
in rind-ring, 23 in rind-python, and 12 or fewer in each of the rest.
[Every published function runs under a test](/quest/m2/confidence/uncovered-functions.md)
closes them. The report's "Measure coverage" step lists each file.

## `unsafe`

`unsafe` appears only in `low`, the FIPS build's DRBG handle, the bindings,
rind-openssl, and test code. Every block in `rind`, rind-dart, and
rind-openssl carries a `SAFETY:` comment, which clippy's
`undocumented_unsafe_blocks` lint enforces in CI.
Counted outside comments and literals by `admin/audit unsafe` at `2abc90e9`:

| Area | `unsafe` | What it is | What justifies it |
|---|---|---|---|
| `rind/src/low/x86_64` | 453 | `asm!`, naked functions, and intrinsics | [`rind::doc::inline_assembly_safety`](rind/src/low/inline_assembly_safety.rs), with the calling-convention, bounds, and `admin/prove bytes` checks above |
| `rind/src/low/aarch64` | 304 | the same | the same |
| `rind/src/low/arm` | 89 | `global_asm!` and the calls into it | the same |
| `rind/src/low/generic` | 22 | SSE2 intrinsics in `aes_nohw`, `ReuseCache`'s one-time initialization, the volatile wipe, a cast between same-layout arrays, and MD5's empty `asm!` barrier | each block's `SAFETY:` comment; Miri checks `ReuseCache` and the wipe |
| `rind/src/low/portable` | 3 | volatile writes and reads for the wipe and the constant-time compare | the same |
| other `rind/src/low` files | 89 | test harnesses (`abi`, `guard_pages`, `ct_binsec`, `tests`, `vartime_planted`), the `asm_call!` macro, and `Mcdt`'s MXCSR loads and `cpuid` | test code, but for the macro and `Mcdt`, which `SAFETY:` comments and `admin/ct-vartime` cover |
| `rind/src/mid` | 2 | a test's call into aws-lc | test code |
| `rind/src` | 10 | the FIPS build's DRBG handle, its test's `fork`, and a test helper | `SAFETY:` comments |
| `rind-dart` | 235 | the C ABI Dart's FFI calls | `SAFETY:` comments, `dart test`, and ctgrind over its exports |
| `rind-python` | 6 | Python's buffer protocol | `SAFETY:` comments |
| `rind-openssl` | 245 | the C ABI OpenSSL's core calls, and the `OSSL_PARAM` arrays it passes | `SAFETY:` comments, `fuzz::openssl`, and OpenSSL's own tests with it loaded |
| `rind-fips` | 608 | the unpublished FIPS module's C ABI | out of scope until published |

The rest, in `rind/tests`, rind-rcgen's tests, the fuzz targets, `admin`,
and the unpublished bench, timing, and cpuid crates, is test code or tooling.
