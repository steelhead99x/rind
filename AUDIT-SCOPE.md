# Third-party audit scope

What an outside security audit of rind covers, in which order, and what it
need not redo. rind has had no third-party audit. [AUDIT.md](AUDIT.md) is the
guide to what is there to review: the threat model, where the code came from,
and what each automated check establishes. This page turns it into an
engagement: a phased scope, an inventory of what each phase reads, how to
reproduce what the project's own checks say, and where the auditor's time buys
the most.

Nothing here commissions an audit or promises one. The decisions an
engagement needs, such as the firm, the budget, and whether the report is
public, are the maintainer's and are not made here.

## Phases

The scope is two phases, so the first engagement can be small and its findings
shape the second.

- **Phase 1** is what a TLS or QUIC deployment on rind runs on, and what
  everything else stands on: the `low` kernels (assembly, intrinsics, and the
  portable and generic Rust beside them), the `mid` primitives and
  constructions, the `high` keys, signatures, encodings, and hashes that a
  caller's bytes reach first, the `rind-rustls` provider boundary, and the
  formal-verification trusted computing base (what a proof assumes rather than
  proves).
- **Phase 2** is the rest of what rind publishes: ML-DSA, SLH-DSA,
  Argon2id, ristretto255, hash-to-curve, the protocols (OPRF, FROST,
  SPAKE2+, ECVRF, blind RSA), the other adapters, and the
  bindings (`rind-python`, `rind-dart`, `rind-openssl`), which add `unsafe`
  and a C ABI. `rind-fips` is in it only once it is published.

The ML-DSA and SLH-DSA PKCS#8 loaders are in Phase 1: `rind-rustls` loads
every PKCS#8 key through rind, so when any crate in the build enables rind's
`ml-dsa` or `slh-dsa` feature, Cargo feature unification lets a hostile key
reach them. The loaders sit inside `high/signature/ml_dsa.rs` and `slh_dsa.rs`
and call the key expansion in `mid/mldsa.rs` and `slhdsa.rs`, so those four
files count whole, signing and verifying code included, with the `low` ML-DSA
kernels that loading reaches (the transform, reduction, norm check, and
sampling ones). The kernels only signing and verifying run stay in Phase 2.

ML-KEM is in Phase 1, not Phase 2, because `rind-rustls` offers
`X25519MLKEM768` first by default, so a handshake runs it whenever the
peer negotiates it. HPKE is in Phase 1 for the same reason: `rind-rustls`
backs rustls's HPKE trait with rind's `hpke` module, which a client using
Encrypted ClientHello runs.

Phase 1 comes first because a flaw there reaches every user, and because Phase
2's protocols and bindings call Phase 1's code: an auditor who has read it
reads them faster.

### Inventory

Counts are physical lines of tracked files at `4f4909ef`, from
`admin/audit-scope table`; they are a dated snapshot, which no check keeps
current, so rerun it at the commit the audit names.
`admin/audit-scope files [1|2]` prints every file in a phase with its area,
lines, and whether it is generated, tab-separated, for an auditor's own
spreadsheet. "Generated" is code an importer or `admin/parse-asm` writes, or
an imported `.s` file; `admin/regenerate` fails if it differs from what the
importer writes at its pin, so a reviewer reads the importer and its pin
([AUDIT.md's Provenance](AUDIT.md#provenance)), not the output. rind's
structured copy of aws-lc's aarch64 ChaCha20-Poly1305
(`rind/src/low/aarch64/chacha20poly1305/`) is hand-written: no importer
writes it. rind's structured copy of aws-lc's x86_64 AVX2 seal
(`rind/src/low/x86_64/chacha20poly1305/`) is generated, by
`admin/chacha20poly1305-x86/generate`, which a reviewer reads with the Lean
program it also writes, and which fails if the aws-lc text it copies
changes. Hand-written lines include each file's inline unit tests. Tests under `rind/tests` and
`rind/src/test`, vectors, fuzz targets, and tooling are not counted, since
they are not what ships. The Lean split is by file name, from
[`proofs/README.md`'s layout](proofs/README.md#layout), and is a reading aid:
the trust base's own list, [`proofs/README.md#trust-base`](proofs/README.md#trust-base),
is authoritative.

**Phase 1: the audit's first engagement**

| Area | Files | Hand-written lines | Generated lines |
|---|---:|---:|---:|
| HOL Light: rind's proofs of its own assembly | 18 | 23,357 | 0 |
| HOL Light: rind-authored models and specs in its s2n-bignum fork | 10 | 4,429 | 0 |
| Lean TCB: files that state axioms | 25 | 5,913 | 0 |
| Lean TCB: hand models, ISA models, and transliterated specs | 136 | 37,651 | 0 |
| Lean: proofs and Aeneas glue (machine-checked) | 129 | 52,436 | 0 |
| `high`: HPKE, for `rind-rustls`'s Encrypted ClientHello | 1 | 1,792 | 0 |
| `high`: ML-DSA and SLH-DSA keys, for their PKCS#8 loaders | 2 | 562 | 0 |
| `high`: keys, signatures, encodings, and hashing | 26 | 16,019 | 0 |
| `low/aarch64` | 280 | 6,462 | 206,151 |
| `low/aarch64`: ML-DSA kernels key loading reaches | 11 | 1,100 | 3,133 |
| `low/arm` | 31 | 2,716 | 15,599 |
| `low/generic` | 40 | 11,379 | 0 |
| `low/generic`: ML-DSA kernels key loading reaches | 1 | 632 | 0 |
| `low/portable` | 12 | 1,106 | 0 |
| `low/x86_64` | 449 | 15,596 | 408,678 |
| `low/x86_64`: ML-DSA kernels key loading reaches | 14 | 827 | 9,557 |
| `low` shared files | 15 | 5,297 | 0 |
| `mid`: ML-DSA and SLH-DSA keys, for their PKCS#8 loaders | 2 | 3,035 | 0 |
| `mid`: primitives and constructions | 34 | 16,008 | 42,161 |
| `rind-rustls`: the TLS provider | 13 | 3,600 | 0 |
| `rind` crate root: public API and errors | 7 | 2,641 | 0 |
| **Total** | **1,256** | **212,558** | **685,279** |

Lean `axiom` declarations: 173 in 25 files. `sorry`: 0.

**Phase 2: follow-on**

| Area | Files | Hand-written lines | Generated lines |
|---|---:|---:|---:|
| `high`: protocols (OPRF, FROST, SPAKE2+, VRF, blind RSA, KDFs) | 12 | 9,667 | 0 |
| `low/aarch64`: ML-DSA signing and verifying, and Argon2, kernels | 7 | 0 | 1,041 |
| `low/generic`: ML-DSA signing and verifying, and Argon2, kernels | 1 | 255 | 0 |
| `low/x86_64`: ML-DSA signing and verifying, and Argon2, kernels | 8 | 225 | 2,272 |
| `mid`: KDF, hash-to-curve, and ristretto255 | 10 | 2,978 | 0 |
| `rind-dart`: Dart FFI and the `cryptography` drop-in | 27 | 7,140 | 0 |
| `rind-fips`: FIPS module (unpublished) | 38 | 10,662 | 0 |
| `rind-openssl`: OpenSSL 3 provider | 7 | 2,618 | 0 |
| `rind-python`: Python bindings and the `cryptography` drop-in | 48 | 5,382 | 0 |
| `rind` FIPS build glue | 3 | 1,345 | 0 |
| other `rind-<consumer>` adapters | 60 | 13,092 | 0 |
| **Total** | **221** | **53,364** | **3,313** |

### Phase 1 in more detail

Where the hand-written lines are, and what the reviewer does with each:

- **`low` assembly glue and hand-written kernels** (`low/x86_64`,
  `low/aarch64`, `low/arm`). The hand-written part is Rust
  `asm!` and intrinsics for what rind wrote itself (marked ⚡ or "rind" in
  [ALGORITHMS.md](ALGORITHMS.md)), the Rust that calls imported routines, CPU
  dispatch (`cpu.rs`, `entry.rs`), and the `Mcdt`/DIT guards. The generated
  part is read as its importer and pin.
- **`low/generic` and `low/portable`**: pure-Rust arithmetic and the backend
  that runs wherever rind has no assembly. These are the code a non-x86_64,
  non-aarch64 deployment runs, and they are the only code Miri executes.
- **`mid`**: constructions over the kernels: AEADs, SHA-2 and SHA-3, the NIST
  curves, X25519, Ed25519, RSA (with its key-size floors), ML-KEM, and the
  random source. Its generated lines are the NIST curves' precomputed tables
  (`admin/p256-precomp` and its siblings).
- **`high`** (the Phase 1 half): key and signature types, ASN.1, PKCS#1/#8,
  SEC1, and SPKI parsing, ECDSA, RSA, hashing, and constant-time compare. It
  is where hostile bytes first arrive, so it is in the first engagement even
  though it holds no assembly.
- **`rind-rustls`**: the provider boundary: cipher suites, key exchange
  groups, signing and verification, the ticketer, and HPKE. Its API is
  rustls's `aws_lc_rs` provider's item for item, so the review is of what
  differs; its README lists those differences (for example, the ticketer's
  XChaCha20-Poly1305 and the NIST HPKE suites' refusals).
- **Formal-verification TCB**: the Lean files that state axioms, the hand
  models and transliterated specs, and verified-garbage's ISA models, plus
  rind's HOL Light proofs of its own assembly. The proofs themselves are
  machine-checked; the auditor reads what they assume and what they are
  about, not their bodies ([below](#what-is-machine-checked-and-what-needs-a-human)).
  The HOL Light row counts the files of rind's s2n-bignum fork that rind wrote.
  The fork also edits upstream's x86 model files (`instruction.ml`, `decode.ml`,
  `x86.ml`, and `simulator.ml`, for `RORX`, `ANDN`, the SHA-NI instructions, and
  others): those edits are in Phase 1 too, but are not counted, since the files
  are upstream's. Read the diff from the base commit that
  [`thirdparty/s2n-bignum/RIND.md`](thirdparty/s2n-bignum/RIND.md) names, in the
  sections it lists.

## Reproducing the project's own checks

Everything runs from a clean clone with [Nix](https://nixos.org); the
`flake.nix` pins the toolchains. [TESTING.md](TESTING.md) says which check
reaches which primitive on which CPU tier, and [CONTRIBUTING.md](CONTRIBUTING.md)
says how to run them. The ones an auditor will want:

| What | Command | Notes |
|---|---|---|
| Unit tests, vectors, differential tests | `nix develop --command cargo nextest run --workspace` | Wycheproof, CAVP, ACVP, CCTV, and RFC vectors, and aws-lc-rs as a differential oracle. `SLOW_TESTS=1` adds the large sets. |
| CI's whole gate | `nix develop --command just gate` | CI's gate over every crate, with the lints, structure, license, adapter-API, and constant-time scans among them. `just ci` and `just check` pick checks from the branch's diff, so on a clean checkout of a tag they can skip the ones a source change would trigger. |
| Constant time under valgrind | `nix develop .#ctgrind --command admin/ctgrind` | Weekly in CI. Sees only the paths the tests take. |
| Constant time, symbolically | `nix develop .#binsec --command admin/ct-binsec` | Checks each `ct_binsec_...` region for every secret. |
| Constant time under SDE and qemu | `nix develop .#sde --command admin/ct-sde`; `nix develop .#ct-qemu --command admin/ct-qemu` | The AVX-512, VAES, SHA extension, and armv7 crypto paths valgrind cannot run. |
| Variable-time instructions | `nix develop .#ct-vartime --command admin/ct-vartime` | Scans release builds for divisions and floating point. |
| HOL Light and Lean proofs | `nix develop .#prove --command admin/prove`, on x86_64 Linux with AVX2 (aarch64 macOS runs only `admin/prove lean`, per [TESTING.md](TESTING.md)) | Also `admin/prove bytes`, which checks the release build holds the bytes each proof is about. |
| Imported code matches its pin | `nix develop .#regenerate --command admin/regenerate` | Reruns every importer; fails on a difference. |
| Zeroing and heap scratch | `nix develop --command cargo nextest run -p rind --test zeroing --test heap_scratch` | |

The audit should name a commit, ideally a release tag, and the auditor should
report the commit each finding was made at, since the proofs and `regenerate`
pins move.

## Threat model

[AUDIT.md's threat model](AUDIT.md#threat-model) is the audit's: an attacker
who chooses every input and measures how long operations take, remotely and
from the same host. rind's promises are the four in
[SECURITY.md's "What counts"](SECURITY.md#what-counts): hostile input is an
error, never a panic or an unbounded cost; secret-dependent code is constant
time; results are correct; and keys, keyed state, and heap scratch derived
from a private key are wiped. A finding against any of the four is a finding.

Outside it, as AUDIT.md lists: fault injection, power and electromagnetic
analysis, speculative execution beyond the constant-time rule, a compromised
toolchain or dependency, a compiler other than CI's, a CPU or operating system
that breaks the constant-time assumptions [PLATFORMS.md](PLATFORMS.md)
describes, the operating system's random source, and a caller's misuse the API
permits. An auditor who finds the model wrong, or a promise with an
unreasonable exception, should say so; the model is part of what is audited.

## What is machine-checked, and what needs a human

[AUDIT.md's "Checks and their limits"](AUDIT.md#checks-and-their-limits) lists
what each check does and does not establish. For an auditor, the useful cut is
by property.

| Property | Machine-checked | Needs a human |
|---|---|---|
| Functional correctness of imported assembly | The published proofs of s2n-bignum and mlkem-native (HOL Light), HACL\* and Vale (F\*), fiat-crypto (Coq), and aws-lc-verification (SAW); for s2n-bignum's, mlkem-native's, Vale's, and aws-lc's routines `admin/prove bytes` checks that the release build holds the bytes the proof is about | That each proof's specification is the standard's, and that its preconditions hold at every call. Phase 1 does not re-prove upstream's theorems. |
| Functional correctness of rind's own assembly | rind's HOL Light proofs for the routines [`proofs/README.md`](proofs/README.md#hol-light-proofs) lists | Every hand-written routine without a proof (the ⚡ and "rind" cells of [ALGORITHMS.md](ALGORITHMS.md)), where vectors, differential tests, and fuzzing are the only checks. This is the largest Phase 1 item. |
| Functional correctness of rind's Rust | Lean proofs over Charon and Aeneas's translation, for the operations [BENCHMARKS.md's verified code](BENCHMARKS.md#verified-code) lists | That the translation is faithful, that each hand model computes what the Rust it quotes does, that each restated upstream theorem is the upstream statement, and that each transliterated spec is the standard. These are the [trust base](proofs/README.md#trust-base). |
| Correspondence of assembly to its call sites | `low::abi` (calling convention), `low::guard_pages` (bounds, on Unix), `admin/prove bytes` (clobbers and bytes) | The `asm!` operand constraints and `unsafe` contracts, which `low::inline_assembly_safety` argues; the `unsafe` blocks themselves ([AUDIT.md's table](AUDIT.md#unsafe)). |
| Constant time | valgrind, SDE, qemu, BINSEC, and `ct-vartime` over the paths each can run; s2n-bignum's `_SAFE` theorems for the routines it proves | Whatever no tool reaches: wasm; macOS, iOS, Windows, and Android builds; AES-GCM and ML-DSA on aarch64 under BINSEC; every secret the tests do not mark; the `Mcdt` and DIT handling around the multiplier and the Apple speculation barrier. |
| Memory safety | `unsafe` confined to `low` and the bindings; Miri and sanitizers on the portable backend and Rust code; guard pages on kernels | Assembly, which none of the dynamic tools instrument; the C ABIs of the bindings. |
| Hostile input | Wycheproof and fuzzing against aws-lc-rs, adapter fuzz targets that edit handshakes in flight | Cost bounds "by design": that no parser, loop, or allocation scales with attacker-chosen length beyond what the API documents; the protocols with no differential oracle (ECVRF, OPRF, blind RSA, SPAKE2+, FROST). |
| Wiping | `rind/tests/zeroing.rs` and `heap_scratch.rs` over the values they drop and the blocks they free | That every key type, and every heap scratch derived from a private key, is covered; that the wipe survives the optimizer in builds CI does not make. |
| API misuse resistance | Types make some misuse a compile error; `admin/adapter-api` checks the adapters' public items against upstream | Whether a caller can still do the unsafe thing by the API's intended route: nonce handling, key reuse, error types that distinguish what they should not (oracles in RSA, ECDSA, and AEAD failures). |
| Randomness | Random bytes have neither vectors nor a differential test | The `getrandom` use, behavior across `fork`, and the FIPS build's DRBG (`rind/src/fips_rng.rs`). |
| CPU dispatch | The tiers in [TESTING.md](TESTING.md#tiers) run under SDE and qemu | That every feature check selects only code the CPU, and the compile-time target, can run, and that no feature is assumed from another's presence. |

### Where Phase 1 should spend its time

In this order, which is [AUDIT.md's "Where the checks are thinnest"](AUDIT.md#where-the-checks-are-thinnest)
restated as a work list:

1. rind's own hand-written arithmetic with no proof, the ⚡ and "rind" cells of
   ALGORITHMS.md, such as parts of P-384 and P-521, x86_64 SHA-256, the
   portable RSA multiplication (its Montgomery products on 64-bit limbs too,
   whose proof is parked until
   quest/m4/verified/rsa-verify-portable-four-product.md), and armv7 Ed25519.
2. Code ported by hand from C or from another Rust backend: aws-lc's
   constant-time SSE2 AES and integer GHASH, and curve25519-dalek's AVX2
   backend, ported to intrinsics.
3. Imported assembly that runs without a proof: aws-lc's ChaCha20-Poly1305 on
   x86_64, RSAZ, Montgomery multiplication without ADX, the AVX2 SHA-2, VAES
   AES-GCM, and all of armv7's but its NEON GHASH, its SHA-256 with the
   crypto extension, and its NEON SHA-384/512; rind's structured copy of
   aws-lc's aarch64 ChaCha20-Poly1305, read in its four `.s` files rather
   than through the importer; and its copy of aws-lc's x86_64 AVX2 seal, read
   through `admin/chacha20poly1305-x86/generate`. Lean proves both copies
   constant-time but not that they compute the AEAD.
4. The Lean trust base: for each restated axiom, that it is the upstream
   theorem at the pinned revision with the preconditions rind's call sites
   meet; for each hand model, that it is what the Rust it quotes does; for
   each transliterated spec, that it is the standard.
5. `high`'s parsers and the `rind-rustls` boundary, as hostile-input code.
6. CPU dispatch, `Mcdt`, and DIT: the code that decides which of the above runs
   and in what mode.
7. The constant-time gaps: builds and primitives no tool reaches, and the
   secrets the tests do not mark.

## Out of scope

For both phases:

- The upstream proofs themselves. The HOL Light, F\*, Coq, and SAW proofs that
  s2n-bignum, HACL\*, Vale, fiat-crypto, and aws-lc-verification publish are
  taken as theorems, as the Lean proofs take them as axioms. The auditor
  checks that rind restates them faithfully and runs the object code they are
  about.
- Third-party crates rind links (`curve25519-dalek`, `fiat-crypto`,
  `getrandom`, `libcrux-*`, `libc`, `cfg-if`) beyond how rind calls them.
  [AUDIT.md's pins table](AUDIT.md#provenance) lists them.
- Unpublished crates and tooling: `rind-bench`, `rind-cpuid`, `rind-timing`,
  `rind-acvp`, the fuzz targets, the site, and `admin/` apart from the importers,
  `admin/parse-asm`, and `admin/regenerate`, which the generated-code rule makes
  the audited unit. `rind-fips` is out
  until published, and FIPS 140-3 validation is a separate process.
- The threat model's exclusions, listed above, and a flaw in a crate an
  adapter plugs into, such as rustls.
- Supply chain and release engineering: whether a release's build is
  reproducible, and the CI configuration, which the threat model excludes.
- Performance.

Phase 1 also leaves out Phase 2's code, apart from the PKCS#8 loaders above:
the ML-DSA signing and verifying kernels, Argon2id, ristretto255, hash-to-curve, the
protocols other than HPKE, the other adapters, and the bindings.

## What an engagement delivers

Each finding names the commit, the file and lines, the property of the four
above it breaks (or the model assumption it challenges), and a reproduction
or a failing test where one exists. Findings go to the maintainer privately as
[SECURITY.md](SECURITY.md#reporting-a-vulnerability) says; a fixed vulnerability gets the advisories
[SECURITY.md](SECURITY.md#supported-versions) describes. The auditor should also state what they
read and did not, per row of the inventory above, so the report says which
parts of Phase 1 have been looked at and which have not.
