<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/wordmark.svg">
    <img width="280" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/wordmark-light.svg" alt="rind: a curled strip of green graviola peel forms the r, followed by ind">
  </picture>
</p>

<p align="center">
  <strong>Cryptography slop. Fast, somewhat formally verified, and in pure Rust.</strong><br>
  A drop-in for ring, aws-lc-rs, and rustls.
</p>

<p align="center">
  <a href="https://crates.io/crates/rind"><img alt="Latest release" src="https://img.shields.io/crates/v/rind"></a>
  <a href="https://docs.rs/rind/"><img alt="Documentation" src="https://img.shields.io/docsrs/rind"></a>
  <a href="https://github.com/kixel-ai/rind/actions/workflows/build.yml?query=branch%3Amain"><img alt="Build Status" src="https://img.shields.io/github/actions/workflow/status/kixel-ai/rind/build.yml"></a>
</p>

- 🏎️ **As fast as aws-lc-rs and ring.** rind matches or beats both on
  [nearly every operation][benchmarks] TLS and QUIC run, from the handshake
  to each packet's AEAD.
- 🛡️ **Verified where it counts.** On x86_64 and aarch64, rind's
  elliptic-curve, RSA, ML-KEM, and ML-DSA arithmetic builds on [s2n-bignum]'s
  formally verified assembly, and rind's own [Lean proofs][proofs] carry
  X25519 and Ed25519 from its API down to it, as [Verified code][verified]
  lists.
- 🦀 **No C toolchain.** rind's assembly lives in Rust source: no C
  compiler, cmake, nasm, or perl, for the host or a cross target. A rustls
  client builds [faster][build-cost] over rind than over aws-lc-rs or ring.

## Every benchmark, on every CPU

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/kixel-ai/rind/main/benchmarks/overview-dark.svg">
  <img alt="Time over the fastest library's, by operation, library, and host" src="https://raw.githubusercontent.com/kixel-ai/rind/main/benchmarks/overview.svg">
</picture>

Each row is an operation and each column a library, with one square per
machine: x86_64 from Haswell to Zen 3 and Arrow Lake, and an Apple M4.
Green is the fastest library on that machine, or within 10% of it, and
red is over 8× slower. A shield marks formally verified code. Where
another library leads, mostly at short messages on Apple silicon, where
rind alone sets DIT around each call, [Known gaps][gaps] says why and what
closes it. [BENCHMARKS.md][benchmarks] has every time, build time, and
binary size.

The [launch post][launch-post] tells why rind exists and what building it
cost in AI tokens.

## Compared with the alternatives

<!-- comparison: `admin/bench-report render` writes this table -->
| Library | Build tools beyond rustc | Lacks, of the 14 algorithms benchmarked | Formally verified | Fastest, or within 10% |
|---|---|---|---|---|
| rind | [none](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#build-cost) | none | [aarch64: SHA-256 (some CPUs), SHA-512, SHA-3, HMAC (some CPUs), HKDF (some CPUs), X25519, Ed25519, P-256, P-384 (some operations); x86_64: AES-GCM (some CPUs), SHA-512 (some CPUs), SHA-3, X25519, Ed25519 (some CPUs, some operations), P-256 (some CPUs), P-384 (some operations), RSA (some CPUs, some operations)](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#verified-code) | [331 of its 354 times](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#speed) |
| [aws-lc-rs](https://github.com/aws/aws-lc-rs) | [cc](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#build-cost) | XChaCha20-Poly1305 (aws-lc has it, through aws-lc-sys) | [x86_64: SHA-512 (some CPUs)](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#verified-code) | [127 of its 354 times](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#speed) |
| [ring](https://github.com/briansmith/ring) | [cc](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#build-cost) | XChaCha20-Poly1305, P-521, ML-KEM | [none](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#verified-code) | [94 of its 294 times](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#speed) |
| [RustCrypto + dalek](https://github.com/RustCrypto) | [none](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#build-cost) | none | [none](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#verified-code) | [27 of its 282 times](https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#speed) |
<!-- end comparison -->

Build tools are what a minimal binary needs, algorithms count only what
[BENCHMARKS.md][benchmarks] times, a proof counts only when it covers an
operation's whole computation, and the last column counts each library's
times against the fastest library's on the same machine.

What the table leaves out favors the others:

- **FIPS 140-3.** aws-lc-rs's `fips` feature builds against an
  AWS-LC-FIPS module. Its newest releases build
  [AWS-LC-FIPS 4.x][aws-lc-rs-fips], which an accredited lab has tested and
  NIST is still reviewing, and older releases build earlier modules that
  hold [NIST certificates][aws-lc-fips]. rind has no FIPS validation.
- **Audits.** ring was in scope of [Cure53's 2020 audit of
  rustls][rustls-audit]. RustCrypto's [aes-gcm][rustcrypto-aes-gcm] and
  [chacha20poly1305][rustcrypto-chacha] have had an audit by NCC Group, and
  its [rsa][rustcrypto-rsa] crate an earlier one its code has since diverged
  from, it says; its p256, ml-kem, and ml-dsa crates say they have had none.
  rind has had no third-party audit.
- **Maturity and reach.** ring has run in production for years, and
  RustCrypto covers far more algorithms. Both build without `std`, which
  rind does not yet.

## Switch in one line

rind is new, so exercise due caution.

```toml
[dependencies]
# A rustls CryptoProvider: turn off rustls's default features, which compile aws-lc-rs.
rind-rustls = "0.23"
rustls = { version = "0.23", default-features = false, features = ["std", "tls12"] }

# Or keep your code, and rename the dependency: ring and aws-lc-rs's APIs, name for name.
ring = { package = "rind-ring", version = "0.17" }
aws-lc-rs = { package = "rind-aws-lc-rs", version = "1" }

# Or use rind's own API.
rind = "0.3"
```

### With rustls

Install [rind-rustls][] at startup, then use rustls as normal:

```rust,ignore
rind_rustls::default_provider().install_default().unwrap();
```

### With an agent

Paste this into your coding agent, in your repository:

```text
Move this repository from ring or aws-lc-rs to rind, following
https://raw.githubusercontent.com/kixel-ai/rind/main/MIGRATE.md
```

It migrates on a local branch, reports the build time, binary size,
benchmarks, and tests before and after, and asks before opening a PR or
filing an issue. To migrate by hand, [MIGRATING.md][migrating] maps each
ring and aws-lc-rs item to rind's.

### Directly

The `rind` crate's own API covers AES-GCM, ChaCha20-Poly1305, and
XChaCha20-Poly1305, QUIC header protection, X25519 and ECDH, ML-KEM,
HPKE, ECDSA, Ed25519, ML-DSA, SLH-DSA, and RSA signatures, RSA blind signatures, FROST threshold signatures, ECVRF, OPRFs, RSA-OAEP, SHA-1, SHA-2, and SHA-3,
HMAC, HKDF, PBKDF2, Argon2id, SPAKE2+, and AES key wrap. Each algorithm is a constant or a type and each key
type has one role, so misuse fails to compile:

```rust
use rind::ecdsa::{KeyPair, PublicKey, sign, verify};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let key_pair = KeyPair::generate(&sign::P256_SHA256_ASN1)?;
    let signature = key_pair.sign(b"hello")?;

    let encoded = key_pair.public_key().as_ref();
    let public_key = PublicKey::new(&verify::P256_SHA256_ASN1, encoded)?;
    public_key.verify(b"hello", signature.as_ref())?;
    Ok(())
}
```

[docs.rs][docs] documents every module, and [ARCHITECTURE.md][architecture]
describes the API's shape.

## Adapters

Each crate's README shows its setup.

| Crate | For |
|---|---|
| [rind-ring][] | ring 0.17's API, name for name |
| [rind-aws-lc-rs][] | aws-lc-rs 1.x's API, name for name, for every item rind backs |
| [rind-dimpl][] | DTLS 1.2 and 1.3 through [dimpl](https://github.com/algesten/dimpl) |
| [rind-str0m][] | WebRTC through [str0m](https://github.com/algesten/str0m) |
| [rind-openmls][] | MLS through [OpenMLS](https://github.com/openmls/openmls) |
| [rind-jsonwebtoken][] | JWTs through [jsonwebtoken](https://github.com/Keats/jsonwebtoken) |
| [rind-object-store][] | S3, Azure, and GCS request signing through [object_store](https://github.com/apache/arrow-rs-object-store) |
| [rind-rcgen][] | certificates through [rcgen](https://github.com/rustls/rcgen) |
| [rind-openssl][] | X25519 and Ed25519 for whatever links OpenSSL 3, as a provider its configuration loads; built from source |
| [rind-dart][] | Dart and Flutter, through FFI, as the `rind` package on [pub.dev](https://pub.dev/packages/rind) |
| [rind_cryptography][] | Dart and Flutter, as the `rind_cryptography` package, with the `cryptography` package's API on rind |
| [rind-python][] | Python, as the `pyrind` package on PyPI, with rind's own API |
| [pyrind-cryptography][] | Python, as the `pyrind-cryptography` package on PyPI, with pyca/cryptography's `hazmat` API on pyrind |

## Before you depend on it

rind was written with AI coding agents, and no one outside the project has
audited it. It is not FIPS 140-3 validated. [The comparison][comparison]
lists what the established libraries have that rind lacks, and where another
library is faster, [Known gaps][gaps] says why and what closes it.

## Wiping keys

rind wipes keys, keyed state, and heap scratch derived from a private key
on drop only under its `wipe` feature, as RustCrypto does with `zeroize`;
aws-lc-rs always wipes, and ring never does. The benefit of wiping is to avoid *unused keys* being leaked
in a heap dump, like with Heartbleed. But IMO, you have bigger issues at that point, and it's not worth the perf hit by default.
Enable it on `rind` itself, and Cargo turns it on beneath every
adapter too. rind-aws-lc-rs also has its own `wipe`, which turns on rind's
and wipes the adapter's own copies of secrets.

```toml
[dependencies]
rind = { version = "0.3", features = ["wipe"] }
```

## Data-independent timing

On Apple silicon, each rind call that handles a secret turns on DIT
(data-independent timing) at entry and back off on return. From the M3, DIT
turns off the data memory-dependent prefetcher that
[GoFetch](https://gofetch.fail/) leaks keys from constant-time code through,
and clearing it on return leaves the rest of the thread as the application
set it. The M1 and M2 have no such switch, so they pay the toggle's cost
without that protection. Arm says DIT changes nothing on its current cores, so rind sets it
only on Apple's platforms; aws-lc-rs and ring never set it.

DIT is a second layer, not the constant-time guarantee: on every platform,
rind's secret-handling code avoids branches, memory indices, and
variable-time instructions that depend on a secret, and [TESTING.md][testing]
lists the check each primitive gets.

Turning DIT on and off costs about 45-60 ns a call on Apple's M1 and M4, a
fifth of sealing a 1350-byte packet. A loop of small calls, such as sealing
a batch of QUIC packets, holds a guard around the batch to pay it once:

```rust
let _dit = rind::cpu::Dit::hold();
```

The guard covers every rind call its thread makes, including those through
rind-rustls and the other adapters, and does nothing off Apple's platforms.

## Platforms

rind has assembly for x86_64, aarch64, and 32-bit arm from ARMv7 on, and runs
portable Rust on any other architecture. CI tests Linux (glibc and musl),
macOS, and Windows on x86_64 and aarch64, Linux and Windows on 32-bit x86, iOS
in the simulator, Android on aarch64, armv7, ARMv5TE, x86_64, and 32-bit x86,
and Linux on armv7, ARMv6, big-endian s390x, riscv64gc (glibc and musl),
loongarch64, powerpc64le, and big-endian powerpc64 and powerpc. rind needs only
what each target enables at compile time, so it runs on every CPU the target
does.
[PLATFORMS.md][platforms] lists what each architecture runs without each
feature.

## Versions

rind is below 1.0, so a minor release is its breaking one. There is no date
for 1.0: it comes once the API takes one shape, every key type loading,
exporting, and naming things the same way, and no breaking change is planned.

- A patch release, such as 0.3.1 to 0.3.2, adds API and fixes bugs: code
  that built against an earlier patch of the same minor still builds. A fix
  can make rind refuse input it wrongly accepted.
- A minor release, such as 0.3 to 0.4, may break the API. rind batches
  breaking changes so that few minor releases are needed, the changelog
  marks each as **breaking**, and [MIGRATING.md][migrating] maps ring's and
  aws-lc-rs's names onto the API as it now stands.
- The minimum supported Rust version is each crate's `rust-version`, shown on
  its crates.io page. rind's is 1.90, and CI checks rind and every crate that
  shares it on 1.90. It rises only in a minor release, and only to a Rust at
  least nine releases (about a year) older than the latest stable, the window
  rustls allows itself. Correcting a `rust-version` the code never built on
  is a fix, which a patch can ship.
- Each adapter's version follows the upstream it adapts, as
  [CONTRIBUTING.md][releases] says. rind is not part of an adapter's API, so
  an adapter's patch release may move it to rind's next minor, and to that
  minor's `rust-version`. An adapter whose upstream needs a newer Rust than
  rind declares that one, as rind-openmls declares OpenMLS's 1.91, and CI
  does not yet check such a crate on its own `rust-version`.
- [SECURITY.md][supported-versions] says which releases get security fixes,
  and [PLATFORMS.md][platforms] which targets and CPUs rind supports.

## Contributing

AI reviews and contributions are welcome. rind plans its work as quests,
Markdown files under [`quest/`][quests], with skills for Claude Code and
Codex. With [quest][quest-setup] installed, have your agent run
`/quest-plan` to propose a change or report a finding, or `/quest-start` to
take a quest from the backlog. Report a vulnerability privately instead, as
[SECURITY.md][security] says. [CONTRIBUTING.md][contributing] covers
building, testing, and how a PR lands.

## Learn more

- [ALGORITHMS.md][algorithms]: whose code runs each algorithm on each CPU,
  what of it is formally verified, its sources and their licenses, and how
  the main paths work.
- [PLATFORMS.md][platforms]: the CPU features each architecture requires, and
  what runs without the optional ones.
- [ARCHITECTURE.md][architecture]: the API's design, its modules, and the
  layers beneath them.
- [BENCHMARKS.md][benchmarks]: every operation's time, build time, and binary
  size, against the other libraries.
- [AUDIT.md][audit]: where a security review starts: the threat model, each
  line's source and pin, what each check does and does not establish, and
  where the checks are thinnest.

## Built on great work

rind began as a fork of [Graviola] by Joe Birr-Pixton, and no longer tracks
it. **Graviola is an outstanding project**: a fast, carefully designed
cryptography library with a refreshingly simple Rust-only build. rind owes
it its starting point, much of its code, and the example it follows. If
Graviola covers your needs, please give it a look and support its authors.

**[aws-lc-rs] is excellent, too.** It is the library we would use if we did
not need to build without C. AWS-LC supplies many of rind's implementations,
and aws-lc-rs is our reference for behavior, differential tests, and
performance.

The credit for the underlying algorithms, implementations, and proofs
belongs to their authors, including [s2n-bignum], [HACL\*], [libcrux],
[fiat-crypto], and the other projects [ALGORITHMS.md lists][sources]. rind's
contribution is to distill and integrate their work.

The rind logo is a tribute to [Graviola's fruit illustration][graviola-logo],
reimagined as a curled strip of its protective rind. A [wordmark][rind-wordmark]
for dark backgrounds starts white `ind` beneath the curl and extends it to
the right.

## License

rind's own code is licensed under Apache-2.0 OR ISC OR MIT-0. Code copied
from other projects keeps its source's license, which [LICENSE] lists.

[Graviola]: https://github.com/ctz/graviola
[graviola-logo]: https://github.com/ctz/graviola/blob/main/admin/picture.png
[rind-wordmark]: https://raw.githubusercontent.com/kixel-ai/rind/main/admin/wordmark.svg
[aws-lc-rs]: https://github.com/aws/aws-lc-rs
[aws-lc-rs-fips]: https://github.com/aws/aws-lc-rs/blob/main/aws-lc-rs/README.md#fips
[aws-lc-fips]: https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/FIPS.md#validations
[rustls-audit]: https://github.com/rustls/rustls/blob/main/audit/TLS-01-report.pdf
[rustcrypto-aes-gcm]: https://github.com/RustCrypto/AEADs/tree/master/aes-gcm#security-notes
[rustcrypto-chacha]: https://github.com/RustCrypto/AEADs/tree/master/chacha20poly1305#security-notes
[rustcrypto-rsa]: https://github.com/RustCrypto/RSA#readme
[s2n-bignum]: https://github.com/awslabs/s2n-bignum
[HACL\*]: https://github.com/hacl-star/hacl-star
[libcrux]: https://github.com/cryspen/libcrux
[fiat-crypto]: https://github.com/mit-plv/fiat-crypto
[docs]: https://docs.rs/rind/
[quest-setup]: https://github.com/moq-dev/quest/blob/main/SETUP.md
[LICENSE]: https://github.com/kixel-ai/rind/blob/main/LICENSE
[rind-rustls]: https://github.com/kixel-ai/rind/tree/main/rind-rustls
[rind-ring]: https://github.com/kixel-ai/rind/tree/main/rind-ring
[rind-aws-lc-rs]: https://github.com/kixel-ai/rind/tree/main/rind-aws-lc-rs
[rind-dimpl]: https://github.com/kixel-ai/rind/tree/main/rind-dimpl
[rind-str0m]: https://github.com/kixel-ai/rind/tree/main/rind-str0m
[rind-openmls]: https://github.com/kixel-ai/rind/tree/main/rind-openmls
[rind-jsonwebtoken]: https://github.com/kixel-ai/rind/tree/main/rind-jsonwebtoken
[rind-openssl]: https://github.com/kixel-ai/rind/tree/main/rind-openssl
[rind-object-store]: https://github.com/kixel-ai/rind/tree/main/rind-object-store
[rind-rcgen]: https://github.com/kixel-ai/rind/tree/main/rind-rcgen
[rind-dart]: https://github.com/kixel-ai/rind/tree/main/rind-dart
[rind_cryptography]: https://github.com/kixel-ai/rind/tree/main/rind-dart/cryptography
[rind-python]: https://github.com/kixel-ai/rind/tree/main/rind-python
[pyrind-cryptography]: https://github.com/kixel-ai/rind/tree/main/rind-python/cryptography
[quests]: https://github.com/kixel-ai/rind/blob/main/quest/README.md
[launch-post]: https://moq.dev/blog/rind/
[contributing]: https://github.com/kixel-ai/rind/blob/main/CONTRIBUTING.md
[releases]: https://github.com/kixel-ai/rind/blob/main/CONTRIBUTING.md#releases
[supported-versions]: https://github.com/kixel-ai/rind/blob/main/SECURITY.md#supported-versions
[security]: https://github.com/kixel-ai/rind/blob/main/SECURITY.md
[migrating]: https://github.com/kixel-ai/rind/blob/main/MIGRATING.md
[benchmarks]: https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md
[gaps]: https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#known-gaps
[comparison]: https://github.com/kixel-ai/rind/blob/main/README.md#compared-with-the-alternatives
[build-cost]: https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#build-cost
[verified]: https://github.com/kixel-ai/rind/blob/main/BENCHMARKS.md#verified-code
[testing]: https://github.com/kixel-ai/rind/blob/main/TESTING.md#primitives
[proofs]: https://github.com/kixel-ai/rind/blob/main/proofs/README.md
[algorithms]: https://github.com/kixel-ai/rind/blob/main/ALGORITHMS.md
[sources]: https://github.com/kixel-ai/rind/blob/main/ALGORITHMS.md#sources
[platforms]: https://github.com/kixel-ai/rind/blob/main/PLATFORMS.md
[architecture]: https://github.com/kixel-ai/rind/blob/main/ARCHITECTURE.md
[audit]: https://github.com/kixel-ai/rind/blob/main/AUDIT.md
