# Security policy

## Reporting a vulnerability

Report it privately through GitHub: on the repository's Security tab, choose
[Report a vulnerability](https://github.com/kixel-ai/rind/security/advisories/new).
Don't open an issue, pull request, or quest for it, since those are public.

Say which package and version it affects, the target and CPU, and how to
reproduce it. If the flaw is in code rind took from another project, which
[ALGORITHMS.md](ALGORITHMS.md#sources) names, it may affect that project too:
report it there as well.

## What counts

These are the promises rind's code makes, and breaking one is a
vulnerability on every target, wasm included:

- **Hostile input.** A malformed key, signature, ciphertext, or encoding
  returns an error. A panic, or a cost the input can make unbounded, is a
  vulnerability.
- **Constant time.** No branch, memory index, or variable-time instruction in
  rind's secret-handling code depends on a secret.
- **Correct results.** rind computes what the algorithm's specification says,
  and accepts no forged signature or tag.
- **Wiping.** A key, keyed state, or heap scratch derived from a private key
  is wiped before it is freed, where [Wiping keys](README.md#wiping-keys) says
  rind wipes it.

Out of scope:

- The workspace's unpublished crates: rind-bench, rind-cpuid, rind-fips,
  rind-timing, and the fuzz targets. A flaw in rind's own code that rind-fips
  builds is a flaw in rind.
- What a wasm engine's compiler does to rind's constant-time code, which
  [PLATFORMS.md](PLATFORMS.md) says is unchecked. A secret-dependent branch or
  index in rind's own source is in scope.
- A flaw in a crate an adapter plugs into, such as rustls: report it to that
  project.

## Reviewing rind

[AUDIT.md](AUDIT.md) is where a security review of rind starts: its threat
model, where its code came from, what each check establishes, and where the
checks are thinnest.

DIT (data-independent timing) is a second layer beside the constant-time
promise. [Data-independent timing](README.md#data-independent-timing) says
what it rests on: Apple's documented barrier on Apple's cores (on Linux
too, picked from `MIDR_EL1`), and on any
other aarch64 core only the Arm architecture's rule (Arm ARM DDI 0487 M.d,
C5.1.3.3 and B1.5.6), which we have not tested on hardware.

## Advisories and CVEs

A confirmed vulnerability is fixed in the private GitHub security advisory
its report opened, and rind requests its CVE through that advisory, from
GitHub as the CVE Numbering Authority, before publishing it with the fixed
releases. [security.txt](https://rind.kixel.ai/.well-known/security.txt)
points scanners here.

## Supply chain

- **Dependencies.** `cargo vet` holds each crate version rind's lockfile
  resolves for the published `rind` crate, on any target and feature, to a
  safe-to-deploy audit: imported from Mozilla's, Google's, the Bytecode
  Alliance's, or ISRG's audits, rind's own in
  [supply-chain/audits.toml](supply-chain/audits.toml), trust in every
  release from a publisher Mozilla and the Bytecode Alliance also trust
  (dtolnay, BurntSushi, rust-lang-owner, alexcrichton), or an exemption in
  [supply-chain/config.toml](supply-chain/config.toml) for a version rind used
  before it began vetting. A new crate or version fails CI until one covers
  it; a newer version a dependent's own lockfile resolves is not covered.
  `cargo deny` checks every crate the workspace uses against RustSec's
  advisories, licenses, and sources.
- **Provenance.** A release attests, through GitHub's artifact attestations
  (SLSA build provenance signed through Sigstore), the `.crate` files it
  published to crates.io, pyrind's and pyrind-cryptography's files on PyPI,
  and rind-dart's prebuilt libraries on its GitHub release, each naming the
  commit it was built from as the provenance's first resolved dependency,
  which can be older than the commit that started the run. Check a file with
  `gh attestation verify <file> --repo kixel-ai/rind`; cargo keeps each
  crate it downloaded under `~/.cargo/registry/cache/`.
- **Reproducible builds.** Each build of rind-dart's prebuilt libraries and
  pyrind's wheels, nightly and for a release, runs twice from a clean target
  directory, and a release stops unless both match bit for bit. Both builds
  run on one runner, at the same paths and with the same toolchain: the Apple
  libraries record their build path, and the release takes the Rust stable of
  its day.
- **CI.** Every third-party GitHub Action is pinned to a commit, and a pull
  request's workflows get a read-only token. OpenSSF Scorecard scores the
  repository weekly:
  [its report](https://scorecard.dev/viewer/?uri=github.com/kixel-ai/rind).

## Supported versions

Below 1.0, only the latest release of each package rind publishes gets fixes:
the `rind` crate and its `rind-<consumer>` adapter crates on crates.io, and its
packages on pub.dev and PyPI. A fix lands on `main` and ships as a new release
of each package it affects, through the release PR that release-plz opens from
`main`. rind keeps no release branch below 1.0, so a fix is not backported: a
user on an earlier minor, such as 0.3 once 0.4 is out, takes the fix by moving
to the latest minor, which its changelog and [MIGRATING.md](MIGRATING.md)
describe.

From 1.0, the last minor of the previous major also gets security fixes for 6
months after the new major's first release, on a `release/<major>.<minor>`
branch, such as `release/1.4`, that release-plz opens its release PR from.
Every other earlier release takes the fix by upgrading.

A fix reaches crates.io and `pyrind` on PyPI when the release PR merges.
`pyrind-cryptography`'s version is bumped by hand, so a fix confined to it
publishes once its version is bumped and the `pyrind` it requires is released.
The Dart packages
on pub.dev publish from their own `rind-dart-v<version>` and
`rind-cryptography-v<version>` tags, so a fix reaches them once those tags'
workflows finish.

A fixed vulnerability gets a GitHub security advisory and a RustSec advisory.
