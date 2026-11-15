# [M] Prebuilt rind-openssl libraries

## Goal

Each rind-openssl release ships its shared library built for Linux on x86_64
and aarch64 and for macOS on arm64, with checksums and build provenance, so
an nginx, Node, Python, or Ruby deployment installs the provider without a
Rust toolchain.

## Plan

- Decided (maintainer): the libraries ship as assets on rind-openssl's
  GitHub releases under a `rind-openssl-v*` tag; distribution packages and
  shipping nowhere were rejected.
- rind-openssl is unpublished (`publish = false`): crates.io serves source,
  and OpenSSL loads a built library, so today the only route is
  `cargo build --release -p rind-openssl` from a checkout.
- Follow rind-dart's release, which already builds a shared library per
  target and attaches them to its tag's GitHub release
  (`.github/workflows/dart-release.yml` and `dart-libraries.yml`): a
  `rind-openssl-v*` tag, built on GitHub-hosted runners since the repository
  is public, Linux against an old glibc so one library loads on current
  distributions, each attested with `actions/attest-build-provenance`.
- Test each built library against the OpenSSL 3 its runner's distribution
  ships, as `rind-openssl/tests/provider.rs` does, before attaching it.
- Version it as the crate is: 3.x for OpenSSL 3's provider ABI, bumped as
  rind-dart's version is.
