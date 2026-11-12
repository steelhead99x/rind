# [S] An aws-lc-rs patch shim replaces aws-lc-rs across a binary's tree

## Goal

A binary that adds `[patch.crates-io] aws-lc-rs = { git = "https://github.com/moq-dev/rind-patch" }` builds every crate in its tree on aws-lc-rs 1.x against rind-aws-lc-rs, with aws-lc-sys gone from `cargo tree`, and CI proves it with a fixture.

## Plan

- Add an unpublished crate named `aws-lc-rs` (1.x) that re-exports the published rind-aws-lc-rs, as a member of [moq-dev/rind-patch](https://github.com/moq-dev/rind-patch)'s workspace beside `ring/`, and patch rind-aws-lc-rs to rind's checkout in `sh/patch.sh` as it does rind-ring.
- Extend `patch/fixture`, which `sh/patch.sh` runs, with s2n-quic-crypto and jsonwebtoken's `aws_lc_rs` feature, which both build on rind-aws-lc-rs today. Check that `cargo tree -i aws-lc-sys` prints nothing, and exercise each. The maintainer kept rustls's `aws_lc_rs` provider, rustls-webpki's `aws-lc-rs` feature, and rcgen's `aws_lc_rs` feature out of the fixture on 2026-11-07 while rind-aws-lc-rs lacked ML-DSA. ML-DSA is offered: webpki and rcgen build on it. rustls's provider still names `tls_prf` and, from 0.23.46, `kem::ML_KEM_1024`.
- Document it in MIGRATE.md and move the MIGRATING.md rows it unblocks, such as s2n-quic. quinn-proto and libp2p reach aws-lc-rs through rustls, which still does not build on rind-aws-lc-rs (`tls_prf`, and `kem::ML_KEM_1024` from rustls 0.23.46). ML-DSA is offered.
