# rind replaces ring and aws-lc-rs throughout a binary's dependency tree

## Goal

A crate that calls aws-lc-rs's API switches to rind by renaming one dependency, as one on ring already can with rind-ring. A binary replaces ring or aws-lc-rs everywhere in its tree, including dependencies that hard-wire them such as quinn-proto, s2n-quic, and libp2p, with one `[patch.crates-io]` line that points at [kixel-ai/rind-patch](https://github.com/kixel-ai/rind-patch).

## Plan

Decided with the maintainer on 2026-11-07, in m2 adoption:

- A published `rind-aws-lc-rs` offers aws-lc-rs 1.x's API, versioned 1.x by the adapter rule (CONTRIBUTING.md's Releases). It stands alone rather than sharing rind-ring's code (the maintainer's call on 2026-11-07, since the two APIs differ in most details), and adds the extras rind already has, such as ML-KEM, AES-KW, and AES-CBC.
- Git-only shim crates in kixel-ai/rind-patch that are actually named `ring` (0.17.x) and `aws-lc-rs` (1.x) wrap the adapters, so a binary can patch them in. Cargo patches only with a crate of the same name, which crates.io has already taken, so the shims are never published.
- A patch applies only in a binary's own workspace. A dependency that calls an item rind doesn't offer fails to build, and the docs list those items.
- The `ring` shim ships first, since rind-ring already covers ring 0.17's API.
- MIGRATE.md and MIGRATING.md gain the patch route next to "port each call to rind's API". Every MIGRATING.md row the shims unblock moves out of Unsupported, such as s2n-quic; quinn-proto and libp2p still reach aws-lc-rs through rustls, which does not build on rind-aws-lc-rs yet (`tls_prf`, and `kem::ML_KEM_1024` from rustls 0.23.46). ML-DSA is offered.
