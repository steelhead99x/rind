# [S] rind-openssl's ML-DSA test passes on aarch64

## Goal

`rind-openssl/tests/ctgrind.rs`'s `ml_dsa` test passes on aarch64 Linux, so main's nightly `build (ubuntu-24.04-arm, stable)` and `asan (ubuntu-24.04-arm)` rows go green again.

## Plan

Planned with the maintainer on 2026-11-27 (`/quest-run`, found by [kixel-ai/rind#1137](https://github.com/kixel-ai/rind/pull/1137)).

- Caused by [kixel-ai/rind#1053](https://github.com/kixel-ai/rind/pull/1053), which added ML-KEM and ML-DSA to rind-openssl for OpenSSL 3.5+. Since then, `EVP_DigestSignInit_ex` returns 0 at `rind-openssl/tests/ctgrind.rs:390` on aarch64, in main's nightly [build](https://github.com/kixel-ai/rind/actions/runs/45922743778) and [sanitizers](https://github.com/kixel-ai/rind/actions/runs/45922292656) runs. The other three tests in the file pass there.
- Reproduce it on an aarch64 Linux host and find why signature initialisation fails there: the OpenSSL version the row links, provider dispatch, or an aarch64-only path in rind's ML-DSA glue. Fix that cause. If the row's OpenSSL predates 3.5, the test must require 3.5 the way the rest of `rind-openssl` does; don't skip only aarch64.
