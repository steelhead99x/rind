# [S] ML-DSA signing checks its likeliest rejection first

## Goal

ML-DSA signing orders its rejection checks by how often each rejects, as mldsa-native's `bbbb8bc4` (2026-09-22, "sign: Order rejection checks by rejection rate") does: the low bits of `w0 - c*s2` first, then `z`, then `c*t0`, so a rejected attempt skips the work the later checks need. BENCHMARKS.md's ML-DSA signing against aws-lc-rs says what it gained.

## Plan

Found by the 2026-11-14 [upstream-updates](/quest/m2/upstream-updates.md) run. rind ported its signing from mldsa-native v2.0.0, before that commit, and checks `z` for each polynomial first (`sign_internal`, `rind/src/mid/mldsa.rs`).

- The order reveals nothing new: each check's result is already public (`rejected` in `rind/src/mid/mldsa.rs` declassifies it, as mldsa-native does), and today a `z` rejection already skips the `w0 - c*s2` work, so which check fails first is visible either way. Each check stays constant-time on its own; keep `admin/ctgrind`'s signing test passing.
- [kixel-ai/rind#767](https://github.com/kixel-ai/rind/pull/767) made a key expand once, so the reorder works over the expanded key's `s1`, `s2`, and `t0`.
- Measure with `rind-bench`'s ML-DSA bench before and after, on x86_64 and aarch64; drop the change if it gains nothing measurable.
