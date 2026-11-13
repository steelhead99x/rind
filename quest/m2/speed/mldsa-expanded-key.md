# [M] An ML-DSA key expands once

## Goal

An ML-DSA key pair or public key does its expansion once and keeps it, behind the API it has today, so each signature and each verification after that skips the work that depends only on the key: rebuilding the matrix `A` from its seed, and unpacking and transforming the secret vectors. When it happens is the Plan's to say: a public key expands on its first verification, not at load. BENCHMARKS.md shows sign and verify against aws-lc-rs with the key already loaded.

## Plan

Found by the 2026-11-12 audit; it needed no decision, since the API does not change.

- Today every signature unpacks `s1`, `s2`, and `t0`, runs the NTT on each, and expands `A` again (`sign_internal`, `rind/src/mid/mldsa.rs:497-536`). Every verification expands `A` into a fresh `vec!` (`verify_internal`, `mldsa.rs:643-656`), and `MlDsaVerifier` keeps only `tr` (`rind/src/high/signature.rs:1670`). `A` is `k * l` polynomials of SHAKE128 output, 30 for ML-DSA-65.
- Measure first, to know what the key-only work is worth: time sign and verify as they are, then with `A` and the vectors hoisted. The report has no ML-DSA numbers to start from: BENCHMARKS.md lists ML-DSA-65 under "Not timed" on every host, though `rind-bench/benches/mldsa.rs` exists, until [the refresh](/quest/m2/bench/report-refresh.md) runs.
- Bench both shapes of use: verify with a key already loaded, and load then verify once, which is what a TLS handshake does with a certificate. Both go through the one public path, `PublicKey::new` then `verify` (`rind/src/high/signature.rs:260`, `:366`), which rind-rustls runs for each certificate (`rind-rustls/src/verify.rs:187`), so a key cannot tell whether a second verification will follow. Expand on the first `verify` and keep the result, not at load: that verification does the expansion today's does, plus whatever keeping the matrix costs, which is its allocation outliving the call, the once-cell, and the wipe on drop. If the bench shows that extra on load-then-verify-once, there is no uncached route to fall back to without new API. Stop and bring both numbers to the maintainer, with the choices: accept it, keep the expansion for signing keys only, which are held where a verification key often is not, or plan a separate call as its own quest.
- Compare with what aws-lc-rs does on each path, and follow it where rind has a choice.
- The expanded secret vectors are as good as the key. They live on the heap, are wiped through `low::zeroise` before they are freed, and `rind/tests/zeroing.rs` and the `heap_scratch` tests cover them, as AGENTS.md requires. `A` and `t1` are public, but a key type wipes its whole value.
- Signing's secret-dependent paths are already under `admin/ctgrind`; add its test for whatever loading now does with the secret.
- Hold the larger key in memory deliberately: say in the type's docs what a loaded key costs for each parameter set.

## Related

- [Benchmark report refresh, before rind 0.4](/quest/m2/bench/report-refresh.md) - the first ML-DSA numbers in the report
