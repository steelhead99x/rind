# Handoff: FIPS builds of rind-rustls and rind-aws-lc-rs

Delete this file before the claim lands. It is notes for the next agent.

Quest: [`quest/m4/fips/adapters.md`](https://github.com/kixel-ai/rind/blob/main/quest/m4/fips/adapters.md) on kixel-ai/rind `main` at `fdeaebc2`.

Claim: [kixel-ai/rind#873](https://github.com/kixel-ai/rind/pull/873), draft, head `steelhead99x:quest/m4/fips/adapters` at `1f06a93ed49f944ba401b3a5fd276fa2c502e5cd` (`chore(quest): claim quest/m4/fips/adapters.md`, `Quest-Claim: e41b1d491235189d`). The commit is empty on top of `fdeaebc2`. Leave that PR a draft until `just ci` is green. Fork handoff: [steelhead99x/rind#144](https://github.com/steelhead99x/rind/pull/144).

Do not merge this handoff into the quest branch. Implement on this branch, delete this file, and merge into `quest/m4/fips/adapters` with a merge commit only once the work is ready, so [kixel-ai/rind#873](https://github.com/kixel-ai/rind/pull/873) fast-forwards.

## Done when

- `rind-aws-lc-rs` and `rind-rustls` accept their upstreams' `fips` feature and back it with `rind-fips`. A consumer who builds aws-lc-rs or rustls with `fips` swaps the package or the provider and changes nothing else.
- With the feature, `try_fips_mode()` is `Ok(())`. Without it, it still returns `Err("FIPS mode not enabled!")`.
- rustls's provider pieces report `fips()` exactly where rustls 0.23.36's `crypto::aws_lc_rs` provider does, including `CryptoProvider` defaults: TLS 1.3 AES-GCM through the TLS IV unit, P-256 and P-384 ECDH, X25519MLKEM768 (ML-KEM inside the module, X25519 outside it), and ECDSA, RSA, Ed25519, and ML-DSA signatures.
- `rind-aws-lc-rs`'s README no longer lists `fips` as refused. It lists the aws-lc-rs FIPS functions the module cannot back.
- Tests cover both feature states. `nix develop -c just ci` passes.
- The finishing PR deletes `quest/m4/fips/adapters.md` and every link to it.

## Where

- `rind-aws-lc-rs/Cargo.toml`: the `fips` feature is absent, and `[package.metadata.rind.api] skip` refuses it. README lines that say the feature is refused. `src/lib.rs` `try_fips_mode`, `fips_version`, `try_fips_cpu_jitter_entropy`. `src/aead/tls.rs` `TlsRecordOpeningKey` (today a `LessSafeKey`). `tests/aws-lc-rs/unit/lib.rs` `test_fips` expects `try_fips_mode` to fail.
- `rind-rustls/Cargo.toml`: the same `skip` for `fips`. `src/lib.rs` `default_provider` always offers the non-FIPS defaults, including ChaCha20-Poly1305. README "What rind cannot back" is MLKEM1024 and ML-DSA, which [steelhead99x/rind#137](https://github.com/steelhead99x/rind/pull/137) is adding on another branch.
- `rind-fips`: approved API only, glibc Linux x86_64 and aarch64 (`#![cfg(rind_fips_module)]`, empty elsewhere). `aead::TlsRecordSealingKey` seals TLS 1.3. There is no `TlsRecordOpeningKey`; `aead::Key` opens. `hkdf` refuses an empty salt and an empty `info`. `version()` is a string, `self_test()` aborts on failure. README already says a FIPS build of rind-aws-lc-rs wraps `aead::Key` for aws-lc-rs's opening type.
- `rind-acvp`: `KDA/HKDF/<hash>` is registered. `HKDF/<hash>/extract` and `HKDFExpandLabel/<hash>` are not. Add the TLS 1.3 KDF only if the rustls FIPS provider derives those secrets through the module.
- `MIGRATE.md` still says to drop the `fips` feature.

## Feature map

`fips` on `rind-aws-lc-rs` matches a package rename that still passes `features = ["fips"]`. `fips` on `rind-rustls` matches rustls's `fips` feature (dev-dependency rustls 0.23.36; the library dependency is rustls 0.23.20, so confirm that release already has the feature).

Approved operations go through `rind-fips`. X25519, ChaCha20-Poly1305, and the other algorithms the module leaves out stay on `rind`, and their `fips()` is false. rustls's `default_provider` under `fips` keeps only suites and groups whose `fips()` is true and drops ChaCha20-Poly1305 from `DEFAULT_CIPHER_SUITES`. Copy that shape from rustls `crypto/aws_lc_rs/mod.rs` at v0.23.36. `SecureRandom` and `KeyProvider` `fips()` follow `try_fips_mode().is_ok()`, as rustls does.

`TlsRecordOpeningKey` in the FIPS build wraps `rind_fips::aead::Key`. Sealing stays on `TlsRecordSealingKey`.

These stay unimplemented, and the README names them: `try_fips_cpu_jitter_entropy` and `fips_cpu_jitter_entropy` (the module takes OS entropy), `awslc_version`, and `try_fips_self_test` (`self_test()` aborts and returns nothing). `fips_version()` has no AWS-LC module number to return.

## Tests and CI

On glibc Linux x86_64, in `nix develop`:

- `cargo check -p rind-aws-lc-rs --locked --features fips` and the same without `fips`.
- `cargo test -p rind-aws-lc-rs --locked --features fips` and without. The existing `test_fips` must follow the feature.
- `cargo check -p rind-rustls --locked --features fips` and `cargo test -p rind-rustls --locked --features fips`.
- A comparison, under `fips` and without it, of each suite, group, and signature algorithm's `fips()` with rustls's aws-lc-rs provider.
- A TLS 1.3 AES-GCM seal with `TlsRecordSealingKey` opened through the FIPS `TlsRecordOpeningKey`.
- wasm and the default feature set stay building with `fips` off. `rind-fips` does not build there.

Then `just ci` in that shell. `sh/dispatch.sh` selects the `adapters` module from `rind-aws-lc-rs` and `rind-rustls` sources. `admin/adapter-api` skips `fips` because turning it on for the upstream crate builds AWS-LC's FIPS module. Decide whether the diff can learn the `fips` API without that build.

## Ordering with fork PR 137

[steelhead99x/rind#137](https://github.com/steelhead99x/rind/pull/137) (`cursor/rustls-pq-parity-5a1c`, base `quest/m3/parity/rustls`, upstream claim [kixel-ai/rind#860](https://github.com/kixel-ai/rind/pull/860)) adds MLKEM1024 and ML-DSA to rind-rustls. It touches `rind-rustls/Cargo.toml`, `src/lib.rs`, `src/kx_group.rs`, `src/kx_group/mlkem.rs`, `src/sign.rs`, `src/verify.rs`, the README, and the handshake tests. This quest's FIPS provider needs ML-DSA and already has X25519MLKEM768 on main. MLKEM1024 is not in this quest's FIPS list.

The two quest branches both come from upstream `main` and both edit rind-rustls. Landing either second conflicts. Prefer to implement the FIPS provider after #860 has landed, so ML-DSA has one implementation. Do not merge #137 or fork `main` into `quest/m4/fips/adapters`: those commits are not on upstream `main`, and the claim PR would try to land them. If both proceed together, expect conflicts in the files above and in the `omitted` list (#137 drops `kx_group::MLKEM1024`; this work drops the `fips` skip).

## Open questions

- `fips_version()`: recommend `None`, and name it in the README as a function the module cannot back. Change that if Deno's FIPS build ([denoland/deno#36906](https://github.com/denoland/deno/pull/36906)) requires `Some`.
- `try_fips_self_test`: recommend leaving it omitted, because `rind_fips::self_test` aborts instead of returning `Result`.
- TLS 1.3 KDF in `rind-acvp`: recommend registering `HKDF/<hash>/extract` and `HKDFExpandLabel/<hash>` only after a trace shows the FIPS provider's key schedule calls the module's HKDF.
- `admin/adapter-api`: recommend a rind-only `--features fips` build in the test lane, and keep the upstream `fips` feature out of the API diff if that diff would compile AWS-LC's FIPS module.
