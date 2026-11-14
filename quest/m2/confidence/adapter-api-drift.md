# [M] The adapters' API drift is fixed

## Goal

Every entry in `admin/adapter-api.drift` is gone, and the file with it: the adapter matches its upstream's API there, or the item moves to the adapter's `omitted` and README with the maintainer's agreement. `admin/adapter-api` then holds each adapter to its upstream with no exceptions beyond what rind cannot back.

## Plan

`admin/adapter-api` found these on 2026-11-12, against the versions Cargo.lock resolved then:

- rind-ring: `rsa` and the RSA items in `signature` exist without `alloc`, where ring gates them behind it; `rsa::RsaParameters` is `UnwindSafe` and `RefUnwindSafe` where ring's is not; `error::KeyRejected` and `error::Unspecified` implement `std::error::Error` without `std`.
- rind-aws-lc-rs: `aead::Nonce`'s `From` impls, `kem::EncapsulationKey` and `kem::DecapsulationKey` being `Send` and `Sync` when `Id: Sync` where aws-lc-rs requires `Id: AlgorithmIdentifier`, `aead::RandomizedNonceKey::seal_in_place_append_tag`'s lifetime, `signature::VerificationAlgorithm`'s bounds, `rand::SystemRandom`'s impls, an added `modulus_len` on `rsa::PublicKey` and `signature::RsaSubjectPublicKey`, the missing `encoding::AsDer` impls for `signature::PqdsaPrivateKey` and `signature::PqdsaPublicKey` (found 2026-11-13, once trait impls compared their target), and `rand::SecureRandom` (missing `mut_fill`) and `rand::RandomlyConstructable`, with their blanket impls' bounds (found 2026-11-14, once impls for foreign types were compared), under `dev-tests-only`.
- rind-rustls: `Ticketer` exists without `std`, and the TLS 1.2 suites without `tls12`, where rustls gates them; `hpke`'s suites are `&dyn Hpke`, not `&HpkeAwsLcRs<..>`.

Decisions (2026-11-13):

- ✅ Keep this follow-up, picked with the check's PR (#698) (rejected: drop).
- ✅ The `drift` lists may only shrink, so new drift fails now (rejected: fix all drift before the check lands).
- ✅ rind-rustls's `hpke` suite type is drift to fix, since a divergence is a bug; match upstream's `&HpkeAwsLcRs<..>` type and drop the README note (rejected: move it to `omitted`).

`admin/adapter-api.drift` holds the full signatures; rerun `admin/adapter-api --bless` after each fix.
[moq-dev/rind#679](https://github.com/moq-dev/rind/pull/679) changes rind-aws-lc-rs; rebase this onto it.

The check itself has one known gap (CodeRabbit on #698, 2026-11-13): impls on an unexported type that a public item names, such as `impl RsaEncoding for Padding` behind ring's `RSA_PKCS1_SHA256`, are not compared, because the type renders as `$private` and is never visited. Collect the impls of exported traits for such types, keeping sealing traits out, before deleting the drift file.
