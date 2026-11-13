# [XL] The API takes one shape

## Goal

Every key type in `rind` loads, exports, and hands out its public key the same way, and every module names the same thing the same way, so a caller who has learned one can guess the next. The maintainer has seen the API as per-algorithm modules (`ecdsa::KeyPair`, `ed25519::KeyPair`, `rsa::KeyPair`, `ml_dsa::KeyPair<P>`) in a draft PR with its full migration, and rind 0.4 ships whichever shape they chose.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit), after an audit that read the public modules side by side:

- ✅ Spike per-algorithm modules, and fold the naming fixes below into whichever shape wins (rejected: keep today's modules and fix names only; commit to per-algorithm modules without a spike). The spike exists because the cost is only visible in the diff: what MIGRATING.md gains, and what every adapter has to change.
- ✅ rind 0.4 waits for the verdict and the winner (rejected: fix names in today's modules for 0.4 and redesign in 0.5; only HKDF joins 0.4). [rind 0.4 ships once](/quest/m2/api/release-0.4.md) requires this quest.

Steps:

1. Open a draft PR that moves the signature key types into per-algorithm modules and applies every fix below. It carries the whole MIGRATING.md change and every adapter's change, since those are what the maintainer is judging. ARCHITECTURE.md's description of `high` changes with it.
2. Hand it back as a draft, with a `Maintainer:` item under `Waiting` for the verdict. Give both options their cost from the diff: lines of adapter change, and rows MIGRATING.md gains or loses.
3. If accepted, finish it. If rejected, the same PR drops the module moves and keeps the fixes in today's modules. Either lands as one `!` change.

What the audit found, on `main` that day. Each is a fix in either shape:

- A public key's `new` means three different things. It takes the raw encoding in `agreement` (`rind/src/high/agreement.rs:533`), `kem` (`kem.rs:81`), `hpke` (`hpke.rs:292`), and `vrf` (`vrf.rs:305`). It takes SubjectPublicKeyInfo only in `blind_rsa` (`blind_rsa.rs:215`). It sniffs PKCS#1 or SubjectPublicKeyInfo in `oaep` (`oaep.rs:177`) and `signature` (`signature.rs:260`), which also has `from_spki` (`signature.rs:291`). Pick one meaning for `new` and name the others.
- `vrf` alone calls its private key `SecretKey`, loads it with `from_bytes`, exports it with `to_bytes`, and returns `SecretKeyBytes` (`vrf.rs:65,111,156,258`). `agreement` and `hpke` say `PrivateKey`, and `signature` and `blind_rsa` say `KeyPair`. Two modules name a key for what it does: `kem` has `DecapsulationKey` and `EncapsulationKey` (`kem.rs:31,71`), FIPS 203's names, and `oaep` has `DecryptingKey` and `EncryptingKey` (`oaep.rs:70,168`). Say in the PR whether those four stay or join the rest.
- `public_key()` returns a borrow in `agreement` (`agreement.rs:158`) and `vrf` (`vrf.rs:164`), and an owned value in `signature` (`signature.rs:989,1539,1776`), `kem` (`kem.rs:42`), `hpke` (`hpke.rs:226`), `oaep` (`oaep.rs:119`), and `blind_rsa` (`blind_rsa.rs:161`). The borrow is the newer decision ([kixel-ai/rind#529](https://github.com/kixel-ai/rind/pull/529)).
- A key pair's `to_spki()` duplicates `public_key().to_spki()`, and `agreement::PrivateKey`, `blind_rsa::KeyPair`, and `MlDsaKeyPair` lack it. AGENTS.md asks for one way to do each job.
- A parameter set is `signature::sign::MlDsaParameterSet` (`signature.rs:1608`) for ML-DSA, `SlhDsaParameterSet` in [kixel-ai/rind#641](https://github.com/kixel-ai/rind/pull/641) for SLH-DSA, and a trait named `kem::Algorithm` in [kixel-ai/rind#606](https://github.com/kixel-ai/rind/pull/606) for ML-KEM.
- `gcm::TagLength` (`rind/src/aead/gcm.rs:22`) and `RsaPssSaltLength` (`signature.rs:1181`) are public enums without `#[non_exhaustive]`, so a new variant is a breaking change.
- `key_wrap::AesKek` has a `_padded` twin of each method, and a method named `unwrap` (`rind/src/mid/aes_kw.rs:59,82,114,155`), which reads as `Option::unwrap` at every call site.

Modules that land while this quest runs join the sweep. On that day they were Argon2 ([kixel-ai/rind#634](https://github.com/kixel-ai/rind/pull/634)), a free `derive` with a const length where PBKDF2 is `Secret::new(algorithm, secret).derive(iterations, salt, out)` (`rind/src/high/pbkdf2.rs:47,61`); SPAKE2+ ([kixel-ai/rind#689](https://github.com/kixel-ai/rind/pull/689)), whose `start` takes four or five positional arguments and whose loaders are `from_bytes`, `from_w1`, and `from_record`; OPRF ([kixel-ai/rind#705](https://github.com/kixel-ai/rind/pull/705)); SLH-DSA; and ML-KEM. Don't hold those PRs for this: sweep what is on `main` when the spike is written, and again before it lands.

The adapters promise their upstream's API, so none of this renames anything of theirs. They change only where they call rind.

Don't reopen what [the API epic](/quest/m2/api/README.md) rejected: `SharedSecret`'s `AsRef<[u8]>`, GCM's short tags, `constant_time::verify`'s two errors, and the hash in `verify_digest` all stay.

## Related

- [A PKCS#8 key of unknown type loads in one call](/quest/m2/api/pkcs8-any.md) - builds on the key types this settles
