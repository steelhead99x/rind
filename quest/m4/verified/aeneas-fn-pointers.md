# [XL] Every hand model of untranslated Rust is retired

## Goal

Aeneas translates the Rust that `proofs/` models by hand today, so each hand model, its quote check in `admin/prove`, and each hypothesis that stands in for Rust the translation leaves opaque is deleted, and the theorems are proven over the translation. A model whose limitation upstream has not lifted stays, listed in `proofs/README.md` with the issue that blocks it.

## Plan

Scope (maintainer, 2026-11-09): ✅ widen this one quest to retire every hand model of untranslated Rust (rejected: one quest per Aeneas limitation; leave it to the recurring re-audit). It was "Aeneas translates function pointers", which covered half of them. Re-sized from L to XL: seven kinds of limitation where there was one, ten quote-checked models of 3,451 lines that every API theorem in `proofs/` sits on, and each retirement re-proves the theorems above the model it removes.

The models, each quoting the Rust it models, which `admin/prove:41-97` checks against the source, by the limitation that blocks them:

- Function pointers ([AeneasVerif/aeneas#1500](https://github.com/AeneasVerif/aeneas/issues/1500), open: "Function pointers are not supported yet"), the dispatch every API reaches its algorithms through:
  - `proofs/Rind/X86_64/Dispatch.lean`: `agreement::Algorithm`'s `generate` and `load` and `Keyed`'s `Ops` (`rind/src/high/agreement.rs:20`, `:253`), and `quic::Algorithm`'s `new` and `Masker` (`rind/src/aead/quic.rs:17`, `:100`);
  - `DigestDispatch.lean` and `DigestAlgorithm.lean`: `digest::Algorithm`'s `hash` and `start` (`rind/src/high/digest.rs:20`);
  - `HmacDispatch.lean`: `hmac::Algorithm`'s `key` and the key and tag `Ops` (`rind/src/high/hmac.rs:114`, `:430`);
  - `AeadDispatch.lean`: `aead::Algorithm`'s `expand` and `Sealer`'s `Ops` (`rind/src/aead.rs:62`, `:245`);
  - `SignatureDispatch.lean`: `Verification` and `Parsed` (`rind/src/high/signature.rs:140`, `:222`);
  - `proofs/Rind/Aarch64/EcdsaDispatch.lean`: `EcdsaOps` and the ECDSA statics (`rind/src/high/signature.rs:793`, `:844`).
- Calls through `&dyn` (the same issue, whose title is that case): `proofs/Rind/Aarch64/P256Dispatch.lean` and `EcdsaDispatch.lean` model key generation's draws through `&mut dyn RandomSource` (`rind/src/mid/p256.rs:153`, `:223`).
- `'static` borrows ([AeneasVerif/aeneas#727](https://github.com/AeneasVerif/aeneas/issues/727), open): `DigestAlgorithm.lean` models `Digest`, whose `&'static Algorithm` (`rind/src/high/digest.rs:387`) Aeneas cannot end a borrow of `Digest` across.
- Nested borrows ([AeneasVerif/aeneas#1186](https://github.com/AeneasVerif/aeneas/issues/1186), open, a slice of slice references read in a loop):
  - `proofs/Rind/X86_64/HkdfExpand.lean`: `Prk::expand_into`'s `info: &[&[u8]]` (`rind/src/high/hkdf.rs:76`);
  - the `Drbg` hypothesis (`proofs/Rind/Aarch64/P256Ecdsa.lean:2303`): `HmacDrbg::update` takes the same shape (`rind/src/high/hmac_drbg.rs:44`), so `admin/prove:373` leaves the module opaque and the ECDSA theorems assume it seeds and draws without panicking.
- A closure that returns a borrow of its argument (no issue found): `EcdsaDispatch.lean` takes `Buffer::write`'s `write` (`rind/src/high/signature.rs:91`) as a Lean function.
- Raw-pointer loads, `transmute`, and zipped iterators: `proofs/Rind/X86_64/AesNi.lean` models the AES-NI key expansion and block cipher (`rind/src/low/x86_64/aes.rs:392`) and `u128_to_m128i`. Aeneas merged a heap model for raw pointers ([AeneasVerif/aeneas#1428](https://github.com/AeneasVerif/aeneas/pull/1428), 2026-10-13) before rind's pin, with [#1433](https://github.com/AeneasVerif/aeneas/pull/1433) open after it; `Iterator::zip` has [#1053](https://github.com/AeneasVerif/aeneas/issues/1053); no issue covers `transmute` between a vector and bytes. Try the pin on these first.
- Atomics and interior mutability (no request for support found; [AeneasVerif/aeneas#1525](https://github.com/AeneasVerif/aeneas/issues/1525), open, reports `Cell::set` and `Atomic*::fetch_add` modelled as pure):
  - the `Cached` hypothesis (`P256Ecdsa.lean:1828`): `ReuseCache`'s `AtomicU8` and `UnsafeCell` (`rind/src/low/generic/reuse_cache.rs:19`);
  - the `Held` hypothesis (`P256Ecdsa.lean:1819`) and the `new_secret` half of each `Runs` hypothesis: the entry guard's thread-local `Cell` (`rind/src/low/entry.rs:8`).
- Standard-library impls Aeneas's library has no model of:
  - the `VecAsMut` and `VecExtend` hypotheses (`proofs/Rind/X86_64/AesGcm.lean:297`, `:302`): `Vec<u8>`'s `AsMut<[u8]>` and `Extend<&u8>`;
  - `proofs/Rind/Core.lean:17-140`: 18 `core` items modelled after the standard library. These retire as Aeneas's library gains each.

Not this quest's, and they stay:

- `proofs/Rind/X86_64/Simd.lean`: `core::arch` intrinsics are LLVM builtins with no Rust to translate. `admin/prove` tests its models against the CPU instead.
- `Fills` (`P256Ecdsa.lean:2432`), that the system random source returns, and the dispatch half of `Runs`, `RunsSha512`, `RunsDouble`, `RunsValeAesGcm`, `RunsHmac`, and `RunsDigest`, which CPU the code is on: facts about the machine, not Rust.
- `ShaBlocks`, retired by its own quest. `P256Order` is proved in `proofs/Rind/P256Order.lean`.

Route:

- Start with what needs no upstream change: the raw-pointer loads on the pinned Aeneas, and the two `Vec` impls as models in `Rind/Core.lean`.
- For the rest, find out what Aeneas's and Charon's maintainers plan, and contribute support upstream if they welcome it. There is no standing approval to post: stop and ask the maintainer before posting outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [moq-dev/rind#448](https://github.com/moq-dev/rind/pull/448)).
- If upstream won't take a feature, report the options, such as restructuring rind's dispatch into something Aeneas translates without losing speed, and let the maintainer pick.
- Retire each model as its limitation lifts: move the Aeneas pin, translate the Rust, re-prove the theorems over it, delete the model and its `check_quote` and `only_quoted` lines, and update `proofs/README.md`'s trust base and `benchmarks/verified.toml`'s entries, which name the hand models.

## Waiting

- AeneasVerif/aeneas: function pointers and `&dyn` calls translate. Check `gh issue view 1500 --repo AeneasVerif/aeneas`; open on 2026-11-09.
- AeneasVerif/aeneas: a borrow can end across a `'static` reference. Check `gh issue view 727 --repo AeneasVerif/aeneas`; open on 2026-11-09.
- AeneasVerif/aeneas: a slice of borrowed slices translates. Check `gh issue view 1186 --repo AeneasVerif/aeneas`; open on 2026-11-09.
