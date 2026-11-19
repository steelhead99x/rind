# [S] ML-KEM encapsulates from a caller-supplied message

## Goal

A caller whose interface hands it the random source, such as the KEM traits' `encapsulate_with_rng`, or a test that replays known-answer vectors, encapsulates ML-KEM with 32 random bytes it supplies, through `rind::kem`'s public API, and the shared secret is FIPS 203's for that message, byte for byte. Nothing changes for the caller that encapsulates with the system random source.

## Plan

`rind::kem` draws ML-KEM's 32-byte message from the system source with no way to supply it. An adapter that ignored the caller's RNG would silently drop the randomness the caller chose, so [rind implements RustCrypto's traits](/quest/m2/rustcrypto/traits.md) could not honestly implement `kem`'s `Encapsulate`, and a known-answer replay through the public API was impossible. Fork draft PR steelhead99x/rind#162 implements the first item below; it is not posted upstream.

- Add one public type, `kem::Message`, in the shape the repo already uses for caller-supplied secret randomness (`ed25519::Seed`, `ml_dsa::Seed`, `vrf::Seed`, X-Wing's `Seed<A>`): a newtype that wipes on drop ✅ (rejected: the three below).
  - `Message::from_random_bytes(&mut [u8; 32])` takes fresh random bytes and zeroes the caller's array, so the caller keeps no copy to reuse.
  - `Message::encapsulate(self, &EncapsulationKey<A>)` consumes the message, so one message is used once. The type has no `Clone`, `Copy`, `Default`, or public bytes.
  - Its docs say the bytes must be fresh, uniform, from a CSPRNG, and never reused, guessable, or attacker-chosen, because the secret derives from them; the type cannot check that.
  - `EncapsulationKey::encapsulate` stays the one way to encapsulate with the system source. `Message` is a value the caller holds, not a second method on the key, and it is not a shim: nothing could do its job without it.
  - Only the public `Message` wipes on drop. `mid::mlkem::Message` stays unwiped, so the message `encapsulate` draws is an unwiped stack temporary, as REVIEW.md says.
- Rejected, so don't raise them again without new evidence:
  - Breaking `encapsulate` to take a random source or a `Message` each call, which is what `quest context`'s "make the breaking change to `foo`" would mean. Every caller that wants the system source then builds one by hand, and it breaks `rind-rustls`, `rind-openmls`, `rind-aws-lc-rs`, and the benches for the sake of one adapter.
  - `EncapsulationKey::encapsulate_with_message(&[u8; 32])`. It is the `foo_with_x` form `quest context` forbids, and a borrowed array can be reused, logged, or kept, so the secret is easy to repeat by accident.
  - Leaving the KEM traits out of the RustCrypto adapter and deleting that line of its quest. The adapter then cannot serve generic code over `kem`, which is what the quest is for.
- No existing public or crate-visible seam does the job: `mid::mlkem`'s `encaps_internal` is `pub(crate)`, and a feature or `doc(hidden)` export of it would be the same second entry point with fewer guards.
- X-Wing's derandomized encapsulation takes a 64-byte seed and HPKE derives its keys separately, so neither reuses this 32-byte type; it stays ML-KEM's.
- It is additive and adds no wire change, so no `!`.
- Tests: Wycheproof's and ACVP's ML-KEM encapsulation vectors through the public type for all three sets; the same message and key give the same ciphertext and secret and another message does not; aws-lc-rs decapsulates what a supplied message encapsulates; a dropped `Message` is zero in every byte; and `admin/ctgrind` marks the message secret.

## Waiting

- Maintainer: go-ahead for the public API, since the review of the draft finds `Message` close to the `foo_with_x` rule. Options: this newtype (recommended); `EncapsulationKey::encapsulate_message(Message)`, which is the same type with a second method on the key; or drop the KEM traits from the adapter. Done when this item is removed and the PR merges.
- Maintainer: the route. Land it under this quest first (recommended, as it is a public API addition), or with the adapter work under the traits quest's claim.

## Related

- [rind implements RustCrypto's traits](/quest/m2/rustcrypto/traits.md) - the consumer, `rind-kem`'s `Encapsulate::encapsulate_with_rng`
