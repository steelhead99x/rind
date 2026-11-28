# [XS] The 64-bit Poly1305 state is wiped when it is dropped

## Goal

`rind/src/low/generic/poly1305.rs`'s `Poly1305`, which x86_64's separate-pass ChaCha20-Poly1305 and the 64-bit portable backend run, wipes itself on drop as its 32-bit sibling does (`poly1305_32.rs`'s `impl Drop`), so the clamped key `r`, the pad `s`, the accumulator `h`, buffered message bytes, and, once [steelhead99x/rind#355](https://github.com/steelhead99x/rind/pull/355) lands, the cached powers r² and r⁴ of its SSE2 lanes no longer stay on the stack after a seal or open. AGENTS.md has every keyed type wipe itself.

## Plan

Found 2026-11-28 by #355's review (both reviewers' notes): the state never had a `Drop`, and #355 adds about 400 bytes of key powers to it. Planned as its own quest by the owner rather than fixed in #355.

- Add `impl Drop for Poly1305 { fn drop(&mut self) { zeroise_value(self) } }` and `impl Zeroable for Poly1305 {}`, as `poly1305_32.rs` does. `finish(mut self)` keeps working: it takes the value and drops it after reading the tag, with no destructuring move out of it.
- `Zeroable` promises that all-zero bytes are a valid value. Once #355's `Option<Powers>` cache is in the state, that is not guaranteed for an `Option`, so hold the cache in a form whose empty state is all zeros (for example the powers plus a `u64` flag that zero means unset) before marking `Poly1305` `Zeroable`.
- Test it as `poly1305_32_zeroing.rs` tests the 32-bit state: drop the value in place after a short update and after one long enough to fill the SSE2 cache on x86_64, then check its memory is zero. Tag correctness stays with the existing vector tests.
- Measure ChaCha20-Poly1305's 32 B, 1350 B, and 16 KB rows against aws-lc-rs on a host without SSE4.1 (or forced, as #355 does) before and after: every seal and open pays the fixed wipe, so the short rows show its cost.
