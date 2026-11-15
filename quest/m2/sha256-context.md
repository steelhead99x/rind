# [M] SHA-256's streaming context costs no more than one-shot on short inputs

## Goal

`digest::Context::new`, `update`, and `finish` for SHA-256 run within noise of one-shot `digest::digest` at 16 B and 64 B on x86_64 and aarch64.

## Plan

Found on 2026-11-12, benchmarking pyca/verified-garbage against rind on a Ryzen 9 9950X: SHA-256 through the context took about 36 ns at 16 to 64 B, against 19 ns one-shot. Decided with the maintainer the same day: ✅ a quest in m2. TLS and QUIC hash many short transcripts through the context.

[kixel-ai/rind#764](https://github.com/kixel-ai/rind/pull/764) removed the largest cost, a store-to-load forwarding stall: `finish` loaded the buffer `update` had just written with 16-byte loads spanning two of memcpy's overlapping stores, and waited for them to reach the cache. At 64 B on Zen 5 the context fell from 59.7 to 41.0 ns. What remains, measured on 2026-11-14 with each row pinned to one core, best of three:

| | one-shot | context | `Box`ed context | cloned, then finished |
|---|---:|---:|---:|---:|
| Zen 5, 16 B | 19.5 ns | 23.5 ns | 40.2 ns | 37.7 ns |
| Zen 5, 64 B | 36.5 ns | 41.0 ns | 65.7 ns | 59.3 ns |
| Arrow Lake, 16 B | 13.4 ns | 16.8 ns | 37.6 ns | 33.2 ns |
| Arrow Lake, 64 B | 24.0 ns | 26.3 ns | 49.5 ns | 44.1 ns |
| Apple M4, 16 B | 57.0 ns | 65.3 ns | 89.6 ns | 62.7 ns |
| Apple M4, 64 B | 75.8 ns | 84.3 ns | 110.8 ns | 81.5 ns |

The M4 rows, measured on `kixtop` on 2026-11-14 (best of three, unpinned), show the same 8 ns context gap before and after #764, and a `Box`ed context about 5 ns slower after it: macOS allocates the now 64-byte-aligned context through its slower aligned path.

- Close the last 3 to 4 ns: three indirect calls (the `State` enum's match, the backend's `OnceLock` path, the finish routine) and `finish` resetting the context it consumes.
- The `Box`ed row is the shape rind-rustls' `start` uses. Moving the 256-byte context through glibc's `memcpy` writes it in stores the next update's loads span, bringing the stall back. Build the context in its box, and win back the M4's 5 ns of aligned allocation, such as by aligning the context less where that keeps x86_64's gain.
- Keep one consuming `finish`, decided with the maintainer on 2026-11-15: ✅ one consuming `finish` (rejected: a non-consuming `finish(&self)`). rind-rustls clones only in `fork_finish`, a few times per handshake, about 0.2 µs against a 77 µs resumed handshake, so the cloned row is not worth a second way to finish.
- HMAC-SHA256's context runs about 20 ns over one-shot on Zen 5 (71.0 against 50.0 ns at 16 B), mostly moves of the keyed state in `with_key`. Same fix as the box.
- Prove nothing is lost: the digest proofs in `proofs/` cover the context path, so a change there keeps `admin/prove` passing.
