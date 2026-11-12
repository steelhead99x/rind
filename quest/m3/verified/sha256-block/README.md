# x86_64 SHA-NI SHA-256 is proven

## Goal

x86_64 with SHA-NI runs a proven SHA-256 at today's speed, the in-register finish included, so SHA-256, HMAC-SHA256, and HKDF-SHA256 earn ✓ there.

This epic's own work is the ✓: `Rind/X86_64/ShaBlocks.lean`'s `Sha256Blocks` no longer assumes `shaext` or `shaext_finish`, `HashAxioms.lean` pins the frozen routine's axiom in their place, `benchmarks/verified.toml` gives the x86_64 SHA-NI cells their proof line, noting the pinned unmerged s2n-bignum PR, and `BENCHMARKS.md` is rendered from it.

## Plan

Planned with the maintainer on 2026-11-03 from the audit, which found no SHA-256 block function rind runs is proven on any path. Performance comes first: never take a proven routine that is measurably slower.

Route (maintainer, 2026-11-09): start on [awslabs/s2n-bignum#450](https://github.com/awslabs/s2n-bignum/pull/450) at a pinned commit (draft and untouched since 2026-09-08), measure its `sha256_compress_hw`, switch only if it ties at every size, and otherwise freeze rind's own routine as assembly and prove it on #450's spec. The ✓ notes the pin until upstream merges. Unmerged upstream comes in as the calibration settled: each unmerged s2n-bignum file rind needs is vendored unchanged under `proofs/hol-light/s2n-bignum/` at its upstream path, with its PR and commit in [that directory's README](/proofs/hol-light/s2n-bignum/README.md). aarch64's routine is proven the same way in `proofs/hol-light/aarch64/sha256_block_data_order_hw.ml` ([moq-dev/rind#552](https://github.com/moq-dev/rind/pull/552)).

Step 1, measured 2026-11-11 on a Ryzen 9 9950X (Zen 5), a shared host, so noisy, with criterion and interleaved runs of one binary ([moq-dev/rind#611](https://github.com/moq-dev/rind/pull/611)): #450's routine at 7ef212f3 is aws-lc's `sha256_block_data_order_shaext` and ties today's routine from 1200 bytes up, but run as rind's other block functions are, with padding in memory, it is much slower on short input. SHA-256 is 1.60x slower at 32 bytes, HMAC-SHA256 with a reused key 1.50x at 32 bytes and 1.25x at 64, and HKDF-SHA256 7-15% slower. Feeding it today's padded lanes through 16-byte stores, which forward, still costs 11-16% at 32 and 64 bytes and in HKDF, since the state and digest then round-trip memory and the finish takes two calls. So rind keeps its own routine: no switch.

Step 2's shape (decided 2026-11-11 in #611, without the maintainer): split the finish rather than prove LLVM's output of today's `sha256_finish` whole.
- LLVM's output is 714 instructions with 13 branches on the tail's length, byte-sized loads, and calls to panic handlers, and needs `pslldq` and `por`, which neither s2n-bignum nor #450 models. A HOL Light proof would case-split every tail length over bytes.
- Instead the padding becomes plain Rust that Aeneas translates, and the rounds and the digest become one `asm!` block whose rounds are LLVM's output of today's intrinsics.
- As built ([moq-dev/rind#626](https://github.com/moq-dev/rind/pull/626)): the padding returns the tail's count of whole 16-byte lanes, the lane where the message ends as two little-endian words with the 0x80 and, when it is the last lane and fits, the length, and the length; the block loads the whole lanes from the message itself, zeros the rest, and puts the length in the last lane or in a second block when the lane count is 4. Passing all eight words in registers instead made a one-block SHA-256 twice as slow on Arrow Lake: today's code loads whole lanes 16 bytes at a time, and Rust cannot. Through a stack buffer, read back with 8-byte loads, the words measured 1-4% slower and 7.7% at SHA-256 32 bytes.
- Rejected: proving LLVM's whole output, for the reasons above.
- Its cost (maintainer, 2026-11-12, on [moq-dev/rind#626](https://github.com/moq-dev/rind/pull/626)): ✅ accept the split's fixed cost on short input, an exception to performance first, since it is what lets SHA-256, HMAC, and HKDF earn ✓ on x86_64 SHA-NI. It ties at 64 bytes and up on SHA-256 and at 1200 bytes and up everywhere; below that SHA-256 and HMAC cost 0.5-3% on Arrow Lake, HKDF-SHA256 expand 5.3% on Arrow Lake, and HMAC at 32 bytes 4.3% on Zen 3 (rejected: keep tuning, such as moving the end lane's assembly into the block, which grows the HOL Light proof; drop the split and prove LLVM's whole finish).

