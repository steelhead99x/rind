# [S] X-Wing

## Goal

`rind::kem` offers X-Wing (draft-connolly-cfrg-xwing-kem), the hybrid of X25519 and ML-KEM-768 that HPKE registers as KEM `0x647A` and draft-ietf-hpke-pq names MLKEM768-X25519, and that the MLS post-quantum ciphersuites `0x0010`, `0x0011`, and `0x0020` use, faster than any other Rust implementation.

## Plan

From [the scope](/quest/m4/pq/README.md), 2026-11-06.

- Compose it from rind's own X25519, ML-KEM-768 key generation from a seed, SHAKE256, and SHA3-256; no new arithmetic. The private key is the 32-byte seed, expanded on load; the decapsulation key keeps the expanded keys so decapsulation doesn't re-derive them.
- Its wire format hasn't changed since draft-06. The draft moved to the Independent Submission stream at draft-11, and draft-irtf-cfrg-concrete-hybrid-kems calls its MLKEM768-X25519 "identical to X-Wing", so one implementation serves X-Wing, HPKE, and MLS.
- API: a sealed `XWing` marker beside ML-KEM's, so `DecapsulationKey<XWing>` and friends work as ML-KEM's do, plus seed import and export, which HPKE's `DeriveKeyPair` and X-Wing's own key format need.
- Measured on desktop and kixtop: libcrux-kem takes 30 to 33 µs to generate, 47 to 55 µs to encapsulate, and 57 to 67 µs to decapsulate, and RustCrypto's `x-wing` 1.5 to 2 times that. rind's parts sum to about 11, 25, and 19 µs on desktop.
- aws-lc-rs has no X-Wing, so test against draft-11's Appendix C vectors and draft-ietf-hpke-pq's MLKEM768-X25519 vectors, and differentially against libcrux-kem and RustCrypto's `x-wing`, as the [epic](/quest/m4/pq/README.md) decided. If no earlier leaf has, add the epic's line to AGENTS.md's differential-testing rule. ctgrind covers keygen and decapsulation.

## Related

- [HPKE's post-quantum KEMs](/quest/m4/protocols/hpke-pq.md) - offers X-Wing in `hpke` as KEM `0x647A`, which this quest leaves to it
