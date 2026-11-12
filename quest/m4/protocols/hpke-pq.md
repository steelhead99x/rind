# [M] HPKE's post-quantum KEMs

## Goal

rind's `hpke` module offers the post-quantum KEMs registered for HPKE that `rind::kem` implements: ML-KEM-512, ML-KEM-768, and ML-KEM-1024 (`0x0040` to `0x0042`) and X-Wing (`0x647A`, which draft-ietf-hpke-pq names MLKEM768-X25519), each with every KDF and AEAD `hpke` has.

## Plan

Planned in the quest audit of 2026-11-09, which found these KEMs without an owner: HPKE ([moq-dev/rind#585](https://github.com/moq-dev/rind/pull/585)) left them to the post-quantum epic, whose [X-Wing](/quest/m4/pq/x-wing.md) and ML-KEM quests stop at `rind::kem`.

- These KEMs are not Diffie-Hellman: `Encap` and `Decap` are the KEM's own, and `DeriveKeyPair` takes the KEM's seed, as draft-ietf-hpke-pq defines it. That makes this quest the consumer ML-KEM's decapsulation key import and export waited for; add the seed form here, and nothing wider.
- MLKEM768-P256 and MLKEM1024-P384 (`0x0050`, `0x0051`) join in [their own quest](/quest/m4/pq/cfrg-hybrids.md), which waits on the CFRG draft.
- [IANA's registry](https://www.iana.org/assignments/hpke/hpke.xhtml) lists all four code points today, against draft-connolly-cfrg-hpke-mlkem-04 and draft-connolly-cfrg-xwing-kem-06. draft-ietf-hpke-pq, which takes them over, is at -05 and not yet an RFC: reread it when this starts, and build what it then says.
- rind-rustls gains nothing: rustls's aws-lc-rs provider ships no post-quantum HPKE suite (rustls 0.23.46, `src/crypto/aws_lc_rs/hpke.rs:25`), and an adapter offers exactly its upstream's API. rind-openmls then takes openmls_rust_crypto's `draft-ietf-mls-pq-ciphersuites` feature, offering each MLS post-quantum ciphersuite of that provider whose KEM this adds (rind has ML-DSA already), and its README drops the feature from what rind cannot back.
- Test against Wycheproof's `hpke_mlkem512_*`, `hpke_mlkem768_*`, and `hpke_mlkem1024_*` files (encap, decrypt, and sequence, added by [C2SP/wycheproof#273](https://github.com/C2SP/wycheproof/pull/273)) and draft-ietf-hpke-pq's Appendix A vectors; differentially against [rozbb/rust-hpke](https://github.com/rozbb/rust-hpke), whose `src/kem` has `mlkem.rs` and `xwing.rs`, or `hpke-rs`, whichever has released them (aws-lc-rs exposes no HPKE); and ctgrind on `DeriveKeyPair` and decapsulation.

## Required

- [X-Wing](/quest/m4/pq/x-wing.md) - X-Wing and its seed import
