# [XS] HPKE runs the IETF revision's edge-case vectors

## Goal

rind's HPKE tests run the edge-case test vectors that the IETF revision of RFC 9180 (hpkewg/hpke) adds, including the DHKEM(P-256) `DeriveKeyPair` vector whose first candidate is at or above the group order, so the key comes from counter 1.

## Plan

Found by the 2026-11-14 [upstream-updates](/quest/m2/upstream-updates.md) run: hpkewg/hpke's `e298f94` (2026-06-29, "Fix #65: add edge-case test vectors (#70)") adds them as an appendix of `draft-ietf-hpke-hpke.md`, in Markdown only, so `admin/sync-vectors` cannot fetch them. Today no test reaches the second candidate of `PrivateKey::derive` (`rind/src/high/hpke.rs`).

- Copy them by hand into `hpke.rs`'s tests, citing the revision of the draft they come from, with the empty and zero-byte `aad`, `pt`, `info`, and exporter context cases beside the rejection-sampling one.
- Add only the suites rind offers; X448 and the PQ KEMs stay out.
