# [S] rind-openssl's ctgrind tests pass on the nightly toolchain

## Goal

rind-openssl's x25519 and ed25519 ctgrind tests pass in main's nightly, which builds them with the nightly toolchain, without weakening what they check.

## Plan

- They fail at `rind-openssl/tests/ctgrind.rs:78` in main's nightly, run 43769414294 (kixel-ai/rind Actions). Find whether a rind change or the toolchain moved, from the last green nightly, and name a causing PR under `## Caused by` if there is one.
- If nightly rustc now emits a secret-dependent branch or index, that is a constant-time bug to fix in rind's code, not to suppress. Add a `admin/ctgrind.supp` entry only for a report traced to code outside rind that handles no secret, saying why in the entry.
