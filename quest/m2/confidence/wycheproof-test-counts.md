# [XS] Wycheproof loaders check each file's test count

## Goal

Every Wycheproof loader fails when the tests it ran are fewer than the file's `numberOfTests`, so a truncated vector file or a group the harness skips cannot pass unnoticed.

## Plan

Found by the `tests` audit's run on `main` at `253c93f6`, decided with the owner on 2026-11-21. `rind/src/test.rs`'s `wycheproof` and `wycheproof_groups` assert only that a file has groups and tests, and `rind/tests/wycheproof.rs`'s `TestFile` reads neither `numberOfTests` nor counts what a test skipped beyond its own `Summary`.

- Read the top-level `numberOfTests` in both helpers and in `wycheproof.rs`'s `TestFile`, and assert the tests read equal it.
- In `wycheproof.rs`, assert that tests run plus tests `Summary` reports skipped equal it, so each skip stays a reported one.
- Check each vendored file under `thirdparty/vectors/wycheproof/testvectors_v1/` meets it, which `admin/sync-vectors` could also verify when it vendors a file.
