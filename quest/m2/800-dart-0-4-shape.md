# Dart 0.4 shape fixes

Difficulty: 6/10 (estimate)


## Goal

Dart's ECDSA and RSA ids are tested, fresh-process checks do not race the build hook, and naming and docs are corrected.

## Plan

Upstream draft #800, fork branch `fork/800-gaps` at `bc56b761`. Score 8/10. Push the branch and open a fork PR first.

Mediums:
- The renumbered ECDSA cross-hash ids and the legacy RSA verify ids are untested.
- Fresh-process checks can race the build hook. Give them separate output folders.
- The copy-on-read bytes getter is missing from the changelog.

Lows:
- The `from_spki` name reads like the parse direction.
- `_Handle` is copied four times.
- The P-521 length bounds are duplicated.
- Every RSA public-key export allocates 8 KiB.
- The FFI export bodies are hand-copied.
- The crate doc names the wrong file.
- The verify exports have no doc comments.
- A test depends on the working directory.
- The RSA bit-range doc is wrong for the legacy ids.
