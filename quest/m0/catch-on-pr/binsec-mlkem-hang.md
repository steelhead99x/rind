# [S] BINSEC's ML-KEM checks finish every run

## Goal

`admin/ct-binsec`'s ML-KEM checks finish within seconds on every backend and every run, as they do in almost every run today. The cause of their occasional hang is found and fixed, not hidden by a longer timeout or a retry. ML-KEM's own code changes only as far as the check needs.

## Plan

Planned with the maintainer on 2026-11-17, from the `/quest-run` of 2026-11-16 and 2026-11-17: ✅ find and fix the cause (rejected: not planning it, since rerunning a two-in-seventy advisory failure is cheap; raising the timeout, which hides the hang).

- What failed: ctgrind's `binsec (portable)` job, `admin/ct-binsec --timeout 480`, twice in at least 135 completed runs since 2026-11-15, on two pull requests:
  - `ct_binsec_mlkem1024`, [run 43884518954](https://github.com/kixel-ai/rind/actions/runs/43884518954), a manual dispatch on kixel-ai/rind#812's branch. That head rewrote `mid/mlkem.rs`, the code `ct_binsec_mlkem*` checks, so this one may be that PR's regression, not a flake.
  - `ct_binsec_mlkem512`, [run 43941913029](https://github.com/kixel-ai/rind/actions/runs/43941913029) on kixel-ai/rind#811, which touches no portable code (its `rind/src/test/binsec.rs` change is a comment), so this is the clean case.
- Each timed out at 480 s on one pending path, every check it reached passing, with zero SMT queries: BINSEC never asked its solver anything, so the stall is not the solver. The harness pins only the key, `DecapKey::keygen_internal(&[1; 64])`; it decapsulates a fresh ciphertext each run, since `encaps()` draws its message from `SystemRandom` (the `mlkem` helper in `rind/src/test/binsec.rs`). The same tests pass in 6 to 9 s in the other runs, so the cause is something that varies by run. Candidates: that random ciphertext, the only input that changes between runs (pinning the message with `encaps_internal` would test this and make the check reproducible); the core dump BINSEC starts from, which holds the process's memory as the runner's glibc and kernel left it; the runner's CPU, which picks glibc's `memcpy` and `memset` variants and which the log never names; the runner itself being starved.
- Reproduce it first, for example by looping the one test in a dispatched run that logs the runner's CPU, then fix the cause in the harness or the test's setup.

## Related

- [Failures show up on the PR that causes them](/quest/m0/catch-on-pr/README.md) - this flake turns PR checks red for changes that didn't cause it.
