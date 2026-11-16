# [M] A child forked mid self-test never hangs

## Goal

`rind-fips/tests/fork.rs`'s `a_child_forked_mid_self_test_tests_and_exits`
passes every run: a process that forks while its other threads run the
self-tests and draw randomness leaves the child a module it can test, draw
from, and exit through. Today the child sometimes hangs until the test's
10 s deadline kills it.

## Plan

- Found 2026-11-13 merging `main` into
  [kixel-ai/rind#606](https://github.com/kixel-ai/rind/pull/606): with both
  fork tests running in one process, `cargo test -p rind-fips --test fork`
  failed 9 of 50 runs on `main` at 398040cf and 6 of 50 on #606's merge, so
  CI's `build` job, which runs it, flakes on every branch. Run alone, the
  self-test case did not hang in 40 runs, so the draw test's threads take
  part.
- First get the hung child's stacks. `ptrace_scope` 1 blocks attaching gdb
  to it from outside, so run the test under gdb with `detach-on-fork off`,
  or have the child arm an alarm that dumps its own threads.
- Suspects: a lock the module's `fork_prepare` does not hold.
  [kixel-ai/rind#723](https://github.com/kixel-ai/rind/pull/723), which
  replaced `rind/src/fips_rng.rs`'s per-process DRBG self-test `Once` with
  an `AtomicBool`, did not fix it: on 2026-11-15, #606's merge of `main` at
  d9fd1a34 still failed 5 of 50 runs.
- Fix it at the root, holding the lock across `fork` or making the child
  never wait on it; the test's deadline and fork count stay as they are.
