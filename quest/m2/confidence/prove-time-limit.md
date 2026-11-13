# [S] The HOL Light proofs finish within their job's limit

## Goal

The `hol-light` job of `prove.yml` passes on a pull request that changes nothing it checks, every time, with room for the proofs planned next. A proof that fails still fails the job; only the cancellations at the time limit stop.

## Plan

Found on 2026-11-13 while landing [kixel-ai/rind#711](https://github.com/kixel-ai/rind/pull/711), which changes one README under `proofs/hol-light/` and had the job cancelled at its limit twice. [kixel-ai/rind#719](https://github.com/kixel-ai/rind/pull/719) hit it too: a run cancelled at the limit passed on rerun in 27m40s.

Decided 2026-11-13 (maintainer, /quest-run follow-up): ✅ plan it (rejected: leave it). It stays in this epic, where the maintainer kept it earlier that day, rather than m1.

Measured on the job's 106 attempts from 2026-11-12 22:49 to 2026-11-13 12:26 UTC, on GitHub-hosted `ubuntu-24.04` runners:

- 57 passed, in 23.2 to 29.9 minutes (median 26.0), and 28 were cancelled at the 30-minute limit (`.github/workflows/prove.yml:42`), on pull requests that added no proof: the spread between runners decides the result.
- A run spends about 2 minutes on Nix and `admin/prove bytes`, then runs the two programs one after the other: aarch64 in 295 to 406 s, x86_64 in 1010 to 1079 s (`admin/prove` prints each total).
- [kixel-ai/rind#629](https://github.com/kixel-ai/rind/pull/629), x86_64 SHA-384/512 on AVX2, takes x86_64 to 2007 s and the job to 46 minutes, so it raises the limit to 60 on its branch. The m4 and m5 verified epics add more entries to `hol_light_proofs`, mostly x86_64.

So splitting alone, recommended here before these numbers, gives an aarch64 job of about 9 minutes and an x86_64 job of about 20 today and 36 once #629 lands: past 30 again with the next proof.

- Run each architecture in its own job, since `admin/prove` already builds one program for each and they share nothing but the s2n-bignum model. That takes the wall time from the slower sum to the x86_64 job alone.
- Also size each job's limit from its measured run time with room for the queued proofs, since the limit only catches a hang: about 60 minutes for x86_64 covers #629 with room, and aarch64 needs far less. Report the numbers on the PR's own head.
- Time each proof: print the elapsed time after each `loadt`, beside each architecture's total (`admin/prove:303`), so the log says which proofs the time goes to and when x86_64 nears its limit again.
- When x86_64 alone nears its limit, sharding its proofs across jobs is the next step; each shard pays the `base.ml` load again (about 4 minutes on the maintainer's host). Not needed now.
- Whether the proofs a pull request does not touch need to run on it at all is a wider question. If the timing says the split is not enough, bring that to the maintainer with the numbers and do not decide it here.
- [kixel-ai/rind#693](https://github.com/kixel-ai/rind/pull/693) did the same for `miri.yml`; follow what it settled about pull-request triggers where it applies.
- [kixel-ai/rind#701](https://github.com/kixel-ai/rind/pull/701), x86_64 SHA-NI SHA-256, raises the limit to 60 minutes, as #629 does on its branch: on its run the job spent 2 minutes on Nix and the bytes, aarch64 took 402 s, and x86_64 was still running when the job hit 30 minutes. The split and per-job limits remain this quest's.
- #629 also edits the job's `timeout-minutes`; whichever of the two lands second merges the other's change.

## Related

- [Every rind path is proven, with the smallest trust base](/quest/m4/verified/README.md) - the proofs that make this job longer
