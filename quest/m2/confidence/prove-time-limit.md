# [S] The HOL Light proofs finish within their job's limit

## Goal

The `hol-light` job of `prove.yml` passes on a pull request that changes nothing it checks, every time, with room for the proofs planned next. A proof that fails still fails the job; only the cancellations at the time limit stop.

## Plan

Found on 2026-11-13 while landing [kixel-ai/rind#711](https://github.com/kixel-ai/rind/pull/711), which changes one README under `proofs/hol-light/` and had the job cancelled at its limit twice.

- The job has 30 minutes (`.github/workflows/prove.yml:42`) on a GitHub-hosted `ubuntu-24.04` runner. In the workflow's runs of 2026-11-13 it passed in 23, 24, 26, 27, 27, 27, and 29 minutes and was cancelled at 30 minutes four times, on pull requests that added no proof: the spread between runners decides the result.
- It only grows. `admin/prove hol-light` loads every entry of `hol_light_proofs` in one job, and the m4 and m5 verified epics add entries.
- A cancelled run counts as failed for `quest merge`, which refuses the head until someone reruns it, so each one costs a PR a half-hour rerun.
- Time each proof first. `admin/prove` already prints each architecture's total (`admin/prove:303`); print the elapsed time after each `loadt` as well, so the log says which proofs the time goes to.
- Recommended: one job per architecture, since `admin/prove` already builds one file for each and they share nothing but the s2n-bignum model. Raising the limit alone is the same fix with a shorter life; take it only if the split saves little, and say what the numbers were.
- Whether the proofs a pull request does not touch need to run on it at all is a wider question. If the timing says the split is not enough, bring that to the maintainer with the numbers and do not decide it here.
- [kixel-ai/rind#693](https://github.com/kixel-ai/rind/pull/693) did the same for `miri.yml`; follow what it settled about pull-request triggers where it applies.

## Related

- [Every rind path is proven, with the smallest trust base](/quest/m4/verified/README.md) - the proofs that make this job longer
