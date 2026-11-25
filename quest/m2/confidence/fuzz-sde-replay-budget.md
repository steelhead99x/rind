# [S] The keys corpus replays under SDE within its job

## Goal

`fuzz.yml`'s `Replay keys under SDE` finishes both of its tiers inside its job's limit, so the weekly fuzz run passes and every corpus input reaches the AVX-512, VAES, and SHA-extension paths, and the job keeps fitting as the corpus grows.

## Plan

Found by [kixel-ai/rind#971](https://github.com/kixel-ai/rind/pull/971)'s dispatched run. The job hits its 60-minute timeout on main's weekly runs ([run 44892064887](https://github.com/kixel-ai/rind/actions/runs/44892064887), [run 43645306794](https://github.com/kixel-ai/rind/actions/runs/43645306794)) and on that PR's run ([run 45435272600](https://github.com/kixel-ai/rind/actions/runs/45435272600)), where the first tier (Diamond Rapids, every path) alone took 48.5 minutes over 1281 inputs, and the second was cancelled. SDE runs an SLH-DSA signature, which `keys` makes for every SLH-DSA key it loads, in about 44 s, so a few dozen such inputs fill the job. That PR adds the ten other SLH-DSA sets to `keys`, so more inputs reach that path.

Recommendation: measure which inputs dominate, then bound the job by design rather than by raising its timeout:
- give each SDE tier its own job, as the other replays are already split per architecture;
- and, if one tier still runs long, sign under SDE only once per SLH-DSA parameter set and path rather than once per input, such as by giving the SLH-DSA signing its own target whose corpus stays small.

The move off GitHub-hosted runners may change the limit; plan against whatever the runner then allows.

## Related

- [CI speed](/quest/m0/ci-speed/README.md) - SDE keeps every CPU tier weekly
