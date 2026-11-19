# [M] rind's workarounds and fork changes are offered upstream

## Goal

Every `UPSTREAM.md` workaround entry not yet reported has an issue (or a PR, where the fix is small and clear) in its upstream project, and its entry links to it. Entries whose upstream has since fixed the bug have their workaround removed instead.

Every upstream under `UPSTREAM.md`'s Forks has an issue offering to upstream rind's changes to it, listed from the fork's change list, and its entry's **Offered** links to it.

## Plan

Planned with the maintainer on 2026-11-10: ✅ report once rind is more mature, at the maintainer's call (rejected: after rind 1.0; after m2 completes).

Extended with the maintainer on 2026-11-13: ✅ once rind is complete enough, file an issue on each upstream rind forks offering its changes, in this quest (rejected: a separate quest). Both go out under the same maturity call and in the same batch of drafts.

- These projects are outside [the orgs AGENTS.md lists](/AGENTS.md#development). Show the maintainer the batch of issue drafts and post only what they approve.
- Recheck each bug against the upstream's current release first, and search for an existing report, before drafting.
- For each fork, drop from the offer what upstream has merged since, and group the rest the way upstream would review it, such as s2n-bignum's model additions apart from rind's specs. The issue offers PRs; it does not open them.
- Decided 2026-11-18 (maintainer, /quest-complete): ✅ not yet (rejected: start reporting now); ask again once rind 0.4 ships and the benchmark report refresh lands, so reports cite a released version.

## Waiting

- Maintainer: say rind is mature enough to start reporting upstream. An agent can't judge this; it is the maintainer's view of rind's standing. Not yet, as of 2026-11-18: ask again once [rind 0.4 ships](/quest/m2/api/release-0.4.md). Clear it by removing this item.
