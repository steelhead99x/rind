# Getting oriented

[ARCHITECTURE.md](ARCHITECTURE.md) covers the API and the layering,
[PLATFORMS.md](PLATFORMS.md) the CPU requirements,
[ALGORITHMS.md](ALGORITHMS.md) whose code runs on each path,
[Building and testing](#building-and-testing) the tests, and
[TESTING.md](TESTING.md) what checks each primitive on each CPU tier.
Agents should also read [AGENTS.md](AGENTS.md) and the instructions nested
under the files they change.

# Building and testing

`thirdparty/vectors` holds the aws-lc, BoringSSL, Wycheproof, CAVP, and CCTV
vector files the tests read, which `admin/sync-vectors` copies from the
revisions it pins, so a plain clone runs every test. `SLOW_TESTS=1` adds
the large sets, such as CCTV's million ML-KEM vectors, which the nightly
`build` workflow runs on every CPU tier.

Run performance benchmarks:
```shell
cargo bench
```

[BENCHMARKS.md](BENCHMARKS.md#updating-this-report) says how to refresh the benchmark report.

With [Nix](https://nixos.org), `nix develop` (or direnv) provides CI's
toolchain, and `just check` runs CI's gate over what the branch changed,
three modules at a time (`sh/dispatch.sh` lists the `CHECK_*` variables that
change that); the scheduled workflows' tools are in [TESTING.md](TESTING.md#running-the-tools).

# Commits

PRs land on `main` as squash commits, so the PR title becomes the commit subject in `git log`; the body keeps the PR's commit messages and co-author trailers, not the PR description.

- Use conventional-commit subjects (`feat(rustls): ...`, `fix: ...`, `chore: ...`, `docs: ...`)
- Never commit binaries or build artifacts.

# PRs

Keep the body short and structured, not narrated.
Have at least these sections:

- **Problem**: a summary of the problem and why this PR is needed.
- **Approach**: a summary of the approach taken to solve the problem.
- **Impact**: a bullet point for every public API change made. A breaking one says how to migrate, and the PR title marks it with `!` (`feat!: ...`).
- **Alternatives**: any alternative approaches considered.
- **Follow-ups**: any issues encountered or quests created.

Run `just ci` before every push.

The scheduled workflows run as [TESTING.md](TESTING.md#scheduled-workflows) lists, or on demand with `gh workflow run <name> --ref <branch>`, a `bench` or `ctgrind` dispatch naming only what the change reaches. None of them runs on a pull request, where only what gates a merge runs: dispatch the ones your change reaches on your branch before review, and mutate a diff with `admin/mutants --in-diff`. `prove` also runs on each push to main that reaches it, checking the bytes, and the HOL Light and Lean proofs and the cosimulation for inputs main has not passed. Its proofs gate no merge: a failure on main alerts, and a release waits for them (see [Releases](#releases)). `admin/mutants` runs a whole campaign only on GitHub-hosted runners.
PRs land on `main` through GitHub's merge queue, one PR at a time, as squash commits.
Queue the reviewed head with `quest merge <pr> --land <sha>` (`/quest-merge` does this).
`pr-check.yml` runs `just ci` over the PR's diff on a GitHub-hosted runner, so a check that the PR's own changes fail shows red here first; it does not rerun when main moves, so the queue can still fail a group it passed. It is advisory, since main's ruleset requires only the queue's build.
release-plz's release PR skips it, since the queue's `just ci` and `just release-check` still run on it.
The required `Queue build / Build` check skips on pull requests; the merge group runs `just ci` against the merge group's base on the self-hosted runner, and that job's own result decides the group.
When the group's diff touches the inputs of `regenerate` or of `prove`, that build also runs `regenerate`, or `prove`'s x86_64 `vg`, beside its other checks (`CHECK_QUEUE` in `sh/dispatch.sh`), so a change cannot land that breaks them on `main`; `vg`'s aarch64 job runs only nightly. When the group's diff reaches x86_64 code, the build also runs the tests under the Intel SDE models `admin/x86-cpu` lists (`admin/x86-cpu all`): in full on one model for each distinct set of dispatch paths, and each other model's assertion of its paths.
That build lives in `.github/workflows/queue-build.yml`, which the merge group calls from `main`, so a PR's edit to it runs only after the PR lands.
A PR the queue drops for a failed build or a conflict gets a Codex fixer, which requeues it or hands it back with a diagnosis.
The admin bypass of `main`'s ruleset is for emergencies.

# AI

AI-assisted issues, pull requests, reviews, and comments are welcome.
Prefer a quest for work needing durable scope or coordination.

# Vulnerabilities

Report a vulnerability privately, as [SECURITY.md](SECURITY.md) says, never in
an issue, pull request, or quest.

# Reviews

A release-plz PR, which only bumps versions and changelogs, needs no review beyond the maintainer's approval to merge it.

# Upstream

rind began as a fork of [ctz/graviola](https://github.com/ctz/graviola) and no longer tracks it: graviola's changes are not merged in, and rind is reshaped freely.
Report bugs that also affect graviola, or any other source rind imports, upstream; never block on the fix.
Each `Written for Graviola by ...` header is attribution; keep it on files that carry one.

When rind needs an upstream changed, by its own fix or an unmerged upstream pull request, it forks that upstream and vendors the fork's whole tree in this repository, in place of a submodule, and takes upstream's later commits by merging them into it.
Never vendor an upstream file unchanged from an older base, or only the changed files over a pinned upstream: the first reverts every later upstream commit to that file, and the second silently shadows them.
[UPSTREAM.md](UPSTREAM.md#forks) names each fork and where its list of rind's changes lives, so they can be offered upstream.

[UPSTREAM.md](UPSTREAM.md) lists every workaround for a bug or gap in a tool or dependency rind doesn't own.
A PR that adds such a workaround adds its entry there and names the entry in the workaround's comment; a PR that drops one removes it from its entry, and deletes the entry once it lists no workaround.

# Releases

release-plz opens a release PR from `main`, and publishing happens only when that PR merges.
release-plz owns crate versions.
It creates a GitHub Release for each tag it pushes, with its changelog entry as the body, and only rind's marked latest.
If creating one fails, the release job stops there and alerts, leaving later crates and pyrind's PyPI upload undone. Rerun the failed `Release` run, which finishes them but skips the tag already pushed, then create that tag's Release by hand with `gh release create <tag> --verify-tag --latest=false --title <tag> --notes-file <its CHANGELOG.md entry>`, passing `--latest` for rind's.

A release PR merges only after `just release-check` passes at its head, so nothing publishes that the full suite has not passed.
It dispatches every scheduled workflow but `bench` and `dart-libraries` on the PR's branch, so each runs its whole scheduled matrix on the head, and waits for them all, which takes as long as the slowest. Mutation testing covers every change since the previous release.
An agent merging a release PR, as `/quest-merge` does, runs it first.
It records the result as the `release-check` status on the head the runs tested, so a release-plz update to the PR needs a new run.
`just ci` fails a scheduled workflow that a dispatch would not run whole.
Before a release PR's commit publishes, `release.yml`'s Proofs job waits for a `prove` run on `main` with the commit's inputs to pass (`sh/release-proved.sh`): that run checked the bytes, the cosimulation, and every HOL Light and Lean proof of the released code that main had not passed on the same inputs. A failure there stops the release and alerts. After a flake, rerun that `prove` run's failed jobs, then the failed `Release` run; a real failure needs a fix on main and a new release PR.

Each published `rind-<consumer>` adapter's version begins with the breaking part of the upstream version it adapts (major.minor below 1.0, major from 1.0 on), so rind-rustls 0.23.x adapts rustls 0.23; the rest of the version is the adapter's own.
`sh/adapter-versions.sh`, in `just ci`, fails when the two drift.
An adapter's API is its upstream's, so it changes only with upstream's; the PR that moves an adapter to upstream's next breaking release sets the adapter's version to match.
release-plz cannot cap a bump: a breaking change it finds in an adapter, by cargo-semver-checks or a `!` commit, makes its release PR propose the next breaking version, which that check then fails.
A change that restores upstream's API fixes a bug: set its patch version by hand, and the maintainer yanks the divergent releases if needed. Hold or revert any other breaking change.
A version set by hand ahead of the published one is kept as is, and the next release PR publishes it.

The release job publishes through crates.io trusted publishing, so no registry token is stored: crates.io issues a short-lived token only to `release.yml` running in the `publish` environment, which only `main` can deploy to.
Trusted publishing cannot create a crate, so the maintainer publishes a new crate's first version by hand from `main` before the release PR that would publish it merges.
Use a crates.io token scoped to `publish-new` for that crate name with a short expiry, never stored as a secret, and revoke it afterwards.
Then add the crate's trusted publisher for `release.yml` and the `publish` environment, so release-plz publishes every later version, and turn on its crates.io "require trusted publishing" setting, as every published rind crate has, so no API token can publish it.
