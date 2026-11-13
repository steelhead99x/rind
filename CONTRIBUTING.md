# Getting oriented

[ARCHITECTURE.md](ARCHITECTURE.md) covers the API and the layering,
[PLATFORMS.md](PLATFORMS.md) the CPU requirements,
[ALGORITHMS.md](ALGORITHMS.md) whose code runs on each path,
[Building and testing](#building-and-testing) the tests, and
[TESTING.md](TESTING.md) what checks each primitive on each CPU tier.
Agents should also read [AGENTS.md](AGENTS.md) and the instructions nested
under the files they change.

# Building and testing

`thirdparty/vectors` holds aws-lc's and BoringSSL's vector files, which
`admin/sync-vectors` copies from the revisions it pins. `SLOW_TESTS=1` adds
the large sets, such as CCTV's million ML-KEM vectors, which the nightly
`build` workflow runs on every CPU tier.

Run performance benchmarks:
```shell
cargo bench
```

[BENCHMARKS.md](BENCHMARKS.md#updating-this-report) says how to refresh the benchmark report.

With [Nix](https://nixos.org), `nix develop` (or direnv) provides CI's
toolchain, and `just check` runs CI's gate over what the branch changed; the
nightly tools are in [TESTING.md](TESTING.md#running-the-tools).
`just wasm` runs the nightly wasm job: it tests rind on `wasm32-wasip2`
under wasmtime, with `SLOW_TESTS=1`. aws-lc-rs does not build for wasm, so
the live differential tests stay on `just portable`. Ed25519's CCTV verdicts
are compared with a file recorded from aws-lc, and a native test checks that
file against aws-lc. `ReuseCache`'s threaded test does not run there.
`wasm32-unknown-unknown` stays a compile check. The pull-request gate
clippy-checks `rind-ring` there with `wasm32_unknown_unknown_js`.

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

The platform workflows inherited from graviola run nightly or on demand with `gh workflow run <name> --ref <branch>`, and on a pull request that touches their inputs, a cheap subset each: one ctgrind row, the armv7, portable, and Dart jobs of `build`, and a timing build. `mutants` never runs on a pull request; mutate its diff with `admin/mutants --in-diff`, and dispatch a whole campaign, which `admin/mutants` runs only on GitHub-hosted runners. These runs are advisory, since a path-filtered workflow cannot be a required check, but fix a red one before merging.
PRs land on `main` through GitHub's merge queue, one PR at a time, as squash commits.
Queue the reviewed head with `quest merge <pr> --land <sha>` (`/quest-merge` does this).
The required `Queue` check skips on pull requests; the merge group runs `just ci` against the merge group's base on the self-hosted runner.
That build lives in `.github/workflows/queue-build.yml`, which the merge group calls from `main`, so a PR's edit to it runs only after the PR lands.
A PR the queue drops for a failed build or a conflict gets a Codex fixer, which requeues it or hands it back with a diagnosis.
The admin bypass of `main`'s ruleset is for emergencies.

# AI

AI-assisted issues, pull requests, reviews, and comments are welcome.
Prefer a quest for work needing durable scope or coordination.

# Reviews

A release-plz PR, which only bumps versions and changelogs, needs no review beyond the maintainer's approval to merge it.

# Upstream

rind began as a fork of [ctz/graviola](https://github.com/ctz/graviola) and no longer tracks it: graviola's changes are not merged in, and rind is reshaped freely.
Report bugs that also affect graviola, or any other source rind imports, upstream; never block on the fix.
Each `Written for Graviola by ...` header is attribution; keep it on files that carry one.

[UPSTREAM.md](UPSTREAM.md) lists every workaround for a bug or gap in a tool or dependency rind doesn't own.
A PR that adds such a workaround adds its entry there and names the entry in the workaround's comment; a PR that drops one removes it from its entry, and deletes the entry once it lists no workaround.

# Releases

release-plz opens a release PR from `main`, and publishing happens only when that PR merges.
release-plz owns crate versions.

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
