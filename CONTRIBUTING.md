# Getting oriented

[ARCHITECTURE.md](ARCHITECTURE.md) covers the API and the layering,
[PLATFORMS.md](PLATFORMS.md) the CPU requirements,
[ALGORITHMS.md](ALGORITHMS.md) whose code runs on each path,
[Building and testing](#building-and-testing) the tests, and
[TESTING.md](TESTING.md) what checks each primitive on each CPU tier.
Agents should also read [AGENTS.md](AGENTS.md) and the instructions nested
under the files they change.

# Building and testing

Compile:
```shell
cargo build --release
```

Run tests:
```shell
git submodule update --init thirdparty/cavp thirdparty/cctv thirdparty/wycheproof
cargo test
```

`thirdparty/vectors` holds aws-lc's and BoringSSL's vector files, which
`admin/sync-vectors` copies from the revisions it pins. `SLOW_TESTS=1` adds
the large sets, such as CCTV's million ML-KEM vectors, which the nightly
`build` workflow runs on every CPU tier.

Run performance benchmarks:
```shell
cargo bench
```

`admin/bench-report collect` runs the report's benchmarks, then
`admin/build-cost`, on each benchmark host in turn over ssh, in the Nix dev
shell and under `quest gate`, which waits for the host to have room but
shares it with other gated work, so its numbers are noisier than the nightly
`bench` workflow's runners, which give the clean ones; it skips any host that is still busy, and writes their results and the hosts' details as JSON under
`.tmp/bench-report/`. `admin/bench-report nightly` saves the latest nightly
`bench` run's results, and `admin/bench-report render --from DIR` copies a
collection's measured hosts into `benchmarks/data/` and writes
`BENCHMARKS.md` and its SVGs, which the README shows too, from them, `benchmarks/verified.toml`, and
`benchmarks/gaps.toml`, which must hold a quest or a reason for every gap
over 10%.

With [Nix](https://nixos.org), `nix develop` (or direnv) provides CI's
toolchain, and `just check` runs CI's gate over what the branch changed.
On Linux, `just armv7` runs the nightly armv7 job: it builds and lints for
32-bit ARM, then runs the tests under qemu with the ARMv8 crypto extension,
with NEON alone, and with NEON denied. `just qemu <shell>` runs an entry of
the nightly `qemu` job, which lints and tests the portable backend: `s390x`
(big-endian), `riscv64`, `riscv64-musl`, `loongarch64`, `armv6` and
`armv6-softfloat` (the Raspberry Pi 1's core), or `powerpc64le`, `powerpc64`,
and `powerpc` (the last two big-endian) under qemu, or `i686` (32-bit x86)
natively.
`just wasm` runs the nightly wasm job: it tests rind on `wasm32-wasip2`
under wasmtime, with `SLOW_TESTS=1`. aws-lc-rs does not build for wasm, so
the live differential tests stay on `just portable`. Ed25519's CCTV verdicts
are compared with a file recorded from aws-lc, and a native test checks that
file against aws-lc. `ReuseCache`'s threaded test does not run there.
`wasm32-unknown-unknown` stays a compile check. The pull-request gate
clippy-checks `rind-ring` there with `wasm32_unknown_unknown_js`.
`just miri` runs the nightly `miri` job, the portable backend's tests under
Miri, on x86_64, and `just miri s390x-unknown-linux-gnu` big-endian.
`nix develop .#ctgrind --command admin/ctgrind` runs the nightly
constant-time checks under valgrind, `nix develop .#sde --command
admin/ct-sde` those of the AVX-512, VAES, SHA extension, and SHA512 code
valgrind cannot run, under Intel SDE, and `nix develop .#ct-qemu --command
admin/ct-qemu` those of the armv7 crypto extension code valgrind hides, under
qemu; on an aarch64 host, `nix develop .#ct-qemu-aarch64 --command
admin/ct-qemu --target aarch64-unknown-linux-gnu` those of the aarch64 code
that runs only with SHA3, and `nix develop .#binsec --command admin/ct-binsec
[--exact] [test]` has BINSEC prove the region of each `ct_binsec_...` test
constant time for every secret, symbolically. None of them but BINSEC, which
sees divisions, can see an instruction whose timing depends on its
operands, so `admin/ct-vartime`, which `just check` runs when rind changes,
scans its release builds for every architecture it builds for, and its
portable backend's on x86_64 and armv7, for divisions and floating-point arithmetic, and fails on one that `admin/ct-vartime.toml` does
not list as taking only public operands.
`nix develop .#dudect --command admin/timing dudect` times each secret
operation whose secret the API lets it set (not key generation, encapsulation,
or varied ML-KEM decapsulation keys) on two classes of secret, as dudect does,
and `admin/timing marvin` runs the Marvin toolkit against RSA-OAEP decryption. They need quiet
hardware: the weekly `timing` workflow runs them on GitHub's runners, and a
shared host adds noise that no gate removes.
`nix develop .#prove --command admin/prove` checks rind's HOL Light proofs of
its assembly, then translates the Rust under proof to Lean with Aeneas and
checks the proofs in [`proofs/`](proofs/README.md).

# Commits

PRs land on `main` as squash commits, so the PR title becomes the commit subject in `git log`; the body keeps the PR's commit messages and co-author trailers, not the PR description.

- Use conventional-commit subjects (`feat(rustls): ...`, `fix: ...`, `chore: ...`, `docs: ...`)
- AI commit attribution goes in a `Co-Authored-By:` trailer, not the commit body.
- Never commit binaries or build artifacts.

# PRs

Keep the body short and structured, not narrated.
Have at least these sections:

- **Problem**: a summary of the problem and why this PR is needed.
- **Approach**: a summary of the approach taken to solve the problem.
- **Impact**: a bullet point for every public API change made. A breaking one says how to migrate, and the PR title marks it with `!` (`feat!: ...`).
- **Alternatives**: any alternative approaches considered.
- **Follow-ups**: any issues encountered or quests created.

When pushing additional commits to an existing PR, update the title and description if needed.
Never rebase or force-push a pushed branch; merge the base branch in instead.
Check that the PR is still open before pushing to its branch, since a push after merge recreates the deleted branch.

Open a draft PR while working, without asking once the scope is settled.
Run `just ci` before every push, and mark the PR ready with `/quest-review` when the work is done.
Keep it a draft only while its description lists a decision the maintainer still owns.
Fix any merge conflicts and failing CI checks.

The platform workflows inherited from graviola run nightly or on demand with `gh workflow run <name> --ref <branch>`, and on a pull request that touches their inputs, a cheap subset each: one ctgrind row, the armv7, portable, and Dart jobs of `build`, a mutation run over the PR's diff, and a timing build. These runs are advisory, since a path-filtered workflow cannot be a required check, but fix a red one before merging.
PRs land on `main` through GitHub's merge queue, one PR at a time, as squash commits.
Queue the reviewed head with `quest merge <pr> --land <sha>` (`/quest-merge` does this).
The required `Queue` check skips on pull requests; the merge group runs `just ci` against the merge group's base on the self-hosted runner.
That build lives in `.github/workflows/queue-build.yml`, which the merge group calls from `main`, so a PR's edit to it runs only after the PR lands.
The host's `quest land watch` daemon runs the Codex fixer when the queue drops a PR for a failed build or a conflict, and re-enqueues healthy heads at the back of the queue.
A fix that needs a maintainer decision is handed back with a diagnosis on the PR.
The admin bypass of `main`'s ruleset is for emergencies.

# AI

AI-assisted issues, pull requests, reviews, and comments are welcome.
Prefer a quest for work needing durable scope or coordination.

# Reviews

Before a PR is marked ready, and before each push to one that is, the other vendor's model reviews the committed branch locally through `/quest-review`.
On a PR whose author has write access, the PR body's `## Review` record of that review is the required review when it names the head being merged, with every finding fixed or refuted.
So is a recorded skip of a change the author judged too trivial to review.
A release-plz PR, which only bumps versions and changelogs, needs no review beyond the maintainer's approval to merge it.

Online reviewers are optional: never wait for or request one.
Address their findings already posted on the head when merging:

- If you don't agree with a finding, reply to it and move on.
- If it's a relatively easy improvement, fix it, review the new head locally, and push. Update the summary if needed.

# Follow-ups

Record out-of-scope findings as follow-up quests with `/quest-plan`, not GitHub issues.

# Upstream

rind began as a fork of [ctz/graviola](https://github.com/ctz/graviola) and no longer tracks it: graviola's changes are not merged in, and rind is reshaped freely.
Report bugs that also affect graviola, or any other source rind imports, upstream; never block on the fix.
Each `Written for Graviola by ...` header is attribution; keep it on files that carry one.

[UPSTREAM.md](UPSTREAM.md) lists every workaround for a bug or gap in a tool or dependency rind doesn't own.
A PR that adds such a workaround adds its entry there and names the entry in the workaround's comment; a PR that drops one removes it from its entry, and deletes the entry once it lists no workaround.

# Releases

release-plz opens a release PR from `main`, and publishing happens only when that PR merges.
release-plz owns crate versions; bump one only when asked.

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
