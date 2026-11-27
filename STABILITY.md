# Stability

[README.md](README.md#versions) says what a version number promises: below 1.0 a minor release may break the API, a patch release adds API and fixes bugs, and each adapter's version follows the upstream it adapts. This file says what is checked before a release, and what 1.0 waits on.

## Checked before every release

- **A break needs a mark.** `sh/semver.sh`, in `just ci`, runs cargo-semver-checks on each published crate a branch changes, comparing it with the same crate at the branch's merge-base, not with crates.io, since `main` holds every breaking change the next minor release batches. A break in `rind` fails unless the PR title or a commit subject carries `!` (`feat!: ...`); a break in an adapter fails even then, since an adapter's API is its upstream's, unless the change sets its version to its upstream's next breaking release or carries `!` with the adapter's name as the scope (`fix(rind-ring)!: ...`), as a fix that restores parity with its upstream does; that change also sets the adapter's patch version by hand, since release-plz would otherwise propose a breaking version `sh/adapter-versions.sh` refuses, and the gate fails a marked adapter still at its released version. A crate new in the branch has no baseline and is skipped. `pr-check.yml` passes the PR title, so a PR retitled with `!` needs a new push to rerun; the merge queue reads the squash commit.
- **Releases.** release-plz runs the same tool when it opens a release PR, and proposes the next breaking version when it finds a break. `sh/adapter-versions.sh` fails an adapter version that drifts from its upstream's, and `admin/adapter-api` fails an adapter whose API differs from its upstream's. [CONTRIBUTING.md](CONTRIBUTING.md#releases) has the rest.
- **Rust version.** `rind` and each crate that shares its `rust-version` is built and linted on in CI (`msrv`), and it rises only as README.md says. An adapter whose upstream needs a newer Rust declares that version instead, and `msrv` leaves it out.

## Before 1.0

README.md names three conditions, and each is open work:

- The API takes one shape. The per-algorithm signature modules landed in [kixel-ai/rind#781](https://github.com/kixel-ai/rind/pull/781); [the API epic](quest/m2/api/README.md) holds what remains.
- Every key type loads, exports, and names things the same way.
- No breaking change is planned. [rind 0.4 ships once](quest/m2/api/release-0.4.md) carries every one planned so far.

1.0 also requires two things README.md does not say:

- **An outside audit.** Someone outside the project audits the Phase 1 scope of [the audit scope quest](quest/m2/trust/third-party-audit-scope.md), and the report is published. README.md says no one outside the project has audited rind; 1.0 does not ship with that sentence. FIPS 140-3 validation is not a requirement.
- **One full minor release without a break.** `rind` ships one full minor release with no breaking change, such as 0.5 after 0.4, meaning no change marked `!` that `sh/semver.sh` lets through. 1.0 is that line re-tagged.

## Security backports

Below 1.0, only the latest release gets a security fix. From 1.0, the last minor of the previous major also gets security fixes for 6 months after the new major ships, on a `release/<major>.<minor>` branch that release-plz opens its release PR from. [SECURITY.md](SECURITY.md#supported-versions) has the policy as users read it.

What rind lacks today, which README.md also says:

- An outside audit, which [the audit scope quest](quest/m2/trust/third-party-audit-scope.md) prepares.
- FIPS 140-3 validation, which 1.0 does not wait for.

The checks a release already passes are in [TESTING.md](TESTING.md): constant time (ctgrind and the `ct-vartime` scan), fuzzing, nightly coverage, mutation testing, and the proofs a release waits for.
