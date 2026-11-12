# Migrate a repository to rind

These are instructions for a coding agent. The user's prompt sent you here to
move their Rust repository from ring or aws-lc-rs to
[rind](https://github.com/moq-dev/rind), on a local branch, and to report
what changed. Follow them in order.

Never push, open a PR, or file an issue unless the user agrees when you offer
it at the end. Work only in their repository and its ignored scratch space.

## 1. Survey

Start from the default branch with no changes, tracked or ignored, and note
its commit. If the project commits no `Cargo.lock`, run
`cargo generate-lockfile` before branching.

A library, a crate other projects depend on, may go rind-only only when
every target its users build is covered, as step 2 defines both. Its own CI's
targets are not enough: a user who builds it for another target would lose
it. A rind-only library replaces the old backend, including the default, by
the steps below for a rind-only library. It adds no `[patch]` and no CPU
check, which only a binary adds. A library with any uncovered user target
keeps its current backend as the default. It gains a non-default feature
that builds it on rind instead, named like its existing backend features,
and tested in CI beside them on its covered targets only. For that library,
everything below applies to the build with that feature, and its
measurements compare it with the old backend's feature in otherwise the same
command. A rind-only library measures its default build against the old
default.

1. Find where ring and aws-lc-rs come from, with the default features and
   each feature set the project's release or CI builds:

   ```sh
   cargo tree --target all -e normal,build -i ring
   cargo tree --target all -e normal,build -i aws-lc-rs
   cargo tree --target all -e normal,build -i aws-lc-sys
   ```

   A "nothing to print" warning or a "did not match any packages" error
   means that feature set does not build the crate. Each path reaches it in
   one of five ways:

   - **rustls, or a crate above it**, such as reqwest, hyper-rustls, tonic,
     or ureq.
   - **A crate a `rind-*` adapter serves**: rcgen, dimpl, str0m,
     jsonwebtoken, or object_store.
   - **The project calls ring's API.**
   - **The project calls aws-lc-rs's API.**
   - **A crate that hard-wires ring 0.17**, such as quinn-proto.

   Look up each crate in [MIGRATING.md]'s "Crates with their own crypto
   backend". A crate listed as Patch or Unsupported, or one not listed whose
   source calls ring or aws-lc-rs with no feature or hook to replace it,
   hard-wires them. A binary replaces ring 0.17 throughout its tree with
   the ring patch, but not aws-lc-rs or an older ring. Dev-dependencies may
   keep ring; only what ships must move.

2. List the targets, as full target triples:

   - A binary's release targets: those the project's CI, whatever runs it,
     builds for release, including Docker images' platforms, and any
     `dist-workspace.toml`, `[workspace.metadata.dist]`, or `Cross.toml`.
   - A library's user targets: the union of the targets its CI builds or
     tests, those its README, docs, or `[package.metadata.docs.rs]` say it
     supports, and every target the backend it replaces tests: for ring,
     the targets in ring's `.github/workflows/ci.yml`, and for aws-lc-rs,
     those in aws-lc-rs's `.github/workflows/tests.yml` and `cross.yml`, each
     at the tag of the version the lockfile holds. A library that documents
     a narrower set of supported targets uses that set in place of the
     backend's.

   Look up each triple in [PLATFORMS.md]'s target table. It is covered when
   its row says CI runs the tests of every rind crate the project uses: the
   rows marked "tests" cover the `rind` crate and every adapter, and
   `wasm32-wasip2` covers the `rind` crate alone. A row marked "built",
   `aarch64-apple-ios`, is covered, since `aarch64-apple-ios-sim` runs the
   same aarch64 code on the same OS. A row marked "compiled",
   `wasm32-unknown-unknown`, is uncovered. A triple the table does not list
   is uncovered, even when another row differs from it only in vendor, OS,
   or environment, such as `x86_64-pc-windows-gnu`,
   `aarch64-pc-windows-gnullvm`, `x86_64-unknown-freebsd`, or
   `armv7-unknown-linux-musleabihf`, and even where `rind/build.rs` would
   select the portable backend for it. Note each covered target the table
   says rind checks no constant time on, such as `wasm32-wasip2`, for the
   report's rind gaps. Step 3 builds each covered release target.
   Distribution packages and `cargo install` build where the project does
   not; list what they lose under Breaking changes rather than stopping.

3. Compare the project's `rust-version`, or without one the oldest
   toolchain its CI runs, with the latest rind release's, which
   `cargo info rind` prints. If the project's is older, ask the user whether
   to raise it, and stop if they decline. Raising it includes any toolchain
   or image its CI pins. A library that keeps rind behind a non-default
   feature keeps its own `rust-version`, since only that feature needs
   rind's: say so in its docs. A rind-only library raises its
   `rust-version` to rind's when it is older.

Stop here, before changing anything, if a binary releases an uncovered
target, a library has no covered target in its own CI to test rind on, a
dependency in what ships hard-wires aws-lc-rs, a ring older
than 0.17, or in a library, which cannot patch for its users, any ring, or the
project calls an item rind lacks: for ring's API, one [rind-ring's README]
leaves out, and for aws-lc-rs's, one [rind-aws-lc-rs's README] leaves out.
MIGRATING.md on `main` may name items not yet released, which count as
missing. A library with an uncovered user target does not stop: it keeps its
backend as the default, as above, and adds no rind CI job on that target.
Check every condition, then report each that holds in the format of
step 5, without the table, naming the target, dependency path, or item, and
make the offers in step 6. Do not migrate part of the graph: a build that
still links ring or aws-lc-rs gains nothing.

## 2. Migrate

Create a branch named `rind`. Depend on the latest crates.io release of each
rind crate you use, as `cargo info` reports it, in the project's version
style. Never run a bare `cargo update`; the report lists any existing version
Cargo changes to fit rind in.

For each way the survey found:

- **rustls and the crates above it.** Depend on `rind-rustls`. Turn off each
  crate's default provider feature and turn on the providerless one that
  [MIGRATING.md] lists, such as reqwest's `rustls-no-provider`, and drop a
  direct rustls dependency that only picked a provider. Then either pass
  `rind_rustls::default_provider()` where the crate takes a provider, or
  install it as the process default in each binary's `main`, before any TLS
  config is built:

  ```rust
  rind_rustls::default_provider().install_default().expect("no provider installed yet");
  ```

  Tests share a process, so install it there through one helper that
  ignores the error from a second install. rustls panics naming the missing
  `CryptoProvider` in each test that needs it.
- **A crate a `rind-*` adapter serves.** Follow the adapter's row in
  [MIGRATING.md] and its README.
- **ring's API.** Rename the dependency, with no code changes:
  `ring = { package = "rind-ring", version = "0.17" }`. A library that
  keeps its old backend adds `rind-ring` as an optional dependency instead,
  with `#[cfg(feature = "<its feature>")] extern crate rind_ring as ring;`
  at its crate root. A rind-only library renames the dependency as a binary
  does. rind-ring keeps ring's signatures, such as
  `digest::Context::finish(self)`, so leave the code as it is: MIGRATING.md's
  tables map to rind's own API, where `finish` takes `&mut self`.
- **aws-lc-rs's API.** Rename the dependency the same way, with no code
  changes: `aws-lc-rs = { package = "rind-aws-lc-rs", version = "1" }`. A
  library that keeps its old backend uses
  `#[cfg(feature = "<its feature>")] extern crate rind_aws_lc_rs as
  aws_lc_rs;` instead of renaming. Drop the `fips` feature, which
  rind-aws-lc-rs refuses.
- **A crate that hard-wires ring 0.17.** Patch ring in the root `Cargo.toml`
  of each binary's workspace, then run `cargo update -p ring`, which changes
  ring alone:

  ```toml
  [patch.crates-io]
  ring = { git = "https://github.com/moq-dev/rind-patch" }
  ```

  This moves every crate in the tree on ring 0.17, the project's own ring
  calls included, which then need no rename. Move rustls and the crates an
  adapter serves as above all the same, since their rind routes skip
  ring's API. A dependency that then fails to build calls an item
  [rind-ring's README] leaves out: stop, and report it as a rind gap.

rind panics on a CPU missing a feature it requires. At the start of each
binary's `main`, refuse one by exiting with the error from an adapter's
`default_provider()` or `rind::cpu::check()`.
A library leaves this to the binaries that use it, and says so in its docs.

Commit as you go, with messages in the project's style.

## 3. Verify

1. Confirm nothing that ships links ring or aws-lc-rs: for each feature set
   the project ships, or a library's rind feature, the three `cargo tree`
   commands from the survey print no dependency path, or only
   dev-dependencies. With the ring patch, `-i ring` instead prints
   `ring v0.17.999` from rind-patch and no other ring.
2. Build each release target, adding its standard library with
   `rustup target add` where it is missing. Where the host has the target's
   linker, run the release build with `--target`. Otherwise run
   `cargo build --release --target <target> -p rind`, which assembles rind
   without linking, and report the target as built but not linked. Report a
   target whose standard library you cannot install as not built. A target
   that fails to build stops the migration: report it as a rind gap.
3. Run the project's own lints and checks, such as clippy, `cargo fmt`, and
   cargo-deny. rind's license requires Apache-2.0 and ISC, which a
   cargo-deny allow list may need.

## 4. Measure

Measure the default branch, then the `rind` branch, back to back, with the
same toolchain, command, and profile, on the quietest machine you have.
Restore a clean tree between runs. Use the build, test, and benchmark
commands and the release profile and features from the project's CI, adding
`--locked`.

1. Run `cargo fetch`, so downloads stay out of the timing.
2. Time a clean release build twice, each `cargo clean` then the release
   build command under `time`, and keep the faster. Note the load average.
3. For each binary the project releases, strip a copy outside `target/` with
   the platform's `strip`, and record its size in bytes.
4. Run each test command and record what passes and fails.
5. Run the project's existing benchmarks that exercise TLS, hashing, signing,
   or encryption, and save their output. Note any you skip and why, such as
   one that runs for hours. Write no new benchmarks.

A test that fails only after migrating is a finding to diagnose: a mistake in
your migration gets fixed, and a difference in rind is reported as a rind gap,
never hidden by changing the test.

## 5. Report

Reply with this report, filling in every row:

```markdown
## rind migration: <repository> at <commit>

**Result**: migrated on local branch `rind` (<n> commits) | stopped: <reason>

| | ring or aws-lc-rs | rind | Change |
|---|---|---|---|
| Clean release build (`<command>`) | <seconds> s | <seconds> s | <percent> |
| Stripped `<binary>` | <bytes> | <bytes> | <percent> |
| Tests (`<command>`), a row per command | <passed>/<total> | <passed>/<total> | |
| `<benchmark>` | <time> | <time> | <percent> |

- **Release targets**: each target, and built, built without linking, not
  built, or failed.
- **Uncovered targets**: for a library, each user target rind does not
  cover, and where the list came from, or none. A binary that has one
  stopped.
- **How it moved**: each path from the survey, what changed for it, and any
  dependency version Cargo changed.
- **Still linked**: dev-dependencies that keep ring or aws-lc-rs, or none.
- **Breaking changes**: any change users see, such as a raised
  `rust-version`, ring's types changed in a public API, a provider they must
  now install, or architectures that built from source before and no longer
  do, or none.
- **rind gaps**: anything missing, slower, larger, or harder than it should
  be, or none.
- **Host**: CPU, OS, and `rustc --version`.
```

Give a percentage as the change from before to after, negative when rind is
smaller or faster. Leave out a row that does not apply, such as a binary for
a library, and say why below the table.

## 6. Offer

Ask the user, and do each only if they agree:

1. **Open a PR on their repository** from the `rind` branch, with the report
   as its description.
2. **File an issue on [moq-dev/rind](https://github.com/moq-dev/rind/issues)**
   for each rind gap. First search its open issues, and the plans under
   [`quest/`](https://github.com/moq-dev/rind/tree/main/quest): comment on a
   matching issue instead of filing a duplicate, and for a gap a quest
   already plans, name the quest in the report instead. Each issue names the
   repository, the item or target, and how the project uses it, and ends
   with `(Written by <your model>)`.

[MIGRATING.md]: https://raw.githubusercontent.com/moq-dev/rind/main/MIGRATING.md
[PLATFORMS.md]: https://raw.githubusercontent.com/moq-dev/rind/main/PLATFORMS.md
[rind-ring's README]: https://raw.githubusercontent.com/moq-dev/rind/main/rind-ring/README.md
[rind-aws-lc-rs's README]: https://raw.githubusercontent.com/moq-dev/rind/main/rind-aws-lc-rs/README.md
