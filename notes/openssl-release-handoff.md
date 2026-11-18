# Handoff: prebuilt rind-openssl libraries

Delete this file before merging anything into `quest/m4/openssl-release`. It is notes for the next agent. A merge that still contains it would put the note on the upstream claim.

Upstream claim: https://github.com/kixel-ai/rind/pull/874 (draft). Head is `steelhead99x:quest/m4/openssl-release`, base is kixel-ai/rind `main`.

Fork handoff: https://github.com/steelhead99x/rind/pull/146

The claim branch is empty commit `4797ac7e73a8d8cb963d123a473dd95e70dbaf65` (`chore(quest): claim quest/m4/openssl-release.md`, `Quest-Claim: b03f4034f4deb7b7`). Its parent is kixel-ai/rind `main` at `863ad5a8f2be2ad333e42bc0279c19ca0cf6a5c4` (`BINSEC's ML-KEM checks finish every run (#841)`). The commit changes no files.

This quest is under [quest/m4/README.md](../quest/m4/README.md) (long-term work: an OpenSSL provider and FIPS) and [quest/README.md](../quest/README.md) (m4 is the C and regulated-deployment milestone). [quest/m4/openssl-provider.md](../quest/m4/openssl-provider.md) is the NIST-curve work. This quest ships the shared library the provider already builds.

## Goal

Each rind-openssl release ships its shared library for Linux x86_64, Linux aarch64, and macOS arm64, with checksums and build provenance, so an nginx, Node, Python, or Ruby deployment installs the provider without a Rust toolchain.

`quest/m4/openssl-release.md` already decides the shape:

- The libraries are assets on rind-openssl's GitHub releases, under a `rind-openssl-v*` tag. Distribution packages, and shipping nothing, were rejected.
- The crate stays unpublished (`publish = false` in `rind-openssl/Cargo.toml`). OpenSSL loads a built library. Today the only route is `cargo build --release -p rind-openssl`.
- Follow rind-dart: `.github/workflows/dart-release.yml` and `.github/workflows/dart-libraries.yml`. Build on GitHub-hosted runners, because the repository is public. Link the Linux libraries against an old glibc so one file loads on current distributions. Attest each with `actions/attest-build-provenance`.
- Test each built library against the OpenSSL 3 that runner's distribution ships, the way `rind-openssl/tests/provider.rs` does, before attaching it.
- Version it as the crate is: 3.x for OpenSSL 3's provider ABI, bumped the way rind-dart's version is. The manifest is already `3.0.0`.

## Done when

A `rind-openssl-v*` tag on kixel-ai/rind, named `rind-openssl-v` plus the version in `rind-openssl/Cargo.toml`, has a GitHub release that is not marked latest. The release holds:

- `rind_openssl-x86_64-unknown-linux-gnu.so`
- `rind_openssl-aarch64-unknown-linux-gnu.so`
- `rind_openssl-aarch64-apple-darwin.dylib`
- a SHA-256 checksum file covering those three

Each library was loaded by that runner's OpenSSL 3, and the check passed, before upload. Each library has a GitHub artifact attestation from `actions/attest-build-provenance` for the build that produced those bytes. `rind-openssl/README.md` tells a deployment how to download the file, check the digest, verify the attestation, and point `openssl.cnf`'s `module` line at it. The source build stays documented. The crate stays `publish = false`.

Keep https://github.com/kixel-ai/rind/pull/874 a draft until those assets exist. This note is not that work.

## Where the code is

Release path to copy:

- `.github/workflows/dart-release.yml` — on `rind-dart-v*`, and only when `github.repository_owner == 'kixel-ai'`. Calls the library workflow, checks the tag against the package version, and creates the GitHub release with the app token from `actions/create-github-app-token` (`permission-contents: write`) in the `pub.dev` environment. Flags: `--verify-tag --latest=false`. A rerun keeps assets an earlier run already released.
- `.github/workflows/dart-libraries.yml` — one shared library per target. The Linux row is `ubuntu-latest` plus `cargo-zigbuild` `0.24.1`, with triples `*-unknown-linux-gnu.2.17` (glibc 2.17, the same floor as pyrind's manylinux2014 wheels in `.github/workflows/python.yml`). The Apple row is `macos-latest`. This workflow does not load the libraries into OpenSSL, and it does not attest them.
- `sh/dart-library.sh` — the build. Linux runs `cargo-zigbuild rustc --release --locked --lib --target <triple>.2.17` and copies from `target/<triple>/release/` (the glibc suffix is only on `--target`). macOS copies `librind_dart.dylib`.
- `sh/dart-prebuilt.sh` — `shasum -a 256` of each library. Dart writes the digest into `hook/prebuilt.json`. rind-openssl has no package that downloads the file, so the digest goes on the GitHub release.
- `.github/workflows/release.yml` and `.release-plz.toml` — release-plz publishes crates and opens GitHub releases for them. `release_always = false`, `git_release_enable = true`, and `git_release_latest = false` except for rind. `rind-python` is `git_only = true` because it is `publish = false` and still gets a tag. rind-dart and rind-openssl have no package entry.
- `.github/workflows/alert.yml` and `sh/alert.sh` — a workflow that runs outside a pull request must be named in `alert.yml`, or `sh/alert.sh check` fails.
- `sh/release-check.sh` — dispatches every scheduled workflow except `bench` and `dart-libraries`. `just ci` runs `sh/release-check.sh --check`, which fails a scheduled workflow a dispatch would not run whole.
- `sh/pins.sh` — every third-party action is `uses: owner/repo@<40-hex> # vX.Y.Z`.

Provider:

- `rind-openssl/Cargo.toml` — version `3.0.0`, `publish = false`, `crate-type = ["cdylib", "rlib"]`, lib name `rind_openssl`. Dependencies are `rind` and `zeroize`. `openssl-sys` is a unix dev-dependency, so the shipped cdylib does not link libcrypto. OpenSSL loads it and calls `OSSL_provider_init` (`rind-openssl/src/lib.rs`).
- `rind-openssl/README.md` — setup is `cargo build --release -p rind-openssl`, which writes `target/release/librind_openssl.so`, or `.dylib` on macOS.
- `rind-openssl/openssl.cnf` — `module = /usr/local/lib/ossl-modules/librind_openssl.so`, the default provider kept beside it, `?provider=rind`.
- `rind-openssl/tests/provider.rs` — the same keys through rind and through the default provider (X25519, Ed25519, PEM, a TLS 1.3 handshake). `documented_config_loads_rind` is the test that loads a cdylib through `OPENSSL_CONF`.
- `rind-openssl/tests/common/mod.rs` — the other tests register the rlib with `OSSL_PROVIDER_add_builtin`. `library()` searches for some `librind_openssl.so`, and its comment says that file is not necessarily this build's. A passing `cargo test -p rind-openssl` does not prove the file about to be uploaded.
- `rind-openssl/tests/ctgrind.rs` — valgrind over the provider. A packaging change adds no secret path, so it needs no new ctgrind run.
- `sh/openssl.sh` — builds the cdylib and runs the flake's static `evp_test` (`nix develop .#openssl`, `OPENSSL_EVP_TEST` in `flake.nix`). That OpenSSL is nixpkgs', not the runner's. Keep it as the CI check. The pre-upload check is the runner's OpenSSL.
- `README.md` and `rind/README.md` — the rind-openssl row says "built from source".

`actions/attest-build-provenance` appears only in the quest. The dart workflows do not call it.

## Plan

1. Add `sh/openssl-library.sh`, from `sh/dart-library.sh`, for the three targets. Linux: `cargo-zigbuild` at the `0.24.1` pin in `dart-libraries.yml`, `--target x86_64-unknown-linux-gnu.2.17` and `--target aarch64-unknown-linux-gnu.2.17`, and copy `target/<triple>/release/librind_openssl.so` to `rind_openssl-<triple>.so`. macOS: `cargo rustc --release --locked --lib --target aarch64-apple-darwin`, and copy `librind_openssl.dylib` to `rind_openssl-aarch64-apple-darwin.dylib`. Use Rust's default Apple deployment target, as the dart script does.
2. Load that exact file before upload. Write a temp config the way `sh/openssl.sh` does (escape the path; `openssl.cnf` treats `#` as a comment and `$` as a variable) with `module =` set to the artifact. Run the runner's OpenSSL 3 so `openssl list -providers` names rind, then run the provider tests against that file. `documented_config_loads_rind` is the existing load path; `common::library()` has to be pointed at this artifact, or the check sets `OPENSSL_CONF` and drives OpenSSL the same way. Install the headers `openssl-sys` needs (`libssl-dev` and `pkg-config` on Ubuntu; Homebrew `openssl@3` on macOS). The nix dev shell's OpenSSL is the wrong library for this test.
3. Add `.github/workflows/openssl-libraries.yml`, `workflow_call` with a `ref` input and `workflow_dispatch`, read-only apart from attestations. One job per target, `fail-fast: false`:
   - Linux x86_64 on `ubuntu-24.04`. Build the glibc 2.17 `.so` with zig, then load it with that image's OpenSSL 3.
   - Linux aarch64 on `ubuntu-24.04-arm`. Same zig link, then load it there. dart-libraries builds this target on `ubuntu-latest` and never loads it. An x86_64 runner cannot load an aarch64 `.so`, so this quest needs the arm runner.
   - macOS arm64 on `macos-latest`. `.github/workflows/build.yml` records that `macos-latest` is aarch64, and that `macos-15-intel` is the x86_64 Mac runner. This quest does not ship the x86_64 Mac library.
4. In that build job, after the load test passes, attest the library with `actions/attest-build-provenance` (`subject-path` is the file), pinned to a full commit SHA with a version comment. Job permissions: `id-token: write`, `attestations: write`, `contents: read`. Upload the artifact only after the attestation step.
5. Add `.github/workflows/openssl-release.yml` on tags `rind-openssl-v*`, with `if: github.repository_owner == 'kixel-ai'`. Call the library workflow with `ref: ${{ github.ref }}`. Download the three artifacts, fail if one is missing, and hash them with `shasum -a 256` into a `SHA256SUMS` asset. Require the tag to equal `rind-openssl-v` plus the version in `rind-openssl/Cargo.toml` (the dart-release check, read from Cargo.toml). Create the release with the app token, `--verify-tag --latest=false`. If the release already exists, leave its assets, as dart-release does on a rerun.
6. Give both workflows a top-level `name:` and add those names to `.github/workflows/alert.yml`. `sh/alert.sh check` compares that list with every workflow that runs outside a pull request.
7. Document the install in `rind-openssl/README.md`: the release URL `https://github.com/kixel-ai/rind/releases/download/rind-openssl-v<version>/<file>`, `shasum -a 256 -c SHA256SUMS`, `gh attestation verify <file> --repo kixel-ai/rind`, then the existing `OPENSSL_CONF` steps. The macOS asset is a `.dylib`; the sample `openssl.cnf` names a `.so`. Update the "built from source" row in `README.md` and `rind/README.md`.
8. Leave `publish = false`. Leave `.release-plz.toml` alone until the maintainer answers the question below. The first tag is `rind-openssl-v3.0.0` while the manifest stays `3.0.0`. Pushing it is a maintainer action on kixel-ai/rind after the workflow is on `main`, the same way `quest/m2/adoption/rind-cryptography-release.md` has the maintainer push `rind-dart-v*`.

Skip a schedule unless a nightly is wanted. A `schedule:` entry makes `sh/release-check.sh` dispatch the workflow on release PRs, and `sh/release-check.sh --check` fails when that dispatch would skip jobs. dart-libraries is in the skip list because it builds against crates the release has not published yet. An openssl build from the checkout has no such reason.

## Checksums and provenance

The checksum is a `SHA256SUMS` file on the release, one `shasum -a 256` line per library, the command `sh/dart-prebuilt.sh` already uses. The installer checks the file they downloaded. There is no `hook/prebuilt.json` equivalent.

Provenance is a GitHub artifact attestation. `actions/attest-build-provenance` records the file digest under the workflow's OIDC identity. Verify with `gh attestation verify <file> --repo kixel-ai/rind`. Attest the bytes the load test passed, in the build job, and upload those same bytes. The app token that creates the release is a different credential and does not mint the attestation.

The public repository and the GitHub-hosted runners are what make that identity mean this workflow in kixel-ai/rind built the file. The `kixel-ai` owner guard matches dart-release, so a tag on a fork does not publish.

## CI

From the Nix dev shell. The fork's `origin/main` is a different history. Pass the claim's parent, or a newer kixel-ai/rind `main` if it has moved:

```sh
nix develop --command just ci 863ad5a8f2be2ad333e42bc0279c19ca0cf6a5c4
```

`just ci` is `CI_STRICT=1 sh/dispatch.sh ci`. For this change it selects:

- `gh`, when `.github/` changes: `actionlint`, `sh/pins.sh`, `sh/alert.sh check`, `sh/release-check.sh --check`.
- `rs`, when `rind-openssl/` changes: `cargo fmt`, clippy, and `cargo nextest` for the crates `sh/select.sh` names.
- `openssl`, when `rind-openssl/`, `sh/openssl.sh`, or the flake changes: `nix develop .#openssl --command sh/openssl.sh`. A new `sh/openssl-library.sh` does not match that regex. shellcheck still runs: the `shell` module has an empty pattern and checks every `sh/*.sh`. `nix` and `site` also run on every diff.
- `quest` (`quest check`, the flake's `quest-cli`) when `quest/` or `flake.lock` changes. Run it when the finishing PR edits `quest/m4/openssl-release.md`:

```sh
nix develop --command quest check
```

The three release libraries are verified on the runners above, not by `just ci`. `cargo build --release -p rind-openssl` on one host links that host's glibc. That is the source-build path, not the release asset.

## Risks and open questions

- On the macOS runner, `/usr/bin/openssl` is LibreSSL. The load test has to use Homebrew's OpenSSL 3 (`brew --prefix openssl@3`) and record `openssl version` in the log. On the Ubuntu runners the distro package is OpenSSL 3. Confirm the maintainer accepts Homebrew's formula as the OpenSSL 3 for the arm64 asset.
- `cargo test -p rind-openssl` links the rlib. The upload gate has to load the zig-built file. A green run that only registered the builtin is a different binary.
- No environment currently deploys `rind-openssl-v*` tags. `publish` is `main` only (`.github/workflows/release.yml`). `pub.dev` is the dart tags. The app key that can create the release lives in an environment, and the maintainer has to add one, or widen one, before the first tag does anything.
- Push the tag by hand, as rind-dart, or set `git_only = true` like rind-python? The quest says the version is bumped as rind-dart's is: a maintainer-pushed tag, and no release-plz entry. `git_only` would make release-plz create the tag and a GitHub release when a release PR merges, and this workflow would then attach assets to a release that already exists. Leave `.release-plz.toml` unchanged until that choice is made.
- Ship the first assets at the current `3.0.0`, or bump first? The manifest is `3.0.0` and nothing has been tagged. Recommend `rind-openssl-v3.0.0`.
- `quest/m4/openssl-provider.md` adds P-256, P-384, and P-521 behind `ec = 1`. These assets ship the provider as it is: X25519 and Ed25519. A later 3.x tag can add the curves.
- glibc 2.17 is the link floor, the same one dart and pyrind use. The Ubuntu 24.04 load test shows that file runs on a current glibc. It does not boot a glibc 2.17 container.

## Landing

Implement on this branch. Delete `notes/openssl-release-handoff.md` before merging into `quest/m4/openssl-release`. Land that merge with a merge commit, so the claim commit stays on the branch https://github.com/kixel-ai/rind/pull/874 tracks. This pull request is notes only. Merging it as it stands would put the note on the claim.

Upstream claim: https://github.com/kixel-ai/rind/pull/874
