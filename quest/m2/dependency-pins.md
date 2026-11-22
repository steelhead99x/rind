# [S] Keep every pin something updates or checks

## Goal

Each version pin outside `Cargo.toml`'s workspace is either moved by an updater or checked against what it must match, and each CI install names a version, so a pin cannot drift for months unseen as `just` did.

## Plan

Found by the 2026-11-21 dependency audit.

- `.github/dependabot.yml` has two ecosystems, `github-actions` and `cargo` at `/`. Add `bun` for `/site` and `/site/deploy` (astro 7.4.12 against 7.4.13, svelte 5.57.3 against 5.59.1, wrangler 4.159.0 against 4.166.0 on 2026-11-21) and `cargo` for the standalone manifests that are their own workspaces: `admin/build-cost-fixtures/*` and `patch/fixture` have no lockfile, so they take whatever resolves, and `admin/wasm-fixture` is in the workspace already. Give each the same 7-day cooldown and major ignore.
- Pins of tools Dependabot cannot see, with their newest release on 2026-11-21: `just@1.58.0` in `.github/actions/just/action.yml` (1.59.0 since 2026-10-15; the audit moved it, since the action says to match nixpkgs' just in `flake.lock`), `cargo-nextest@0.9.149` in `ctgrind.yml` (0.9.152), `MATURIN_VERSION` 1.15.0 in `python.yml` (1.16.0), `CARGO_ZIGBUILD_VERSION` in `dart-libraries.yml`, `build==1.6.1` in `release.yml`, `cross` at a git rev in `build.yml`. A weekly `quest` or `sh/` check that prints each against its registry would do; so would a renovate-style custom regex manager, if the maintainer prefers a bot. Add a check that fails when the `just` pin differs from `nix eval nixpkgs#just.version` at `flake.lock`'s revision, which is the one pin that says what it must equal.
- Installs that name no version: `cargo install cargo-fuzz` (`fuzz.yml`), `cargo binstall -y cargo-codspeed` (`bench.yml`), `pip install cryptography mypy` (`python.yml`, with `--only-binary`), and the `python:3.11-*` job containers by tag. Pin the first two with `--version` and `--locked`, the pip installs with `==`, and the containers by digest, each bumped with the rest above.
- `rind-python/cryptography/pyproject.toml` builds with `flit_core>=3.12,<4` and flit_core 4.2.0 is out (2026-10-27): try 4 and widen the bound, or record what stops it.
- `site/package.json` pins `entities` 4.5.0, and 9.0.0 is out. `site/src/lib/markdown.ts` takes `decodeHTMLStrict` from it: check that 9 still exports it, and take it or note why not.

## Related

- [Take what rind's upstreams changed since their pins](/quest/m2/upstream-updates.md) - the crates and copied code
