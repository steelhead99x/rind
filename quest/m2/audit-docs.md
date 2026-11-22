# [M] Audit the docs

## Goal

Run the `docs` audit: `quest audit docs` prints what it checks, what each finding becomes, and how to plan its next run.

## Audit

- docs

## Plan

Baseline from the 2026-11-21 run (m1) at `1b2ae8abc`, whose findings and results stay in its PR: read what changed since with `git log 1b2ae8abc..`.

- Scope it excluded: `thirdparty/` (vendored upstream docs), the vendored `rind-ring/tests/ring` and `rind-aws-lc-rs/tests/aws-lc-rs` READMEs, `quest/` (`quest check` owns it), the release-plz-written `CHANGELOG.md` files, and BENCHMARKS.md, which `admin/bench-report render` generates, so a fix there goes in the generator or `benchmarks/`.
- Check first: [docs-tidy](/quest/m2/docs-tidy.md) and [docs-links-check](/quest/m2/docs-links-check.md), if still open, hold the previous run's follow-ups.
- Method that worked: a script over `git ls-files` that checks every relative link and anchor in the Markdown (GitHub's heading slugs, `-1` for repeats) and every `github.com/kixel-ai/rind/blob/main/...#anchor` URL against the tree; another that checks each inline-code `admin/`, `sh/`, `rind/` path exists and each `just`, `admin/prove`, and `admin/ctgrind` subcommand is in its script; `RUSTFLAGS='-W missing_docs' cargo check -p <crate>` for each published adapter, since only `rind`, `rind-ring`, `rind-aws-lc-rs`, and `rind-fips` enforce the lint; `admin/audit unsafe` against AUDIT.md's table; the registries' APIs for every package the README names, since crates.io, pub.dev, and docs.rs answer a page for a missing package.
- External URLs: GET with a browser user agent, at most one request per host every 3 seconds. GitHub answers 429 at 1.5 seconds, and the whole list (about 620 URLs, 540 on GitHub, most of them release-plz's `compare/` links) takes over an hour, so run it in the background first.
- CLAUDE.md does not exist; `AGENTS.md` is the one agent file, with nested ones under the skills.

## Required

- [m1](/quest/m1/README.md) - the audit runs once per milestone

## Scheduled

- 2026-11-28 - one week after the last run
