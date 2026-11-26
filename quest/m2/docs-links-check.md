# [S] Check every Markdown link and anchor in the gate

## Goal

A relative link, a link into `main`'s tree, or an anchor in any repository Markdown file that does not resolve fails `quest gate`, so a renamed heading or moved file cannot leave a dead link. Today only the built site's pages are checked (`site/scripts/check.ts`), and the 2026-11-21 docs audit found `ALGORITHMS.md` linking `#ml-kem-768`, a heading that does not exist, by script.

## Plan

- Check every tracked `.md` file outside `thirdparty/`, `quest/` (which `quest check` owns), and the vendored `tests/ring` and `tests/aws-lc-rs` suites: relative and root-absolute targets exist, `#anchor`s match a heading slug under GitHub's rules (lowercase, punctuation dropped, spaces to hyphens, `-1` for a repeat) or an `<a name>`, and `https://github.com/kixel-ai/rind/blob/main/PATH#anchor` URLs resolve against the checked-out tree, the way the README's reference links do. The audit's script did this in 60 lines of Python over the 60 files, with no false positives.
- Run it from `sh/dispatch.sh` when a Markdown file or the heading of one changes, beside the other fast checks; it needs no network.
- Leave external URLs out: they flake. The `docs` audit checks them with GET and a browser user agent, at no more than one request per host every 3 seconds, since GitHub answers 429 faster than that, and crates.io, PyPI, and pub.dev through their APIs.
- Decide whether it extends `site/scripts/check.ts`, whose `anchors()` already slugs a repository file's headings the way GitHub does, or is its own `admin/` script.
