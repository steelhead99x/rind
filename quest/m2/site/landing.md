# [L] The landing page builds from the repository

## Goal

`site/` holds an Astro project whose build writes the landing page as static files: rind's pitch, the one prompt that migrates a repository, a section on what rind is not, and links to everything else. CI builds it on every pull request, so a change that breaks the site fails before it merges. Nothing is deployed yet.

## Plan

[The epic](/quest/m2/site/README.md) holds the decisions: Astro with Svelte components, static output, the README's voice, no analytics, and pages an agent can read.

- `site/` has its own `package.json` and lockfile and is not a member of the Cargo workspace, so no crate, and nobody building one, touches it. Use bun, as the maintainer's other sites do, and add it to the flake's dev shell. Take the current Astro and Svelte releases.
- The page, top to bottom: the wordmark from `admin/`, the README's headline ("Cryptography slop. Fast, somewhat formally verified, and in pure Rust.") with the line under it, and its three claims (as fast as aws-lc-rs and ring, verified where it counts, no C toolchain), each linking to its proof. Until the showpieces land, those links go to BENCHMARKS.md, its Verified code section, and its Build cost section.
- The call to action is what the README already offers: the prompt that sends a coding agent to `MIGRATE.md`, with a copy button, and the manual route beside it. [The migration pages](/quest/m2/site/migrate.md) replace the manual link when they exist.
- "Before you depend on it", in plain words: rind was written with AI, has had no independent audit, and is not FIPS validated, and aws-lc-rs, ring, and RustCrypto each have something it lacks. Link BENCHMARKS.md's Known gaps, and SECURITY.md and the comparison table once [the trust quests](/quest/m2/trust/README.md) land them. State nothing here that the repository does not.
- The footer: GitHub, crates.io, docs.rs, the launch post, MoQ, and "Built by Kixel" linking kixel.ai.
- The agent layer comes with the scaffold, so later pages get it for free: each page is also written as Markdown at its path with `.md`, `llms.txt` lists every page with a line on what it answers, `robots.txt` allows AI crawlers by name, and there is a sitemap. Write the prose answer first: a page opens with what it tells the reader, not with a welcome.
- No request leaves for a third party: fonts, scripts, and images are served from the site. With no analytics, that makes "this page does not track you" true without a footnote.
- Light and dark, as the README's images already are. The page reads fully with JavaScript off.
- Every number and claim on the page is read from the repository at build time or quoted from a file in it. Where the README states one by hand, quote the README, so there is one place to correct.
- CI: a job that installs with the lockfile frozen, builds, and checks the output's links. If the merge queue does not run it, a data change can land that breaks the site, so add it there too.
- Hand the PR back as a draft with a `Maintainer:` item under `## Waiting` for the words, since they are in the maintainer's voice and theirs to change. Attach a screenshot of the page in both themes.

## Related

- [Someone evaluating rind finds what they look for](/quest/m2/trust/README.md) - SECURITY.md and the comparison table that the candor section links once they exist
