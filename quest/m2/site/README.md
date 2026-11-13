# rind.kixel.ai gets a developer from a first visit to a first build

## Goal

A Rust developer who has never heard of rind lands on `rind.kixel.ai`, sees the proof for what it claims, and leaves with the change that moves their project to it from the library they use today. The site is static files built from this repository's own data, so a merge that changes a benchmark, a proof, or an adapter changes the site with it.

Non-goals: it is not the home of rind's reference documents, which stay in the repository and on docs.rs with links from the site, and it does not track its visitors.

## Plan

Decided 2026-11-12 (maintainer, /quest-plan):

- ✅ A landing site for someone evaluating rind (rejected: a home for all the docs, rendered from the repository's Markdown; one page of links).
- ✅ Its source is `site/` in this repository (rejected: a repository of its own, as the maintainer's other sites have; a route in another site's Worker). The facts it shows are kept and checked here, so it reads them in the same commit.
- ✅ Three showpieces: [a benchmark explorer](/quest/m2/site/benchmarks.md), [a page per library migrated from](/quest/m2/site/migrate.md), and [a map of the verified code](/quest/m2/site/verified.md) (rejected: an in-browser playground, since wasm runs rind's portable backend, its slowest, and would show a visitor the wrong number).
- ✅ Astro, with the interactive pieces as Svelte components (rejected: SvelteKit prerendered with `adapter-static`; Zola; Astro with the launch post's SolidJS charts unchanged). The maintainer wants static output for search and answer engines. Astro's pages are HTML with no JavaScript unless a component asks for it, and the maintainer already runs Astro on moq.dev and Svelte elsewhere.
- ✅ Built for agents as well as people (rejected: static pages only; the same with JSON-LD on every page, since structured data has no shown effect on AI answers). Every page is also served as Markdown at its path with `.md`, `llms.txt` indexes them, and `robots.txt` welcomes AI crawlers. Nothing exists only inside a widget: an interactive piece filters or navigates content the static HTML already holds.
- ✅ Cloudflare, [deployed by CI](/quest/m2/site/deploy.md) on a merge to `main` (rejected: deployed by hand; GitHub Pages).
- ✅ The README's voice, with its headline as the site's. An agent drafts the rest from the README and the launch post, and the maintainer edits the words in the PR before they go live (rejected: a straighter voice for the site; the maintainer writes all of it).
- ✅ A section that says what rind is not (rejected: links to the caveats only; the pitch alone).
- ✅ No analytics of any kind (rejected: Cloudflare's request counts at the edge; Cloudflare Web Analytics).
- ✅ One footer line, "Built by Kixel", linking kixel.ai (rejected: no mention; a section about Kixel).
- ✅ The site goes live when it is built and is announced later, with [the correctness post](/quest/m4/correctness-announcement.md) (rejected: unpublished until the announcement; announce the site by itself; no announcement).
- ✅ m2 for the site, m4 for the announcement.

The epic's own work, once its children are on `main` and the site is up:

- Link the site from the README, set `homepage` in each published crate's `Cargo.toml`, and set the repository's homepage on GitHub.
- A social card (`og:image`) drawn from the wordmark in `admin/`, so a pasted link shows rind and not a blank box.
- Read every page as a visitor and as an agent would: each link resolves, each page's `.md` twin says what the page says, and `llms.txt` lists them all.
