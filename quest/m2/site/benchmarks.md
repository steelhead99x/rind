# [M] A visitor explores the benchmarks by CPU and library

## Goal

The site has a benchmarks page that shows what BENCHMARKS.md shows, built from the same data, where a visitor picks their CPU and the libraries they care about and sees every operation. The page's static HTML and its Markdown twin already hold the numbers; the controls only filter them.

## Plan

Decided 2026-11-12 (maintainer, /quest-plan): ✅ one of the site's three showpieces.

- The data is `benchmarks/data/*.json` for the hosts and `benchmarks/data/tiers.json` for the CPU tiers, with `benchmarks/verified.toml` for the ✓ marks and `benchmarks/gaps.toml` for the known gaps. `admin/bench-report` decides which hosts and rows the report shows (`HOSTS`, `OPERATIONS`, `TIERS`, and `TIER_ROWS`). It is Python and the site's build is not, so have it write those lists as data the site reads; a second copy in the site would let the two disagree about what counts.
- The launch post's charts drew this data in SolidJS ([moq-dev/moq.dev](https://github.com/moq-dev/moq.dev), `src/components/rind/`, under MIT and Apache-2.0). Port what fits to Svelte and credit it; do not import them unchanged.
- The data files are about 800 KB together. Reduce them at build time to what the page draws, and keep each time available in the Markdown twin as a table an agent can read.
- Show where rind loses as plainly as where it wins, with what `gaps.toml` decided about it. Each entry holds either a reason or the quest that closes the gap, never both (`admin/bench-report:1070`), so the page shows the reason or links the quest by its title, as the report's gap table does. No gap over 10% is without an entry, since `load_gaps` refuses one. The colour rule is the report's: within 10% of the fastest counts as fastest.
- Let a visitor link to a view, such as one host and two libraries, so a number quoted elsewhere can point at its source.
- Say when and at which commit each host was measured, as the report does.
- The landing page's speed claim then links here.

## Required

- [The landing page builds from the repository](/quest/m2/site/landing.md) - the `site/` project this adds a page to

## Related

- [Benchmark report refresh, before rind 0.4](/quest/m2/bench/report-refresh.md) - refreshes the data this page reads
