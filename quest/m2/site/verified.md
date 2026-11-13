# [S] A visitor sees which operations run proven code on which CPU

## Goal

The site has a page that maps every operation the benchmark report times to the CPUs where its whole computation is covered by a published formal proof, with a link to each proof, and shows the same for the other libraries. An operation with no proof yet is shown as plainly as one with.

## Plan

Decided 2026-11-12 (maintainer, /quest-plan): ✅ one of the three showpieces. The maintainer's next announcement is about correctness, which the launch post did not cover, so this page is what that post will point at.

- `benchmarks/verified.toml` holds the proofs: each entry names the library, the operations, optionally the architecture and the CPU features it needs or must lack, whose proof it is, and its link. Its header says what earns a ✓ and what does not; put that rule on the page in a few sentences, since the mark means nothing without it.
- That file lists only what is proven, so it cannot show a gap. The rows come from `admin/bench-report`'s `OPERATIONS` (`admin/bench-report:181`), which is every operation the report times, and a cell with no matching entry is the gap.
- A column is a CPU, and a cell is what `proof_for` (`admin/bench-report:930`) returns for it: the entry whose architecture, OS, and CPU features that CPU satisfies. An entry naming no architecture covers every column, as libcrux's do. The report's hosts each record their features (`rind_cpu.cpuid` in `benchmarks/data/<host>.json`), so they can be columns today. The CPU tiers of the nightly bench cannot yet: `tiers.json` records each runner's model name, not its features. Draw against the hosts, or record a feature set per tier first; say in the PR which, and why.
- `proof_for` matches an entry to a CPU and does not ask whether the library ran there. graviola refuses to start on `ovh-iad`, which lacks ADX, and the host file says so (`refused`), and an operation a library does not offer has no time in `results`. Give such a cell its own mark, "does not run here" or "not offered", so it reads as neither proven nor a gap.
- `admin/bench-report` is Python and the site's build is not. Have it write the resolved grid as data the site reads, so the matching rule is written once. The same goes for which hosts [the benchmark explorer](/quest/m2/site/benchmarks.md) shows.
- BENCHMARKS.md's Verified code section lists the entries from the same file, and its host tables carry the marks. The page must agree with both.
- The gaps are then visible as gaps, and the grid fills in by itself as [the proofs](/quest/m4/verified/README.md) land, with no edit to the site.
- Say what the proofs trust and what they leave out (DER parsing, randomness), from the file's own header and `proofs/README.md`.
- The landing page's "verified where it counts" claim then links here.

## Required

- [The landing page builds from the repository](/quest/m2/site/landing.md) - the `site/` project this adds a page to

## Related

- [Every rind path is proven, with the smallest trust base](/quest/m4/verified/README.md) - the proofs that fill the map in
