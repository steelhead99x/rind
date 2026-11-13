# [M] Mutation testing runs weekly on native runners

## Goal

`mutants.yml` runs once a week over the week's changes, on native x86_64 and aarch64 runners only (the portable campaign included, forced on x86_64), and a surviving mutant still fails the run. The SDE, macOS, and qemu armv7 passes are gone, and so is their configuration in `admin/mutants` and `.cargo/mutants.toml`.

## Plan

Decided with the maintainer on 2026-11-12: ✅ slim it (rejected: drop mutation testing entirely; keep every architecture nightly).

- Its yield since it started on Nov 7 is test gaps, not bugs: [moq-dev/rind#603](https://github.com/moq-dev/rind/pull/603) added edge-case tests (twin multiplication at infinity, `Fe4` mask lanes), and [moq-dev/rind#570](https://github.com/moq-dev/rind/pull/570) made an AVX-512 GHASH bound explicit. Its cost: about 700 hosted machine-hours in its two days on PRs, 64% of rind's gated CPU on the agent hosts, armv7 shards at a 197 min median under qemu, and line-pinned exclusions that drift ([moq-dev/rind#655](https://github.com/moq-dev/rind/pull/655), [moq-dev/rind#687](https://github.com/moq-dev/rind/pull/687)).
- Keep the `portable` campaign [moq-dev/rind#651](https://github.com/moq-dev/rind/pull/651) added: it is native on x86_64 and reaches what armv7 shares with the portable backend, so it covers most of what the dropped armv7 campaign did.
- Drop the armv7 (qemu), `avx512` (SDE), and macOS DIT jobs and their `admin/mutants` modes and exclusions. The macOS DIT mutant on `Entry`'s `Drop` goes unmutated; `enables_dit_whenever_the_cpu_has_it` still tests the behavior.
- Weekly, mutating the diff since the last weekly run, on `ubuntu-latest` and `ubuntu-24.04-arm` (the Mac mini's Linux VM once it is a runner).
- Fix TESTING.md and the workflow's header to match.

## Related

- [Adapter crates' surviving mutants](/quest/m2/confidence/mutants-adapters.md) - narrowed to the adapter survivors that hide behavior, leaving `Debug` and `Display` excluded
