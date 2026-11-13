# [S] Mutation testing runs weekly on native runners

## Goal

`mutants.yml` runs once a week over the week's changes, on native x86_64 and aarch64 runners only (the portable campaign included, forced on x86_64), and a surviving mutant still fails the run. The macOS DIT campaign is gone, and so is its configuration in `admin/mutants`.

## Plan

Decided with the maintainer on 2026-11-12: ✅ slim it (rejected: drop mutation testing entirely; keep every architecture nightly).

- Its yield since it started on Nov 7 is test gaps, not bugs: [moq-dev/rind#603](https://github.com/moq-dev/rind/pull/603) added edge-case tests (twin multiplication at infinity, `Fe4` mask lanes), and [moq-dev/rind#570](https://github.com/moq-dev/rind/pull/570) made an AVX-512 GHASH bound explicit. Its cost: about 700 hosted machine-hours in its two days on PRs, and line-pinned exclusions that drift ([moq-dev/rind#655](https://github.com/moq-dev/rind/pull/655), [moq-dev/rind#687](https://github.com/moq-dev/rind/pull/687)).
- [kixel-ai/rind#717](https://github.com/kixel-ai/rind/pull/717) already dropped the armv7 (qemu) and `avx512` (SDE) campaigns, with their `admin/mutants` modes and exclusions, and excluded the AVX-512-only and armv7-only code the remaining campaigns list.
- Drop the macOS DIT job (`mutants.yml`'s `macos` campaign) and the `aarch64-apple-darwin` campaign in `admin/mutants`. The DIT code goes unmutated; `enables_dit_whenever_the_cpu_has_it` still tests the behavior. The Linux aarch64 campaign lists the Apple-only DIT code, such as `rind/src/low/aarch64/cpu.rs`'s `dit` module, under `cfg(target_vendor = "apple")`, whose mutants only the macOS campaign caught: exclude those in `.cargo/mutants.toml` with that reason, or the weekly run reports them as survivors. Check the `Dit`, `Entry`, and `enter_cpu_state` mutants the macOS campaign's `--re` names the same way.
- Weekly, mutating the diff since the last weekly run, on `ubuntu-latest` and `ubuntu-24.04-arm` (the Mac mini's Linux VM once it is a runner). Keep the dispatched whole campaigns and their `shards` job; a weekly run sizes its shards as a dispatch does.
- Fix the workflow's header to match.

## Related

- [Adapter crates' surviving mutants](/quest/m2/confidence/mutants-adapters.md) - narrowed to the adapter survivors that hide behavior, leaving `Debug` and `Display` excluded
