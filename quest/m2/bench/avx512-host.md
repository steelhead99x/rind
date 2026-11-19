# [S] A contributor-held AVX-512 host measures the gated AVX-512 kernels

## Goal

Keep rules that need an AVX-512 core GitHub's runners do not reliably provide are settled on a contributor-held AVX-512 host (chip recorded at measurement time), hosted by @steelhead99x and run by the maintainer. Each kernel such a rule gates is turned on where it wins on the cores its rule names and stays off where it does not, with the numbers published either way.

## Plan

- First, [Argon2id's AVX-512 fill](/quest/m4/protocols/argon2-simd.md): its rule keeps libsodium's AVX-512 layout only where it beats the AVX2 port on Zen 4 or 5 and on Sapphire Rapids. So far it has been measured only on a Granite Rapids GitHub runner, at 1.29x the AVX2 port at 16 MiB and 1.22x at 64 MiB ([run 44019772236](https://github.com/steelhead99x/rind/actions/runs/44019772236)). That is neither core the rule names, so the gate stays off.
- The host's chip decides which half of a rule it can close: a Zen 4 or 5 closes the AMD half, a Sapphire Rapids the Intel half, and an Intel core that lowers its clock for 512-bit vectors is the only kind that can measure [the 256-bit rule](/quest/m2/speed/avoid-zmm.md). Record the chip with the first run, and say in each result which rule it closes and which it leaves open. `fedora` (Zen 5) and GitHub's EPYC runners may cover the AMD half first; then this host adds whichever half they leave.
- Acceptance, for each kernel measured:
  - `lscpu` (model name, family, model, stepping, and the `avx512*`, `vaes`, and `vpclmulqdq` flags) recorded beside the numbers.
  - The kernel and its 256-bit sibling timed in interleaved rounds of one binary, at the sizes its rule names, against the fastest other library where one has the primitive (RustCrypto's `argon2` for Argon2id).
  - Results published as a labelled set in [rind-results](https://github.com/steelhead99x/rind-results), with the rind commit they measured.
  - The gate flipped, in the kernel's own quest and PR, only if its keep rule holds on every core it names; otherwise the numbers go in that quest's Plan and the gate stays.
- Candidate follow-ups, each added to its own quest when this host's chip can settle it:
  - [The 256-bit rule](/quest/m2/speed/avoid-zmm.md) was adopted unmeasured; on a downclocking Intel core, time AES-GCM on one core while another runs scalar work, with and without the rule, as its Plan names.
  - ML-KEM-768's Keccak lane sharing, which [kixel-ai/rind#812](https://github.com/kixel-ai/rind/pull/812) merged (its quest is finished and gone), keeps each port only where it measures faster; an AVX-512 host would show whether that holds on other cores.
  - AES-GCM's 512-bit kernel from 2 KB (`AVX512_KERNEL_MINIMUM_CIPHER_LEN`) and ML-KEM's 8-way sampler, the two zmm routines the 256-bit rule's inventory found, checked against their 256-bit siblings on the host's core.
  - X25519 and Ed25519 ([kixel-ai/rind#845](https://github.com/kixel-ai/rind/pull/845)) and RSA ([kixel-ai/rind#814](https://github.com/kixel-ai/rind/pull/814)) on AVX-512 were timed against pyca/verified-garbage on Zen 4 only, and their quests are finished and gone; an Intel AVX-512 core would show whether the switch holds there.
- The host is never named here or in a PR beyond its chip.

## Waiting

- Maintainer: approve using a contributor-held AVX-512 host for these measurements, before it is used. Options: approve (recommended: it settles rules no reachable host can), approve for Argon2id only, or decline and rely on `fedora` and GitHub's runners. Once approved, the host is the maintainer's to run; @steelhead99x helps. An agent cannot decide whether rind accepts a contributor-held host. Check for the maintainer's answer on this quest's PR.
- steelhead99x: the host is hosted by @steelhead99x and run by the maintainer. After approval, helps with whatever the maintainer wants, including recording `lscpu`. Check with the recorded `lscpu` output.

## Related

- [Argon2id fills memory with the fastest kernel on aarch64 and AVX-512](/quest/m4/protocols/argon2-simd.md) - the first keep rule this measures
- [The Mac mini joins the benchmark report](/quest/m2/bench/mac-mini.md) - the maintainer-held host this mirrors
- [fedora joins the benchmark report as its AVX-512 host](/quest/m2/bench/fedora.md) - the maintainer's Zen 5 host, which covers part of the same rules
