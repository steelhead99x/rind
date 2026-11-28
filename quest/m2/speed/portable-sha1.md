# [S] The portable backend's SHA-1 is as fast as aws-lc's integer code

## Goal

On the weekly bench's portable row, SHA-1 and HMAC-SHA-1 take no more than aws-lc's time from 1200 B up, closing the 1.11 to 1.24× gap that `benchmarks/gaps.toml`'s portable SHA-1 entry records, without slowing armv7 without NEON, which already runs aws-lc's integer `sha1_block_data_order_nohw`.

## Plan

Planned 2026-11-27 (owner: close the top five benchmark gaps, overriding the entry's reason that SHA-1 is too rare on targets without assembly to speed up).

- Done in [steelhead99x/rind#348](https://github.com/steelhead99x/rind/pull/348): the portable `generic::sha1` writes out all 80 rounds, so every schedule index is a constant, as aws-lc's integer code does. It passes `admin/ctgrind` on the portable backend, where `hmac::tests::secret_key_and_message` marks the key and message secret, and a differential test against RustCrypto's block function. On a shared VM it ran about 1,355 instructions a block against aws-lc's 1,442.
- What remains: the weekly bench's portable tier re-measures `sha1/*` and `hmac-sha1/*`. If both hold at or under 1.0× from 1200 B up, the report refresh removes the gap's entry and this quest. If either does not, the next step goes here.
- Also unmeasured: the unrolled body on riscv64 under QEMU, which the plan named (the writer's host had no riscv target), and its size on Xtensa, whose small instruction cache keeps SHA-384/512 rolled (ALGORITHMS.md). If the Xtensa block grew much, keep a rolled body there, as `sha512_rolled` does.
