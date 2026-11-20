# [XL] rind's HOL Light proofs are ported to Lean

## Goal

Every proof in `proofs/hol-light/` is a Lean theorem on pyca/verified-garbage's instruction models, functional correctness and a leakage contract alike, about the bytes rind's build emits. Each axiom in `proofs/Rind/<Arch>/` that restated one restates the Lean theorem instead, still one per wrapper under the composition rule, as [the trial](/quest/m2/lean-assembly-trial.md) does for `compress_hw`. `admin/prove hol-light`, its CI jobs, and the DMTCP session tooling go. Upstream s2n-bignum theorems rind imports stay axioms, checked by `admin/prove bytes`.

## Plan

Decided with the maintainer on 2026-11-18 (/quest-plan): ✅ port the existing HOL Light proofs to Lean in m5, once the trial shows the cost (rejected: keep them in HOL Light forever; port them before measuring). Why: the goal is one Lean trust base for rind's own proofs, and porting removes the slowest jobs in `prove`, about 95 minutes of HOL Light per pull request run on 2026-11-17.

- Wait for [the trial](/quest/m2/lean-assembly-trial.md): its PR resizes this quest and may split it into an epic, one child per architecture or proof family.
- What the fork of s2n-bignum still carries for rind's own proofs, such as the x86 model additions, the AArch32 model, and `common/chacha20poly1305.ml` with its `hol_light_specs` load, leaves with the last proof that needs it. Its upstream code and theorems rind imports stay.
- armv7's proofs run on the fork's AArch32 model. VG has an ARMv7 model too, but rind vendors only its x86_64 and aarch64 models: vendor ARMv7's through `admin/import-vg-models` and cosimulate it against qemu-arm, as `admin/prove cosim` does today.
- A routine the trial's PR and the maintainer kept in HOL Light is ported here too: the exceptions last only until this port, so nothing needs `admin/prove hol-light` once it goes. armv7's proofs are among them.
- Each ported proof keeps every check its HOL Light route had, as [the trial](/quest/m2/lean-assembly-trial.md) does: the build's instruction bytes, relocations, and statics (such as x86_64 SHA-256's `K` table) are checked against the theorem, which keeps the HOL Light theorem's frame (return address, the registers and memory it may change), and `admin/prove vg` cosimulates every instruction the routine runs before its old model check retires.
- Keep CI's checks as the jobs go: move `admin/prove bytes`, today a step of `hol-light-aarch64`, to a job that stays, and retire `admin/prove cosim` and its job only once no proof rests on the AArch32 model or the fork's x86 additions it also checks, and VG's cosimulation covers armv7.
- Retire each routine's dedicated constant-time harness as its leakage contract lands, as the trial decided, once a check that stays traces its Rust wrapper on that path, as [the leakage-contracts quest](/quest/m2/verified-garbage/leakage-contracts.md) requires for VG's routines.

## Required

- [aarch64 SHA-256 on the SHA-2 instructions is proven in Lean, constant time included](/quest/m2/lean-assembly-trial.md) - measures the cost and sets the route
