# [XS] dudect is removed; Marvin stays

## Goal

`admin/timing dudect`, its dev shell, and its job in the weekly `timing` workflow are gone. The Marvin toolkit's run against RSA decryption stays, and TESTING.md and AUDIT.md describe what remains.

## Plan

Decided with the maintainer on 2026-11-18 (/quest-plan): ✅ drop dudect (rejected: keep it). The reason is noise, not cost (about an hour a day). It is statistical on shared runners, no commit in the history shows it finding anything, and ctgrind, BINSEC, `admin/ct-sde`, `admin/ct-qemu`, and `admin/ct-vartime` check, deterministically, the leaks rind's constant-time rule names: secret-dependent branches, memory indexes, and the variable-time instructions `admin/ct-vartime` lists. What is lost is a measurement on real hardware, which could catch a timing effect outside those models, such as a microarchitectural one; dudect's noise on shared runners kept it from catching one in practice. Marvin stays because RSA decryption's timing is where real attacks have landed, and it measures `rind::rsa`'s whole decryption on real hardware.

- Remove whatever only dudect uses: its flake shell, harness code, and `timing.yml` steps. Keep `rind-timing` for Marvin, and keep the cycle counter `marvin.rs` takes from its `dudect` module (`ticks`, `ticks_per_second`), moved out of that module.
- `timing.yml`'s pull-request `smoke` job runs `admin/timing dudect --list` in the `.#timing` shell, the only pull-request check of that shell. Replace it with one that still enters `.#timing` and builds what Marvin runs, so a broken shell is caught before the weekly run.
