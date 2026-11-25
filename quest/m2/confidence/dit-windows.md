# [S] rind sets DIT on Windows and the BSDs' aarch64 cores

## Goal

On aarch64 Windows, FreeBSD, and OpenBSD, rind finds FEAT_DIT where the core has it, such as Qualcomm's Oryon in Snapdragon X laptops, and sets DIT around each secret call as it does on Linux, Android, and Apple's platforms.

## Plan

Rust's `is_aarch64_feature_detected!("dit")` reports DIT only on Linux, Android, and Apple's platforms (checked in std_detect for Rust 1.98: Windows asks `IsProcessorFeaturePresent`, which has no DIT flag, and the BSDs parse ID_AA64PFR0_EL1 without its DIT field), so `low/aarch64/cpu.rs`'s `detect` never sets DIT elsewhere and PLATFORMS.md says so.

- Windows publishes each core's ID_AA64PFR0_EL1 as the registry value `CP 4020` under `HKLM\HARDWARE\DESCRIPTION\System\CentralProcessor\<n>`; DIT is bits 51:48. Read it there, or propose the field upstream to std_detect and wait for a Rust release. Recommendation: upstream first, since rind has no Windows FFI today and a registry read is weight for one bit.
- FreeBSD and OpenBSD already read ID_AA64PFR0_EL1 in std_detect; adding DIT's field there is a one-line upstream change.
- `enables_dit_whenever_the_os_reports_it` runs only on Unix, which reports the illegal instruction as a signal; on Windows it needs a structured exception or the registry value to compare against.
- First show DIT is worth it on these cores: on an aarch64 Windows or BSD host with FEAT_DIT, such as a Snapdragon X laptop, time rind's secret paths with DIT set and clear, both its cost and whether any instruction rind runs varies with data when it is clear. If DIT changes nothing measurable there, delete this quest instead of detecting it.

Decided 2026-11-24 (maintainer, /quest-run): ✅ measure first, then choose between the registry read and upstream detection (rejected: propose upstream now; read the registry now; drop the quest).

## Waiting

- Maintainer: an aarch64 Windows or BSD host with FEAT_DIT that agents can reach over SSH. Check by SSHing to it and reading ID_AA64PFR0_EL1's DIT field.
