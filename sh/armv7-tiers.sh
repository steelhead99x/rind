# shellcheck shell=bash disable=SC2034
# Sourced by sh/armv7.sh and `admin/coverage armv7`: sets the command prefix
# each of rind's armv7 tiers runs its tests under, `crypto`, `cortex_a15`, and
# `no_neon`, given the armv7 shell's qemu runner.
#
# The crypto extension's tier takes qemu's `max` CPU, which has it and so
# NEON. The NEON-denied tier hides NEON, and with it the extension, behind
# rind's software mask, leaving only the scalar paths. Each runs natively on
# an aarch64 host whose CPU can run it, such as GitHub's arm64 runners: arm64
# Linux refuses the 32-bit personality on a CPU without AArch32, such as
# Graviton 4 or a VM on Apple silicon, and under it /proc/cpuinfo lists the
# AArch32 features, which on a Raspberry Pi 4 lack the extension. The
# Cortex-A15 is ARMv7 with NEON but without the extension: its tier stays
# under qemu on every host, where an instruction from the extension faults.
native=(env -u CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUNNER)
crypto=(env QEMU_CPU=max)
cortex_a15=(env QEMU_CPU=cortex-a15)
no_neon=(env)
if [[ "$(uname -m)" == aarch64 ]] && features=$(setarch linux32 grep -m1 '^Features' /proc/cpuinfo 2>/dev/null); then
    echo "armv7: the NEON-denied tier runs natively" >&2
    no_neon=("${native[@]}")
    has_crypto=true
    for feature in aes pmull sha1 sha2; do
        [[ " ${features#*:} " == *" $feature "* ]] || has_crypto=false
    done
    if [[ "$has_crypto" == true ]]; then
        echo "armv7: the crypto extension's tier runs natively" >&2
        crypto=("${native[@]}")
    fi
fi
