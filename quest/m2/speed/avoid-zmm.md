# [S] Intel cores that downclock for 512-bit vectors run the 256-bit kernels

## Goal

On the Intel cores that lower their clock when 512-bit registers are in use, rind picks its 256-bit kernels wherever it has a 512-bit one, if a measurement shows the 512-bit kernels slow other work there, so a server that mixes rind with other work does not slow the other work down.

## Plan

Decided 2026-11-15 (maintainer, closing [kixel-ai/rind#788](https://github.com/kixel-ai/rind/pull/788)): ✅ measure first; rind adds no unmeasured complexity for performance. This replaces the 2026-11-12 decision to adopt the rule unmeasured. No host here can measure it: `fedora` is Zen 5, `nixos` Zen 3, and `desktop` Arrow Lake without AVX-512, so none downclocks, and SDE emulates instructions, not frequency.

- The measurement: on an affected core, AES-GCM throughput, and the throughput of scalar work on the same core and a sibling core while AES-GCM runs, with the 512-bit kernels and with the 256-bit ones. Repeat for ML-KEM key generation and `cipher::ChaCha20`. If the 512-bit kernels cost the scalar work more than they gain, adopt the rule; if not, delete this quest and say in PLATFORMS.md that rind measured and kept them.
- The implementation is on branch `quest/m2/speed/avoid-zmm` at 100cdf282, as #788 described it: a `SLOW_ZMM` bit from `cpuid` leaf 1 that `HaveAvx512ForAesGcm` and `HaveAvx512ForMlKem` refuse, `rind-cpuid` and the `admin/x86-cpus` scans updated, a Check Ice Lake step in `x86-cpu.yml`, and PLATFORMS.md. Merge main into it rather than rewrite it. It predates `cipher::ChaCha20`'s `vg_chacha20_apply_avx512vl` ([kixel-ai/rind#811](https://github.com/kixel-ai/rind/pull/811)), which computes on zmm registers despite its name and has `vg_chacha20_apply_avx2` as its 256-bit sibling, so the rule must cover it too.
- The list, as #788 read it: Intel family 6, models 0x55, 0x6a, 0x6c, 0x7d, 0x7e, 0x8c, 0x8d (85, 106, 108, 125, 126, 140, 141: Skylake-SP through Tiger Lake), from BoringSSL's `CRYPTO_cpu_avoid_zmm_registers` (`crypto/cpu_intel.cc`, google/boringssl@8f2554dc344d403fd6d628773d39637c323eb801), plus 0x9d (157, Ice Lake NNPI) from Linux's `zmm_exclusion_list` (`arch/x86/kernel/cpu/intel.c`, torvalds/linux@23c62304dde29abe92013d85910d03a77dada35d). aws-lc has no such rule (aws/aws-lc@5ed12cce0fd4453f2f63300d44325ed14f845d6f), so adopting it is one place rind follows BoringSSL instead.
- Redo the inventory: count a routine only if an instruction or intrinsic in it is 512 bits wide, not for `out("zmmN")` clobber lists. #788 found AES-GCM and ML-KEM's 8-way sampler, and RSAZ's IFMA routines (`rsaz_avx512.rs`) use ymm registers only. Since then VG's AVX-512 routines landed as byte-encoded assembly that a text search cannot read, so disassemble each under `rind/src/low/x86_64/vg/` that runs behind an AVX-512 check (`HaveAvx512Vl`, `HaveAvx512ForVgMlKem`, `HaveAvx512ForRsa`, the IFMA P-256 and Ed25519 ones, and `HaveIfmaForVgChaCha20Poly1305`, whose 256-bit sibling is aws-lc's AVX2 one pass) to count it.

## Waiting

- Maintainer: an Ice Lake or Tiger Lake host an agent can reach over SSH, idle, with frequency and performance counters visible, such as an AWS `c6i.metal` (Ice Lake server) for an hour, or such a machine of your own. Skylake-SP and Cascade Lake do not do: they lack the VAES, VPCLMULQDQ, and VBMI2 that the AES-GCM and ML-KEM 512-bit kernels need. An agent holds no paid cloud account to rent one. GitHub-hosted runners were considered and rejected: some report Ice Lake Xeons, but they are shared VMs whose clock rind cannot observe or hold still. Check with `ssh <host> "grep -m1 '^model[[:space:]]' /proc/cpuinfo"` printing 106, 108, 125, 126, 140, or 141 (decimal), and `ssh <host> "grep -m1 '^flags' /proc/cpuinfo | tr ' ' '\\n' | grep -cxE 'avx512bw|avx512vl|vaes|vpclmulqdq|avx512vbmi|avx512_vbmi2|avx512ifma'"` printing 7, since a virtual CPU can mask some of the features the 512-bit kernels' checks ask for.

## Related

- [VAES AES-GCM](/quest/m4/verified/aes-gcm-x86-vaes.md) - proves the kernels this chooses between
