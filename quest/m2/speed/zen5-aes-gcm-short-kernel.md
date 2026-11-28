# [S] AES-GCM on Zen 5 runs BoringSSL's 512-bit kernel from 256 bytes

## Goal

On Zen 5, AES-GCM seals and opens from 256 bytes to 2 KB run BoringSSL's 512-bit kernel (`aes_gcm_{enc,dec}_update_vaes_avx512`) instead of rind's AVX-512 by-16 path, wherever the kernel is faster, without moving the 2 KB threshold Intel's cores were tuned at.

## Plan

Found by [kixel-ai/rind#1139](https://github.com/kixel-ai/rind/pull/1139), which timed both under rind's glue on `fedora` (Ryzen 9 9950X), min of 20000 interleaved rounds, a 13-byte AAD to 512 bytes and 32 above:

- With `AVX512_KERNEL_MINIMUM_CIPHER_LEN` at 256 instead of 2048, seals at 1350 B took 0.81 (AES-128), 0.78 (AES-192), and 0.67 (AES-256) of the by-16 path's time, and opens 0.88 to 0.90; from 512 B to 1536 B, seals 0.70 to 0.90 and opens 0.75 to 1.00. At 256 B, AES-128 took 1.04 both ways, and AES-192 and AES-256 0.85 to 0.96. This is the `fedora` gap `benchmarks/gaps.toml` records at 1350 B, where pyca/verified-garbage's API sealed AES-256 in 0.89 of rind's time: the kernel beats VG's code there too.
- Make the threshold a property of the table, picked once at key setup by CPU family as `HaveAvx512ForAesGcm::vg` picks VG's code, keeping 2048 on Intel and on Zen 4 unless a Zen 4 measurement says otherwise. Re-measure 256 to 2047 bytes on Zen 5 to set the threshold; it may be 512 for AES-128.
- `proofs/Rind/X86_64/AesGcmAvx512.lean` proves the tier below 2 KB by the by-16 and by-8 paths; a threshold that varies moves the kernel's proof obligation, which [the VAES quest](/quest/m4/verified/aes-gcm-x86-vaes.md) owns, below 2 KB on Zen 5. State the theorems over the table's threshold rather than the constant.

## Related

- [VAES AES-GCM](/quest/m4/verified/aes-gcm-x86-vaes.md) - proves the kernels this chooses between
