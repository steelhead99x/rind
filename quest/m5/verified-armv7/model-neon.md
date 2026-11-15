# [XL] The AArch32 model covers NEON and the crypto extension

## Goal

The AArch32 model in `thirdparty/s2n-bignum/aarch32/` holds the NEON register file and decodes, and cosimulates against qemu-arm, every Advanced SIMD and ARMv8 crypto-extension instruction armv7's assembly in `low/arm/` runs, so [armv7's assembly](/quest/m5/verified-armv7/assembly.md) can prove its NEON and crypto routines on it.

## Plan

- State: Q0-Q15, with D0-D31 as their halves, since A32 writes a D register without touching its pair; nothing armv7's assembly runs uses the VFP S registers.
- Instructions, from a scan of `low/arm/{aws_lc,boringssl,openssl}/*.s`: `VLD1`, `VST1`, `VLDM`, `VSTM`, `VLDR`, `VSTR`, `VPUSH`, and `VPOP`; `VMOV`, `VDUP`, `VEXT`, `VTBL`, `VTRN`, `VZIP`, `VSWP`, `VREV32`, and `VREV64`; `VADD`, `VSUB`, `VAND`, `VBIC`, `VORR`, `VEOR`, and `VBSL`; `VSHL`, `VSHR`, `VSHLL`, `VSHRN`, `VSLI`, and `VSRI`; `VMUL`, `VMULL` (`.p64` included), and `VMLAL`. The crypto extension's `AESE`, `AESD`, `AESMC`, `AESIMC`, `SHA1*`, and `SHA256*` appear only as `.byte` and `.inst`, so decode those words from the routines' bytes, as `admin/prove` extracts them.
- Where an operation is the same as AArch64's, such as AES rounds, SHA-2 steps, and polynomial multiplication, state it with the definitions s2n-bignum's aarch64 model already has.
- The executor transports Q0-Q15 too; qemu-arm's `-cpu max` runs the crypto extension, which `cortex-a15` lacks.

## Required

- [The AArch32 model covers armv7's integer assembly](/quest/m5/verified-armv7/model.md) - the decoder and state this extends, so the two do not edit `decode.ml` at once
