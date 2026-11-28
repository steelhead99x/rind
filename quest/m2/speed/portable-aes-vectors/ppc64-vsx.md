# [L] The portable backend's AES bitslices eight blocks in VSX on powerpc64le

## Goal

On `powerpc64le-unknown-linux-gnu`, whose POWER8 baseline enables AltiVec and VSX at compile time, `aes_nohw.rs` bitslices eight blocks a pass in 128-bit vector words. It replaces the four-block `u64` path only where a measurement on POWER hardware or an equivalent shows it faster. Big-endian `powerpc64` and 32-bit `powerpc`, whose targets enable no vectors, keep their paths.

## Plan

- `core::arch::powerpc64`'s vector intrinsics are unstable (`stdarch_powerpc`), and stable Rust has no `asm!` vector-register class there, so decide the route first: wait for stabilization, write the word module as `asm!` over general registers that LLVM can't vectorize, or refuse the quest. Record what is found in this Plan.
- The SSE2 `word` module is the template. VSX's `vsldoi` gives the byte shifts and `vsrw`/`vslw` the row rotations. Its loads are big-endian element order even on powerpc64le unless they use `lxvd2x` with a permute or `lxvb16x` (POWER9), so check the byte order of the compact form.
- Measure on a POWER8 or later host, which no report host has. qemu's times say nothing about hardware, so without such a host this stays unmerged, and `## Waiting` names who could provide one.
- Constant time: valgrind's ppc64le port runs ctgrind; VSX bitwise ops and constant shifts take no secret-dependent time.
