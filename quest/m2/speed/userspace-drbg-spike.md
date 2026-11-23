# [M] Benchmark-gate a fork-safe thread-local userspace DRBG in rind::mid::rng

## Goal

Measure `getrandom::fill` against a fork-safe (`getpid()` + `pthread_atfork`) thread-local userspace DRBG across macOS, older Linux kernels, and modern vDSO Linux kernels, and land the thread-local DRBG (non-FIPS `std` builds only, wiped on thread exit) if and only if it delivers at least a 5% wall-clock speedup on hedged ECDSA signing or TLS handshakes.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ benchmark-gate first and land a fork-safe thread-local userspace DRBG (non-FIPS `std` only, wiped on drop) only where it wins by at least 5% on hedged ECDSA or handshakes (rejected: unconditional userspace DRBG; dropping the idea without measuring).

- **Measurement spike first**:
  - Benchmark `rind/src/mid/rng.rs` (`getrandom::fill` per call) vs. a prototype thread-local userspace DRBG (for example ChaCha20-based fast-key-erasure RNG with automatic reseed threshold) on:
    - macOS (Apple Silicon, `CCRandomGenerateBytes` / `getentropy`),
    - Linux without `vgetrandom` vDSO (older kernel),
    - Linux with modern `vgetrandom` vDSO.
  - Measure both microbenchmarks (32-byte RNG fills) and end-to-end workloads (hedged ECDSA P-256/P-384 signing, ML-KEM/X25519 keygen, and `rustls` full handshakes).
- **Decision gate**:
  - If the win on hedged ECDSA signing or TLS handshakes is `< 5%` across all target OS configurations, record the measurements in the PR / `quest/m2/speed/README.md` and close without adding userspace DRBG complexity.
  - If it wins by `>= 5%` on at least one target OS class (e.g. macOS or non-vDSO Linux), land it cleanly for non-FIPS `std` builds (optionally scoped to the OSes where it wins if vDSO Linux is already neck-and-neck).
- **Safety requirements if landed**:
  - Fork safety: combine `pthread_atfork` with a `getpid()` check (or `MADV_WIPEONFORK` where supported plus `getpid()` fallback) so raw `clone()`/`SYS_fork` can never share RNG state across processes.
  - Fast key erasure / backtracking resistance on every draw and explicit wiping of thread-local state on thread exit (`Drop`), verified with `zeroing.rs`, TSan, and fork tests.
  - FIPS builds (`rind-fips`) continue using the FIPS DRBG untouched.
